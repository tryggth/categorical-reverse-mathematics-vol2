#!/usr/bin/env python3
"""Master verification gatekeeper: DuckDB + 2LTT KernelArena + Mathlib AuditEnv + Royal Octavo TeX."""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import re
import subprocess
import sys
import tomllib
from pathlib import Path
from typing import Any

import duckdb

from compile_db import LOCK_PATH, REPO_ROOT, compile_network
from emit_lean import emit_all, parse_and_map_lean_diagnostics
from emit_tex import BUILD_TEX_DIR, emit_claims_ledger, emit_monograph, load_context, resolve_tex_error
from slice_course import emit_course_pack

LOGS_DIR = REPO_ROOT / "logs"
BUILD_DIR = REPO_ROOT / "build"
MANIFEST_PATH = REPO_ROOT / "manifest.toml"
LAKE_BIN = "/home/tryggth2009/.elan/bin/lake"
KERNEL_ARENA_DIR = REPO_ROOT / "kernel_arena"
MATHLIB_VOL2_DIR = REPO_ROOT / "mathlib_vol2"

TEX_ERROR_RE = re.compile(r"^(.+\.tex):(\d+):\s*(.*)$")
TEX_BAD_PATTERNS = (
    "Undefined control sequence",
    "LaTeX Warning: Reference",
    "There were undefined references",
    "Citation",
    "Emergency stop",
    "! ",
)


def run_logged(cmd: list[str], log_path: Path, cwd: Path | None = None, env: dict[str, str] | None = None) -> tuple[int, str]:
    log_path.parent.mkdir(parents=True, exist_ok=True)
    proc = subprocess.run(
        cmd,
        cwd=str(cwd or REPO_ROOT),
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    combined = proc.stdout + ("\n" + proc.stderr if proc.stderr else "")
    log_path.write_text(combined, encoding="utf-8")
    return proc.returncode, combined


def run_kernel_arena_checks(compile_report: dict[str, Any]) -> tuple[bool, dict[str, Any]]:
    con = duckdb.connect(str(BUILD_DIR / "vol2.duckdb"), read_only=True)
    rows = con.execute(
        "SELECT id, cert_path FROM nodes WHERE formal_pkg = 'kernel_arena' ORDER BY id"
    ).fetchall()
    con.close()

    build_rc, _ = run_logged(
        [LAKE_BIN, "--dir", str(KERNEL_ARENA_DIR), "build"],
        LOGS_DIR / "gate_kernel_arena_build.log",
    )
    results: dict[str, Any] = {"build_ok": build_rc == 0, "certs": {}}
    all_ok = build_rc == 0
    for nid, cert_rel in rows:
        abs_cert = str((REPO_ROOT / cert_rel).resolve())
        slug = nid.replace(":", "_")
        rc, out = run_logged(
            [LAKE_BIN, "--dir", str(KERNEL_ARENA_DIR), "exe", "kernel-arena", "verify", abs_cert],
            LOGS_DIR / f"gate_ka_{slug}.log",
        )
        cert_sha = json.loads((REPO_ROOT / cert_rel).read_text(encoding="utf-8"))["sha256_arena"]
        results["certs"][nid] = {
            "cert_path": cert_rel,
            "sha256_arena": cert_sha,
            "passed": rc == 0,
            "output": out.strip(),
        }
        if rc != 0:
            all_ok = False
    return all_ok, results


def run_mathlib_build_and_audit() -> tuple[bool, list[dict[str, Any]], dict[str, Any] | None]:
    rc_build, out_build = run_logged(
        [LAKE_BIN, "--dir", str(MATHLIB_VOL2_DIR), "build", "HomotopyCRM", "audit_env"],
        LOGS_DIR / "lake_build.log",
    )
    mapped_diags = parse_and_map_lean_diagnostics(out_build)
    if rc_build != 0:
        return False, mapped_diags, None

    audit_manifest = str((BUILD_DIR / "audit_nodes_manifest.json").resolve())
    rc_audit, out_audit = run_logged(
        [LAKE_BIN, "--quiet", "--dir", str(MATHLIB_VOL2_DIR), "exe", "audit_env", audit_manifest],
        LOGS_DIR / "audit_env.raw.log",
    )
    audit_json: dict[str, Any] | None = None
    json_start = out_audit.find("{")
    if json_start >= 0:
        try:
            parsed, _ = json.JSONDecoder().raw_decode(out_audit[json_start:])
            if isinstance(parsed, dict):
                audit_json = parsed
                (LOGS_DIR / "audit_env.json").write_text(
                    json.dumps(audit_json, indent=2) + "\n", encoding="utf-8"
                )
        except json.JSONDecodeError:
            audit_json = None
    if audit_json is None:
        (LOGS_DIR / "audit_env.json").write_text(out_audit, encoding="utf-8")
    audit_ok = (rc_audit == 0) and bool(audit_json and audit_json.get("ok"))
    return audit_ok, mapped_diags, audit_json


def compile_pdf(stem: str, tex_map_name: str | None = None, run_index: bool = False) -> dict[str, Any]:
    env = os.environ.copy()
    env["TEXINPUTS"] = f".:{REPO_ROOT / 'tex'}:{REPO_ROOT}:"
    env["BIBINPUTS"] = f".:{REPO_ROOT}:"

    def _pdflatex(pass_no: int) -> tuple[int, str]:
        return run_logged(
            ["pdflatex", "-interaction=nonstopmode", "-file-line-error", f"{stem}.tex"],
            LOGS_DIR / f"tex_{stem}_pass{pass_no}.log",
            cwd=BUILD_TEX_DIR,
            env=env,
        )

    rc1, _ = _pdflatex(1)
    rc_bib, bib_out = run_logged(
        ["bibtex", stem],
        LOGS_DIR / f"bibtex_{stem}.log",
        cwd=BUILD_TEX_DIR,
        env=env,
    )
    if run_index and (BUILD_TEX_DIR / f"{stem}.idx").exists():
        run_logged(
            ["makeindex", f"{stem}.idx"],
            LOGS_DIR / f"makeindex_{stem}.log",
            cwd=BUILD_TEX_DIR,
            env=env,
        )
    rc2, _ = _pdflatex(2)
    rc3, log3 = _pdflatex(3)

    pdf_path = BUILD_TEX_DIR / f"{stem}.pdf"
    diagnostics: list[dict[str, Any]] = []
    for line in log3.splitlines():
        m = TEX_ERROR_RE.match(line)
        if m:
            fn, ln_s, msg = m.groups()
            nid = resolve_tex_error(tex_map_name, int(ln_s)) if tex_map_name else None
            diagnostics.append({"file": fn, "line": int(ln_s), "message": msg, "node_id": nid})
        elif any(pat in line for pat in TEX_BAD_PATTERNS):
            if (
                "There were undefined references" in line
                or "There were undefined citations" in line
                or "LaTeX Warning: Reference" in line
                or "LaTeX Warning: Citation" in line
                or line.startswith("! ")
            ):
                diagnostics.append({"file": f"{stem}.log", "line": 0, "message": line.strip(), "node_id": None})

    bib_warnings = [ln for ln in bib_out.splitlines() if "Warning--" in ln or "I found no" in ln or "I couldn't" in ln]
    has_undef_ref = ("There were undefined references" in log3) or ("There were undefined citations" in log3)
    passed = (
        rc1 == 0
        and rc_bib == 0
        and rc2 == 0
        and rc3 == 0
        and pdf_path.exists()
        and not has_undef_ref
        and len(bib_warnings) == 0
        and not any(d["line"] > 0 for d in diagnostics)
    )
    return {
        "stem": stem,
        "pdf": str(pdf_path.relative_to(REPO_ROOT)),
        "passed": passed,
        "bibtex_warnings": bib_warnings,
        "has_undefined_refs": has_undef_ref,
        "diagnostics": diagnostics,
    }


def write_sync_digest(compile_report: dict[str, Any], gate_report: dict[str, Any]) -> None:
    with MANIFEST_PATH.open("rb") as fh:
        manifest = tomllib.load(fh)
    tainted = compile_report["tainted_nodes"]
    dirty = compile_report["body_dirty_nodes"]
    clean = compile_report["clean_nodes"]
    ka_res = gate_report.get("kernel_arena", {}).get("certs", {})
    audit_nodes = {n["id"]: n for n in (gate_report.get("audit_env") or {}).get("nodes", [])}
    pdfs = gate_report.get("pdfs", {})

    lines = [
        f"[STATE: Vol II | {manifest['phase']} | Active slice: {manifest['active_slice']} | Tainted nodes: {len(tainted)}]",
        "",
        f"- **Updated:** {dt.datetime.now(dt.timezone.utc).isoformat()}",
        f"- **Working Title (Unlocked):** {manifest['working_title']} — *{manifest['working_subtitle']}*",
        f"- **Volume I Read-Only Fence:** `{'PASS' if gate_report.get('fence_ok') else 'FAIL'}` (`{manifest['vol1_root']}`)",
        f"- **Network Graph (`build/vol2.duckdb`):** {compile_report['node_count']} nodes, {compile_report['edge_count']} edges across 5 fibers; cycles={compile_report['total_cycles']}; TCB violations={len(compile_report['tcb_violations'])}",
        f"- **Taint Summary:** CLEAN={len(clean)}, BODY_DIRTY={len(dirty)}, TAINTED={len(tainted)}",
        "",
        "## Node Verification Matrix",
    ]
    for nid, info in sorted(compile_report["nodes"].items()):
        extra = ""
        if nid in audit_nodes:
            an = audit_nodes[nid]
            extra = f"stratum={an['computed_stratum']} axioms={an['actual_axioms']}"
        elif nid in ka_res:
            extra = f"kernel_arena={'PASS' if ka_res[nid]['passed'] else 'FAIL'}"
        else:
            extra = f"stratum={info['stratum']}"
        lines.append(
            f"- `{nid}` (`{info['kind']}`, `{info['taint_status']}`): spec=`{info['spec_hash'][:8]}` body=`{info['body_hash'][:8]}` {extra}"
        )

    lines.append("")
    lines.append("## Royal Octavo PDF Artifacts")
    for stem, pinfo in pdfs.items():
        lines.append(
            f"- `{pinfo['pdf']}`: `{'PASS' if pinfo['passed'] else 'FAIL'}` (undef_refs={pinfo['has_undefined_refs']}, bib_warns={len(pinfo['bibtex_warnings'])})"
        )

    drill_path = LOGS_DIR / "drill_report.json"
    if drill_path.exists():
        lines.append("")
        lines.append("## Three-Pass Acceptance Drill Confirmation")
        drill = json.loads(drill_path.read_text(encoding="utf-8"))
        for key in ("pass_a", "pass_b", "pass_c"):
            if key in drill:
                lines.append(f"- `{key}`: {drill[key].get('summary', 'recorded')}")

    digest_path = BUILD_DIR / "VOL2_SYNC_DIGEST.md"
    digest_path.write_text("\n".join(lines[:58]) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Volume II Verification Gatekeeper.")
    parser.add_argument("--check-only", action="store_true", help="Run checks without updating verification_lock.json.")
    args = parser.parse_args()

    compile_report = compile_network()
    emit_all()
    ka_ok, ka_res = run_kernel_arena_checks(compile_report)
    lean_ok, lean_diags, audit_json = run_mathlib_build_and_audit()
    fence_rc, _ = run_logged(
        [sys.executable, str(REPO_ROOT / "scripts" / "fence_check.py"), "--verify"],
        LOGS_DIR / "gate_fence_verify.log",
    )
    fence_ok = fence_rc == 0

    audit_by_id = {n["id"]: n for n in (audit_json or {}).get("nodes", [])}
    prose_mismatch_consumers = {m["consumer_id"] for m in compile_report["prose_lock_mismatches"]}

    if args.check_only:
        gate_report = {
            "mode": "check_only",
            "timestamp_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
            "structural_ok": compile_report["structural_ok"],
            "fence_ok": fence_ok,
            "kernel_arena_ok": ka_ok,
            "kernel_arena": ka_res,
            "lean_and_audit_ok": lean_ok,
            "lean_diagnostics": lean_diags,
            "audit_env": audit_json,
            "prose_lock_mismatches": compile_report["prose_lock_mismatches"],
            "tainted_nodes": compile_report["tainted_nodes"],
            "body_dirty_nodes": compile_report["body_dirty_nodes"],
            "clean_nodes": compile_report["clean_nodes"],
        }
        (LOGS_DIR / "gatekeeper_report.json").write_text(
            json.dumps(gate_report, indent=2) + "\n", encoding="utf-8"
        )
        overall_ok = (
            compile_report["structural_ok"]
            and fence_ok
            and ka_ok
            and lean_ok
            and len(compile_report["tainted_nodes"]) == 0
            and len(compile_report["prose_lock_mismatches"]) == 0
        )
        print(
            f"GATEKEEPER_CHECK_ONLY ok={overall_ok} tainted={len(compile_report['tainted_nodes'])} "
            f"clean={len(compile_report['clean_nodes'])} lean_ok={lean_ok} ka_ok={ka_ok}"
        )
        return 0 if overall_ok else 1

    # Full mode: emit TeX + compile all 3 Royal Octavo PDFs
    manifest, guardrails, nodes_meta, symbols, receipts = load_context()
    emit_monograph(manifest, guardrails, nodes_meta, symbols)
    emit_claims_ledger(manifest, guardrails, nodes_meta, receipts, audit_json)
    emit_course_pack("ch01:tab:epistemic-probe-regimes")

    pdfs = {
        "crm_vol2_monograph": compile_pdf("crm_vol2_monograph", "monograph.tex.map.json", run_index=True),
        "crm_vol2_claims_ledger": compile_pdf("crm_vol2_claims_ledger", None, run_index=False),
        "course_pack_ch01_probe_calibration": compile_pdf(
            "course_pack_ch01_probe_calibration", "course_pack.tex.map.json", run_index=False
        ),
    }
    all_pdfs_ok = all(p["passed"] for p in pdfs.values())

    # Update verification_lock.json ONLY for nodes passing every formal, TeX, and prose_paraphrase gate
    now_iso = dt.datetime.now(dt.timezone.utc).isoformat()
    existing_lock: dict[str, Any] = {}
    if LOCK_PATH.exists():
        existing_lock = json.loads(LOCK_PATH.read_text(encoding="utf-8")).get("nodes", {})

    new_lock_nodes: dict[str, Any] = {}
    for nid, info in sorted(compile_report["nodes"].items()):
        if not compile_report["structural_ok"]:
            continue
        if nid in prose_mismatch_consumers:
            continue
        if not all_pdfs_ok:
            continue

        pkg = info["formal_pkg"]
        if pkg == "kernel_arena":
            ka_rec = ka_res["certs"].get(nid, {})
            arec = audit_by_id.get(nid, {})
            if not (ka_ok and ka_rec.get("passed") and lean_ok and arec.get("passed")):
                continue
            new_lock_nodes[nid] = {
                "spec_hash": info["spec_hash"],
                "body_hash": info["body_hash"],
                "stratum": arec["computed_stratum"],
                "actual_axioms": arec["actual_axioms"],
                "cert_sha256": ka_rec.get("sha256_arena"),
                "verified_at_utc": now_iso,
                "passed": True,
            }
        elif pkg == "mathlib_vol2":
            arec = audit_by_id.get(nid, {})
            if not (lean_ok and arec.get("passed")):
                continue
            new_lock_nodes[nid] = {
                "spec_hash": info["spec_hash"],
                "body_hash": info["body_hash"],
                "stratum": arec["computed_stratum"],
                "actual_axioms": arec["actual_axioms"],
                "cert_sha256": None,
                "verified_at_utc": now_iso,
                "passed": True,
            }
        else:
            new_lock_nodes[nid] = {
                "spec_hash": info["spec_hash"],
                "body_hash": info["body_hash"],
                "stratum": info["stratum"],
                "actual_axioms": [],
                "cert_sha256": None,
                "verified_at_utc": now_iso,
                "passed": True,
            }

    # Preserve existing locks for unmodified passing nodes if partial failure happened?
    # Spec says: "Updates manifest/verification_lock.json ONLY for nodes passing every formal, TeX, and prose_paraphrase gate"
    final_lock = {"schema": "vol2.verification_lock.v1", "updated_at_utc": now_iso, "nodes": new_lock_nodes}
    LOCK_PATH.write_text(json.dumps(final_lock, indent=2) + "\n", encoding="utf-8")

    # Recompile DuckDB and re-emit TeX ledger/digest cleanly with locked CLEAN state
    compile_report = compile_network()
    manifest, guardrails, nodes_meta, symbols, receipts = load_context()
    emit_claims_ledger(manifest, guardrails, nodes_meta, receipts, audit_json)
    pdfs["crm_vol2_claims_ledger"] = compile_pdf("crm_vol2_claims_ledger", None, run_index=False)
    all_pdfs_ok = all(p["passed"] for p in pdfs.values())

    overall_ok = (
        compile_report["structural_ok"]
        and fence_ok
        and ka_ok
        and lean_ok
        and all_pdfs_ok
        and len(compile_report["tainted_nodes"]) == 0
        and len(compile_report["body_dirty_nodes"]) == 0
    )

    gate_report = {
        "mode": "full",
        "timestamp_utc": now_iso,
        "overall_ok": overall_ok,
        "structural_ok": compile_report["structural_ok"],
        "fence_ok": fence_ok,
        "kernel_arena_ok": ka_ok,
        "kernel_arena": ka_res,
        "lean_and_audit_ok": lean_ok,
        "lean_diagnostics": lean_diags,
        "audit_env": audit_json,
        "pdfs": pdfs,
        "tainted_nodes": compile_report["tainted_nodes"],
        "body_dirty_nodes": compile_report["body_dirty_nodes"],
        "clean_nodes": compile_report["clean_nodes"],
    }
    (LOGS_DIR / "gatekeeper_report.json").write_text(
        json.dumps(gate_report, indent=2) + "\n", encoding="utf-8"
    )
    write_sync_digest(compile_report, gate_report)
    print(
        f"GATEKEEPER_FULL ok={overall_ok} tainted={len(compile_report['tainted_nodes'])} "
        f"clean={len(compile_report['clean_nodes'])} pdfs_ok={all_pdfs_ok}"
    )
    return 0 if overall_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
