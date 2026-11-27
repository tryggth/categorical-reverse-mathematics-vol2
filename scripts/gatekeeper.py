#!/usr/bin/env python3
"""Master verification gatekeeper: DuckDB + 2LTT KernelArena + Mathlib AuditEnv + Royal Octavo TeX."""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import re
import shutil
import subprocess
import sys
import tomllib
from pathlib import Path
from typing import Any

import duckdb

from compile_db import LOCK_PATH, PUB_LOCK_PATH, REPO_ROOT, compile_network, kernel_arena_expected_stratum
from emit_lean import emit_all, parse_and_map_lean_diagnostics
from emit_public_docs import check_docs_fresh
from emit_tex import BUILD_TEX_DIR, emit_claims_ledger, emit_monograph, load_context, resolve_tex_error
from slice_course import emit_course_pack

LOGS_DIR = REPO_ROOT / "logs"
BUILD_DIR = REPO_ROOT / "build"
MANIFEST_PATH = REPO_ROOT / "manifest.toml"
KERNEL_ARENA_DIR = REPO_ROOT / "kernel_arena"
MATHLIB_VOL2_DIR = REPO_ROOT / "mathlib_vol2"


def resolve_lake_bin() -> str:
    env_lake = os.environ.get("LAKE_BIN")
    if env_lake:
        return env_lake
    which_lake = shutil.which("lake")
    if which_lake:
        return which_lake
    elan_lake = Path.home() / ".elan" / "bin" / "lake"
    if elan_lake.exists():
        return str(elan_lake)
    return "lake"


LAKE_BIN = resolve_lake_bin()

TEX_ERROR_RE = re.compile(r"^(.+\.tex):(\d+):\s*(.*)$")
TEX_BAD_PATTERNS = (
    "Undefined control sequence",
    "LaTeX Warning: Reference",
    "There were undefined references",
    "Citation",
    "Emergency stop",
    "! ",
)


def run_logged(
    cmd: list[str], log_path: Path, cwd: Path | None = None, env: dict[str, str] | None = None
) -> tuple[int, str]:
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
        "SELECT id, cert_path, stratum FROM nodes WHERE formal_pkg = 'kernel_arena' ORDER BY id"
    ).fetchall()
    con.close()

    build_rc, _ = run_logged(
        [LAKE_BIN, "--dir", str(KERNEL_ARENA_DIR), "build"],
        LOGS_DIR / "gate_kernel_arena_build.log",
    )
    self_rc, self_out = run_logged(
        [LAKE_BIN, "--dir", str(KERNEL_ARENA_DIR), "exe", "kernel-arena", "--self-test"],
        LOGS_DIR / "gate_kernel_arena_selftest.log",
    )
    results: dict[str, Any] = {
        "build_ok": build_rc == 0,
        "selftest_ok": self_rc == 0,
        "selftest_output": self_out.strip(),
        "certs": {},
    }
    all_ok = (build_rc == 0) and (self_rc == 0)
    for nid, cert_rel, decl_stratum in rows:
        abs_cert = str((REPO_ROOT / cert_rel).resolve())
        slug = nid.replace(":", "_")
        rc, out = run_logged(
            [LAKE_BIN, "--dir", str(KERNEL_ARENA_DIR), "exe", "kernel-arena", "verify", abs_cert],
            LOGS_DIR / f"gate_ka_{slug}.log",
        )
        cert_obj = json.loads((REPO_ROOT / cert_rel).read_text(encoding="utf-8"))
        cert_sha = cert_obj["sha256_arena"]
        strata_flags = cert_obj.get("strata_flags", {})
        exp_stratum = kernel_arena_expected_stratum(strata_flags)
        stratum_ok = decl_stratum == exp_stratum
        passed = (rc == 0) and stratum_ok
        results["certs"][nid] = {
            "cert_path": cert_rel,
            "sha256_arena": cert_sha,
            "stratum": decl_stratum,
            "expected_stratum": exp_stratum,
            "stratum_ok": stratum_ok,
            "strata_flags": strata_flags,
            "passed": passed,
            "output": out.strip(),
        }
        if not passed:
            all_ok = False
    return all_ok, results


def check_published_endpoint_links(manifest: dict[str, Any]) -> tuple[bool, list[str], list[dict[str, str]]]:
    """Parse every pages_base_url/... link in README/PROCESS/ROADMAP and verify file exists under build/gh_pages/."""
    gh_pages_dir = BUILD_DIR / "gh_pages"
    base_url = str(manifest.get("pages_base_url") or "").strip().rstrip("/")
    if not base_url:
        return False, [], [{"source": "manifest.toml", "url": "", "reason": "MISSING_PAGES_BASE_URL"}]

    url_re = re.compile(re.escape(base_url) + r"(?:/([^\s\)\]>\"'`,;]*))?")
    checked_urls: set[str] = set()
    dead_links: list[dict[str, str]] = []

    for doc_name in ("README.md", "PROCESS.md", "ROADMAP.md"):
        doc_path = REPO_ROOT / doc_name
        if not doc_path.exists():
            dead_links.append({"source": doc_name, "url": "", "reason": "MISSING_DOC"})
            continue
        text = doc_path.read_text(encoding="utf-8")
        for m in url_re.finditer(text):
            raw_rel = m.group(1) or ""
            rel = raw_rel.split("#", 1)[0].split("?", 1)[0].strip().lstrip("/")
            full_url = f"{base_url}/{rel}" if rel else f"{base_url}/"
            checked_urls.add(full_url)
            rel_path = Path(rel) if rel else Path("index.html")
            if rel_path.is_absolute() or ".." in rel_path.parts:
                dead_links.append({"source": doc_name, "url": full_url, "reason": "UNSAFE_REL_PATH"})
                continue
            target_file = gh_pages_dir / rel_path
            if not target_file.is_file():
                dead_links.append(
                    {
                        "source": doc_name,
                        "url": full_url,
                        "reason": f"MISSING_FILE({target_file.relative_to(REPO_ROOT)})",
                    }
                )

    con = duckdb.connect(str(BUILD_DIR / "vol2.duckdb"), read_only=True)
    gh_rows = con.execute(
        "SELECT node_id, published_paths_json FROM pub_targets WHERE channel = 'gh_pages' ORDER BY node_id"
    ).fetchall()
    con.close()
    for pid, pjson in gh_rows:
        for rp in json.loads(pjson):
            rel = str(rp).strip().lstrip("/")
            target_file = gh_pages_dir / rel
            if not target_file.is_file():
                dead_links.append(
                    {
                        "source": pid,
                        "url": f"{base_url}/{rel}",
                        "reason": f"MISSING_PUBLISHED_PATH({target_file.relative_to(REPO_ROOT)})",
                    }
                )
            if pid.startswith("pub:pdf:") and f"{base_url}/{rel}" not in checked_urls:
                dead_links.append(
                    {
                        "source": "README.md",
                        "url": f"{base_url}/{rel}",
                        "reason": f"UNLINKED_PDF_FROM_{pid}",
                    }
                )

    ok = len(checked_urls) > 0 and len(dead_links) == 0
    return ok, sorted(checked_urls), dead_links


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

    bib_warnings = [
        ln for ln in bib_out.splitlines() if "Warning--" in ln or "I found no" in ln or "I couldn't" in ln
    ]
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
    pub_lock: dict[str, Any] = {}
    if PUB_LOCK_PATH.exists():
        pub_lock = json.loads(PUB_LOCK_PATH.read_text(encoding="utf-8"))

    tainted = compile_report["tainted_nodes"]
    dirty = compile_report["body_dirty_nodes"]
    grounding_dirty = compile_report["grounding_dirty_nodes"]
    clean = compile_report["clean_nodes"]
    ka_res = gate_report.get("kernel_arena", {}).get("certs", {})
    audit_nodes = {n["id"]: n for n in (gate_report.get("audit_env") or {}).get("nodes", [])}
    pdfs = gate_report.get("pdfs", {})

    vol1_display = manifest.get("vol1_root_default", "../categorical-reverse-mathematics")
    vol1_head = manifest.get("vol1_pinned_head", "b849be75")
    gh_repo = pub_lock.get("github_repo") or manifest.get("github_repo", "")
    pages_url = pub_lock.get("pages_url") or (
        f"https://{gh_repo.split('/')[0]}.github.io/{gh_repo.split('/')[1]}/"
        if "/" in gh_repo
        else ""
    )
    lean_export_sha = pub_lock.get("lean_export_commit") or "pending"
    wi_counts = compile_report.get("work_item_counts", {})

    lines = [
        f"[STATE: Vol II | {manifest['phase']} | Active slice: {manifest['active_slice']} | Tainted nodes: {len(tainted)}]",
        "",
        f"- **Updated:** {dt.datetime.now(dt.timezone.utc).isoformat()}",
        f"- **Working Title (Unlocked):** {manifest['working_title']} — *{manifest['working_subtitle']}*",
        f"- **Volume I Read-Only Fence:** `{'PASS' if gate_report.get('fence_ok') else 'FAIL'}` (`{vol1_display} (HEAD {vol1_head})`)",
        (
            f"- **Network Graph (`build/vol2.duckdb`):** {compile_report['node_count']} nodes "
            f"({compile_report['core_node_count']} core, {compile_report['work_item_count']} work_item, "
            f"{compile_report['pub_target_count']} pub_target), "
            f"{compile_report['edge_count']} edges across 5 fibers; cycles={compile_report['total_cycles']}; "
            f"TCB violations={len(compile_report['tcb_violations'])}; "
            f"pub out-degree violations={len(compile_report['pub_outdegree_violations'])}; "
            f"honesty violations={len(compile_report['honesty_violations'])}; "
            f"disjoint declarations={compile_report['decl_ownership_count']}"
        ),
        f"- **Taint Summary (Core):** CLEAN={len(clean)}, BODY_DIRTY={len(dirty)}, GROUNDING_DIRTY={len(grounding_dirty)}, TAINTED={len(tainted)}",
        f"- **Project Plan (14 Slices):** VERIFIED={wi_counts.get('VERIFIED', 0)}, ACTIVE={wi_counts.get('ACTIVE', 0)}, PLANNED={wi_counts.get('PLANNED', 0)}",
        (
            f"- **Publication Sinks (`pub_targets`):** CLEAN={len(compile_report['pub_clean_nodes'])}, "
            f"ARTIFACT_DIRTY={len(compile_report['pub_dirty_nodes'])}, TAINTED={len(compile_report['pub_tainted_nodes'])}"
        ),
        "",
        "## Node Verification Matrix",
    ]
    for nid, info in sorted(compile_report["nodes"].items()):
        if info["kind"] in ("work_item", "pub_target"):
            continue
        if nid in audit_nodes:
            an = audit_nodes[nid]
            extra = f"stratum={an['computed_stratum']} axioms={an['actual_axioms']}"
        elif nid in ka_res:
            extra = f"kernel_arena={'PASS' if ka_res[nid]['passed'] else 'FAIL'}"
        else:
            extra = f"stratum={info['stratum']}"
        lines.append(
            f"- `{nid}` (`{info['kind']}`, `{info['cohort']}`, `{info['taint_status']}`): "
            f"spec=`{info['spec_hash'][:8]}` body=`{info['body_hash'][:8]}` "
            f"grounding=`{info['grounding_hash'][:8]}` {extra}"
        )

    lines.append("")
    lines.append("## Royal Octavo PDF Artifacts")
    for _, pinfo in pdfs.items():
        lines.append(
            f"- `{pinfo['pdf']}`: `{'PASS' if pinfo['passed'] else 'FAIL'}` (undef_refs={pinfo['has_undefined_refs']}, bib_warns={len(pinfo['bibtex_warnings'])})"
        )

    lines.extend(
        [
            "",
            "## Public Launch & Publication Sinks",
            f"- **GitHub Repository:** https://github.com/{gh_repo}" if gh_repo else "- **GitHub Repository:** pending",
            f"- **GitHub Pages Observatory:** {pages_url}" if pages_url else "- **GitHub Pages Observatory:** pending",
            f"- **`lean-export` Commit SHA:** `{lean_export_sha}`",
            f"- **Front-Door Docs Freshness (`emit_public_docs.py --check`):** `{'PASS' if gate_report.get('docs_fresh_ok') else 'FAIL'}`",
            (
                f"- **Published Endpoint Dead-Link Gate (`build/gh_pages/`):** "
                f"`{'PASS' if gate_report.get('published_endpoint_links_ok') else 'FAIL'}` "
                f"({len(gate_report.get('published_endpoint_urls', []))} URLs checked, "
                f"{len(gate_report.get('published_dead_links', []))} dead)"
            ),
        ]
    )
    for pid, pinfo in sorted(compile_report.get("pub_targets", {}).items()):
        lines.append(
            f"- `{pid}` (`{pinfo['channel']}`, `{pinfo['sensitivity']}`, `{pinfo['pub_status']}`): cone=`{pinfo['cone_hash'][:8]}`"
        )
    issues = pub_lock.get("issues", {})
    if issues:
        lines.append("")
        lines.append("### Synced GitHub Issues")
        for nid, irec in sorted(issues.items(), key=lambda kv: kv[1].get("number", 999999)):
            lines.append(f"- Issue #{irec.get('number')}: `{nid}` ({irec.get('state', 'open')}) — {irec.get('url', '')}")

    digest_path = BUILD_DIR / "VOL2_SYNC_DIGEST.md"
    digest_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def _core_locks_match(existing_nodes: dict[str, Any], new_nodes: dict[str, Any]) -> bool:
    if set(existing_nodes.keys()) != set(new_nodes.keys()):
        return False
    for nid, nrec in new_nodes.items():
        erec = existing_nodes[nid]
        for k in ("spec_hash", "body_hash", "grounding_hash", "stratum", "actual_axioms", "cert_sha256", "passed"):
            if erec.get(k) != nrec.get(k):
                return False
    return True


def main() -> int:
    parser = argparse.ArgumentParser(description="Volume II Verification Gatekeeper.")
    parser.add_argument("--check-only", action="store_true", help="Run checks without updating lock files.")
    parser.add_argument(
        "--publish",
        action="store_true",
        help="Publish gate: hard-blocks on any mathematical or pub_target taint and locks publication_lock.json.",
    )
    args = parser.parse_args()

    compile_report = compile_network()
    if not compile_report["structural_ok"]:
        sys.stderr.write("GATEKEEPER_FAIL: compile_network reported structural or honesty violations.\n")
        return 1

    if args.publish and (
        compile_report["tainted_nodes"]
        or compile_report["pub_tainted_nodes"]
        or compile_report["prose_lock_mismatches"]
    ):
        sys.stderr.write(
            "PUBLISH_BLOCKED: taint detected — "
            f"tainted={compile_report['tainted_nodes']} "
            f"pub_tainted={compile_report['pub_tainted_nodes']} "
            f"prose_lock_mismatches={len(compile_report['prose_lock_mismatches'])}\n"
        )
        return 1

    emit_all()
    ka_ok, ka_res = run_kernel_arena_checks(compile_report)
    lean_ok, lean_diags, audit_json = run_mathlib_build_and_audit()
    fence_rc, _ = run_logged(
        [sys.executable, str(REPO_ROOT / "scripts" / "fence_check.py"), "--verify"],
        LOGS_DIR / "gate_fence_verify.log",
    )
    fence_ok = fence_rc == 0
    docs_fresh_ok, docs_stale = check_docs_fresh()
    with MANIFEST_PATH.open("rb") as fh:
        manifest_cfg = tomllib.load(fh)
    links_ok, checked_urls, dead_links = check_published_endpoint_links(manifest_cfg)

    audit_by_id = {n["id"]: n for n in (audit_json or {}).get("nodes", [])}
    prose_mismatch_consumers = {m["consumer_id"] for m in compile_report["prose_lock_mismatches"]}

    if args.check_only:
        gate_report = {
            "mode": "check_only",
            "timestamp_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
            "structural_ok": compile_report["structural_ok"],
            "honesty_violations": compile_report["honesty_violations"],
            "pub_outdegree_violations": compile_report["pub_outdegree_violations"],
            "fence_ok": fence_ok,
            "kernel_arena_ok": ka_ok,
            "kernel_arena": ka_res,
            "lean_and_audit_ok": lean_ok,
            "lean_diagnostics": lean_diags,
            "audit_env": audit_json,
            "docs_fresh_ok": docs_fresh_ok,
            "docs_stale": docs_stale,
            "published_endpoint_links_ok": links_ok,
            "published_endpoint_urls": checked_urls,
            "published_dead_links": dead_links,
            "prose_lock_mismatches": compile_report["prose_lock_mismatches"],
            "tainted_nodes": compile_report["tainted_nodes"],
            "body_dirty_nodes": compile_report["body_dirty_nodes"],
            "grounding_dirty_nodes": compile_report["grounding_dirty_nodes"],
            "clean_nodes": compile_report["clean_nodes"],
            "work_item_counts": compile_report["work_item_counts"],
            "pub_tainted_nodes": compile_report["pub_tainted_nodes"],
            "pub_dirty_nodes": compile_report["pub_dirty_nodes"],
            "pub_clean_nodes": compile_report["pub_clean_nodes"],
        }
        (LOGS_DIR / "gatekeeper_report.json").write_text(
            json.dumps(gate_report, indent=2) + "\n", encoding="utf-8"
        )
        overall_ok = (
            compile_report["structural_ok"]
            and len(compile_report["honesty_violations"]) == 0
            and len(compile_report["pub_outdegree_violations"]) == 0
            and fence_ok
            and ka_ok
            and lean_ok
            and docs_fresh_ok
            and len(compile_report["tainted_nodes"]) == 0
            and len(compile_report["grounding_dirty_nodes"]) == 0
            and len(compile_report["prose_lock_mismatches"]) == 0
            and len(compile_report["pub_tainted_nodes"]) == 0
        )
        print(
            f"GATEKEEPER_CHECK_ONLY ok={overall_ok} tainted={len(compile_report['tainted_nodes'])} "
            f"grounding_dirty={len(compile_report['grounding_dirty_nodes'])} "
            f"clean={len(compile_report['clean_nodes'])} pub_tainted={len(compile_report['pub_tainted_nodes'])} "
            f"docs_fresh={docs_fresh_ok} lean_ok={lean_ok} ka_ok={ka_ok}"
        )
        return 0 if overall_ok else 1

    # Full / Publish mode: emit TeX + compile all 5 Royal Octavo PDFs
    manifest, guardrails, nodes_meta, symbols, receipts = load_context()
    emit_monograph(manifest, guardrails, nodes_meta, symbols)
    emit_claims_ledger(manifest, guardrails, nodes_meta, receipts, audit_json)
    emit_course_pack("ch01:tab:epistemic-probe-regimes")
    emit_course_pack("ch02:tab:vertical-class-spectrum")
    emit_course_pack("ch03:tab:piset-four-quadrant-ledger")

    pdfs = {
        "crm_vol2_monograph": compile_pdf("crm_vol2_monograph", "monograph.tex.map.json", run_index=True),
        "crm_vol2_claims_ledger": compile_pdf("crm_vol2_claims_ledger", None, run_index=False),
        "course_pack_ch01_probe_calibration": compile_pdf(
            "course_pack_ch01_probe_calibration",
            "course_pack_ch01_probe_calibration.tex.map.json",
            run_index=False,
        ),
        "course_pack_ch02_class_set_kaleidoscope": compile_pdf(
            "course_pack_ch02_class_set_kaleidoscope",
            "course_pack_ch02_class_set_kaleidoscope.tex.map.json",
            run_index=False,
        ),
        "course_pack_ch03_piset_transgression": compile_pdf(
            "course_pack_ch03_piset_transgression",
            "course_pack_ch03_piset_transgression.tex.map.json",
            run_index=False,
        ),
    }
    all_pdfs_ok = all(p["passed"] for p in pdfs.values())

    # Update verification_lock.json ONLY for core nodes passing every formal, TeX, honesty, and prose_paraphrase gate
    now_iso = dt.datetime.now(dt.timezone.utc).isoformat()
    new_lock_nodes: dict[str, Any] = {}
    for nid, info in sorted(compile_report["nodes"].items()):
        if info["kind"] in ("work_item", "pub_target"):
            continue
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
                "grounding_hash": info["grounding_hash"],
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
                "grounding_hash": info["grounding_hash"],
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
                "grounding_hash": info["grounding_hash"],
                "stratum": info["stratum"],
                "actual_axioms": [],
                "cert_sha256": None,
                "verified_at_utc": now_iso,
                "passed": True,
            }

    existing_lock = json.loads(LOCK_PATH.read_text(encoding="utf-8")) if LOCK_PATH.exists() else {}
    if (
        compile_report["structural_ok"]
        and fence_ok
        and ka_ok
        and lean_ok
        and all_pdfs_ok
        and new_lock_nodes
        and not _core_locks_match(existing_lock.get("nodes", {}), new_lock_nodes)
    ):
        final_lock = {"schema": "vol2.verification_lock.v1", "updated_at_utc": now_iso, "nodes": new_lock_nodes}
        LOCK_PATH.write_text(json.dumps(final_lock, indent=2) + "\n", encoding="utf-8")

    # Recompile DuckDB and re-emit TeX ledger cleanly with locked core CLEAN state
    compile_report = compile_network()
    manifest, guardrails, nodes_meta, symbols, receipts = load_context()
    emit_claims_ledger(manifest, guardrails, nodes_meta, receipts, audit_json)
    pdfs["crm_vol2_claims_ledger"] = compile_pdf("crm_vol2_claims_ledger", None, run_index=False)
    all_pdfs_ok = all(p["passed"] for p in pdfs.values())

    core_gates_ok = (
        compile_report["structural_ok"]
        and len(compile_report["honesty_violations"]) == 0
        and len(compile_report["pub_outdegree_violations"]) == 0
        and fence_ok
        and ka_ok
        and lean_ok
        and all_pdfs_ok
        and docs_fresh_ok
        and (links_ok if args.publish else True)
        and len(compile_report["tainted_nodes"]) == 0
        and len(compile_report["body_dirty_nodes"]) == 0
        and len(compile_report["grounding_dirty_nodes"]) == 0
        and len(compile_report["pub_tainted_nodes"]) == 0
        and len(compile_report["prose_lock_mismatches"]) == 0
    )

    if core_gates_ok:
        pub_lock_full: dict[str, Any] = {}
        if PUB_LOCK_PATH.exists():
            pub_lock_full = json.loads(PUB_LOCK_PATH.read_text(encoding="utf-8"))
        pub_lock_full.setdefault("schema", "vol2.publication_lock.v1")
        pub_lock_full["updated_at_utc"] = now_iso
        pub_lock_full.setdefault("github_repo", manifest.get("github_repo", ""))
        gh_repo = pub_lock_full["github_repo"]
        base_pages = (manifest.get("pages_base_url") or "").strip().rstrip("/")
        if base_pages:
            pub_lock_full["pages_url"] = f"{base_pages}/"
        elif gh_repo and "/" in gh_repo and not pub_lock_full.get("pages_url"):
            owner, rname = gh_repo.split("/", 1)
            pub_lock_full["pages_url"] = f"https://{owner}.github.io/{rname}/"
        pub_lock_full.setdefault("lean_export_commit", "")
        pub_lock_full.setdefault("milestones", {})
        pub_lock_full.setdefault("issues", {})
        pub_lock_full["pub_targets"] = {
            pid: {
                "cone_hash": pinfo["cone_hash"],
                "channel": pinfo["channel"],
                "sensitivity": pinfo["sensitivity"],
                "outputs": pinfo["outputs"],
                "published_paths": pinfo.get("published_paths", []),
                "locked_at_utc": now_iso,
            }
            for pid, pinfo in sorted(compile_report.get("pub_targets", {}).items())
        }
        PUB_LOCK_PATH.write_text(json.dumps(pub_lock_full, indent=2) + "\n", encoding="utf-8")
        compile_report = compile_network()

    overall_ok = (
        core_gates_ok
        and len(compile_report["pub_tainted_nodes"]) == 0
        and len(compile_report["pub_dirty_nodes"]) == 0
    )

    gate_report = {
        "mode": "publish" if args.publish else "full",
        "timestamp_utc": now_iso,
        "overall_ok": overall_ok,
        "structural_ok": compile_report["structural_ok"],
        "honesty_violations": compile_report["honesty_violations"],
        "pub_outdegree_violations": compile_report["pub_outdegree_violations"],
        "decl_ownership_count": compile_report["decl_ownership_count"],
        "fence_ok": fence_ok,
        "kernel_arena_ok": ka_ok,
        "kernel_arena": ka_res,
        "lean_and_audit_ok": lean_ok,
        "lean_diagnostics": lean_diags,
        "audit_env": audit_json,
        "docs_fresh_ok": docs_fresh_ok,
        "docs_stale": docs_stale,
        "published_endpoint_links_ok": links_ok,
        "published_endpoint_urls": checked_urls,
        "published_dead_links": dead_links,
        "pdfs": pdfs,
        "tainted_nodes": compile_report["tainted_nodes"],
        "body_dirty_nodes": compile_report["body_dirty_nodes"],
        "grounding_dirty_nodes": compile_report["grounding_dirty_nodes"],
        "clean_nodes": compile_report["clean_nodes"],
        "work_items": compile_report["work_items"],
        "work_item_counts": compile_report["work_item_counts"],
        "pub_targets": compile_report["pub_targets"],
        "pub_tainted_nodes": compile_report["pub_tainted_nodes"],
        "pub_dirty_nodes": compile_report["pub_dirty_nodes"],
        "pub_clean_nodes": compile_report["pub_clean_nodes"],
    }
    (LOGS_DIR / "gatekeeper_report.json").write_text(
        json.dumps(gate_report, indent=2) + "\n", encoding="utf-8"
    )
    write_sync_digest(compile_report, gate_report)
    print(
        f"GATEKEEPER_{'PUBLISH' if args.publish else 'FULL'} ok={overall_ok} "
        f"tainted={len(compile_report['tainted_nodes'])} "
        f"body_dirty={len(compile_report['body_dirty_nodes'])} "
        f"grounding_dirty={len(compile_report['grounding_dirty_nodes'])} "
        f"clean={len(compile_report['clean_nodes'])} "
        f"pub_clean={len(compile_report['pub_clean_nodes'])} "
        f"pub_dirty={len(compile_report['pub_dirty_nodes'])} "
        f"pub_tainted={len(compile_report['pub_tainted_nodes'])} "
        f"docs_fresh={docs_fresh_ok} pdfs_ok={all_pdfs_ok}"
    )
    return 0 if overall_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
