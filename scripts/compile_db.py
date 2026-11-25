#!/usr/bin/env python3
"""DuckDB 5-fiber network compiler, hash calculator, TCB enforcer, and taint engine."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import tomllib
from pathlib import Path
from typing import Any

import duckdb

REPO_ROOT = Path(__file__).resolve().parent.parent
NODES_DIR = REPO_ROOT / "nodes"
SCHEMA_PATH = Path(__file__).resolve().parent / "schema.sql"
BIB_PATH = REPO_ROOT / "references_vol2.bib"
LOCK_PATH = REPO_ROOT / "manifest" / "verification_lock.json"
DB_PATH = REPO_ROOT / "build" / "vol2.duckdb"
REPORT_PATH = REPO_ROOT / "build" / "compile_report.json"
AUDIT_MANIFEST_PATH = REPO_ROOT / "build" / "audit_nodes_manifest.json"

SYM_RE = re.compile(r"\{\{sym:([A-Za-z0-9_.:-]+)\}\}")
REF_RE = re.compile(r"\{\{ref:([A-Za-z0-9_.:-]+)\}\}")
CITE_RE = re.compile(r"\\cite(?:\[[^\]]*\])?\{([^}]+)\}")
BIB_ENTRY_RE = re.compile(r"@\w+\s*\{\s*([^,\s]+)\s*,")

FIBERS = ("logical_dep", "lean_dep", "prose_paraphrase", "notation", "curriculum")


def canonical_json(obj: Any) -> str:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def parse_bib_keys(bib_path: Path) -> set[str]:
    if not bib_path.exists():
        return set()
    text = bib_path.read_text(encoding="utf-8")
    return set(BIB_ENTRY_RE.findall(text))


def expand_cert_ast(nodes_by_id: dict[int, dict[str, Any]], node_id: int) -> Any:
    """Build a canonical, ID-free AST subtree from a certificate node DAG."""
    node = nodes_by_id[node_id]
    op = node["op"]
    args = node.get("args", [])
    if op in ("UnivS", "UnivF", "Var"):
        return {"op": op, "val": args[0]}
    if op in ("BoolS", "BoolF", "TrueF", "FalseF"):
        return {"op": op}
    return {
        "op": op,
        "children": [expand_cert_ast(nodes_by_id, child_id) for child_id in args],
    }


def load_cert_data(cert_rel_path: str) -> dict[str, Any]:
    cert_path = REPO_ROOT / cert_rel_path
    if not cert_path.exists():
        raise FileNotFoundError(f"Certificate file not found: {cert_path}")
    return json.loads(cert_path.read_text(encoding="utf-8"))


def compute_node_hashes(node: dict[str, Any]) -> tuple[str, str]:
    """Compute canonical spec_hash (VOL2_SPEC_V1) and body_hash (VOL2_BODY_V1)."""
    formal_pkg = node["formal_pkg"]
    spec_payload = node.get("spec", {})
    body_payload = node.get("body", {})

    if formal_pkg == "kernel_arena":
        cert_rel = spec_payload.get("cert_path") or node.get("cert_path")
        if not cert_rel:
            raise ValueError(f"kernel_arena node {node['id']} missing cert_path")
        cert = load_cert_data(cert_rel)
        nodes_by_id = {int(n["id"]): n for n in cert["nodes"]}
        goal_ast = expand_cert_ast(nodes_by_id, int(cert["goal_type_node"]))
        proof_ast = expand_cert_ast(nodes_by_id, int(cert["proof_term_node"]))
        spec_core = {
            "id": node["id"],
            "kind": node["kind"],
            "axis": node["axis"],
            "grounding_tier": node["grounding_tier"],
            "formal_pkg": formal_pkg,
            "spec": {
                "decl_name": cert["decl_name"],
                "universe_depth_k": cert["universe_depth_k"],
                "expected_strata_flags": cert["strata_flags"],
                "dim_contexts": cert["dim_contexts"],
                "goal_type_ast": goal_ast,
                "statement": spec_payload.get("statement", ""),
                "hypotheses": spec_payload.get("hypotheses", []),
            },
        }
        body_core = {
            "body": body_payload,
            "proof_term_ast": proof_ast,
            "fuel_hint": cert["fuel_hint"],
            "sha256_arena": cert["sha256_arena"],
        }
    else:
        spec_core = {
            "id": node["id"],
            "kind": node["kind"],
            "axis": node["axis"],
            "grounding_tier": node["grounding_tier"],
            "formal_pkg": formal_pkg,
            "spec": spec_payload,
        }
        body_core = {"body": body_payload}

    spec_hash = hashlib.sha256(b"VOL2_SPEC_V1\x00" + canonical_json(spec_core).encode("utf-8")).hexdigest()
    body_hash = hashlib.sha256(b"VOL2_BODY_V1\x00" + canonical_json(body_core).encode("utf-8")).hexdigest()
    return spec_hash, body_hash


def extract_texts_for_macros(node: dict[str, Any]) -> list[str]:
    texts: list[str] = []
    body = node.get("body", {})
    for key in ("tex", "notes", "caption"):
        val = body.get(key)
        if isinstance(val, str):
            texts.append(val)
    spec = node.get("spec", {})
    for key in ("statement", "notes", "contract"):
        val = spec.get(key)
        if isinstance(val, str):
            texts.append(val)
    return texts


def load_all_nodes() -> list[dict[str, Any]]:
    nodes: list[dict[str, Any]] = []
    seen_ids: dict[str, Path] = {}
    for path in sorted(NODES_DIR.rglob("*.toml")):
        with path.open("rb") as fh:
            data = tomllib.load(fh)
        nid = data["id"]
        if nid in seen_ids:
            raise ValueError(f"Duplicate node id '{nid}' in {path} and {seen_ids[nid]}")
        seen_ids[nid] = path
        data["_file_path"] = str(path.relative_to(REPO_ROOT))
        nodes.append(data)
    return nodes


def compile_network() -> dict[str, Any]:
    raw_nodes = load_all_nodes()
    bib_keys = parse_bib_keys(BIB_PATH)
    lock_data: dict[str, Any] = {}
    if LOCK_PATH.exists():
        lock_data = json.loads(LOCK_PATH.read_text(encoding="utf-8")).get("nodes", {})

    # 1. Register symbols and compute hashes
    nodes_by_id: dict[str, dict[str, Any]] = {}
    symbols_map: dict[str, dict[str, str]] = {}
    for node in raw_nodes:
        nid = node["id"]
        spec_hash, body_hash = compute_node_hashes(node)
        node["_spec_hash"] = spec_hash
        node["_body_hash"] = body_hash
        nodes_by_id[nid] = node
        if node["kind"] == "symbol":
            exports = node.get("spec", {}).get("exports", [])
            for sym in exports:
                key = sym["key"]
                if key in symbols_map:
                    raise ValueError(f"Duplicate symbol key '{key}'")
                symbols_map[key] = {
                    "macro_key": key,
                    "symbol_node_id": nid,
                    "latex_macro": sym["latex"],
                    "description": sym.get("description", ""),
                }

    # 2. Extract and validate all 5 edge fibers + references + bibkeys
    edges: list[tuple[str, str, str, str]] = []
    unresolved_errors: list[str] = []

    for node in raw_nodes:
        nid = node["id"]
        edge_cfg = node.get("edges", {})

        for fiber in ("logical_dep", "lean_dep", "curriculum"):
            for prov in edge_cfg.get(fiber, []):
                if prov not in nodes_by_id:
                    unresolved_errors.append(f"UNRESOLVED_{fiber.upper()}: {nid} -> {prov}")
                else:
                    edges.append((prov, nid, fiber, "{}"))

        for pp in edge_cfg.get("prose_paraphrase", []):
            target = pp["target_id"]
            if target not in nodes_by_id:
                unresolved_errors.append(f"UNRESOLVED_PROSE_PARAPHRASE: {nid} -> {target}")
            else:
                meta = {
                    "locked_spec_hash": pp.get("locked_spec_hash", ""),
                    "scope_note": pp.get("scope_note", ""),
                }
                edges.append((target, nid, "prose_paraphrase", canonical_json(meta)))

        # Auto-extract notation / index edges from {{sym:...}} and {{ref:...}} + check citations
        seen_notation_providers: set[str] = set()
        for text in extract_texts_for_macros(node):
            for sym_key in SYM_RE.findall(text):
                if sym_key not in symbols_map:
                    unresolved_errors.append(f"UNRESOLVED_SYM: {nid} references {{{{sym:{sym_key}}}}}")
                else:
                    prov = symbols_map[sym_key]["symbol_node_id"]
                    if prov != nid and prov not in seen_notation_providers:
                        seen_notation_providers.add(prov)
                        edges.append((prov, nid, "notation", canonical_json({"macro_key": sym_key})))
            for ref_id in REF_RE.findall(text):
                if ref_id not in nodes_by_id:
                    unresolved_errors.append(f"UNRESOLVED_REF: {nid} references {{{{ref:{ref_id}}}}}")
                else:
                    if ref_id != nid and ref_id not in seen_notation_providers:
                        seen_notation_providers.add(ref_id)
                        edges.append((ref_id, nid, "notation", canonical_json({"ref_id": ref_id})))
            for cite_group in CITE_RE.findall(text):
                for key in [k.strip() for k in cite_group.split(",") if k.strip()]:
                    if key not in bib_keys:
                        unresolved_errors.append(f"UNRESOLVED_BIBKEY: {nid} cites '{key}'")

        for key in node.get("cite_keys", []):
            if key not in bib_keys:
                unresolved_errors.append(f"UNRESOLVED_BIBKEY: {nid} cite_keys contains '{key}'")

    # 3. Populate DuckDB and execute structural SQL gates
    DB_PATH.parent.mkdir(parents=True, exist_ok=True)
    if DB_PATH.exists():
        DB_PATH.unlink()
    con = duckdb.connect(str(DB_PATH))
    con.execute(SCHEMA_PATH.read_text(encoding="utf-8"))

    for key, srec in symbols_map.items():
        con.execute(
            "INSERT INTO symbols VALUES (?, ?, ?, ?)",
            [srec["macro_key"], srec["symbol_node_id"], srec["latex_macro"], srec["description"]],
        )

    for node in raw_nodes:
        nid = node["id"]
        spec = node.get("spec", {})
        mathlib_spec = spec.get("mathlib", {})
        ka_spec = spec.get("kernel_arena", {})
        if node["formal_pkg"] == "mathlib_vol2":
            module = mathlib_spec.get("module")
            decl_names = mathlib_spec.get("decl_names", [])
            expected_axioms = mathlib_spec.get("expected_axioms", [])
            cert_path = None
        elif node["formal_pkg"] == "kernel_arena":
            module = "HomotopyCRM.Vol2.CertChecks"
            decl_names = ka_spec.get("decl_names", [])
            expected_axioms = ka_spec.get("expected_axioms", [])
            cert_path = spec.get("cert_path") or node.get("cert_path")
        else:
            module = None
            decl_names = []
            expected_axioms = []
            cert_path = None

        locked = lock_data.get(nid, {})
        con.execute(
            "INSERT INTO nodes VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
            [
                nid,
                node["kind"],
                node["title"],
                node.get("chapter", ""),
                node.get("section", ""),
                node["axis"],
                node["grounding_tier"],
                node["formal_pkg"],
                node.get("stratum", "none"),
                module,
                json.dumps(decl_names),
                json.dumps(sorted(expected_axioms)),
                cert_path,
                node["_spec_hash"],
                node["_body_hash"],
                "CLEAN",
                "",
                locked.get("spec_hash"),
                locked.get("body_hash"),
                node["_file_path"],
                json.dumps({k: v for k, v in node.items() if not k.startswith("_")}),
            ],
        )

    for src_id, dst_id, fiber, meta_json in edges:
        con.execute("INSERT INTO edges VALUES (?, ?, ?, ?)", [src_id, dst_id, fiber, meta_json])

    for nid, lrec in lock_data.items():
        if nid in nodes_by_id:
            con.execute(
                "INSERT INTO verification_receipts VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                [
                    nid,
                    lrec.get("spec_hash", ""),
                    lrec.get("body_hash", ""),
                    lrec.get("stratum", "none"),
                    json.dumps(lrec.get("actual_axioms", [])),
                    lrec.get("cert_sha256"),
                    lrec.get("verified_at_utc", ""),
                    bool(lrec.get("passed", False)),
                ],
            )

    # Gate (a): Terminating recursive CTE cycle checks per fiber and across union
    max_depth = len(raw_nodes) + 1
    cycles_by_fiber: dict[str, list[Any]] = {}
    for fiber in FIBERS:
        rows = con.execute(
            """
            WITH RECURSIVE walk(start_id, curr_id, path, has_cycle) AS (
              SELECT src_id, dst_id, [src_id, dst_id], (src_id = dst_id)
              FROM edges WHERE fiber = ?
              UNION ALL
              SELECT w.start_id, e.dst_id, list_append(w.path, e.dst_id),
                     (e.dst_id = w.start_id OR list_contains(w.path, e.dst_id))
              FROM walk w
              JOIN edges e ON w.curr_id = e.src_id AND e.fiber = ?
              WHERE NOT w.has_cycle AND len(w.path) < ?
            )
            SELECT start_id, curr_id, path FROM walk WHERE has_cycle LIMIT 20
            """,
            [fiber, fiber, max_depth],
        ).fetchall()
        cycles_by_fiber[fiber] = [list(r) for r in rows]

    union_cycles = con.execute(
        """
        WITH RECURSIVE unique_edges AS (
          SELECT DISTINCT src_id, dst_id FROM edges
        ),
        walk(start_id, curr_id, path, has_cycle) AS (
          SELECT src_id, dst_id, [src_id, dst_id], (src_id = dst_id)
          FROM unique_edges
          UNION ALL
          SELECT w.start_id, e.dst_id, list_append(w.path, e.dst_id),
                 (e.dst_id = w.start_id OR list_contains(w.path, e.dst_id))
          FROM walk w
          JOIN unique_edges e ON w.curr_id = e.src_id
          WHERE NOT w.has_cycle AND len(w.path) < ?
        )
        SELECT start_id, curr_id, path FROM walk WHERE has_cycle LIMIT 20
        """,
        [max_depth],
    ).fetchall()
    cycles_by_fiber["structural_union"] = [list(r) for r in union_cycles]

    # Gate (b): vol1_external in-degree == 0
    vol1_indegree_violations = con.execute(
        """
        SELECT e.src_id, e.dst_id, e.fiber
        FROM edges e
        JOIN nodes n ON e.dst_id = n.id
        WHERE n.kind = 'vol1_external' OR n.grounding_tier = 'vol1_external'
        """
    ).fetchall()

    # Gate (c): Two-Package TCB SQL gate (0 lean_dep edges between mathlib_vol2 and kernel_arena)
    tcb_violations = con.execute(
        """
        SELECT e.src_id, e.dst_id, src.formal_pkg, dst.formal_pkg
        FROM edges e
        JOIN nodes src ON e.src_id = src.id
        JOIN nodes dst ON e.dst_id = dst.id
        WHERE e.fiber = 'lean_dep'
          AND (
            (src.formal_pkg = 'mathlib_vol2' AND dst.formal_pkg = 'kernel_arena')
            OR (src.formal_pkg = 'kernel_arena' AND dst.formal_pkg = 'mathlib_vol2')
          )
        """
    ).fetchall()

    # Gate (e): Multi-fiber forward transitive taint cone + prose_paraphrase lock check
    direct_taint: dict[str, list[str]] = {}
    prose_lock_mismatches: list[dict[str, str]] = []

    for node in raw_nodes:
        nid = node["id"]
        reasons: list[str] = []
        lrec = lock_data.get(nid)
        if lrec is None or not lrec.get("passed", False):
            reasons.append("NO_VERIFIED_LOCK")
        elif lrec.get("spec_hash") != node["_spec_hash"]:
            reasons.append("SPEC_HASH_CHANGED")
        if reasons:
            direct_taint[nid] = reasons

    pp_rows = con.execute(
        """
        SELECT e.src_id, e.dst_id, e.metadata_json, src.spec_hash
        FROM edges e
        JOIN nodes src ON e.src_id = src.id
        WHERE e.fiber = 'prose_paraphrase'
        """
    ).fetchall()
    for target_id, consumer_id, meta_raw, target_spec_hash in pp_rows:
        meta = json.loads(meta_raw)
        locked_target_hash = meta.get("locked_spec_hash", "")
        if locked_target_hash != target_spec_hash:
            prose_lock_mismatches.append(
                {
                    "consumer_id": consumer_id,
                    "target_id": target_id,
                    "locked_spec_hash": locked_target_hash,
                    "actual_spec_hash": target_spec_hash,
                    "code": "PROSE_LOCK_MISMATCH",
                }
            )
            direct_taint.setdefault(consumer_id, []).append(
                f"PROSE_LOCK_MISMATCH({target_id})"
            )

    tainted_nodes: set[str] = set(direct_taint.keys())
    if tainted_nodes:
        placeholders = ",".join("?" for _ in tainted_nodes)
        cone_rows = con.execute(
            f"""
            WITH RECURSIVE taint_cone(id, depth) AS (
              SELECT id, 0 FROM nodes WHERE id IN ({placeholders})
              UNION ALL
              SELECT e.dst_id, tc.depth + 1
              FROM taint_cone tc
              JOIN edges e ON tc.id = e.src_id
              WHERE tc.depth < ?
            )
            SELECT DISTINCT id FROM taint_cone
            """,
            [*sorted(tainted_nodes), max_depth],
        ).fetchall()
        tainted_nodes = {r[0] for r in cone_rows}

    body_dirty_nodes: list[str] = []
    clean_nodes: list[str] = []
    node_statuses: dict[str, dict[str, Any]] = {}

    for node in sorted(raw_nodes, key=lambda n: n["id"]):
        nid = node["id"]
        if nid in tainted_nodes:
            reasons = direct_taint.get(nid, ["UPSTREAM_TAINTED"])
            status = "TAINTED"
            reason = "; ".join(reasons)
        else:
            lrec = lock_data.get(nid, {})
            if lrec.get("body_hash") != node["_body_hash"]:
                status = "BODY_DIRTY"
                reason = "BODY_HASH_CHANGED"
                body_dirty_nodes.append(nid)
            else:
                status = "CLEAN"
                reason = ""
                clean_nodes.append(nid)
        con.execute(
            "UPDATE nodes SET taint_status = ?, taint_reason = ? WHERE id = ?",
            [status, reason, nid],
        )
        node_statuses[nid] = {
            "id": nid,
            "kind": node["kind"],
            "formal_pkg": node["formal_pkg"],
            "stratum": node.get("stratum", "none"),
            "spec_hash": node["_spec_hash"],
            "body_hash": node["_body_hash"],
            "taint_status": status,
            "taint_reason": reason,
        }

    # Generate audit_nodes_manifest.json with reflexive transitive backward lean_dep cones
    audit_nodes: list[dict[str, Any]] = []
    for node in sorted(raw_nodes, key=lambda n: n["id"]):
        if node["formal_pkg"] not in ("mathlib_vol2", "kernel_arena"):
            continue
        nid = node["id"]
        anc_rows = con.execute(
            """
            WITH RECURSIVE anc(id, depth) AS (
              SELECT ?, 0
              UNION ALL
              SELECT e.src_id, a.depth + 1
              FROM anc a
              JOIN edges e ON e.dst_id = a.id AND e.fiber = 'lean_dep'
              WHERE a.depth < ?
            )
            SELECT DISTINCT id FROM anc
            """,
            [nid, max_depth],
        ).fetchall()
        allowed = sorted({r[0] for r in anc_rows})
        spec = node.get("spec", {})
        if node["formal_pkg"] == "mathlib_vol2":
            decl_names = spec.get("mathlib", {}).get("decl_names", [])
            exp_axioms = spec.get("mathlib", {}).get("expected_axioms", [])
        else:
            decl_names = spec.get("kernel_arena", {}).get("decl_names", [])
            exp_axioms = spec.get("kernel_arena", {}).get("expected_axioms", [])
        audit_nodes.append(
            {
                "id": nid,
                "formal_pkg": node["formal_pkg"],
                "stratum": node.get("stratum", "emerald"),
                "decl_names": decl_names,
                "expected_axioms": sorted(exp_axioms),
                "allowed_ancestors": allowed,
            }
        )

    AUDIT_MANIFEST_PATH.parent.mkdir(parents=True, exist_ok=True)
    AUDIT_MANIFEST_PATH.write_text(
        json.dumps({"nodes": audit_nodes}, indent=2) + "\n", encoding="utf-8"
    )

    total_cycles = sum(len(v) for v in cycles_by_fiber.values())
    structural_ok = (
        total_cycles == 0
        and len(vol1_indegree_violations) == 0
        and len(tcb_violations) == 0
        and len(unresolved_errors) == 0
    )

    report = {
        "structural_ok": structural_ok,
        "node_count": len(raw_nodes),
        "edge_count": len(edges),
        "cycles_by_fiber": cycles_by_fiber,
        "total_cycles": total_cycles,
        "vol1_indegree_violations": [list(r) for r in vol1_indegree_violations],
        "tcb_violations": [list(r) for r in tcb_violations],
        "unresolved_errors": unresolved_errors,
        "prose_lock_mismatches": prose_lock_mismatches,
        "tainted_nodes": sorted(tainted_nodes),
        "body_dirty_nodes": sorted(body_dirty_nodes),
        "clean_nodes": sorted(clean_nodes),
        "nodes": node_statuses,
    }
    REPORT_PATH.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    con.close()
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description="Compile Volume II 5-fiber DuckDB network.")
    parser.add_argument("--print-hashes", action="store_true", help="Print computed spec/body hashes.")
    args = parser.parse_args()
    report = compile_network()
    if args.print_hashes:
        for nid, info in report["nodes"].items():
            print(f"{nid}: spec={info['spec_hash']} body={info['body_hash']} status={info['taint_status']}")
    print(
        f"COMPILE_DB structural_ok={report['structural_ok']} nodes={report['node_count']} "
        f"edges={report['edge_count']} cycles={report['total_cycles']} "
        f"tcb_violations={len(report['tcb_violations'])} "
        f"tainted={len(report['tainted_nodes'])} body_dirty={len(report['body_dirty_nodes'])} "
        f"clean={len(report['clean_nodes'])}"
    )
    if not report["structural_ok"]:
        sys.stderr.write(json.dumps(report, indent=2) + "\n")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
