#!/usr/bin/env python3
"""DuckDB 5-fiber network compiler, hash calculator, TCB & honesty enforcer, and taint engine."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
import tomllib
from pathlib import Path
from typing import Any

import duckdb

REPO_ROOT = Path(__file__).resolve().parent.parent
NODES_DIR = REPO_ROOT / "nodes"
SCHEMA_PATH = Path(__file__).resolve().parent / "schema.sql"
MANIFEST_PATH = REPO_ROOT / "manifest.toml"
GUARDRAILS_PATH = REPO_ROOT / "manifest" / "guardrails.toml"
BIB_PATH = REPO_ROOT / "references_vol2.bib"
LOCK_PATH = REPO_ROOT / "manifest" / "verification_lock.json"
PUB_LOCK_PATH = REPO_ROOT / "manifest" / "publication_lock.json"
DB_PATH = REPO_ROOT / "build" / "vol2.duckdb"
REPORT_PATH = REPO_ROOT / "build" / "compile_report.json"
AUDIT_MANIFEST_PATH = REPO_ROOT / "build" / "audit_nodes_manifest.json"


def resolve_vol1_bib_path() -> Path:
    manifest: dict[str, Any] = {}
    if MANIFEST_PATH.exists():
        manifest = tomllib.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    raw = os.environ.get("CRM_VOL1_ROOT", manifest.get("vol1_root_default", "../categorical-reverse-mathematics"))
    p = Path(raw)
    root = p if p.is_absolute() else (REPO_ROOT / p).resolve()
    return root / "references.bib"

SYM_RE = re.compile(r"\{\{sym:([A-Za-z0-9_.:-]+)\}\}")
REF_RE = re.compile(r"\{\{ref:([A-Za-z0-9_.:-]+)\}\}")
CITE_RE = re.compile(r"\\cite(?:\[[^\]]*\])?\{([^}]+)\}")
BIB_ENTRY_RE = re.compile(r"@\w+\s*\{\s*([^,\s]+)\s*,")
LOCATOR_RE = re.compile(
    r"(Thm\.|Theorem|Prop\.|Proposition|Lem\.|Lemma|Cor\.|Corollary|"
    r"Def\.|Definition|Ex\.|Example|Rem\.|Remark|Ch\.|Chapter|Sec\.|§|\\S|pp?\.|Exp\.|Table|Fig\.)",
    re.IGNORECASE,
)

FIBERS = ("logical_dep", "lean_dep", "prose_paraphrase", "notation", "curriculum")

VALID_KINDS = {
    "vol1_external",
    "symbol",
    "definition",
    "theorem",
    "proposition",
    "lemma",
    "corollary",
    "counterexample",
    "remark",
    "conjecture",
    "principle",
    "problem",
    "inline_claim",
    "prose_block",
    "summary_table",
    "course_pack",
    "work_item",
    "pub_target",
}

VALID_PUB_CHANNELS = {"main_docs", "gh_pages", "lean_export", "gh_issues"}
VALID_PUB_SENSITIVITIES = {
    "spec_and_metrics",
    "spec_and_body",
    "spec_body_and_grounding",
    "lean_only",
    "plan_and_problems",
}
CORE_EXEMPT_GROUNDING_KINDS = ("symbol", "course_pack", "work_item", "pub_target")

CANONICAL_PRIMARY_CATEGORIES = {
    "Proved by Lean code",
    "Proved by 2LTT certificate",
    "English language proof in monograph",
    "External theorem",
    "Folklore",
    "Unfounded",
    "Authorial framework definition",
    "Standard definition",
    "Open problem",
    "Pinned Volume I contract",
    "Verified paraphrase container",
}

VALID_BLUEPRINT_TIERS = {
    "none",
    "lean_ok",
    "lean_witness",
    "twoltt_ok",
    "twoltt_witness",
}

CANONICAL_CHAR_TYPES = {
    "Categorical Equivalence",
    "Duality",
    "Choice Calibration",
    "Conservation / Solvency",
    "Cohomological / Spectral Obstruction",
    "Torsion Obstruction",
    "Postnikov / Coinductive Completeness",
    "Model-Theoretic Amalgamation",
    "Topological Separation",
    "Inhabitation & Finiteness",
    "Homotopy Type / Classifying Space",
    "Counterexample / Disproof",
    "Framework Definition",
    "Metamathematical Principle",
    "Open Problem",
}

PHASE0_SEQ_ORDER = {
    "vol1:def:doctrinal-philosophy": 1,
    "sym:probe-suite": 5,
    "ch01:prose:meta-crm-roadmap": 10,
    "ch01:rem:trident-mode3-2ltt-bootstrap": 18,
    "ch01:def:probe-suite": 20,
    "ch01:def:adm-pareto-frontier": 22,
    "ch01:thm:scotoma-pareto-trichotomy": 24,
    "ch01:thm:flow-f1-threshold-order": 26,
    "ch01:cex:flow-f1-frontier-nonmonotone": 28,
    "ch01:tab:epistemic-probe-regimes": 29,
}


def node_cohort(kind: str) -> str:
    if kind in ("theorem", "proposition", "lemma", "corollary", "counterexample"):
        return "Cohort I"
    if kind in ("definition", "remark", "conjecture", "principle", "problem", "vol1_external", "symbol"):
        return "Cohort II"
    if kind == "inline_claim":
        return "Cohort III"
    if kind in ("prose_block", "summary_table"):
        return "Cohort IV"
    if kind == "work_item":
        return "Project Plan"
    if kind == "pub_target":
        return "Publication Sink"
    return "Course Pack"


def canonical_json(obj: Any) -> str:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def parse_bib_keys(bib_path: Path) -> set[str]:
    if not bib_path.exists():
        return set()
    try:
        text = bib_path.read_text(encoding="utf-8")
    except OSError:
        return set()
    return set(BIB_ENTRY_RE.findall(text))


def kernel_arena_expected_stratum(strata_flags: dict[str, Any]) -> str:
    if strata_flags.get("inner_univalence_V") or strata_flags.get("inner_coalgebra_nu"):
        return "sapphire"
    if strata_flags.get("outer_strict_eq") or strata_flags.get("smallness_replacement"):
        return "amber"
    return "emerald"


def resolve_published_paths(pub: dict[str, Any]) -> list[str]:
    src = pub.get("published_paths_source")
    if src:
        src_path = REPO_ROOT / str(src)
        if src_path.exists():
            try:
                data = json.loads(src_path.read_text(encoding="utf-8"))
                packs = data.get("packs")
                if isinstance(packs, dict) and packs:
                    return sorted(
                        f"pdfs/{entry['stem']}.pdf"
                        for entry in packs.values()
                        if isinstance(entry, dict) and entry.get("stem")
                    )
            except (OSError, json.JSONDecodeError, TypeError):
                pass
        return [
            out.removeprefix("build/gh_pages/")
            for out in pub.get("outputs", [])
            if isinstance(out, str) and out.startswith("build/gh_pages/")
        ]
    raw = pub.get("published_paths", [])
    return [str(p) for p in raw]


def expand_cert_ast(nodes_by_id: dict[int, dict[str, Any]], node_id: int) -> Any:
    """Build a canonical, ID-free AST subtree from a certificate node DAG."""
    node = nodes_by_id[node_id]
    op = node["op"]
    args = node.get("args", [])
    if op in ("UnivS", "UnivF", "Var", "DimVar"):
        return {"op": op, "val": args[0]}
    if op in (
        "BoolS",
        "BoolF",
        "TrueF",
        "FalseF",
        "Dim0",
        "Dim1",
        "CofTop",
        "CofBot",
        "UnitS",
        "StarS",
        "EmptyF",
        "UnitF",
        "StarF",
    ):
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
    elif node["kind"] == "work_item":
        spec_core = {
            "id": node["id"],
            "kind": node["kind"],
            "axis": node["axis"],
            "plan": node.get("plan", {}),
        }
        body_core = {"body": body_payload}
    elif node["kind"] == "pub_target":
        spec_core = {
            "id": node["id"],
            "kind": node["kind"],
            "axis": node["axis"],
            "pub": node.get("pub", {}),
        }
        body_core = {"body": body_payload}
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


def compute_grounding_hash(node: dict[str, Any]) -> str:
    """Compute canonical grounding_hash (VOL2_GROUNDING_V1) isolated from spec/body hashes."""
    grounding_payload = node.get("grounding", {})
    return hashlib.sha256(
        b"VOL2_GROUNDING_V1\x00" + canonical_json(grounding_payload).encode("utf-8")
    ).hexdigest()


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


def compute_tracked_lean_hashes() -> list[list[str]]:
    """Compute SHA-256 digests of tracked Lean sources and build configs for lean_only cone_hash."""
    tracked_files: list[Path] = []
    for rel in (
        "lean-toolchain",
        "kernel_arena/lakefile.toml",
        "kernel_arena/lake-manifest.json",
        "kernel_arena/lean-toolchain",
        "kernel_arena/Main.lean",
        "kernel_arena/KernelArena.lean",
        "mathlib_vol2/lakefile.toml",
        "mathlib_vol2/lake-manifest.json",
        "mathlib_vol2/lean-toolchain",
        "mathlib_vol2/AuditEnv.lean",
        "mathlib_vol2/HomotopyCRM.lean",
    ):
        p = REPO_ROOT / rel
        if p.exists():
            tracked_files.append(p)
    ka_src = REPO_ROOT / "kernel_arena" / "KernelArena"
    if ka_src.exists():
        for p in sorted(ka_src.rglob("*.lean")):
            if "Generated" not in p.parts:
                tracked_files.append(p)
    certs_dir = REPO_ROOT / "certs"
    if certs_dir.exists():
        for p in sorted(certs_dir.rglob("*.2ltt.json")):
            tracked_files.append(p)
    out: list[list[str]] = []
    for p in sorted(set(tracked_files), key=lambda x: str(x.relative_to(REPO_ROOT))):
        h = hashlib.sha256(p.read_bytes()).hexdigest()
        out.append([str(p.relative_to(REPO_ROOT)), h])
    return out


def compile_network() -> dict[str, Any]:
    raw_nodes = load_all_nodes()
    local_bib_keys = parse_bib_keys(BIB_PATH)
    all_bib_keys = local_bib_keys | parse_bib_keys(resolve_vol1_bib_path())
    manifest: dict[str, Any] = {}
    if MANIFEST_PATH.exists():
        manifest = tomllib.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    guardrail_ids: set[str] = set()
    if GUARDRAILS_PATH.exists():
        guardrail_ids = {
            g["id"] for g in tomllib.loads(GUARDRAILS_PATH.read_text(encoding="utf-8")).get("guardrail", [])
        }
    lock_data: dict[str, Any] = {}
    if LOCK_PATH.exists():
        lock_data = json.loads(LOCK_PATH.read_text(encoding="utf-8")).get("nodes", {})
    pub_lock_full: dict[str, Any] = {}
    if PUB_LOCK_PATH.exists():
        pub_lock_full = json.loads(PUB_LOCK_PATH.read_text(encoding="utf-8"))
    pub_lock_targets: dict[str, Any] = pub_lock_full.get("pub_targets", {})

    # 1. Register symbols and compute hashes
    nodes_by_id: dict[str, dict[str, Any]] = {}
    symbols_map: dict[str, dict[str, str]] = {}
    unresolved_errors: list[str] = []
    honesty_violations: list[str] = []

    for node in raw_nodes:
        nid = node["id"]
        kind = node["kind"]
        if kind not in VALID_KINDS:
            unresolved_errors.append(f"INVALID_KIND: {nid} has unknown kind '{kind}'")
        spec_hash, body_hash = compute_node_hashes(node)
        grounding_hash = compute_grounding_hash(node)
        node["_spec_hash"] = spec_hash
        node["_body_hash"] = body_hash
        node["_grounding_hash"] = grounding_hash
        node["_seq_order"] = int(node.get("seq_order", PHASE0_SEQ_ORDER.get(nid, 1000)))
        nodes_by_id[nid] = node
        if kind == "symbol":
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
                    if key not in local_bib_keys:
                        unresolved_errors.append(f"UNRESOLVED_BIBKEY: {nid} cites '{key}'")

        for key in node.get("cite_keys", []):
            if key not in local_bib_keys:
                unresolved_errors.append(f"UNRESOLVED_BIBKEY: {nid} cite_keys contains '{key}'")

    # 3. Populate DuckDB and execute structural & honesty SQL gates
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

    decl_owner_map: dict[str, str] = {}

    for node in raw_nodes:
        nid = node["id"]
        kind = node["kind"]
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
            if cert_path:
                cert_obj = load_cert_data(cert_path)
                exp_stratum = kernel_arena_expected_stratum(cert_obj.get("strata_flags", {}))
                if node.get("stratum", "none") != exp_stratum:
                    honesty_violations.append(
                        f"HONESTY_KA_STRATUM: {nid} declares stratum='{node.get('stratum')}' "
                        f"but cert strata_flags require '{exp_stratum}'"
                    )
        else:
            module = None
            decl_names = []
            expected_axioms = []
            cert_path = None

        locked = lock_data.get(nid, {})
        con.execute(
            "INSERT INTO nodes VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
            [
                nid,
                kind,
                node["title"],
                node.get("chapter", ""),
                node.get("section", ""),
                node["_seq_order"],
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
                node["_grounding_hash"],
                "CLEAN",
                "",
                locked.get("spec_hash"),
                locked.get("body_hash"),
                locked.get("grounding_hash"),
                node["_file_path"],
                json.dumps({k: v for k, v in node.items() if not k.startswith("_")}),
            ],
        )

        # Invariant 1: 1-to-1 Declaration Ownership
        if node["formal_pkg"] == "mathlib_vol2" and not decl_names:
            honesty_violations.append(f"HONESTY_EMPTY_DECLS: {nid} has formal_pkg='mathlib_vol2' with empty decl_names")
        if node["formal_pkg"] in ("mathlib_vol2", "kernel_arena"):
            for d in decl_names:
                if d in decl_owner_map:
                    honesty_violations.append(
                        f"DUPLICATE_DECL_OWNERSHIP: '{d}' claimed by both '{decl_owner_map[d]}' and '{nid}'"
                    )
                else:
                    decl_owner_map[d] = nid
                    con.execute(
                        "INSERT INTO decl_ownership VALUES (?, ?, ?)",
                        [d, nid, "lean_decl"],
                    )
            if node["formal_pkg"] == "kernel_arena" and cert_path:
                if cert_path in decl_owner_map:
                    honesty_violations.append(
                        f"DUPLICATE_DECL_OWNERSHIP: '{cert_path}' claimed by both '{decl_owner_map[cert_path]}' and '{nid}'"
                    )
                else:
                    decl_owner_map[cert_path] = nid
                    con.execute(
                        "INSERT INTO decl_ownership VALUES (?, ?, ?)",
                        [cert_path, nid, "twoltt_cert"],
                    )

        # Validate [plan] on work_item nodes
        if kind == "work_item":
            plan = node.get("plan")
            if not isinstance(plan, dict):
                unresolved_errors.append(f"MISSING_PLAN: {nid} lacks [plan] block")
            else:
                ms = plan.get("milestone")
                mnum = plan.get("milestone_num")
                scode = plan.get("slice_code")
                tmods = plan.get("target_modules")
                dnodes = plan.get("deliverable_nodes")
                grs = plan.get("guardrails")
                summ = plan.get("summary")
                if not isinstance(ms, str) or not ms.strip():
                    unresolved_errors.append(f"INVALID_PLAN: {nid} missing non-empty plan.milestone")
                if isinstance(mnum, bool) or not isinstance(mnum, int) or not (1 <= mnum <= 10):
                    unresolved_errors.append(f"INVALID_PLAN: {nid} plan.milestone_num must be int in 1..10")
                if not isinstance(scode, str) or not scode.strip():
                    unresolved_errors.append(f"INVALID_PLAN: {nid} missing non-empty plan.slice_code")
                if not isinstance(tmods, list) or not all(isinstance(x, str) for x in tmods):
                    unresolved_errors.append(f"INVALID_PLAN: {nid} plan.target_modules must be list of strings")
                if not isinstance(dnodes, list) or not all(isinstance(x, str) for x in dnodes):
                    unresolved_errors.append(f"INVALID_PLAN: {nid} plan.deliverable_nodes must be list of strings")
                if not isinstance(grs, list) or not all(isinstance(x, str) for x in grs):
                    unresolved_errors.append(f"INVALID_PLAN: {nid} plan.guardrails must be list of strings")
                elif guardrail_ids:
                    for gid in grs:
                        if gid not in guardrail_ids:
                            unresolved_errors.append(f"INVALID_PLAN_GUARDRAIL: {nid} unknown guardrail '{gid}'")
                if not isinstance(summ, str) or not summ.strip():
                    unresolved_errors.append(f"INVALID_PLAN: {nid} missing non-empty plan.summary")

        # Validate [pub] on pub_target nodes
        if kind == "pub_target":
            pub = node.get("pub")
            if not isinstance(pub, dict):
                unresolved_errors.append(f"MISSING_PUB: {nid} lacks [pub] block")
            else:
                ch = pub.get("channel")
                sens = pub.get("sensitivity")
                outs = pub.get("outputs")
                if ch not in VALID_PUB_CHANNELS:
                    unresolved_errors.append(f"INVALID_PUB_CHANNEL: {nid} has '{ch}'")
                if sens not in VALID_PUB_SENSITIVITIES:
                    unresolved_errors.append(f"INVALID_PUB_SENSITIVITY: {nid} has '{sens}'")
                if not isinstance(outs, list) or len(outs) == 0 or not all(isinstance(x, str) for x in outs):
                    unresolved_errors.append(f"INVALID_PUB_OUTPUTS: {nid} pub.outputs must be non-empty string list")

        # Parse & validate [grounding] on non-exempt nodes
        if kind not in CORE_EXEMPT_GROUNDING_KINDS:
            g = node.get("grounding")
            if not isinstance(g, dict):
                honesty_violations.append(f"MISSING_GROUNDING: {nid} lacks top-level [grounding] block")
                continue

            primary_category = g.get("primary_category", "")
            blueprint_tier = g.get("blueprint_tier", "")
            char_types = g.get("characterization_types", [])
            witness_scope = g.get("witness_scope", "")
            dual_pillars = g.get("dual_pillars", [])

            if primary_category not in CANONICAL_PRIMARY_CATEGORIES:
                honesty_violations.append(
                    f"INVALID_PRIMARY_CATEGORY: {nid} has '{primary_category}'"
                )
            if blueprint_tier not in VALID_BLUEPRINT_TIERS:
                honesty_violations.append(
                    f"INVALID_BLUEPRINT_TIER: {nid} has '{blueprint_tier}'"
                )
            if not isinstance(char_types, list) or len(char_types) == 0:
                honesty_violations.append(
                    f"EMPTY_CHARACTERIZATION_TYPES: {nid} requires non-empty characterization_types"
                )
            else:
                for ct in char_types:
                    if ct not in CANONICAL_CHAR_TYPES:
                        honesty_violations.append(
                            f"INVALID_CHARACTERIZATION_TYPE: {nid} has unknown '{ct}'"
                        )
            if not isinstance(witness_scope, str):
                honesty_violations.append(f"INVALID_WITNESS_SCOPE: {nid} witness_scope must be string")
                witness_scope = ""
            if not isinstance(dual_pillars, list):
                honesty_violations.append(f"INVALID_DUAL_PILLARS: {nid} dual_pillars must be array")
                dual_pillars = []

            # Invariant 2: Two-Tier Blueprint Honesty
            gtier = node["grounding_tier"]
            fpkg = node["formal_pkg"]
            if gtier == "lean_ok" and blueprint_tier != "lean_ok":
                honesty_violations.append(
                    f"HONESTY_BLUEPRINT_TIER: {nid} has grounding_tier='lean_ok' but blueprint_tier='{blueprint_tier}'"
                )
            if gtier == "twoltt_ok" and blueprint_tier != "twoltt_ok":
                honesty_violations.append(
                    f"HONESTY_BLUEPRINT_TIER: {nid} has grounding_tier='twoltt_ok' but blueprint_tier='{blueprint_tier}'"
                )
            if blueprint_tier in ("lean_witness", "twoltt_witness") and not witness_scope.strip():
                honesty_violations.append(
                    f"HONESTY_MISSING_WITNESS_SCOPE: {nid} has blueprint_tier='{blueprint_tier}' without non-empty witness_scope"
                )
            if blueprint_tier in ("lean_ok", "lean_witness") and fpkg != "mathlib_vol2":
                honesty_violations.append(
                    f"HONESTY_BLUEPRINT_PKG: {nid} has blueprint_tier='{blueprint_tier}' with formal_pkg='{fpkg}'"
                )
            if blueprint_tier in ("twoltt_ok", "twoltt_witness") and fpkg != "kernel_arena":
                honesty_violations.append(
                    f"HONESTY_BLUEPRINT_PKG: {nid} has blueprint_tier='{blueprint_tier}' with formal_pkg='{fpkg}'"
                )
            if primary_category == "Proved by Lean code" and blueprint_tier != "lean_ok":
                honesty_violations.append(
                    f"HONESTY_CATEGORY_TIER: {nid} claims 'Proved by Lean code' with blueprint_tier='{blueprint_tier}'"
                )
            if primary_category == "Proved by 2LTT certificate" and blueprint_tier != "twoltt_ok":
                honesty_violations.append(
                    f"HONESTY_CATEGORY_TIER: {nid} claims 'Proved by 2LTT certificate' with blueprint_tier='{blueprint_tier}'"
                )

            # Invariant 3: Citation-Locator Non-Vacuity
            ext_pillars = [
                p for p in dual_pillars
                if isinstance(p, dict) and p.get("kind") == "external_cite"
            ]
            if (
                gtier in ("external_theorem", "folklore", "standard_def")
                or primary_category in ("External theorem", "Folklore", "Standard definition")
            ) and not ext_pillars:
                honesty_violations.append(
                    f"HONESTY_MISSING_EXTERNAL_CITE: {nid} requires at least one external_cite dual_pillar"
                )

            for p in dual_pillars:
                if not isinstance(p, dict):
                    honesty_violations.append(f"INVALID_DUAL_PILLAR: {nid} dual_pillar is not a table")
                    continue
                for req_k in ("kind", "ref", "purpose"):
                    if not isinstance(p.get(req_k), str) or not p.get(req_k, "").strip():
                        honesty_violations.append(
                            f"INVALID_DUAL_PILLAR: {nid} dual_pillar missing non-empty '{req_k}'"
                        )
                if p.get("kind") == "external_cite":
                    bib_ref = p.get("ref", "")
                    loc = p.get("locator", "")
                    if bib_ref not in all_bib_keys:
                        honesty_violations.append(
                            f"HONESTY_UNVERIFIED_CITE: {nid} external_cite ref '{bib_ref}' not in Vol I/II .bib"
                        )
                    if not isinstance(loc, str) or not loc.strip() or not LOCATOR_RE.search(loc):
                        honesty_violations.append(
                            f"HONESTY_VACUOUS_LOCATOR: {nid} external_cite '{bib_ref}' lacks specific Thm./Prop./§/pp. locator ('{loc}')"
                        )

            con.execute(
                "INSERT INTO claim_groundings VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                [
                    nid,
                    node_cohort(kind),
                    primary_category,
                    blueprint_tier,
                    json.dumps(char_types),
                    witness_scope,
                    json.dumps(dual_pillars),
                    node["_grounding_hash"],
                ],
            )

    for src_id, dst_id, fiber, meta_json in edges:
        con.execute("INSERT INTO edges VALUES (?, ?, ?, ?)", [src_id, dst_id, fiber, meta_json])

    for nid, lrec in lock_data.items():
        if nid in nodes_by_id:
            con.execute(
                "INSERT INTO verification_receipts VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
                [
                    nid,
                    lrec.get("spec_hash", ""),
                    lrec.get("body_hash", ""),
                    lrec.get("grounding_hash", ""),
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

    # Gate (b): vol1_external / pinned_vol1 in-degree == 0
    vol1_indegree_violations = con.execute(
        """
        SELECT e.src_id, e.dst_id, e.fiber
        FROM edges e
        JOIN nodes n ON e.dst_id = n.id
        WHERE n.kind = 'vol1_external' OR n.grounding_tier IN ('vol1_external', 'pinned_vol1')
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

    # Gate (d): Publication sink out-degree == 0 to non-pub_target nodes
    pub_outdegree_violations = con.execute(
        """
        SELECT e.src_id, e.dst_id, e.fiber, dst.kind
        FROM edges e
        JOIN nodes src ON e.src_id = src.id
        JOIN nodes dst ON e.dst_id = dst.id
        WHERE src.kind = 'pub_target'
          AND dst.kind <> 'pub_target'
        """
    ).fetchall()

    # Invariant 4: Conjecture Quarantine over logical_dep
    quarantine_rows = con.execute(
        """
        WITH RECURSIVE reach(src_id, dst_id, depth) AS (
          SELECT e.src_id, e.dst_id, 1
          FROM edges e
          WHERE e.fiber = 'logical_dep'
          UNION ALL
          SELECT r.src_id, e.dst_id, r.depth + 1
          FROM reach r
          JOIN edges e ON r.dst_id = e.src_id AND e.fiber = 'logical_dep'
          WHERE r.depth < ?
        )
        SELECT DISTINCT r.src_id, r.dst_id
        FROM reach r
        JOIN nodes src ON r.src_id = src.id
        JOIN nodes dst ON r.dst_id = dst.id
        LEFT JOIN claim_groundings gs ON gs.node_id = src.id
        LEFT JOIN claim_groundings gd ON gd.node_id = dst.id
        WHERE (
            src.grounding_tier IN ('unfounded_conjecture', 'open_problem')
            OR src.kind IN ('conjecture', 'problem')
            OR gs.primary_category IN ('Unfounded', 'Open problem')
          )
          AND (
            dst.grounding_tier IN ('lean_ok', 'twoltt_ok', 'prose_proof')
            OR gd.blueprint_tier IN ('lean_ok', 'twoltt_ok')
            OR gd.primary_category IN (
              'Proved by Lean code',
              'Proved by 2LTT certificate',
              'English language proof in monograph'
            )
          )
        """,
        [max_depth],
    ).fetchall()
    for q_src, q_dst in quarantine_rows:
        is_cond = bool(nodes_by_id[q_dst].get("spec", {}).get("conditional_on_conjecture", False))
        if not is_cond:
            honesty_violations.append(
                f"HONESTY_CONJECTURE_QUARANTINE: unflagged logical_dep path {q_src} -> {q_dst} without spec.conditional_on_conjecture = true"
            )

    # Invariant 5: Cohort IV Paraphrase Completeness
    orphan_cohort4 = con.execute(
        """
        SELECT n.id
        FROM nodes n
        WHERE n.kind IN ('prose_block', 'summary_table')
          AND NOT EXISTS (
            SELECT 1 FROM edges e
            WHERE e.dst_id = n.id AND e.fiber = 'prose_paraphrase'
          )
        ORDER BY n.id
        """
    ).fetchall()
    for (orphan_id,) in orphan_cohort4:
        honesty_violations.append(
            f"HONESTY_COHORT4_PARAPHRASE: Cohort IV node '{orphan_id}' has 0 incoming prose_paraphrase edges"
        )

    # Gate (e): Multi-fiber forward transitive taint cone + prose_paraphrase lock check
    core_nodes = [n for n in raw_nodes if n["kind"] not in ("work_item", "pub_target")]
    core_ids = {n["id"] for n in core_nodes}
    work_item_nodes = [n for n in raw_nodes if n["kind"] == "work_item"]
    pub_target_nodes = [n for n in raw_nodes if n["kind"] == "pub_target"]

    direct_taint: dict[str, list[str]] = {}
    pub_prose_mismatches: dict[str, list[str]] = {}
    prose_lock_mismatches: list[dict[str, str]] = []

    for node in core_nodes:
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
        SELECT e.src_id, e.dst_id, e.metadata_json, src.spec_hash, dst.kind
        FROM edges e
        JOIN nodes src ON e.src_id = src.id
        JOIN nodes dst ON e.dst_id = dst.id
        WHERE e.fiber = 'prose_paraphrase'
        """
    ).fetchall()
    for target_id, consumer_id, meta_raw, target_spec_hash, consumer_kind in pp_rows:
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
            if consumer_kind == "pub_target":
                pub_prose_mismatches.setdefault(consumer_id, []).append(
                    f"PROSE_LOCK_MISMATCH({target_id})"
                )
            else:
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
        tainted_nodes = {r[0] for r in cone_rows if r[0] in core_ids}

    body_dirty_nodes: list[str] = []
    grounding_dirty_nodes: list[str] = []
    clean_nodes: list[str] = []
    node_statuses: dict[str, dict[str, Any]] = {}

    for node in sorted(core_nodes, key=lambda n: n["id"]):
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
            elif lrec.get("grounding_hash", "") != node["_grounding_hash"]:
                status = "GROUNDING_DIRTY"
                reason = "GROUNDING_HASH_CHANGED"
                grounding_dirty_nodes.append(nid)
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
            "cohort": node_cohort(node["kind"]),
            "formal_pkg": node["formal_pkg"],
            "stratum": node.get("stratum", "none"),
            "spec_hash": node["_spec_hash"],
            "body_hash": node["_body_hash"],
            "grounding_hash": node["_grounding_hash"],
            "taint_status": status,
            "taint_reason": reason,
        }

    # Evaluate work_item nodes mechanically from deliverable_nodes status in DuckDB
    sorted_work_items = sorted(work_item_nodes, key=lambda n: (n["_seq_order"], n["id"]))
    work_item_eval: list[dict[str, Any]] = []
    lowest_unverified_id: str | None = None
    for node in sorted_work_items:
        nid = node["id"]
        plan = node.get("plan", {})
        delivs = plan.get("deliverable_nodes", [])
        total = len(delivs)
        if total > 0:
            ph = ",".join("?" for _ in delivs)
            rows = con.execute(
                f"SELECT id, taint_status FROM nodes WHERE id IN ({ph}) AND kind NOT IN ('work_item', 'pub_target')",
                delivs,
            ).fetchall()
            existing_count = len(rows)
            verified_count = sum(1 for _, ts in rows if ts == "CLEAN")
        else:
            existing_count = 0
            verified_count = 0
        is_verified = total > 0 and verified_count == total
        if not is_verified and lowest_unverified_id is None:
            lowest_unverified_id = nid
        work_item_eval.append(
            {
                "node": node,
                "existing_count": existing_count,
                "verified_count": verified_count,
                "total": total,
                "is_verified": is_verified,
            }
        )

    work_items_report: dict[str, Any] = {}
    work_item_counts = {"VERIFIED": 0, "ACTIVE": 0, "PLANNED": 0}
    for rec in work_item_eval:
        node = rec["node"]
        nid = node["id"]
        plan = node.get("plan", {})
        if rec["is_verified"]:
            wi_status = "VERIFIED"
        elif nid == lowest_unverified_id or rec["existing_count"] > 0:
            wi_status = "ACTIVE"
        else:
            wi_status = "PLANNED"
        work_item_counts[wi_status] += 1
        wi_reason = f"{rec['verified_count']}/{rec['total']} deliverables CLEAN"
        con.execute(
            "INSERT INTO work_items VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
            [
                nid,
                plan["milestone"],
                int(plan["milestone_num"]),
                plan["slice_code"],
                json.dumps(plan["target_modules"]),
                json.dumps(plan["deliverable_nodes"]),
                json.dumps(plan["guardrails"]),
                plan["summary"],
                wi_status,
                rec["verified_count"],
                rec["total"],
            ],
        )
        con.execute(
            "UPDATE nodes SET taint_status = ?, taint_reason = ? WHERE id = ?",
            [wi_status, wi_reason, nid],
        )
        work_items_report[nid] = {
            "id": nid,
            "seq_order": node["_seq_order"],
            "milestone": plan["milestone"],
            "milestone_num": int(plan["milestone_num"]),
            "slice_code": plan["slice_code"],
            "target_modules": plan["target_modules"],
            "deliverable_nodes": plan["deliverable_nodes"],
            "guardrails": plan["guardrails"],
            "summary": plan["summary"],
            "status": wi_status,
            "verified_deliverables": rec["verified_count"],
            "total_deliverables": rec["total"],
            "spec_hash": node["_spec_hash"],
        }
        node_statuses[nid] = {
            "id": nid,
            "kind": node["kind"],
            "cohort": node_cohort(node["kind"]),
            "formal_pkg": node["formal_pkg"],
            "stratum": node.get("stratum", "none"),
            "spec_hash": node["_spec_hash"],
            "body_hash": node["_body_hash"],
            "grounding_hash": node["_grounding_hash"],
            "taint_status": wi_status,
            "taint_reason": wi_reason,
        }

    # Evaluate pub_target sinks and deterministic cone_hash in DuckDB
    manifest_meta = {
        k: manifest.get(k, "")
        for k in (
            "working_title",
            "working_subtitle",
            "title_locked",
            "author",
            "location",
            "license",
            "lean_toolchain",
            "vol1_root_default",
            "vol1_pinned_head",
            "vol1_zenodo_doi",
            "github_repo",
            "pages_base_url",
            "citation_date",
            "phase",
            "active_slice",
        )
    }
    issues_meta = pub_lock_full.get("issues", {})
    lean_tool_hashes = compute_tracked_lean_hashes() if pub_target_nodes else []

    pub_resolved_paths: dict[str, list[str]] = {
        n["id"]: resolve_published_paths(n.get("pub", {})) for n in pub_target_nodes
    }
    pub_targets_report: dict[str, Any] = {}
    pub_tainted_nodes: list[str] = []
    pub_dirty_nodes: list[str] = []
    pub_clean_nodes: list[str] = []

    for node in sorted(pub_target_nodes, key=lambda n: (n["_seq_order"], n["id"])):
        nid = node["id"]
        pub = node.get("pub", {})
        channel = pub.get("channel", "")
        sensitivity = pub.get("sensitivity", "")
        outputs = pub.get("outputs", [])
        published_paths = pub_resolved_paths.get(nid, [])

        if nid == "pub:pdf:course-packs":
            cone_sql = """
                WITH RECURSIVE cone(id, depth) AS (
                  SELECT ?, 0
                  UNION ALL
                  SELECT e.src_id, c.depth + 1
                  FROM cone c
                  JOIN edges e ON e.dst_id = c.id AND e.fiber IN ('curriculum', 'logical_dep', 'lean_dep')
                  WHERE c.depth < ?
                )
                SELECT DISTINCT id FROM cone
            """
        else:
            cone_sql = """
                WITH RECURSIVE cone(id, depth) AS (
                  SELECT ?, 0
                  UNION ALL
                  SELECT e.src_id, c.depth + 1
                  FROM cone c
                  JOIN edges e ON e.dst_id = c.id
                  WHERE c.depth < ?
                )
                SELECT DISTINCT id FROM cone
            """
        cone_ids = {r[0] for r in con.execute(cone_sql, [nid, max_depth]).fetchall()}

        if sensitivity == "spec_and_metrics":
            cone_payload: dict[str, Any] = {
                "pub_spec_hash": node["_spec_hash"],
                "manifest": manifest_meta,
                "issues": issues_meta,
                "core_nodes": [
                    list(r)
                    for r in con.execute(
                        "SELECT id, kind, stratum, spec_hash, taint_status FROM nodes "
                        "WHERE kind NOT IN ('work_item', 'pub_target') ORDER BY id"
                    ).fetchall()
                ],
                "work_items": [
                    list(r)
                    for r in con.execute(
                        "SELECT node_id, status, verified_deliverables, total_deliverables FROM work_items ORDER BY node_id"
                    ).fetchall()
                ],
            }
        elif sensitivity == "spec_and_body":
            if nid == "pub:pdf:course-packs":
                core_in_cone = sorted(cid for cid in cone_ids if cid in core_ids)
                if core_in_cone:
                    ph = ",".join("?" for _ in core_in_cone)
                    scoped_rows = [
                        list(r)
                        for r in con.execute(
                            f"SELECT id, kind, stratum, spec_hash, body_hash, taint_status FROM nodes "
                            f"WHERE id IN ({ph}) ORDER BY id",
                            core_in_cone,
                        ).fetchall()
                    ]
                else:
                    scoped_rows = []
                cone_payload = {
                    "pub_spec_hash": node["_spec_hash"],
                    "cone_nodes": scoped_rows,
                }
            else:
                cone_payload = {
                    "pub_spec_hash": node["_spec_hash"],
                    "manifest": manifest_meta,
                    "core_nodes": [
                        list(r)
                        for r in con.execute(
                            "SELECT id, kind, stratum, spec_hash, body_hash, taint_status FROM nodes "
                            "WHERE kind NOT IN ('work_item', 'pub_target') ORDER BY id"
                        ).fetchall()
                    ],
                }
        elif sensitivity == "spec_body_and_grounding":
            cone_payload = {
                "pub_spec_hash": node["_spec_hash"],
                "manifest": manifest_meta,
                "issues": issues_meta,
                "core_nodes": [
                    list(r)
                    for r in con.execute(
                        "SELECT id, kind, stratum, spec_hash, body_hash, grounding_hash, taint_status FROM nodes "
                        "WHERE kind NOT IN ('work_item', 'pub_target') ORDER BY id"
                    ).fetchall()
                ],
                "work_items": [
                    list(r)
                    for r in con.execute(
                        "SELECT node_id, status, verified_deliverables, total_deliverables FROM work_items ORDER BY node_id"
                    ).fetchall()
                ],
                "edges": [
                    list(r)
                    for r in con.execute(
                        "SELECT src_id, dst_id, fiber, metadata_json FROM edges ORDER BY fiber, src_id, dst_id"
                    ).fetchall()
                ],
                "decl_ownership": [
                    list(r)
                    for r in con.execute(
                        "SELECT decl_or_cert, node_id, ownership_kind FROM decl_ownership ORDER BY decl_or_cert"
                    ).fetchall()
                ],
            }
        elif sensitivity == "lean_only":
            cone_payload = {
                "pub_spec_hash": node["_spec_hash"],
                "formal_nodes": [
                    list(r)
                    for r in con.execute(
                        "SELECT id, formal_pkg, module, spec_hash, body_hash, cert_path FROM nodes "
                        "WHERE formal_pkg IN ('mathlib_vol2', 'kernel_arena') ORDER BY id"
                    ).fetchall()
                ],
                "tracked_lean_hashes": lean_tool_hashes,
            }
        else:  # plan_and_problems
            cone_payload = {
                "pub_spec_hash": node["_spec_hash"],
                "work_items": [
                    list(r)
                    for r in con.execute(
                        "SELECT node_id, milestone, milestone_num, slice_code, status, "
                        "verified_deliverables, total_deliverables, summary, deliverable_nodes_json "
                        "FROM work_items ORDER BY node_id"
                    ).fetchall()
                ],
                "problems_and_tainted": [
                    list(r)
                    for r in con.execute(
                        "SELECT id, kind, title, spec_hash, taint_status FROM nodes "
                        "WHERE kind IN ('problem', 'conjecture') "
                        "OR (kind NOT IN ('work_item', 'pub_target') AND taint_status = 'TAINTED') "
                        "ORDER BY id"
                    ).fetchall()
                ],
            }

        pub_providers = [
            {
                "id": r[0],
                "spec_hash": nodes_by_id[r[0]]["_spec_hash"],
                "published_paths": pub_resolved_paths.get(r[0], []),
            }
            for r in con.execute(
                """
                SELECT DISTINCT e.src_id
                FROM edges e
                JOIN nodes src ON e.src_id = src.id
                WHERE e.dst_id = ? AND src.kind = 'pub_target'
                ORDER BY e.src_id
                """,
                [nid],
            ).fetchall()
        ]
        if pub_providers:
            cone_payload["pub_providers"] = pub_providers

        cone_hash = hashlib.sha256(
            b"VOL2_PUB_CONE_V1\x00" + canonical_json(cone_payload).encode("utf-8")
        ).hexdigest()
        locked_cone_hash = pub_lock_targets.get(nid, {}).get("cone_hash")

        in_cone_tainted = sorted(cid for cid in cone_ids if cid in tainted_nodes)
        if sensitivity in ("spec_and_metrics", "spec_body_and_grounding") or (
            sensitivity == "spec_and_body" and nid != "pub:pdf:course-packs"
        ):
            upstream_tainted = sorted(set(in_cone_tainted) | tainted_nodes)
        elif sensitivity == "lean_only":
            upstream_tainted = sorted(
                set(in_cone_tainted)
                | {tid for tid in tainted_nodes if nodes_by_id[tid]["formal_pkg"] in ("mathlib_vol2", "kernel_arena")}
            )
        else:
            upstream_tainted = in_cone_tainted
        prov_tainted = [p["id"] for p in pub_providers if p["id"] in pub_prose_mismatches]
        if prov_tainted:
            upstream_tainted = sorted(set(upstream_tainted) | set(prov_tainted))

        if nid in pub_prose_mismatches:
            pub_status = "TAINTED"
            pub_reason = "; ".join(pub_prose_mismatches[nid])
            pub_tainted_nodes.append(nid)
        elif upstream_tainted:
            pub_status = "TAINTED"
            pub_reason = f"UPSTREAM_TAINTED({','.join(upstream_tainted[:3])})"
            pub_tainted_nodes.append(nid)
        elif locked_cone_hash != cone_hash:
            pub_status = "ARTIFACT_DIRTY"
            pub_reason = "CONE_HASH_CHANGED" if locked_cone_hash else "NO_PUBLICATION_LOCK"
            pub_dirty_nodes.append(nid)
        else:
            pub_status = "CLEAN"
            pub_reason = ""
            pub_clean_nodes.append(nid)

        con.execute(
            "INSERT INTO pub_targets VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
            [
                nid,
                channel,
                sensitivity,
                json.dumps(outputs),
                json.dumps(published_paths),
                cone_hash,
                locked_cone_hash,
                pub_status,
                pub_reason,
            ],
        )
        con.execute(
            "UPDATE nodes SET taint_status = ?, taint_reason = ? WHERE id = ?",
            [pub_status, pub_reason, nid],
        )
        pub_targets_report[nid] = {
            "id": nid,
            "title": node["title"],
            "channel": channel,
            "sensitivity": sensitivity,
            "outputs": outputs,
            "published_paths": published_paths,
            "cone_hash": cone_hash,
            "locked_cone_hash": locked_cone_hash,
            "pub_status": pub_status,
            "pub_reason": pub_reason,
            "spec_hash": node["_spec_hash"],
        }
        node_statuses[nid] = {
            "id": nid,
            "kind": node["kind"],
            "cohort": node_cohort(node["kind"]),
            "formal_pkg": node["formal_pkg"],
            "stratum": node.get("stratum", "none"),
            "spec_hash": node["_spec_hash"],
            "body_hash": node["_body_hash"],
            "grounding_hash": node["_grounding_hash"],
            "taint_status": pub_status,
            "taint_reason": pub_reason,
        }

    # Generate audit_nodes_manifest.json with reflexive transitive backward lean_dep cones
    audit_nodes: list[dict[str, Any]] = []
    for node in sorted(core_nodes, key=lambda n: n["id"]):
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
            ka_flags = None
        else:
            decl_names = spec.get("kernel_arena", {}).get("decl_names", [])
            exp_axioms = spec.get("kernel_arena", {}).get("expected_axioms", [])
            cpath = spec.get("cert_path") or node.get("cert_path")
            ka_flags = load_cert_data(cpath).get("strata_flags", {}) if cpath else None
        audit_entry: dict[str, Any] = {
            "id": nid,
            "formal_pkg": node["formal_pkg"],
            "stratum": node.get("stratum", "emerald"),
            "decl_names": decl_names,
            "expected_axioms": sorted(exp_axioms),
            "allowed_ancestors": allowed,
        }
        if ka_flags is not None:
            audit_entry["cert_strata_flags"] = ka_flags
        audit_nodes.append(audit_entry)

    AUDIT_MANIFEST_PATH.parent.mkdir(parents=True, exist_ok=True)
    AUDIT_MANIFEST_PATH.write_text(
        json.dumps({"nodes": audit_nodes}, indent=2) + "\n", encoding="utf-8"
    )

    total_cycles = sum(len(v) for v in cycles_by_fiber.values())
    structural_ok = (
        total_cycles == 0
        and len(vol1_indegree_violations) == 0
        and len(tcb_violations) == 0
        and len(pub_outdegree_violations) == 0
        and len(unresolved_errors) == 0
        and len(honesty_violations) == 0
    )

    report = {
        "structural_ok": structural_ok,
        "node_count": len(raw_nodes),
        "core_node_count": len(core_nodes),
        "work_item_count": len(work_item_nodes),
        "pub_target_count": len(pub_target_nodes),
        "edge_count": len(edges),
        "decl_ownership_count": len(decl_owner_map),
        "cycles_by_fiber": cycles_by_fiber,
        "total_cycles": total_cycles,
        "vol1_indegree_violations": [list(r) for r in vol1_indegree_violations],
        "tcb_violations": [list(r) for r in tcb_violations],
        "pub_outdegree_violations": [list(r) for r in pub_outdegree_violations],
        "unresolved_errors": unresolved_errors,
        "honesty_violations": honesty_violations,
        "prose_lock_mismatches": prose_lock_mismatches,
        "tainted_nodes": sorted(tainted_nodes),
        "body_dirty_nodes": sorted(body_dirty_nodes),
        "grounding_dirty_nodes": sorted(grounding_dirty_nodes),
        "clean_nodes": sorted(clean_nodes),
        "work_items": work_items_report,
        "work_item_counts": work_item_counts,
        "pub_targets": pub_targets_report,
        "pub_tainted_nodes": sorted(pub_tainted_nodes),
        "pub_dirty_nodes": sorted(pub_dirty_nodes),
        "pub_clean_nodes": sorted(pub_clean_nodes),
        "nodes": node_statuses,
    }
    REPORT_PATH.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    con.close()
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description="Compile Volume II 5-fiber DuckDB network.")
    parser.add_argument("--print-hashes", action="store_true", help="Print computed spec/body/grounding hashes.")
    args = parser.parse_args()
    report = compile_network()
    if args.print_hashes:
        for nid, info in report["nodes"].items():
            print(
                f"{nid}: spec={info['spec_hash']} body={info['body_hash']} "
                f"grounding={info['grounding_hash']} status={info['taint_status']}"
            )
    print(
        f"COMPILE_DB structural_ok={report['structural_ok']} nodes={report['node_count']} "
        f"core={report['core_node_count']} work_items={report['work_item_count']} "
        f"pub_targets={report['pub_target_count']} edges={report['edge_count']} "
        f"decls={report['decl_ownership_count']} cycles={report['total_cycles']} "
        f"tcb_violations={len(report['tcb_violations'])} "
        f"pub_out_violations={len(report['pub_outdegree_violations'])} "
        f"honesty_violations={len(report['honesty_violations'])} "
        f"tainted={len(report['tainted_nodes'])} body_dirty={len(report['body_dirty_nodes'])} "
        f"grounding_dirty={len(report['grounding_dirty_nodes'])} clean={len(report['clean_nodes'])} "
        f"pub_clean={len(report['pub_clean_nodes'])} pub_dirty={len(report['pub_dirty_nodes'])} "
        f"pub_tainted={len(report['pub_tainted_nodes'])}"
    )
    if not report["structural_ok"]:
        sys.stderr.write(json.dumps(report, indent=2) + "\n")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
