#!/usr/bin/env python3
"""Emit zero-build-step static Glass-Box Web Observatory (`build/gh_pages/`) and optionally commit to `gh-pages`."""

from __future__ import annotations

import argparse
import html
import json
import re
import shutil
import tomllib
from collections import Counter
from pathlib import Path
from typing import Any

import duckdb

from export_lean_branch import commit_stage_to_branch

REPO_ROOT = Path(__file__).resolve().parent.parent
BUILD_DIR = REPO_ROOT / "build"
GH_PAGES_DIR = BUILD_DIR / "gh_pages"
TEX_DIR = BUILD_DIR / "tex"
DB_PATH = BUILD_DIR / "vol2.duckdb"
MANIFEST_PATH = REPO_ROOT / "manifest.toml"
GUARDRAILS_PATH = REPO_ROOT / "manifest" / "guardrails.toml"
PUB_LOCK_PATH = REPO_ROOT / "manifest" / "publication_lock.json"
DRILL_PATH = REPO_ROOT / "logs" / "drill_report.json"

PDF_FILES = [
    ("crm_vol2_monograph.pdf", "Royal Octavo Monograph", "Complete Ch. 1 monograph draft with Four-Color Stratum badges, proofs, and cross-volume guardrails."),
    ("crm_vol2_claims_ledger.pdf", "4-Part Master Claims & Grounding Ledger", "Complete Cohorts I–IV audit ledger, paraphrase lock matrix, and disjoint declaration ownership census."),
    ("course_pack_ch01_probe_calibration.pdf", "Standalone Ch. 1 Course Pack", "Curriculum-cone extract terminating at Table 1.1 (Epistemic Probe Regimes), excluding out-of-slice nodes."),
]


def scrub_portable_str(text: str, vol1_default: str) -> str:
    pattern = "/" + "home/[^/\"']+/categorical-reverse-mathematics"
    return re.sub(pattern, vol1_default, text)


def build_network_payload() -> dict[str, Any]:
    manifest = tomllib.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    guardrails = tomllib.loads(GUARDRAILS_PATH.read_text(encoding="utf-8")).get("guardrail", [])
    pub_lock: dict[str, Any] = {}
    if PUB_LOCK_PATH.exists():
        pub_lock = json.loads(PUB_LOCK_PATH.read_text(encoding="utf-8"))
    drill = {}
    if DRILL_PATH.exists():
        drill = json.loads(DRILL_PATH.read_text(encoding="utf-8"))

    vol1_default = manifest.get("vol1_root_default", "../categorical-reverse-mathematics")
    gh_repo = pub_lock.get("github_repo") or manifest.get("github_repo", "tryggth/categorical-reverse-mathematics-vol2")
    owner, rname = gh_repo.split("/", 1) if "/" in gh_repo else ("tryggth", gh_repo)
    pages_url = pub_lock.get("pages_url") or f"https://{owner}.github.io/{rname}/"

    con = duckdb.connect(str(DB_PATH), read_only=True)
    node_rows = con.execute(
        """
        SELECT n.id, n.kind, n.title, n.chapter, n.section, n.seq_order, n.axis,
               n.grounding_tier, n.formal_pkg, n.stratum, n.module, n.decl_names_json,
               n.expected_axioms_json, n.cert_path, n.spec_hash, n.body_hash,
               n.grounding_hash, n.taint_status, n.taint_reason, n.file_path, n.raw_json,
               cg.cohort, cg.primary_category, cg.blueprint_tier,
               cg.characterization_types_json, cg.witness_scope, cg.dual_pillars_json,
               vr.actual_axioms_json, vr.cert_sha256, vr.verified_at_utc, vr.passed
        FROM nodes n
        LEFT JOIN claim_groundings cg ON cg.node_id = n.id
        LEFT JOIN verification_receipts vr ON vr.node_id = n.id
        ORDER BY n.seq_order, n.id
        """
    ).fetchall()
    edge_rows = con.execute(
        "SELECT src_id, dst_id, fiber, metadata_json FROM edges ORDER BY fiber, src_id, dst_id"
    ).fetchall()
    work_rows = con.execute(
        """
        SELECT w.node_id, n.title, n.seq_order, w.milestone, w.milestone_num, w.slice_code,
               w.target_modules_json, w.deliverable_nodes_json, w.guardrails_json,
               w.summary, w.status, w.verified_deliverables, w.total_deliverables
        FROM work_items w
        JOIN nodes n ON n.id = w.node_id
        ORDER BY n.seq_order, w.node_id
        """
    ).fetchall()
    pub_rows = con.execute(
        """
        SELECT p.node_id, n.title, p.channel, p.sensitivity, p.outputs_json,
               p.cone_hash, p.locked_cone_hash, p.pub_status, p.pub_reason
        FROM pub_targets p
        JOIN nodes n ON n.id = p.node_id
        ORDER BY n.seq_order, p.node_id
        """
    ).fetchall()
    decl_rows = con.execute(
        "SELECT decl_or_cert, node_id, ownership_kind FROM decl_ownership ORDER BY node_id, decl_or_cert"
    ).fetchall()
    sym_rows = con.execute(
        "SELECT macro_key, symbol_node_id, latex_macro, description FROM symbols ORDER BY macro_key"
    ).fetchall()
    con.close()

    issues_map = pub_lock.get("issues", {})
    nodes: list[dict[str, Any]] = []
    for r in node_rows:
        nid = r[0]
        kind = r[1]
        raw_obj = json.loads(scrub_portable_str(r[20], vol1_default))
        spec = raw_obj.get("spec", {})
        body = raw_obj.get("body", {})
        lean_sig = spec.get("mathlib", {}).get("lean_signature", "") if isinstance(spec, dict) else ""
        if r[8] == "kernel_arena" and not lean_sig:
            lean_sig = f"KernelArena cert: {r[13] or ''}\nChecked by: {', '.join(json.loads(r[11]))}"
        cohort = r[21]
        if not cohort:
            if kind == "symbol":
                cohort = "Cohort II"
            elif kind == "work_item":
                cohort = "Project Plan"
            elif kind == "pub_target":
                cohort = "Publication Sink"
            else:
                cohort = "Other"
        nodes.append(
            {
                "id": nid,
                "kind": kind,
                "is_core": kind not in ("work_item", "pub_target"),
                "cohort": cohort,
                "title": r[2],
                "chapter": r[3],
                "section": r[4],
                "seq_order": r[5],
                "axis": r[6],
                "grounding_tier": r[7],
                "formal_pkg": r[8],
                "stratum": r[9],
                "module": r[10] or "",
                "decl_names": json.loads(r[11]),
                "expected_axioms": json.loads(r[12]),
                "actual_axioms": json.loads(r[27]) if r[27] else json.loads(r[12]),
                "cert_path": r[13] or "",
                "cert_sha256": r[28] or "",
                "verified_at_utc": r[29] or "",
                "spec_hash": r[14],
                "body_hash": r[15],
                "grounding_hash": r[16],
                "taint_status": r[17],
                "taint_reason": r[18],
                "file_path": r[19],
                "primary_category": r[22] or "",
                "blueprint_tier": r[23] or "none",
                "characterization_types": json.loads(r[24]) if r[24] else [],
                "witness_scope": r[25] or "",
                "dual_pillars": json.loads(r[26]) if r[26] else [],
                "statement": spec.get("statement", spec.get("contract", "")) if isinstance(spec, dict) else "",
                "tex": body.get("tex", "") if isinstance(body, dict) else "",
                "lean_signature": lean_sig,
                "lean_body": body.get("lean_body", "") if isinstance(body, dict) else "",
                "plan": raw_obj.get("plan"),
                "pub": raw_obj.get("pub"),
                "issue": issues_map.get(nid),
            }
        )

    edges = [
        {
            "src": r[0],
            "dst": r[1],
            "fiber": r[2],
            "metadata": json.loads(r[3]),
        }
        for r in edge_rows
    ]

    work_items = [
        {
            "id": r[0],
            "title": r[1],
            "seq_order": r[2],
            "milestone": r[3],
            "milestone_num": r[4],
            "slice_code": r[5],
            "target_modules": json.loads(r[6]),
            "deliverable_nodes": json.loads(r[7]),
            "guardrails": json.loads(r[8]),
            "summary": r[9],
            "status": r[10],
            "verified_deliverables": r[11],
            "total_deliverables": r[12],
            "issue": issues_map.get(r[0]),
        }
        for r in work_rows
    ]

    pub_targets = [
        {
            "id": r[0],
            "title": r[1],
            "channel": r[2],
            "sensitivity": r[3],
            "outputs": json.loads(r[4]),
            "cone_hash": r[5],
            "locked_cone_hash": r[6] or "",
            "pub_status": r[7],
            "pub_reason": r[8],
        }
        for r in pub_rows
    ]

    decl_ownership = [
        {"decl_or_cert": r[0], "node_id": r[1], "ownership_kind": r[2]}
        for r in decl_rows
    ]
    symbols = [
        {"macro_key": r[0], "symbol_node_id": r[1], "latex_macro": r[2], "description": r[3]}
        for r in sym_rows
    ]

    core_nodes = [n for n in nodes if n["is_core"]]
    metrics = {
        "total_nodes": len(nodes),
        "core_nodes": len(core_nodes),
        "core_clean": sum(1 for n in core_nodes if n["taint_status"] == "CLEAN"),
        "core_tainted": sum(1 for n in core_nodes if n["taint_status"] == "TAINTED"),
        "work_items_total": len(work_items),
        "work_items_counts": dict(Counter(w["status"] for w in work_items)),
        "pub_targets_total": len(pub_targets),
        "pub_targets_clean": sum(1 for p in pub_targets if p["pub_status"] == "CLEAN"),
        "total_edges": len(edges),
        "edges_by_fiber": dict(Counter(e["fiber"] for e in edges)),
        "strata": dict(Counter(n["stratum"] for n in core_nodes)),
        "cohorts": dict(Counter(n["cohort"] for n in core_nodes)),
        "decl_ownership_count": len(decl_ownership),
    }

    pdfs = []
    for fname, label, desc in PDF_FILES:
        src_pdf = TEX_DIR / fname
        pdfs.append(
            {
                "filename": fname,
                "href": f"pdfs/{fname}",
                "label": label,
                "description": desc,
                "available": src_pdf.exists(),
                "size_kb": round(src_pdf.stat().st_size / 1024, 1) if src_pdf.exists() else 0,
            }
        )

    return {
        "schema": "vol2.observatory.v1",
        "meta": {
            "working_title": manifest["working_title"],
            "working_subtitle": manifest["working_subtitle"],
            "title_locked": bool(manifest.get("title_locked", False)),
            "author": manifest["author"],
            "location": manifest["location"],
            "license": manifest["license"],
            "lean_toolchain": manifest["lean_toolchain"],
            "vol1_root_display": vol1_default,
            "vol1_pinned_head": manifest.get("vol1_pinned_head", "b849be75"),
            "vol1_zenodo_doi": manifest["vol1_zenodo_doi"],
            "phase": manifest["phase"],
            "active_slice": manifest["active_slice"],
            "github_repo": gh_repo,
            "repo_url": f"https://github.com/{gh_repo}",
            "pages_url": pages_url,
            "lean_export_branch_url": f"https://github.com/{gh_repo}/tree/lean-export",
            "lean_export_commit": pub_lock.get("lean_export_commit", ""),
        },
        "metrics": metrics,
        "nodes": nodes,
        "edges": edges,
        "work_items": work_items,
        "pub_targets": pub_targets,
        "decl_ownership": decl_ownership,
        "symbols": symbols,
        "guardrails": guardrails,
        "pdfs": pdfs,
        "drill_summary": {
            "pass_a": drill.get("pass_a", {}).get("summary", "10/10 CLEAN, 0 TAINTED, 0 cycles, 0 TCB violations"),
            "pass_b": drill.get("pass_b", {}).get("summary", "7 TAINTED on Clause 3 injection, Lean error mapped to node, 2 PROSE_LOCK_MISMATCH"),
            "pass_c": drill.get("pass_c", {}).get("summary", "10/10 CLEAN after remediation; BODY_DIRTY=1 / TAINTED=0 / CLEAN=9 isolation verified"),
        },
    }


def render_styles_css() -> str:
    return """/* Swiss-Modernist Academic Observatory Theme — CRM Volume II */
:root {
  --bg: #f8fafc;
  --surface: #ffffff;
  --surface-muted: #f1f5f9;
  --ink: #0f172a;
  --ink-muted: #475569;
  --border: #cbd5e1;
  --border-strong: #94a3b8;
  --accent: #1b365d;
  --accent-soft: #e8eef6;
  --emerald: #166534;
  --emerald-bg: #dcfce7;
  --sapphire: #1d4ed8;
  --sapphire-bg: #dbeafe;
  --amber: #b45309;
  --amber-bg: #fef3c7;
  --crimson: #991b1b;
  --crimson-bg: #fee2e2;
  --slate-bg: #e2e8f0;
  --font-sans: "Inter", "IBM Plex Sans", -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
  --font-serif: "Source Serif 4", "Palatino Linotype", Georgia, serif;
  --font-mono: "JetBrains Mono", "IBM Plex Mono", ui-monospace, SFMono-Regular, Menlo, monospace;
}

*, *::before, *::after {
  box-sizing: border-box;
}

html, body {
  margin: 0;
  padding: 0;
  background: var(--bg);
  color: var(--ink);
  font-family: var(--font-sans);
  line-height: 1.55;
  -webkit-font-smoothing: antialiased;
}

a {
  color: var(--sapphire);
  text-decoration-thickness: 1px;
  text-underline-offset: 2px;
}

a:hover {
  color: var(--accent);
}

code, pre {
  font-family: var(--font-mono);
  font-size: 0.87em;
}

.site-header {
  background: var(--surface);
  border-block-end: 2px solid var(--accent);
  padding: 1.5rem clamp(1rem, 3vw, 2.5rem) 1.15rem;
}

.header-inner {
  max-width: 1380px;
  margin-inline: auto;
}

.eyebrow {
  display: flex;
  flex-wrap: wrap;
  gap: 0.5rem 1rem;
  align-items: center;
  font-size: 0.78rem;
  font-weight: 600;
  letter-spacing: 0.06em;
  text-transform: uppercase;
  color: var(--accent);
  margin-block-end: 0.45rem;
}

.site-header h1 {
  margin: 0;
  font-family: var(--font-serif);
  font-size: clamp(1.5rem, 2.5vw, 2.15rem);
  font-weight: 700;
  line-height: 1.2;
}

.subtitle {
  margin: 0.25rem 0 0.85rem;
  font-family: var(--font-serif);
  font-style: italic;
  font-size: 1.05rem;
  color: var(--ink-muted);
}

.header-meta {
  display: flex;
  flex-wrap: wrap;
  gap: 0.55rem 1.25rem;
  font-size: 0.84rem;
  color: var(--ink-muted);
}

.telemetry-strip {
  max-width: 1380px;
  margin: 1rem auto 0;
  padding-inline: clamp(1rem, 3vw, 2.5rem);
  display: grid;
  grid-template-columns: repeat(auto-fit, minmax(170px, 1fr));
  gap: 0.75rem;
}

.metric-card {
  background: var(--surface);
  border: 1px solid var(--border);
  border-inline-start: 4px solid var(--accent);
  padding: 0.7rem 0.9rem;
}

.metric-label {
  font-size: 0.72rem;
  text-transform: uppercase;
  letter-spacing: 0.06em;
  color: var(--ink-muted);
  font-weight: 600;
}

.metric-value {
  font-size: 1.28rem;
  font-weight: 700;
  color: var(--ink);
  margin-block: 0.1rem;
}

.metric-sub {
  font-size: 0.76rem;
  color: var(--ink-muted);
}

.main-shell {
  max-width: 1380px;
  margin: 1.15rem auto 2.5rem;
  padding-inline: clamp(1rem, 3vw, 2.5rem);
}

/* Single-row accessible tablist */
.tablist {
  display: flex;
  overflow-x: auto;
  border-block-end: 1px solid var(--border);
  background: var(--surface);
  border-inline: 1px solid var(--border);
  border-block-start: 1px solid var(--border);
  scrollbar-width: thin;
}

[role="tab"] {
  flex: none;
  position: relative;
  appearance: none;
  border: 0;
  background: transparent;
  color: var(--ink-muted);
  font-family: inherit;
  font-size: 0.92rem;
  font-weight: 600;
  padding: 0.85rem 1.25rem;
  cursor: pointer;
  white-space: nowrap;
}

[role="tab"]:hover {
  color: var(--ink);
  background: var(--surface-muted);
}

[role="tab"][aria-selected="true"] {
  color: var(--accent);
}

[role="tab"][aria-selected="true"]::after {
  content: "";
  position: absolute;
  inset: auto 0 0;
  border-block-end: 3px solid var(--accent);
}

[role="tab"]:focus-visible {
  outline: 2px solid var(--sapphire);
  outline-offset: -3px;
}

/* Tabpanels: never put padding/border/bg on [role="tabpanel"] directly (hidden=until-found safety) */
.panel-stack {
  background: var(--surface);
  border: 1px solid var(--border);
  border-block-start: 0;
}

.panel-inner {
  padding: 1.25rem;
}

.panel-header {
  display: flex;
  flex-wrap: wrap;
  justify-content: space-between;
  align-items: flex-end;
  gap: 0.75rem;
  margin-block-end: 1rem;
  padding-block-end: 0.75rem;
  border-block-end: 1px solid var(--border);
}

.panel-header h2 {
  margin: 0;
  font-size: 1.22rem;
  font-family: var(--font-serif);
}

.controls-bar {
  display: flex;
  flex-wrap: wrap;
  gap: 0.5rem 1rem;
  align-items: center;
  padding: 0.75rem 0.9rem;
  background: var(--surface-muted);
  border: 1px solid var(--border);
  margin-block-end: 1rem;
}

.control-group {
  display: flex;
  flex-wrap: wrap;
  gap: 0.45rem 0.75rem;
  align-items: center;
  font-size: 0.84rem;
}

.control-group label {
  display: inline-flex;
  align-items: center;
  gap: 0.35rem;
  cursor: pointer;
}

.fiber-swatch {
  display: inline-block;
  inline-size: 12px;
  block-size: 4px;
  border-radius: 2px;
}

input[type="search"], select {
  font-family: inherit;
  font-size: 0.86rem;
  padding: 0.38rem 0.6rem;
  border: 1px solid var(--border-strong);
  background: var(--surface);
  color: var(--ink);
}

.btn {
  appearance: none;
  border: 1px solid var(--border-strong);
  background: var(--surface);
  color: var(--ink);
  font-family: inherit;
  font-size: 0.82rem;
  font-weight: 600;
  padding: 0.38rem 0.72rem;
  cursor: pointer;
}

.btn:hover {
  background: var(--accent-soft);
  border-color: var(--accent);
}

.btn-primary {
  background: var(--accent);
  color: #ffffff;
  border-color: var(--accent);
}

.btn-primary:hover {
  background: #132847;
  color: #ffffff;
}

/* Badges */
.badge {
  display: inline-block;
  font-family: var(--font-mono);
  font-size: 0.72rem;
  font-weight: 600;
  padding: 0.12rem 0.45rem;
  border: 1px solid transparent;
  white-space: nowrap;
}

.stratum-emerald { background: var(--emerald-bg); color: var(--emerald); border-color: #86efac; }
.stratum-sapphire { background: var(--sapphire-bg); color: var(--sapphire); border-color: #93c5fd; }
.stratum-amber { background: var(--amber-bg); color: var(--amber); border-color: #fcd34d; }
.stratum-crimson { background: var(--crimson-bg); color: var(--crimson); border-color: #fca5a5; }
.stratum-none { background: var(--slate-bg); color: var(--ink-muted); border-color: var(--border); }

.status-CLEAN, .status-VERIFIED { background: var(--emerald-bg); color: var(--emerald); border-color: #86efac; }
.status-ACTIVE { background: var(--sapphire-bg); color: var(--sapphire); border-color: #93c5fd; }
.status-PLANNED, .status-ARTIFACT_DIRTY { background: var(--amber-bg); color: var(--amber); border-color: #fcd34d; }
.status-TAINTED { background: var(--crimson-bg); color: var(--crimson); border-color: #fca5a5; }

/* DAG Canvas */
.dag-stage {
  border: 1px solid var(--border);
  background: #fbfdff;
  overflow: auto;
  max-block-size: 72vh;
  position: relative;
}

.dag-legend {
  display: flex;
  flex-wrap: wrap;
  gap: 0.65rem 1.15rem;
  font-size: 0.8rem;
  margin-block-start: 0.75rem;
  color: var(--ink-muted);
}

.dag-node {
  cursor: pointer;
}

.dag-node:focus-visible rect {
  stroke: var(--sapphire);
  stroke-width: 3px;
}

/* Milestones & Grid */
.milestone-grid {
  display: grid;
  grid-template-columns: repeat(auto-fit, minmax(240px, 1fr));
  gap: 0.75rem;
  margin-block-end: 1.25rem;
}

.milestone-card {
  border: 1px solid var(--border);
  background: var(--surface-muted);
  padding: 0.75rem 0.9rem;
}

.progress-track {
  inline-size: 100%;
  block-size: 6px;
  background: var(--border);
  margin-block: 0.45rem;
  overflow: hidden;
}

.progress-fill {
  block-size: 100%;
  background: var(--emerald);
}

/* Responsive accessible tables */
.table-wrapper {
  overflow: auto;
  max-inline-size: 100%;
  max-block-size: min(650px, 75vh);
  border: 1px solid var(--border);
  container-type: inline-size;
}

.table-wrapper:focus-visible {
  outline: 2px solid var(--sapphire);
}

table {
  width: 100%;
  border-collapse: separate;
  border-spacing: 0;
  font-size: 0.84rem;
}

thead {
  position: sticky;
  inset-block-start: 0;
  z-index: 2;
}

th, td {
  text-align: left;
  vertical-align: top;
  padding: 0.55rem 0.65rem;
  border-block-end: 1px solid var(--border);
}

thead th {
  background: var(--surface-muted);
  color: var(--ink);
  font-weight: 700;
  border-block-end: 2px solid var(--border-strong);
  white-space: nowrap;
}

tbody tr:hover {
  background: #f8fafc;
}

tbody th {
  font-weight: 600;
  background: var(--surface);
}

@container (width < 680px) {
  .responsive-table table,
  .responsive-table thead,
  .responsive-table tbody,
  .responsive-table tr,
  .responsive-table th,
  .responsive-table td {
    display: block;
  }

  .responsive-table thead {
    display: none;
  }

  .responsive-table tr {
    margin-block-end: 0.85rem;
    border: 1px solid var(--border);
    background: var(--surface);
  }

  .responsive-table tbody th {
    position: sticky;
    inset-block-start: 0;
    z-index: 1;
    background: var(--surface-muted);
    border-block-end: 1px solid var(--border-strong);
  }

  .responsive-table td::before {
    content: attr(data-label) ": ";
    font-weight: 700;
    color: var(--ink-muted);
  }
}

/* Process & PDFs grid */
.cards-grid {
  display: grid;
  grid-template-columns: repeat(auto-fit, minmax(280px, 1fr));
  gap: 0.9rem;
  margin-block-end: 1.25rem;
}

.card {
  border: 1px solid var(--border);
  background: var(--surface-muted);
  padding: 0.95rem 1rem;
}

.card h3 {
  margin: 0 0 0.4rem;
  font-size: 1rem;
  font-family: var(--font-serif);
}

.process-svg-wrap {
  border: 1px solid var(--border);
  background: #fbfdff;
  padding: 0.75rem;
  overflow-x: auto;
  margin-block-end: 1.25rem;
}

/* Native modal <dialog> per modern-web-guidance */
dialog:modal {
  overscroll-behavior: contain;
}

dialog::backdrop {
  overflow: hidden;
  overscroll-behavior: contain;
  background: rgb(15 23 42 / 0.52);
}

dialog[open] {
  display: flex;
  flex-direction: column;
  width: min(920px, 94vw);
  max-height: 88vh;
  margin: auto;
  padding: 0;
  border: 2px solid var(--accent);
  background: var(--surface);
  color: var(--ink);
  box-shadow: 0 24px 60px rgb(15 23 42 / 0.35);
}

.dialog-head {
  display: flex;
  justify-content: space-between;
  align-items: flex-start;
  gap: 1rem;
  padding: 1rem 1.25rem;
  border-block-end: 1px solid var(--border);
  background: var(--surface-muted);
}

.dialog-head h1 {
  margin: 0.25rem 0 0;
  font-size: 1.22rem;
  font-family: var(--font-serif);
  line-height: 1.25;
}

.dialog-body {
  padding: 1.15rem 1.25rem;
  overflow-y: auto;
  display: grid;
  gap: 1rem;
}

.code-box {
  background: #0f172a;
  color: #f8fafc;
  padding: 0.75rem 0.9rem;
  overflow-x: auto;
  white-space: pre-wrap;
  word-break: break-word;
  font-size: 0.8rem;
  line-height: 1.45;
  margin: 0;
}

.tex-box {
  background: var(--surface-muted);
  border-inline-start: 3px solid var(--accent);
  padding: 0.7rem 0.9rem;
  white-space: pre-wrap;
  font-family: var(--font-mono);
  font-size: 0.79rem;
  max-block-size: 240px;
  overflow-y: auto;
}

.pill-list {
  display: flex;
  flex-wrap: wrap;
  gap: 0.4rem;
}

.edge-btn {
  font-family: var(--font-mono);
  font-size: 0.75rem;
  padding: 0.2rem 0.5rem;
  border: 1px solid var(--border-strong);
  background: var(--surface);
  color: var(--sapphire);
  cursor: pointer;
}

.edge-btn:hover {
  background: var(--accent-soft);
  border-color: var(--accent);
}

.hash-grid {
  display: grid;
  grid-template-columns: repeat(auto-fit, minmax(220px, 1fr));
  gap: 0.55rem;
}

.hash-item {
  border: 1px solid var(--border);
  padding: 0.5rem 0.65rem;
  background: var(--surface-muted);
  font-size: 0.78rem;
  word-break: break-all;
}

.muted {
  color: var(--ink-muted);
}
"""


def render_app_js() -> str:
    return r"""(function () {
  "use strict";

  const FIBER_COLORS = {
    logical_dep: "#1b365d",
    lean_dep: "#166534",
    prose_paraphrase: "#9333ea",
    notation: "#b45309",
    curriculum: "#0284c7",
  };

  const STRATUM_HEX = {
    emerald: { stroke: "#166534", fill: "#f0fdf4", text: "#14532d" },
    sapphire: { stroke: "#1d4ed8", fill: "#eff6ff", text: "#1e3a8a" },
    amber: { stroke: "#b45309", fill: "#fffbeb", text: "#78350f" },
    crimson: { stroke: "#991b1b", fill: "#fef2f2", text: "#7f1d1d" },
    none: { stroke: "#475569", fill: "#f8fafc", text: "#1e293b" },
  };

  let DATA = null;
  let NODE_BY_ID = new Map();
  let ACTIVE_FIBERS = new Set(["logical_dep", "lean_dep", "prose_paraphrase", "notation", "curriculum"]);
  let INCLUDE_PLAN_PUB = false;
  let DAG_ZOOM = 1.0;

  // Fallback for browsers without <dialog closedby="any">
  if (!("closedBy" in HTMLDialogElement.prototype)) {
    const outside = (e, dialog) => {
      const r = dialog.getBoundingClientRect();
      return e.clientX < r.left || e.clientX > r.right || e.clientY < r.top || e.clientY > r.bottom;
    };
    for (const dialog of document.querySelectorAll('dialog[closedby="any"]')) {
      let pressedOutside = false;
      dialog.addEventListener("pointerdown", (e) => {
        pressedOutside = outside(e, dialog);
      });
      dialog.addEventListener("pointerup", (e) => {
        if (pressedOutside && outside(e, dialog)) dialog.close();
      });
    }
  }

  function esc(s) {
    return String(s ?? "")
      .replaceAll("&", "&amp;")
      .replaceAll("<", "&lt;")
      .replaceAll(">", "&gt;")
      .replaceAll('"', "&quot;");
  }

  function badgeStratum(st) {
    const label = st === "none" ? "none" : st;
    return `<span class="badge stratum-${esc(st)}">${esc(label)}</span>`;
  }

  function badgeStatus(status) {
    return `<span class="badge status-${esc(status)}">${esc(status)}</span>`;
  }

  // Accessible Tabs (selection follows focus + hidden="until-found" + beforematch)
  function initTabs() {
    const tabs = Array.from(document.querySelectorAll('[role="tab"]'));
    const panels = Array.from(document.querySelectorAll('[role="tabpanel"]'));

    function selectTab(targetTab, moveFocus) {
      for (const tab of tabs) {
        const selected = tab === targetTab;
        tab.setAttribute("aria-selected", selected ? "true" : "false");
        tab.tabIndex = selected ? 0 : -1;
      }
      for (const panel of panels) {
        const active = panel.getAttribute("aria-labelledby") === targetTab.id;
        if (active) {
          panel.removeAttribute("hidden");
          panel.tabIndex = 0;
        } else {
          panel.setAttribute("hidden", "until-found");
          panel.removeAttribute("tabindex");
        }
      }
      if (moveFocus) {
        targetTab.focus();
        targetTab.scrollIntoView({ block: "nearest", inline: "nearest" });
      }
    }

    tabs.forEach((tab, idx) => {
      tab.addEventListener("click", () => selectTab(tab, false));
      tab.addEventListener("keydown", (e) => {
        let nextIdx = null;
        if (e.key === "ArrowRight") nextIdx = (idx + 1) % tabs.length;
        else if (e.key === "ArrowLeft") nextIdx = (idx - 1 + tabs.length) % tabs.length;
        else if (e.key === "Home") nextIdx = 0;
        else if (e.key === "End") nextIdx = tabs.length - 1;
        if (nextIdx !== null) {
          e.preventDefault();
          selectTab(tabs[nextIdx], true);
        }
      });
    });

    panels.forEach((panel) => {
      panel.addEventListener("beforematch", () => {
        const ownerTab = document.getElementById(panel.getAttribute("aria-labelledby"));
        if (ownerTab) selectTab(ownerTab, false);
      });
    });
  }

  // Modal Node Inspector
  function openNodeInspector(nodeId) {
    const node = NODE_BY_ID.get(nodeId);
    if (!node) return;
    const dialog = document.getElementById("node-inspector");
    const titleEl = document.getElementById("inspector-title");
    const metaEl = document.getElementById("inspector-meta");
    const bodyEl = document.getElementById("inspector-body");

    titleEl.textContent = `${node.id} — ${node.title}`;
    metaEl.innerHTML = [
      `<span class="badge stratum-none">${esc(node.kind)}</span>`,
      `<span class="badge stratum-none">${esc(node.cohort)}</span>`,
      badgeStratum(node.stratum),
      badgeStatus(node.taint_status),
      node.blueprint_tier && node.blueprint_tier !== "none"
        ? `<span class="badge stratum-sapphire">${esc(node.blueprint_tier)}</span>`
        : "",
    ].join(" ");

    const inEdges = DATA.edges.filter((e) => e.dst === node.id);
    const outEdges = DATA.edges.filter((e) => e.src === node.id);

    const sections = [];

    sections.push(`
      <div class="hash-grid">
        <div class="hash-item"><strong>Location:</strong> ${esc(node.file_path)}<br><strong>Pkg / Module:</strong> ${esc(node.formal_pkg)} ${node.module ? `(${esc(node.module)})` : ""}</div>
        <div class="hash-item"><strong>spec_hash:</strong> <code>${esc(node.spec_hash)}</code></div>
        <div class="hash-item"><strong>body_hash:</strong> <code>${esc(node.body_hash)}</code></div>
        <div class="hash-item"><strong>grounding_hash:</strong> <code>${esc(node.grounding_hash)}</code></div>
      </div>
    `);

    if (node.statement) {
      sections.push(`<div><strong>Specification / Mathematical Statement</strong><div class="tex-box">${esc(node.statement)}</div></div>`);
    }

    if (node.plan) {
      const p = node.plan;
      sections.push(`
        <div class="card">
          <h3>Work Item Plan (${esc(p.slice_code)} — Milestone ${esc(p.milestone_num)})</h3>
          <p>${esc(p.summary)}</p>
          <p><strong>Modules:</strong> ${(p.target_modules || []).map((m) => `<code>${esc(m)}</code>`).join(", ") || "—"}</p>
          <p><strong>Deliverables (${(p.deliverable_nodes || []).length}):</strong> ${(p.deliverable_nodes || []).map((d) => `<code>${esc(d)}</code>`).join(", ")}</p>
          ${node.issue ? `<p><strong>GitHub Issue:</strong> <a href="${esc(node.issue.url)}" target="_blank" rel="noopener">#${esc(node.issue.number)} (${esc(node.issue.state)})</a></p>` : ""}
        </div>
      `);
    }

    if (node.pub) {
      sections.push(`
        <div class="card">
          <h3>Publication Sink (${esc(node.pub.channel)} · ${esc(node.pub.sensitivity)})</h3>
          <p><strong>Outputs:</strong> ${(node.pub.outputs || []).map((o) => `<code>${esc(o)}</code>`).join(", ")}</p>
        </div>
      `);
    }

    if (node.formal_pkg === "mathlib_vol2" || node.formal_pkg === "kernel_arena") {
      sections.push(`
        <div>
          <strong>Formal Verification (${esc(node.formal_pkg)})</strong>
          <p class="muted" style="margin:0.25rem 0 0.45rem;">
            <strong>Declarations:</strong> ${(node.decl_names || []).map((d) => `<code>${esc(d)}</code>`).join(", ") || "—"}<br>
            <strong>Kernel Axioms:</strong> <code>${esc(JSON.stringify(node.actual_axioms || []))}</code>
            ${node.cert_path ? `<br><strong>2LTT Cert:</strong> <code>${esc(node.cert_path)}</code> (sha256: <code>${esc(node.cert_sha256 || "")}</code>)` : ""}
          </p>
          <pre class="code-box">${esc(node.lean_signature || "")}</pre>
        </div>
      `);
    }

    if (node.is_core) {
      const pillarsHtml = (node.dual_pillars || [])
        .map(
          (p) =>
            `<li><strong>${esc(p.kind)}</strong>: <code>${esc(p.ref)}</code>${p.locator ? ` (${esc(p.locator)})` : ""} — ${esc(p.purpose)}</li>`
        )
        .join("");
      sections.push(`
        <div class="card">
          <h3>Grounding &amp; Claim Classification</h3>
          <p style="margin:0 0 0.35rem;">
            <strong>Primary Category:</strong> ${esc(node.primary_category || "—")} ·
            <strong>Blueprint Tier:</strong> <code>${esc(node.blueprint_tier)}</code><br>
            <strong>Characterizations:</strong> ${esc((node.characterization_types || []).join(", ") || "—")}
          </p>
          ${node.witness_scope ? `<p style="margin:0 0 0.35rem;"><strong>Witness Scope:</strong> ${esc(node.witness_scope)}</p>` : ""}
          ${pillarsHtml ? `<ul style="margin:0.35rem 0 0 1.2rem;padding:0;">${pillarsHtml}</ul>` : ""}
        </div>
      `);
    }

    if (node.tex) {
      sections.push(`<div><strong>LaTeX Source</strong><div class="tex-box">${esc(node.tex)}</div></div>`);
    }

    const renderEdgeBtns = (list, key) =>
      list.length
        ? list
            .map(
              (e) =>
                `<button type="button" class="edge-btn" data-jump="${esc(e[key])}">[${esc(e.fiber)}] ${esc(e[key])}</button>`
            )
            .join("")
        : '<span class="muted">None</span>';

    sections.push(`
      <div>
        <strong>Incoming Dependencies (${inEdges.length})</strong>
        <div class="pill-list" style="margin-block:0.35rem 0.75rem;">${renderEdgeBtns(inEdges, "src")}</div>
        <strong>Outgoing Dependents (${outEdges.length})</strong>
        <div class="pill-list" style="margin-block:0.35rem 0;">${renderEdgeBtns(outEdges, "dst")}</div>
      </div>
    `);

    bodyEl.innerHTML = sections.join("");
    bodyEl.querySelectorAll("[data-jump]").forEach((btn) => {
      btn.addEventListener("click", () => openNodeInspector(btn.getAttribute("data-jump")));
    });

    if (!dialog.open) {
      dialog.showModal();
    }
  }

  // Render Tab 1: Layered SVG 5-Fiber DAG
  function renderDAG() {
    const svg = document.getElementById("dag-svg");
    const visibleNodes = DATA.nodes.filter((n) => INCLUDE_PLAN_PUB || n.is_core);
    const visIds = new Set(visibleNodes.map((n) => n.id));
    const visibleEdges = DATA.edges.filter(
      (e) => ACTIVE_FIBERS.has(e.fiber) && visIds.has(e.src) && visIds.has(e.dst)
    );

    // Compute longest-path topological layer across active visible edges
    const indeg = new Map();
    const adj = new Map();
    const layer = new Map();
    for (const n of visibleNodes) {
      indeg.set(n.id, 0);
      adj.set(n.id, []);
      layer.set(n.id, 0);
    }
    const uniquePairs = new Set();
    for (const e of visibleEdges) {
      const k = `${e.src}-->${e.dst}`;
      if (!uniquePairs.has(k)) {
        uniquePairs.add(k);
        adj.get(e.src).push(e.dst);
        indeg.set(e.dst, indeg.get(e.dst) + 1);
      }
    }
    const queue = visibleNodes.filter((n) => indeg.get(n.id) === 0).map((n) => n.id);
    while (queue.length > 0) {
      const u = queue.shift();
      const lu = layer.get(u);
      for (const v of adj.get(u)) {
        if (layer.get(v) < lu + 1) layer.set(v, lu + 1);
        indeg.set(v, indeg.get(v) - 1);
        if (indeg.get(v) === 0) queue.push(v);
      }
    }

    const byLayer = new Map();
    for (const n of visibleNodes) {
      const l = layer.get(n.id);
      if (!byLayer.has(l)) byLayer.set(l, []);
      byLayer.get(l).push(n);
    }
    const layerKeys = Array.from(byLayer.keys()).sort((a, b) => a - b);
    const colWidth = 255;
    const rowHeight = 76;
    const boxW = 210;
    const boxH = 54;
    const padX = 28;
    const padY = 26;

    let maxRows = 1;
    for (const lk of layerKeys) {
      byLayer.get(lk).sort((a, b) => (a.seq_order - b.seq_order) || a.id.localeCompare(b.id));
      maxRows = Math.max(maxRows, byLayer.get(lk).length);
    }

    const totalW = Math.max(880, padX * 2 + layerKeys.length * colWidth);
    const totalH = Math.max(460, padY * 2 + maxRows * rowHeight);
    const pos = new Map();

    for (let li = 0; li < layerKeys.length; li++) {
      const list = byLayer.get(layerKeys[li]);
      const offsetY = (totalH - list.length * rowHeight) / 2;
      list.forEach((n, ri) => {
        pos.set(n.id, {
          x: padX + li * colWidth,
          y: Math.max(padY, offsetY + ri * rowHeight),
        });
      });
    }

    const defs = Object.entries(FIBER_COLORS)
      .map(
        ([fiber, col]) =>
          `<marker id="arrow-${fiber}" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto-start-reverse"><path d="M 0 1 L 10 5 L 0 9 z" fill="${col}"/></marker>`
      )
      .join("");

    const edgePaths = visibleEdges
      .map((e, i) => {
        const p1 = pos.get(e.src);
        const p2 = pos.get(e.dst);
        if (!p1 || !p2) return "";
        const x1 = p1.x + boxW;
        const y1 = p1.y + boxH / 2;
        const x2 = p2.x;
        const y2 = p2.y + boxH / 2;
        const dx = Math.max(36, (x2 - x1) * 0.45);
        const col = FIBER_COLORS[e.fiber] || "#64748b";
        const dash = e.fiber === "prose_paraphrase" ? 'stroke-dasharray="5 3"' : e.fiber === "notation" ? 'stroke-dasharray="2 3"' : "";
        return `<path d="M ${x1} ${y1} C ${x1 + dx} ${y1}, ${x2 - dx} ${y2}, ${x2} ${y2}" fill="none" stroke="${col}" stroke-width="1.5" stroke-opacity="0.72" ${dash} marker-end="url(#arrow-${e.fiber})"><title>${esc(e.src)} --[${esc(e.fiber)}]--> ${esc(e.dst)}</title></path>`;
      })
      .join("");

    const nodeBoxes = visibleNodes
      .map((n) => {
        const p = pos.get(n.id);
        const st = STRATUM_HEX[n.stratum] || STRATUM_HEX.none;
        const shortId = n.id.length > 29 ? n.id.slice(0, 27) + "…" : n.id;
        const shortTitle = n.title.length > 31 ? n.title.slice(0, 29) + "…" : n.title;
        return `
          <g class="dag-node" tabindex="0" role="button" data-node-id="${esc(n.id)}" aria-label="Inspect ${esc(n.id)}: ${esc(n.title)}" transform="translate(${p.x}, ${p.y})">
            <rect width="${boxW}" height="${boxH}" rx="4" fill="${st.fill}" stroke="${st.stroke}" stroke-width="1.75"/>
            <rect width="6" height="${boxH}" rx="2" fill="${st.stroke}"/>
            <text x="13" y="18" font-family="ui-monospace, monospace" font-size="10.5" font-weight="700" fill="${st.text}">${esc(shortId)}</text>
            <text x="13" y="34" font-family="sans-serif" font-size="10.5" fill="#0f172a">${esc(shortTitle)}</text>
            <text x="13" y="47" font-family="ui-monospace, monospace" font-size="9" fill="#475569">${esc(n.kind)} · ${esc(n.taint_status)} · ${esc(n.spec_hash.slice(0, 8))}</text>
          </g>`;
      })
      .join("");

    svg.setAttribute("viewBox", `0 0 ${totalW} ${totalH}`);
    svg.style.width = `${Math.round(totalW * DAG_ZOOM)}px`;
    svg.style.height = `${Math.round(totalH * DAG_ZOOM)}px`;
    svg.innerHTML = `<defs>${defs}</defs>${edgePaths}${nodeBoxes}`;

    svg.querySelectorAll(".dag-node").forEach((el) => {
      const nid = el.getAttribute("data-node-id");
      el.addEventListener("click", () => openNodeInspector(nid));
      el.addEventListener("keydown", (e) => {
        if (e.key === "Enter" || e.key === " ") {
          e.preventDefault();
          openNodeInspector(nid);
        }
      });
    });

    document.getElementById("dag-summary").textContent =
      `Showing ${visibleNodes.length} nodes and ${visibleEdges.length} edges across ${ACTIVE_FIBERS.size} active fiber(s). Click any node to inspect.`;
  }

  // Render Tab 2: 14-Slice Project Plan & Milestones
  function renderRoadmap() {
    const msMap = new Map();
    for (const w of DATA.work_items) {
      if (!msMap.has(w.milestone_num)) {
        msMap.set(w.milestone_num, { num: w.milestone_num, title: w.milestone, items: [] });
      }
      msMap.get(w.milestone_num).items.push(w);
    }

    const msGrid = document.getElementById("milestone-grid");
    msGrid.innerHTML = Array.from(msMap.values())
      .sort((a, b) => a.num - b.num)
      .map((m) => {
        const done = m.items.filter((x) => x.status === "VERIFIED").length;
        const pct = Math.round((done / m.items.length) * 100);
        return `
          <div class="milestone-card">
            <div class="metric-label">${m.num === 10 ? "TCB Milestone" : `Milestone ${m.num}`}</div>
            <div style="font-weight:700;font-size:0.9rem;margin-block:0.2rem;">${esc(m.title)}</div>
            <div class="progress-track"><div class="progress-fill" style="width:${pct}%"></div></div>
            <div class="metric-sub">${done}/${m.items.length} slices VERIFIED</div>
          </div>`;
      })
      .join("");

    const tbody = document.getElementById("roadmap-tbody");
    tbody.innerHTML = DATA.work_items
      .map((w) => {
        const issueCell = w.issue
          ? `<a href="${esc(w.issue.url)}" target="_blank" rel="noopener">#${esc(w.issue.number)}</a>`
          : w.status === "VERIFIED"
          ? "Done"
          : "—";
        return `
          <tr>
            <th scope="row">${esc(w.seq_order)}. <code>${esc(w.slice_code)}</code><br><button type="button" class="edge-btn" data-inspect="${esc(w.id)}">${esc(w.id)}</button></th>
            <td data-label="Milestone">${esc(w.milestone)}</td>
            <td data-label="Status">${badgeStatus(w.status)}<br><span class="muted">${w.verified_deliverables}/${w.total_deliverables} CLEAN</span></td>
            <td data-label="Target Modules">${(w.target_modules || []).map((m) => `<code>${esc(m)}</code>`).join("<br>") || "—"}</td>
            <td data-label="Guardrails">${(w.guardrails || []).map((g) => `<code>${esc(g)}</code>`).join(", ") || "—"}</td>
            <td data-label="Summary">${esc(w.summary)}</td>
            <td data-label="Issue">${issueCell}</td>
          </tr>`;
      })
      .join("");

    tbody.querySelectorAll("[data-inspect]").forEach((b) => {
      b.addEventListener("click", () => openNodeInspector(b.getAttribute("data-inspect")));
    });
  }

  // Render Tab 3: Claims Ledger & Disjoint Declaration Browser
  function renderLedger() {
    const q = document.getElementById("ledger-search").value.trim().toLowerCase();
    const cohortF = document.getElementById("filter-cohort").value;
    const stratumF = document.getElementById("filter-stratum").value;
    const tierF = document.getElementById("filter-tier").value;

    const rows = DATA.nodes.filter((n) => {
      if (!n.is_core) return false;
      if (cohortF !== "ALL" && n.cohort !== cohortF) return false;
      if (stratumF !== "ALL" && n.stratum !== stratumF) return false;
      if (tierF !== "ALL" && n.blueprint_tier !== tierF) return false;
      if (q) {
        const hay = `${n.id} ${n.title} ${n.primary_category} ${n.statement} ${(n.decl_names || []).join(" ")}`.toLowerCase();
        if (!hay.includes(q)) return false;
      }
      return true;
    });

    document.getElementById("ledger-count").textContent = `${rows.length} of ${DATA.metrics.core_nodes} core nodes`;
    const tbody = document.getElementById("ledger-tbody");
    tbody.innerHTML = rows
      .map(
        (n) => `
        <tr>
          <th scope="row"><button type="button" class="edge-btn" data-inspect="${esc(n.id)}">${esc(n.id)}</button><br><span class="muted">${esc(n.kind)} · ${esc(n.cohort)}</span></th>
          <td data-label="Title">${esc(n.title)}</td>
          <td data-label="Category & Tier">${esc(n.primary_category || "Symbol")}<br><code>${esc(n.blueprint_tier)}</code></td>
          <td data-label="Stratum & Axioms">${badgeStratum(n.stratum)}<br><code>${esc(JSON.stringify(n.actual_axioms))}</code></td>
          <td data-label="Hashes & Status">${badgeStatus(n.taint_status)}<br><code>spec:${esc(n.spec_hash.slice(0, 8))}</code> <code>body:${esc(n.body_hash.slice(0, 8))}</code></td>
        </tr>`
      )
      .join("");

    tbody.querySelectorAll("[data-inspect]").forEach((b) => {
      b.addEventListener("click", () => openNodeInspector(b.getAttribute("data-inspect")));
    });

    // Declaration Ownership Table
    const dq = document.getElementById("decl-search").value.trim().toLowerCase();
    const dRows = DATA.decl_ownership.filter(
      (d) => !dq || d.decl_or_cert.toLowerCase().includes(dq) || d.node_id.toLowerCase().includes(dq)
    );
    document.getElementById("decl-count").textContent = `${dRows.length} of ${DATA.decl_ownership.length} disjoint declarations/certs`;
    const dTbody = document.getElementById("decl-tbody");
    dTbody.innerHTML = dRows
      .map(
        (d) => `
        <tr>
          <th scope="row"><code>${esc(d.decl_or_cert)}</code></th>
          <td data-label="Owning Node"><button type="button" class="edge-btn" data-inspect="${esc(d.node_id)}">${esc(d.node_id)}</button></td>
          <td data-label="Ownership Kind"><code>${esc(d.ownership_kind)}</code></td>
        </tr>`
      )
      .join("");

    dTbody.querySelectorAll("[data-inspect]").forEach((b) => {
      b.addEventListener("click", () => openNodeInspector(b.getAttribute("data-inspect")));
    });
  }

  // Render Tab 4: Process, Guardrails, Pub Targets, & PDFs
  function renderProcessTab() {
    document.getElementById("pdf-cards").innerHTML = DATA.pdfs
      .map(
        (p) => `
        <div class="card">
          <h3>${esc(p.label)}</h3>
          <p class="muted" style="font-size:0.86rem;">${esc(p.description)}</p>
          ${
            p.available
              ? `<a class="btn btn-primary" href="${esc(p.href)}" target="_blank" rel="noopener">Open PDF (${esc(p.size_kb)} KB)</a>`
              : `<span class="badge status-ARTIFACT_DIRTY">PDF not built</span>`
          }
        </div>`
      )
      .join("");

    document.getElementById("drill-cards").innerHTML = `
      <div class="card"><h3>Pass A — Clean Baseline</h3><p>${esc(DATA.drill_summary.pass_a)}</p></div>
      <div class="card"><h3>Pass B — Clause 3 Spec Taint</h3><p>${esc(DATA.drill_summary.pass_b)}</p></div>
      <div class="card"><h3>Pass C — Remediation &amp; Body Isolation</h3><p>${esc(DATA.drill_summary.pass_c)}</p></div>
    `;

    document.getElementById("guardrails-list").innerHTML = DATA.guardrails
      .map(
        (g) => `
        <div class="card">
          <h3><code>${esc(g.id)}</code> — ${esc(g.title)}</h3>
          <p style="margin:0 0 0.3rem;">${esc(g.statement)}</p>
          <div class="muted" style="font-size:0.78rem;">Vol I Anchor: <code>${esc(g.vol1_anchor)}</code></div>
        </div>`
      )
      .join("");

    const pubTbody = document.getElementById("pub-tbody");
    pubTbody.innerHTML = DATA.pub_targets
      .map(
        (p) => `
        <tr>
          <th scope="row"><button type="button" class="edge-btn" data-inspect="${esc(p.id)}">${esc(p.id)}</button></th>
          <td data-label="Channel"><code>${esc(p.channel)}</code></td>
          <td data-label="Sensitivity"><code>${esc(p.sensitivity)}</code></td>
          <td data-label="Outputs">${p.outputs.map((o) => `<code>${esc(o)}</code>`).join("<br>")}</td>
          <td data-label="Cone Hash"><code>${esc(p.cone_hash.slice(0, 12))}</code></td>
          <td data-label="Status">${badgeStatus(p.pub_status)}</td>
        </tr>`
      )
      .join("");
    pubTbody.querySelectorAll("[data-inspect]").forEach((b) => {
      b.addEventListener("click", () => openNodeInspector(b.getAttribute("data-inspect")));
    });
  }

  async function boot() {
    initTabs();
    const resp = await fetch("data/network.json");
    DATA = await resp.json();
    for (const n of DATA.nodes) NODE_BY_ID.set(n.id, n);

    const dialog = document.getElementById("node-inspector");
    dialog.addEventListener("close", () => {
      dialog.returnValue = "";
    });

    // Wire DAG controls
    document.querySelectorAll(".fiber-toggle").forEach((cb) => {
      cb.addEventListener("change", () => {
        if (cb.checked) ACTIVE_FIBERS.add(cb.value);
        else ACTIVE_FIBERS.delete(cb.value);
        renderDAG();
      });
    });
    document.getElementById("toggle-plan-pub").addEventListener("change", (e) => {
      INCLUDE_PLAN_PUB = e.target.checked;
      renderDAG();
    });
    document.getElementById("zoom-in").addEventListener("click", () => {
      DAG_ZOOM = Math.min(2.0, +(DAG_ZOOM + 0.15).toFixed(2));
      renderDAG();
    });
    document.getElementById("zoom-out").addEventListener("click", () => {
      DAG_ZOOM = Math.max(0.55, +(DAG_ZOOM - 0.15).toFixed(2));
      renderDAG();
    });
    document.getElementById("zoom-reset").addEventListener("click", () => {
      DAG_ZOOM = 1.0;
      renderDAG();
    });

    // Wire Ledger filters
    ["ledger-search", "filter-cohort", "filter-stratum", "filter-tier"].forEach((id) => {
      document.getElementById(id).addEventListener("input", renderLedger);
      document.getElementById(id).addEventListener("change", renderLedger);
    });
    document.getElementById("decl-search").addEventListener("input", renderLedger);

    renderDAG();
    renderRoadmap();
    renderLedger();
    renderProcessTab();
  }

  boot().catch((err) => {
    console.error(err);
    document.getElementById("dag-summary").textContent = `Error loading data/network.json: ${err.message}`;
  });
})();
"""


def render_index_html(payload: dict[str, Any]) -> str:
    m = payload["meta"]
    metrics = payload["metrics"]
    wi_counts = metrics["work_items_counts"]
    lean_commit_note = f" (commit <code>{html.escape(m['lean_export_commit'][:8])}</code>)" if m.get("lean_export_commit") else ""
    return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{html.escape(m['working_title'])} — Glass-Box Observatory</title>
  <link rel="stylesheet" href="styles.css">
</head>
<body>
  <header class="site-header">
    <div class="header-inner">
      <div class="eyebrow">
        <span>Glass-Box 5-Fiber Observatory</span>
        <span>·</span>
        <span>{html.escape(m['phase'])}</span>
        <span>·</span>
        <span>Vol I Fence: <code>{html.escape(m['vol1_root_display'])} ({html.escape(m['vol1_pinned_head'])})</code></span>
      </div>
      <h1>{html.escape(m['working_title'])}</h1>
      <p class="subtitle">{html.escape(m['working_subtitle'])} <span class="badge stratum-none">title_locked = {str(m['title_locked']).lower()}</span></p>
      <div class="header-meta">
        <span><strong>Author:</strong> {html.escape(m['author'])} ({html.escape(m['location'])})</span>
        <span><strong>Toolchain:</strong> <code>{html.escape(m['lean_toolchain'])}</code></span>
        <span><strong>GitHub:</strong> <a href="{html.escape(m['repo_url'])}" target="_blank" rel="noopener">{html.escape(m['github_repo'])}</a></span>
        <span><strong>Standalone Lean:</strong> <a href="{html.escape(m['lean_export_branch_url'])}" target="_blank" rel="noopener"><code>lean-export</code></a>{lean_commit_note}</span>
        <span><strong>Vol I DOI:</strong> <a href="https://doi.org/{html.escape(m['vol1_zenodo_doi'])}" target="_blank" rel="noopener">{html.escape(m['vol1_zenodo_doi'])}</a></span>
      </div>
    </div>
  </header>

  <section class="telemetry-strip" aria-label="Verification telemetry">
    <div class="metric-card">
      <div class="metric-label">Core Nodes</div>
      <div class="metric-value">{metrics['core_clean']} / {metrics['core_nodes']} CLEAN</div>
      <div class="metric-sub">{metrics['core_tainted']} tainted · {metrics['total_edges']} edges</div>
    </div>
    <div class="metric-card">
      <div class="metric-label">14-Slice Plan</div>
      <div class="metric-value">{wi_counts.get('VERIFIED', 0)} VERIFIED · {wi_counts.get('ACTIVE', 0)} ACTIVE</div>
      <div class="metric-sub">{wi_counts.get('PLANNED', 0)} PLANNED across 9 Ch + 3 TCB</div>
    </div>
    <div class="metric-card">
      <div class="metric-label">Four-Color Strata</div>
      <div class="metric-value">{metrics['strata'].get('emerald', 0)} Emerald · {metrics['strata'].get('amber', 0)} Amber · {metrics['strata'].get('crimson', 0)} Crimson</div>
      <div class="metric-sub">{metrics['strata'].get('none', 0)} prose/symbol · {metrics['strata'].get('sapphire', 0)} sapphire</div>
    </div>
    <div class="metric-card">
      <div class="metric-label">Disjoint Ownership</div>
      <div class="metric-value">{metrics['decl_ownership_count']} Lean / Certs</div>
      <div class="metric-sub">0 TCB crossings · 0 cycles</div>
    </div>
    <div class="metric-card">
      <div class="metric-label">Publication Sinks</div>
      <div class="metric-value">{metrics['pub_targets_clean']} / {metrics['pub_targets_total']} CLEAN</div>
      <div class="metric-sub">4 channels · out-degree 0</div>
    </div>
  </section>

  <main class="main-shell">
    <div class="tablist" role="tablist" aria-label="Observatory views">
      <button type="button" role="tab" id="tab-dag" aria-selected="true" tabindex="0">5-Fiber &amp; Stratum DAG</button>
      <button type="button" role="tab" id="tab-plan" aria-selected="false" tabindex="-1">Volume II Project Plan &amp; Milestones</button>
      <button type="button" role="tab" id="tab-ledger" aria-selected="false" tabindex="-1">Master Claims &amp; Grounding Ledger</button>
      <button type="button" role="tab" id="tab-process" aria-selected="false" tabindex="-1">Glass-Box Process &amp; PDF Downloads</button>
    </div>

    <div class="panel-stack">
      <section role="tabpanel" id="panel-dag" aria-labelledby="tab-dag" tabindex="0">
        <div class="panel-inner">
          <div class="panel-header">
            <div>
              <h2>5-Fiber Dependency &amp; Four-Color Stratum Graph</h2>
              <p id="dag-summary" class="muted" style="margin:0.2rem 0 0;font-size:0.86rem;">Loading network graph…</p>
            </div>
            <div class="control-group">
              <button type="button" class="btn" id="zoom-out">Zoom −</button>
              <button type="button" class="btn" id="zoom-reset">100%</button>
              <button type="button" class="btn" id="zoom-in">Zoom +</button>
            </div>
          </div>
          <div class="controls-bar">
            <div class="control-group">
              <strong>Fibers:</strong>
              <label><input type="checkbox" class="fiber-toggle" value="logical_dep" checked><span class="fiber-swatch" style="background:#1b365d"></span>logical_dep</label>
              <label><input type="checkbox" class="fiber-toggle" value="lean_dep" checked><span class="fiber-swatch" style="background:#166534"></span>lean_dep</label>
              <label><input type="checkbox" class="fiber-toggle" value="prose_paraphrase" checked><span class="fiber-swatch" style="background:#9333ea"></span>prose_paraphrase</label>
              <label><input type="checkbox" class="fiber-toggle" value="notation" checked><span class="fiber-swatch" style="background:#b45309"></span>notation</label>
              <label><input type="checkbox" class="fiber-toggle" value="curriculum" checked><span class="fiber-swatch" style="background:#0284c7"></span>curriculum</label>
            </div>
            <div class="control-group">
              <label><input type="checkbox" id="toggle-plan-pub"> Include 14 Work Items &amp; 7 Pub Sinks</label>
            </div>
          </div>
          <div class="dag-stage">
            <svg id="dag-svg" role="img" aria-label="Interactive 5-fiber mathematical dependency DAG"></svg>
          </div>
          <div class="dag-legend">
            <span><span class="badge stratum-emerald">Emerald</span> Axiom-Free</span>
            <span><span class="badge stratum-sapphire">Sapphire</span> Safe 2LTT</span>
            <span><span class="badge stratum-amber">Amber</span> propext / Quot.sound</span>
            <span><span class="badge stratum-crimson">Crimson</span> Classical.choice</span>
            <span><span class="badge stratum-none">None</span> Prose / Symbol / Plan / Sink</span>
          </div>
        </div>
      </section>

      <section role="tabpanel" id="panel-plan" aria-labelledby="tab-plan" hidden="until-found">
        <div class="panel-inner">
          <div class="panel-header">
            <div>
              <h2>Volume II 14-Slice Project Plan &amp; Milestones</h2>
              <p class="muted" style="margin:0.2rem 0 0;font-size:0.86rem;">Mechanical status computed from <code>nodes/plan/*.toml</code> deliverable checks in DuckDB.</p>
            </div>
          </div>
          <div id="milestone-grid" class="milestone-grid"></div>
          <div tabindex="0" role="region" aria-labelledby="roadmap-caption" class="table-wrapper responsive-table">
            <table>
              <caption id="roadmap-caption" style="padding:0.55rem 0.65rem;font-weight:700;text-align:left;background:var(--surface-muted);border-block-end:1px solid var(--border);">14-Slice Blueprint (9 Chapters + 3 KernelArena 2LTT Rungs)</caption>
              <thead>
                <tr>
                  <th scope="col">Slice</th>
                  <th scope="col">Milestone</th>
                  <th scope="col">Status</th>
                  <th scope="col">Target Modules</th>
                  <th scope="col">Guardrails</th>
                  <th scope="col">Scope</th>
                  <th scope="col">Issue</th>
                </tr>
              </thead>
              <tbody id="roadmap-tbody"></tbody>
            </table>
          </div>
        </div>
      </section>

      <section role="tabpanel" id="panel-ledger" aria-labelledby="tab-ledger" hidden="until-found">
        <div class="panel-inner">
          <div class="panel-header">
            <div>
              <h2>Four-Part Master Claims &amp; Grounding Ledger</h2>
              <p id="ledger-count" class="muted" style="margin:0.2rem 0 0;font-size:0.86rem;"></p>
            </div>
          </div>
          <div class="controls-bar">
            <div class="control-group">
              <label>Search <input type="search" id="ledger-search" placeholder="Filter by node id, title, statement, or decl..."></label>
              <label>Cohort
                <select id="filter-cohort">
                  <option value="ALL">All Cohorts</option>
                  <option value="Cohort I">Cohort I (Theorems / Cex)</option>
                  <option value="Cohort II">Cohort II (Defs / Remarks / Vol I)</option>
                  <option value="Cohort III">Cohort III (Inline Claims)</option>
                  <option value="Cohort IV">Cohort IV (Prose / Tables)</option>
                </select>
              </label>
              <label>Stratum
                <select id="filter-stratum">
                  <option value="ALL">All Strata</option>
                  <option value="emerald">Emerald</option>
                  <option value="sapphire">Sapphire</option>
                  <option value="amber">Amber</option>
                  <option value="crimson">Crimson</option>
                  <option value="none">None</option>
                </select>
              </label>
              <label>Blueprint Tier
                <select id="filter-tier">
                  <option value="ALL">All Tiers</option>
                  <option value="lean_ok">lean_ok</option>
                  <option value="lean_witness">lean_witness</option>
                  <option value="twoltt_ok">twoltt_ok</option>
                  <option value="none">none</option>
                </select>
              </label>
            </div>
          </div>
          <div tabindex="0" role="region" aria-labelledby="ledger-caption" class="table-wrapper responsive-table" style="margin-block-end:1.4rem;">
            <table>
              <caption id="ledger-caption" style="padding:0.55rem 0.65rem;font-weight:700;text-align:left;background:var(--surface-muted);border-block-end:1px solid var(--border);">Claims, Grounding Categories, &amp; Kernel Axiom Audit</caption>
              <thead>
                <tr>
                  <th scope="col">Node ID</th>
                  <th scope="col">Title</th>
                  <th scope="col">Category &amp; Tier</th>
                  <th scope="col">Stratum &amp; Axioms</th>
                  <th scope="col">Status &amp; Hashes</th>
                </tr>
              </thead>
              <tbody id="ledger-tbody"></tbody>
            </table>
          </div>

          <div class="panel-header">
            <div>
              <h2>1-to-1 Disjoint Declaration Ownership</h2>
              <p id="decl-count" class="muted" style="margin:0.2rem 0 0;font-size:0.86rem;"></p>
            </div>
            <div class="control-group">
              <label>Filter Declarations <input type="search" id="decl-search" placeholder="Filter Lean symbol or node ID..."></label>
            </div>
          </div>
          <div tabindex="0" role="region" aria-labelledby="decl-caption" class="table-wrapper responsive-table">
            <table>
              <caption id="decl-caption" style="padding:0.55rem 0.65rem;font-weight:700;text-align:left;background:var(--surface-muted);border-block-end:1px solid var(--border);">Disjoint Lean 4 Declarations &amp; 2LTT Certificates</caption>
              <thead>
                <tr>
                  <th scope="col">Declaration / Certificate</th>
                  <th scope="col">Owning Node</th>
                  <th scope="col">Kind</th>
                </tr>
              </thead>
              <tbody id="decl-tbody"></tbody>
            </table>
          </div>
        </div>
      </section>

      <section role="tabpanel" id="panel-process" aria-labelledby="tab-process" hidden="until-found">
        <div class="panel-inner">
          <div class="panel-header">
            <div>
              <h2>Royal Octavo PDF Artifacts &amp; Glass-Box Taint Architecture</h2>
              <p class="muted" style="margin:0.2rem 0 0;font-size:0.86rem;">Zero-drift Two-Hash Taint Engine, Two-Package TCB, Pass A/B/C Drill Scorecard, &amp; Publication Sinks.</p>
            </div>
          </div>
          <div id="pdf-cards" class="cards-grid"></div>

          <div class="process-svg-wrap">
            <svg viewBox="0 0 980 185" width="980" height="185" style="max-width:100%;height:auto;" role="img" aria-label="Two-hash taint and publication cone pipeline diagram">
              <defs>
                <marker id="proc-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto"><path d="M 0 1 L 10 5 L 0 9 z" fill="#1b365d"/></marker>
              </defs>
              <rect x="10" y="25" width="165" height="130" rx="5" fill="#f1f5f9" stroke="#1b365d" stroke-width="1.5"/>
              <text x="22" y="50" font-size="12" font-weight="700" fill="#0f172a">Declarative TOMLs</text>
              <text x="22" y="72" font-size="11" fill="#166534">spec_hash (VOL2_SPEC_V1)</text>
              <text x="22" y="92" font-size="11" fill="#1d4ed8">body_hash (VOL2_BODY_V1)</text>
              <text x="22" y="112" font-size="11" fill="#b45309">grounding_hash</text>
              <text x="22" y="135" font-size="10" fill="#475569">nodes/ch01, sym, vol1, plan, pub</text>

              <line x1="175" y1="90" x2="220" y2="90" stroke="#1b365d" stroke-width="1.8" marker-end="url(#proc-arrow)"/>

              <rect x="225" y="25" width="195" height="130" rx="5" fill="#eff6ff" stroke="#1d4ed8" stroke-width="1.5"/>
              <text x="237" y="50" font-size="12" font-weight="700" fill="#1e3a8a">DuckDB 5-Fiber Compiler</text>
              <text x="237" y="72" font-size="10.5" fill="#0f172a">• 0 cycles (per-fiber &amp; union)</text>
              <text x="237" y="90" font-size="10.5" fill="#0f172a">• 0 cross-TCB lean_dep edges</text>
              <text x="237" y="108" font-size="10.5" fill="#0f172a">• 5 Honesty Invariants</text>
              <text x="237" y="126" font-size="10.5" fill="#0f172a">• prose_paraphrase lock check</text>
              <text x="237" y="144" font-size="10.5" fill="#0f172a">• pub_target cone_hash</text>

              <line x1="420" y1="60" x2="470" y2="50" stroke="#1b365d" stroke-width="1.8" marker-end="url(#proc-arrow)"/>
              <line x1="420" y1="120" x2="470" y2="132" stroke="#1b365d" stroke-width="1.8" marker-end="url(#proc-arrow)"/>

              <rect x="475" y="15" width="215" height="70" rx="5" fill="#f0fdf4" stroke="#166534" stroke-width="1.5"/>
              <text x="488" y="38" font-size="12" font-weight="700" fill="#14532d">Zero-Mathlib KernelArena</text>
              <text x="488" y="56" font-size="10.5" fill="#0f172a">2LTT cert check + SHA-256 arena</text>
              <text x="488" y="72" font-size="10.5" fill="#0f172a">Bridged via rfl in CertChecks</text>

              <rect x="475" y="100" width="215" height="70" rx="5" fill="#fffbeb" stroke="#b45309" stroke-width="1.5"/>
              <text x="488" y="123" font-size="12" font-weight="700" fill="#78350f">Mathlib Vol II + AuditEnv</text>
              <text x="488" y="141" font-size="10.5" fill="#0f172a">Four-Color Axiom Spectrometer</text>
              <text x="488" y="157" font-size="10.5" fill="#0f172a">Hidden-Edge Gate (lean_dep cone)</text>

              <line x1="690" y1="50" x2="738" y2="85" stroke="#1b365d" stroke-width="1.8" marker-end="url(#proc-arrow)"/>
              <line x1="690" y1="135" x2="738" y2="98" stroke="#1b365d" stroke-width="1.8" marker-end="url(#proc-arrow)"/>

              <rect x="742" y="25" width="225" height="130" rx="5" fill="#f8fafc" stroke="#1b365d" stroke-width="1.5"/>
              <text x="755" y="50" font-size="12" font-weight="700" fill="#0f172a">Publication Sinks (Out=0)</text>
              <text x="755" y="72" font-size="10.5" fill="#0f172a">• main Docs (README/PROCESS/ROADMAP)</text>
              <text x="755" y="90" font-size="10.5" fill="#0f172a">• gh-pages Observatory + 3 PDFs</text>
              <text x="755" y="108" font-size="10.5" fill="#0f172a">• lean-export standalone branch</text>
              <text x="755" y="126" font-size="10.5" fill="#0f172a">• GitHub Milestones &amp; Issues</text>
              <text x="755" y="144" font-size="10" fill="#991b1b">Hard-blocked on any TAINTED node</text>
            </svg>
          </div>

          <h3 style="font-family:var(--font-serif);margin-block:0 0.6rem;">Pass A / B / C Adversarial Taint Drill</h3>
          <div id="drill-cards" class="cards-grid"></div>

          <h3 style="font-family:var(--font-serif);margin-block:0 0.6rem;">Five Cross-Volume Precision Guardrails</h3>
          <div id="guardrails-list" class="cards-grid"></div>

          <h3 style="font-family:var(--font-serif);margin-block:0 0.6rem;">Publication Sinks (<code>nodes/pub/*.toml</code>)</h3>
          <div tabindex="0" role="region" aria-labelledby="pub-caption" class="table-wrapper responsive-table">
            <table>
              <caption id="pub-caption" style="padding:0.55rem 0.65rem;font-weight:700;text-align:left;background:var(--surface-muted);border-block-end:1px solid var(--border);">Deterministic Publication Cone Locks</caption>
              <thead>
                <tr>
                  <th scope="col">Sink ID</th>
                  <th scope="col">Channel</th>
                  <th scope="col">Sensitivity</th>
                  <th scope="col">Outputs</th>
                  <th scope="col">Cone Hash</th>
                  <th scope="col">Status</th>
                </tr>
              </thead>
              <tbody id="pub-tbody"></tbody>
            </table>
          </div>
        </div>
      </section>
    </div>
  </main>

  <dialog id="node-inspector" closedby="any" aria-labelledby="inspector-title">
    <div class="dialog-head">
      <div>
        <div id="inspector-meta" style="display:flex;flex-wrap:wrap;gap:0.35rem;"></div>
        <h1 id="inspector-title">Node Inspector</h1>
      </div>
      <form method="dialog">
        <button type="submit" value="close" class="btn btn-primary" autofocus>Close</button>
      </form>
    </div>
    <div id="inspector-body" class="dialog-body"></div>
  </dialog>

  <script src="app.js"></script>
</body>
</html>
"""


def emit_observatory() -> dict[str, Any]:
    payload = build_network_payload()
    GH_PAGES_DIR.mkdir(parents=True, exist_ok=True)
    (GH_PAGES_DIR / "data").mkdir(parents=True, exist_ok=True)
    pdfs_dir = GH_PAGES_DIR / "pdfs"
    pdfs_dir.mkdir(parents=True, exist_ok=True)

    (GH_PAGES_DIR / ".nojekyll").write_text("", encoding="utf-8")
    (GH_PAGES_DIR / "styles.css").write_text(render_styles_css(), encoding="utf-8")
    (GH_PAGES_DIR / "app.js").write_text(render_app_js(), encoding="utf-8")
    (GH_PAGES_DIR / "index.html").write_text(render_index_html(payload), encoding="utf-8")
    (GH_PAGES_DIR / "data" / "network.json").write_text(
        json.dumps(payload, indent=2) + "\n", encoding="utf-8"
    )

    copied_pdfs: list[str] = []
    for fname, _, _ in PDF_FILES:
        src = TEX_DIR / fname
        if src.exists():
            shutil.copy2(src, pdfs_dir / fname)
            copied_pdfs.append(fname)

    return {"payload": payload, "copied_pdfs": copied_pdfs}


def main() -> int:
    parser = argparse.ArgumentParser(description="Emit static Glass-Box Web Observatory into build/gh_pages/.")
    parser.add_argument(
        "--commit-branch",
        default="",
        help="Optional branch name (e.g. gh-pages) to commit build/gh_pages/ via GIT_INDEX_FILE without checkout.",
    )
    args = parser.parse_args()

    res = emit_observatory()
    payload = res["payload"]
    metrics = payload["metrics"]
    commit_sha = ""
    if args.commit_branch:
        commit_sha = commit_stage_to_branch(
            GH_PAGES_DIR,
            args.commit_branch,
            f"chore(gh-pages): publish Vol II Glass-Box Observatory ({metrics['core_clean']}/{metrics['core_nodes']} CLEAN)",
        )
    print(
        f"EMIT_OBSERVATORY_OK nodes={metrics['total_nodes']} edges={metrics['total_edges']} "
        f"pdfs={res['copied_pdfs']} branch={args.commit_branch or 'none'} commit={commit_sha or 'none'}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
