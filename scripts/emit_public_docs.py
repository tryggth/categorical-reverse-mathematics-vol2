#!/usr/bin/env python3
"""Deterministic front-door documentation generator & freshness checker."""

from __future__ import annotations

import argparse
import json
import sys
import tomllib
from collections import Counter
from pathlib import Path
from typing import Any

import duckdb

REPO_ROOT = Path(__file__).resolve().parent.parent
MANIFEST_PATH = REPO_ROOT / "manifest.toml"
GUARDRAILS_PATH = REPO_ROOT / "manifest" / "guardrails.toml"
PUB_LOCK_PATH = REPO_ROOT / "manifest" / "publication_lock.json"
DB_PATH = REPO_ROOT / "build" / "vol2.duckdb"

STATUS_BADGES = {
    "VERIFIED": "`VERIFIED`",
    "ACTIVE": "`ACTIVE`",
    "PLANNED": "`PLANNED`",
}

STRATUM_LABELS = {
    "emerald": "Emerald (Axiom-Free)",
    "sapphire": "Sapphire (Safe 2LTT)",
    "amber": "Amber (`propext` / `Quot.sound`)",
    "crimson": "Crimson (`Classical.choice`)",
    "none": "None (Prose / Symbol)",
}


def load_public_doc_context() -> dict[str, Any]:
    manifest = tomllib.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    guardrails = tomllib.loads(GUARDRAILS_PATH.read_text(encoding="utf-8")).get("guardrail", [])
    pub_lock: dict[str, Any] = {}
    if PUB_LOCK_PATH.exists():
        pub_lock = json.loads(PUB_LOCK_PATH.read_text(encoding="utf-8"))

    con = duckdb.connect(str(DB_PATH), read_only=True)
    core_rows = con.execute(
        """
        SELECT n.id, n.kind, n.title, n.chapter, n.section, n.seq_order,
               n.formal_pkg, n.stratum, n.module, n.spec_hash, n.body_hash,
               n.grounding_hash, n.taint_status,
               cg.cohort, cg.primary_category, cg.blueprint_tier
        FROM nodes n
        LEFT JOIN claim_groundings cg ON cg.node_id = n.id
        WHERE n.kind NOT IN ('work_item', 'pub_target')
        ORDER BY n.seq_order, n.id
        """
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
        SELECT p.node_id, n.title, p.channel, p.sensitivity, p.outputs_json, p.published_paths_json
        FROM pub_targets p
        JOIN nodes n ON n.id = p.node_id
        ORDER BY n.seq_order, p.node_id
        """
    ).fetchall()
    frontdoor_prov_rows = con.execute(
        """
        SELECT DISTINCT e.src_id
        FROM edges e
        JOIN nodes src ON e.src_id = src.id
        WHERE e.dst_id = 'pub:doc:repo-frontdoor' AND src.kind = 'pub_target'
        ORDER BY e.src_id
        """
    ).fetchall()
    edge_counts = con.execute(
        "SELECT fiber, COUNT(*) FROM edges GROUP BY fiber ORDER BY fiber"
    ).fetchall()
    total_edges = con.execute("SELECT COUNT(*) FROM edges").fetchone()[0]
    decl_counts = con.execute(
        "SELECT ownership_kind, COUNT(*) FROM decl_ownership GROUP BY ownership_kind ORDER BY ownership_kind"
    ).fetchall()
    headline_rows = con.execute(
        """
        SELECT e.src_id, n.title, n.stratum, n.spec_hash, cg.blueprint_tier, e.metadata_json
        FROM edges e
        JOIN nodes n ON n.id = e.src_id
        LEFT JOIN claim_groundings cg ON cg.node_id = n.id
        WHERE e.dst_id = 'pub:doc:repo-frontdoor' AND e.fiber = 'prose_paraphrase'
        ORDER BY n.seq_order, e.src_id
        """
    ).fetchall()
    con.close()

    core_nodes = [
        {
            "id": r[0],
            "kind": r[1],
            "title": r[2],
            "chapter": r[3],
            "section": r[4],
            "seq_order": r[5],
            "formal_pkg": r[6],
            "stratum": r[7],
            "module": r[8],
            "spec_hash": r[9],
            "body_hash": r[10],
            "grounding_hash": r[11],
            "taint_status": r[12],
            "cohort": r[13] or ("Cohort II" if r[1] == "symbol" else "Other"),
            "primary_category": r[14] or "",
            "blueprint_tier": r[15] or "none",
        }
        for r in core_rows
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
            "published_paths": json.loads(r[5]),
        }
        for r in pub_rows
    ]
    pub_targets_by_id = {p["id"]: p for p in pub_targets}
    frontdoor_providers = [r[0] for r in frontdoor_prov_rows]
    headlines = [
        {
            "id": r[0],
            "title": r[1],
            "stratum": r[2],
            "spec_hash": r[3],
            "blueprint_tier": r[4] or "none",
            "scope_note": json.loads(r[5]).get("scope_note", ""),
        }
        for r in headline_rows
    ]
    return {
        "manifest": manifest,
        "guardrails": guardrails,
        "pub_lock": pub_lock,
        "core_nodes": core_nodes,
        "work_items": work_items,
        "pub_targets": pub_targets,
        "pub_targets_by_id": pub_targets_by_id,
        "frontdoor_providers": frontdoor_providers,
        "edge_counts": {r[0]: r[1] for r in edge_counts},
        "total_edges": total_edges,
        "decl_counts": {r[0]: r[1] for r in decl_counts},
        "headlines": headlines,
    }


def _pdf_link_labels(rel_path: str) -> tuple[str, str, str]:
    fname = Path(rel_path).name
    known = {
        "crm_vol2_monograph.pdf": ("Monograph PDF", "Royal Octavo Monograph PDF"),
        "crm_vol2_claims_ledger.pdf": ("4-Part Master Claims Ledger PDF", "4-Part Master Claims & Grounding Ledger PDF"),
        "course_pack_ch01_probe_calibration.pdf": ("Ch. 1 Course Pack PDF", "Standalone Ch. 1 Course Pack PDF"),
        "course_pack_ch02_class_set_kaleidoscope.pdf": ("Ch. 2 Course Pack PDF", "Standalone Ch. 2 Course Pack PDF"),
        "course_pack_ch03_piset_transgression.pdf": ("Ch. 3 Course Pack PDF", "Standalone Ch. 3 Course Pack PDF"),
    }
    if fname in known:
        short_lbl, surface_lbl = known[fname]
        return short_lbl, surface_lbl, fname
    stem_lbl = fname.removesuffix(".pdf").replace("_", " ").title()
    return stem_lbl, f"{stem_lbl} PDF", fname


def render_readme(ctx: dict[str, Any]) -> str:
    m = ctx["manifest"]
    pub_lock = ctx["pub_lock"]
    gh_repo = pub_lock.get("github_repo") or m.get("github_repo", "tryggth/categorical-reverse-mathematics-vol2")
    repo_url = f"https://github.com/{gh_repo}"
    owner, rname = gh_repo.split("/", 1) if "/" in gh_repo else ("tryggth", gh_repo)
    pages_base_raw = (m.get("pages_base_url") or pub_lock.get("pages_url") or f"https://{owner}.github.io/{rname}").rstrip("/")
    pages_url = f"{pages_base_raw}/"
    lean_export_url = f"{repo_url}/tree/lean-export"

    pub_by_id = ctx.get("pub_targets_by_id", {})
    provider_ids = ctx.get("frontdoor_providers") or [
        pid for pid in ("pub:web:observatory", "pub:pdf:monograph", "pub:pdf:claims-ledger", "pub:pdf:course-packs") if pid in pub_by_id
    ]
    web_prov = pub_by_id.get("pub:web:observatory", {})
    web_paths = web_prov.get("published_paths", ["index.html"])
    obs_href = pages_url if "index.html" in web_paths else f"{pages_base_raw}/{web_paths[0].lstrip('/')}"

    pdf_rel_paths: list[str] = []
    for pid in ("pub:pdf:monograph", "pub:pdf:claims-ledger", "pub:pdf:course-packs"):
        if pid in provider_ids or pid in pub_by_id:
            for rp in pub_by_id.get(pid, {}).get("published_paths", []):
                if rp not in pdf_rel_paths:
                    pdf_rel_paths.append(rp)
    for pid in provider_ids:
        if pid.startswith("pub:pdf:") and pid not in ("pub:pdf:monograph", "pub:pdf:claims-ledger", "pub:pdf:course-packs"):
            for rp in pub_by_id.get(pid, {}).get("published_paths", []):
                if rp not in pdf_rel_paths:
                    pdf_rel_paths.append(rp)

    inline_pdf_links = " · ".join(
        f"[{_pdf_link_labels(rp)[0]}]({pages_base_raw}/{rp.lstrip('/')})" for rp in pdf_rel_paths
    )
    table_pdf_rows = [
        f"| **{_pdf_link_labels(rp)[1]}** | Observatory PDF | [{_pdf_link_labels(rp)[2]}]({pages_base_raw}/{rp.lstrip('/')}) |"
        for rp in pdf_rel_paths
    ]

    core = ctx["core_nodes"]
    wis = ctx["work_items"]
    wi_counts = Counter(w["status"] for w in wis)
    stratum_counts = Counter(n["stratum"] for n in core)
    cohort_counts = Counter(n["cohort"] for n in core)
    clean_count = sum(1 for n in core if n["taint_status"] == "CLEAN")
    tainted_count = sum(1 for n in core if n["taint_status"] == "TAINTED")
    lean_decls = ctx["decl_counts"].get("lean_decl", 0)
    certs_count = ctx["decl_counts"].get("twoltt_cert", 0)
    active_wi = next((w for w in wis if w["status"] == "ACTIVE"), None)

    lines = [
        f"# {m['working_title']}",
        f"### *{m['working_subtitle']}*",
        "",
        f"> **[Live Interactive Glass-Box Observatory (GitHub Pages)]({obs_href})** · **[How This Book Is Built (`PROCESS.md`)](PROCESS.md)** · **[14-Slice Project Plan (`ROADMAP.md`)](ROADMAP.md)**  ",
        f"> **Live Royal Octavo PDFs:** {inline_pdf_links}  ",
        f"> **Synced Engineering & Open-Problem Backlog:** [GitHub Issues]({repo_url}/issues) · [Milestones]({repo_url}/milestones)",
        "",
        f"> **Glass-Box 5-Fiber Formalization & Monograph Network (`{m['phase']}`)**  ",
        f"> **Author:** {m['author']} ({m['location']}) · **License:** {m['license']} · **Working Title Locked:** `{str(m.get('title_locked', False)).lower()}`  ",
        f"> **Companion to Volume I:** `{m['vol1_root_default']} (HEAD {m['vol1_pinned_head']})` · Zenodo Concept DOI [`{m['vol1_zenodo_doi']}`](https://doi.org/{m['vol1_zenodo_doi']})",
        "",
        "Volume II is developed as a **single-network, machine-checked mathematical and monograph architecture**. Every mathematical definition, theorem, counterexample, 2LTT certificate, LaTeX section, roadmap slice, and publication sink compiles into `build/vol2.duckdb` across five orthogonal fibers (`logical_dep`, `lean_dep`, `prose_paraphrase`, `notation`, `curriculum`) with zero cycles, disjoint 1-to-1 declaration ownership, and strict separation between **formal statement integrity (`spec_hash`)** and **proof/exposition edits (`body_hash`, `grounding_hash`)**.",
        "",
        "## Book-Creation Architecture",
        "",
        "```mermaid",
        "flowchart LR",
        "  SRC[\"nodes/**/*.toml + certs/*.2ltt.json\"] --> DB[\"DuckDB (5 Acyclic Fibers + Two-Hash Taint Engine)\"]",
        "  DB --> TCB[\"mathlib_vol2 + KernelArena (Two-Package TCB)\"]",
        "  DB --> PDFS[\"5 Royal Octavo PDFs (Monograph, Ledger, Ch.1–Ch.3 Course Packs)\"]",
        "  TCB --> PDFS",
        "  TCB --> SMAIN[\"pub:doc:* -> main (README, PROCESS, ROADMAP)\"]",
        "  PDFS --> SPAGES[\"pub:web/pdf:* -> gh-pages (Observatory + PDFs)\"]",
        "  SPAGES --> SMAIN",
        "  TCB --> SLEAN[\"pub:branch:lean-export -> lean-export (Standalone Lean 4)\"]",
        "  DB --> SISS[\"pub:gh:issues-board -> GitHub Issues & Milestones\"]",
        "```",
        "",
        "> **Branch Guide (Do Not Merge `lean-export` / `gh-pages` into `main`):**",
        "> - **`main`** — Canonical single-network source of truth (`nodes/**/*.toml`, `certs/*.2ltt.json`, `scripts/`, `manifest/`, `README.md`, `PROCESS.md`, `ROADMAP.md`). All mathematical edits and PRs target `main` only.",
        "> - **`lean-export`** — Standalone auto-generated Lean 4 + `KernelArena` projection branch (`scripts/export_lean_branch.py`, committed via `GIT_INDEX_FILE` without DuckDB or LaTeX). **Do not merge `lean-export` into `main`.**",
        "> - **`gh-pages`** — Auto-generated static Glass-Box Observatory + 5 Royal Octavo PDFs (`scripts/emit_observatory.py`, committed via `GIT_INDEX_FILE`). **Do not merge `gh-pages` into `main`.**",
        "",
        "## Live Public Surfaces",
        "",
        "| Surface | Channel | Location |",
        "|---|---|---|",
        f"| **Source Repository (`main`)** | GitHub | [{gh_repo}]({repo_url}) |",
        f"| **Glass-Box Interactive Observatory** | `gh-pages` | [{obs_href}]({obs_href}) |",
        f"| **Standalone Lean 4 + KernelArena Workspace** | `lean-export` | [branch `lean-export`]({lean_export_url}) |",
        *table_pdf_rows,
        "| **Glass-Box Methodology & Taint Engine Guide** | Repository Doc | [PROCESS.md](PROCESS.md) |",
        "| **14-Slice Volume II Project Plan** | Repository Doc | [ROADMAP.md](ROADMAP.md) |",
        "",
        "## Current Verification Telemetry",
        "",
        f"- **Core Mathematical, Prose, & Symbol Nodes:** `{len(core)}` (`{clean_count}` CLEAN, `{tainted_count}` TAINTED across `{ctx['total_edges']}` directed edges)",
        f"- **14-Slice Blueprint (`nodes/plan/*.toml`):** `{wi_counts.get('VERIFIED', 0)} VERIFIED`, `{wi_counts.get('ACTIVE', 0)} ACTIVE`, `{wi_counts.get('PLANNED', 0)} PLANNED`"
        + (f" — active slice: `{active_wi['id']}` ({active_wi['title']})" if active_wi else ""),
        f"- **Publication Sinks (`nodes/pub/*.toml`):** `{len(ctx['pub_targets'])}` sinks (`main_docs`, `gh_pages`, `lean_export`, `gh_issues`) with `0` edges into core/plan nodes (`pub_target -> pub_target` endpoint links allowed)",
        f"- **Two-Package TCB (`{m['lean_toolchain']}`):** `{lean_decls}` disjoint Lean 4 declarations (`HomotopyCRMVol2` + `AuditEnv`) + `{certs_count}` zero-`Mathlib` `KernelArena` 2LTT certificates (`0` cross-package `lean_dep` edges)",
        (
            f"- **Four-Color Stratum Spectrometer:** "
            f"Emerald={stratum_counts.get('emerald', 0)}, "
            f"Sapphire={stratum_counts.get('sapphire', 0)}, "
            f"Amber={stratum_counts.get('amber', 0)}, "
            f"Crimson={stratum_counts.get('crimson', 0)}, "
            f"Prose/Symbol={stratum_counts.get('none', 0)}"
        ),
        (
            f"- **Four-Part Grounding Cohorts:** "
            f"Cohort I={cohort_counts.get('Cohort I', 0)}, "
            f"Cohort II={cohort_counts.get('Cohort II', 0)}, "
            f"Cohort III={cohort_counts.get('Cohort III', 0)}, "
            f"Cohort IV={cohort_counts.get('Cohort IV', 0)}"
        ),
        "",
        "## Headline Verified Nodes (Locked via `prose_paraphrase`)",
        "",
        "| Node ID | Title | Stratum | Blueprint Tier | Spec8 |",
        "|---|---|---|---|---|",
    ]
    for h in ctx["headlines"]:
        lines.append(
            f"| `{h['id']}` | {h['title']} | {STRATUM_LABELS.get(h['stratum'], h['stratum'])} | `{h['blueprint_tier']}` | `{h['spec_hash'][:8]}` |"
        )

    lines.extend(
        [
            "",
            "## Quickstart & Local Verification",
            "",
            "```bash",
            "# 1. Compile the 5-fiber DuckDB network and run structural/honesty gates",
            "python3 scripts/compile_db.py",
            "",
            "# 2. Verify generated front-door documentation freshness",
            "python3 scripts/emit_public_docs.py --check",
            "",
            "# 3. Emit Lean 4 sources and run zero-Mathlib 2LTT KernelArena self-tests + cert checks",
            "python3 scripts/emit_lean.py",
            "lake --dir kernel_arena build",
            "lake --dir kernel_arena exe kernel-arena --self-test",
            "lake --dir kernel_arena exe kernel-arena verify certs/ch01_bool_id_bootstrap.2ltt.json",
            "lake --dir kernel_arena exe kernel-arena verify certs/tcb_r1_path_sym_kan.2ltt.json",
            "lake --dir kernel_arena exe kernel-arena verify certs/tcb_r1_univ_bool_ua_not_holonomy.2ltt.json",
            "",
            "# 4. Build Mathlib Vol II modules and run AuditEnv axiom/stratum/hidden-edge checks",
            "(cd mathlib_vol2 && lake exe cache get && lake build HomotopyCRM audit_env && lake exe audit_env ../build/audit_nodes_manifest.json)",
            "",
            "# 5. Run the complete verification gatekeeper (including Royal Octavo PDFs locally)",
            "python3 scripts/gatekeeper.py",
            "```",
            "",
            f"> **Note on Standalone Lean Use:** If you only want the generated Lean 4 + `KernelArena` codebase without compiling DuckDB or LaTeX, switch to or clone the standalone [`lean-export`]({lean_export_url}) branch.",
            "",
        ]
    )
    return "\n".join(lines)


def render_process(ctx: dict[str, Any]) -> str:
    m = ctx["manifest"]
    edges = ctx["edge_counts"]
    lines = [
        "# Glass-Box Engineering & Verification Methodology (`PROCESS.md`)",
        "",
        f"This document explains the machine-checked **single-network architecture** powering *{m['working_title']}: {m['working_subtitle']}*.",
        "",
        "## 1. Single-Network 5-Fiber DAG & DuckDB SQL Gates",
        "",
        "All mathematical definitions, theorems, counterexamples, inline claims, prose blocks, summary tables, symbol registries, Volume I contracts, roadmap work items (`nodes/plan/*.toml`), and publication sinks (`nodes/pub/*.toml`) live as declarative TOML nodes compiled deterministically by `scripts/compile_db.py` into `build/vol2.duckdb` (`scripts/schema.sql`).",
        "",
        "Edges span **five orthogonal fibers** (currently `{0}` total directed edges):".format(ctx["total_edges"]),
        "",
        f"1. **`logical_dep` ({edges.get('logical_dep', 0)} edges):** Mathematical and structural proof dependencies.",
        f"2. **`lean_dep` ({edges.get('lean_dep', 0)} edges):** Formal Lean 4 module/declaration dependencies verified by the Hidden-Edge Gate.",
        f"3. **`prose_paraphrase` ({edges.get('prose_paraphrase', 0)} edges):** Spec-hash-locked paraphrasing links from formal/claim nodes into Cohort IV prose containers and `pub:doc:repo-frontdoor`.",
        f"4. **`notation` ({edges.get('notation', 0)} edges):** Automatic dependencies induced by `{{{{sym:...}}}}` and `{{{{ref:...}}}}` macros.",
        f"5. **`curriculum` ({edges.get('curriculum', 0)} edges):** Pedagogical dependencies used by `scripts/slice_course.py` to carve standalone Royal Octavo Course Packs.",
        "",
        "DuckDB enforces four structural SQL invariants on every compile:",
        "- **Per-Fiber & Structural-Union Acyclicity:** Terminating `WITH RECURSIVE` CTE cycle checks across each fiber individually and across their union.",
        "- **Pinned Volume I Boundary:** Every `vol1_external` contract has in-degree `0`.",
        "- **Two-Package TCB Isolation:** Zero `lean_dep` edges may cross between `mathlib_vol2` and `kernel_arena`.",
        "- **Publication Sink Discipline:** No edge from a `pub_target` may target a non-`pub_target` node (`0` core pollution, `0` cycles); acyclic `pub_target -> pub_target` endpoint-provider edges are permitted so `pub:doc:repo-frontdoor` tracks published `gh-pages` endpoints.",
        "",
        "## 2. Two-Hash Taint Isolation (`spec_hash`, `body_hash`, `grounding_hash`) & `harvest_body.py`",
        "",
        "Each node splits its content into three cryptographically isolated digests:",
        "",
        "| Hash Domain | Prefix | Covered Fields | Effect of Mutation |",
        "|---|---|---|---|",
        "| `spec_hash` | `VOL2_SPEC_V1\\0` | `id`, `kind`, `axis`, `grounding_tier`, `formal_pkg`, `[spec]` (Lean signatures, statements, or 2LTT goal AST + strata flags) | Direct `TAINTED` on node + transitive `TAINTED` across all downstream fibers + `PROSE_LOCK_MISMATCH` on locked consumers |",
        "| `body_hash` | `VOL2_BODY_V1\\0` | `[body]` (`lean_body`, LaTeX proof/exposition `tex`), plus 2LTT `proof_term_ast`, `fuel_hint`, `sha256_arena` | `BODY_DIRTY` on the edited node **only** (`0` downstream propagation) |",
        "| `grounding_hash` | `VOL2_GROUNDING_V1\\0` | `[grounding]` (`primary_category`, `blueprint_tier`, `characterization_types`, `witness_scope`, `dual_pillars`) | `GROUNDING_DIRTY` on the edited node **only** (re-checked by all 5 Honesty Invariants) |",
        "",
        "When iterating on Lean tactics inside emitted `mathlib_vol2/HomotopyCRM/Vol2/*.lean` files, `scripts/harvest_body.py` harvests ONLY the region between `-- BEGIN_BODY <id>` and `-- END_BODY <id>` back into the source TOML, hard-rejecting (`E_SIGNATURE_MUTATION`) any edit outside body markers.",
        "",
        "## 3. `prose_paraphrase` Anti-Drift Locks",
        "",
        "Every Cohort IV prose container (`prose_block`, `summary_table`) and `pub:doc:repo-frontdoor` attaches explicit `[[edges.prose_paraphrase]]` locks pinning `locked_spec_hash` to the exact `spec_hash` of each referenced theorem or definition. Whenever an underlying mathematical statement changes, `compile_db.py` immediately raises `PROSE_LOCK_MISMATCH`, taints the prose consumer, and hard-blocks `gatekeeper.py --publish` until the prose summary is reviewed and re-locked.",
        "",
        "## 4. Two-Package Trusted Computing Base (`mathlib_vol2` + `kernel_arena`)",
        "",
        "- **`kernel_arena/` (Zero-`Mathlib` 2LTT Kernel):** A standalone Lean 4 package (`leanprover/lean4:v4.28.0`) implementing a two-level type theory checker separating fibrant types (`U^f`) from strict types (`U^s`) with only the one-way lift `U^f -> U^s`. Every certificate JSON (`certs/*.2ltt.json`) carries a canonical SHA-256 arena digest verified both by `lake exe kernel-arena verify` and kernel-reduced (`rfl`, zero axioms) inside `HomotopyCRM.Vol2.CertChecks`.",
        "- **`mathlib_vol2/` (`HomotopyCRMVol2` + `AuditEnv.lean`):** Standard Lean 4 + `mathlib4` formalization package. After `lake build HomotopyCRM audit_env`, `AuditEnv.lean` reflects over the compiled `Environment`, verifies every node's declared `decl_names` (rejecting `.axiomInfo`, `.opaqueInfo`, `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, or unregistered custom axioms), and enforces the **Hidden-Edge Gate**: every `HomotopyCRM.Vol2.*` constant referenced directly or transitively must belong to a declared ancestor in that node's backward `lean_dep` cone.",
        "",
        "## 5. Four-Color Stratum Spectrometer",
        "",
        "`AuditEnv.lean` computes each formal node's constructive stratum directly from `Lean.CollectAxioms.collect` and enforces an exact match with its TOML `stratum`:",
        "",
        "| Stratum | Kernel Axioms | Semantics |",
        "|---|---|---|",
        "| **Emerald** | `[]` | Purely constructive, axiom-free Lean 4 or zero-axiom `KernelArena` kernel reduction |",
        "| **Sapphire** | Safe 2LTT | Constructive two-level type-theoretic extensions (`inner_univalence_V`, `inner_coalgebra_nu`) inside zero-`Mathlib` `KernelArena` |",
        "| **Amber** | `propext`, `Quot.sound` | Propositional extensionality and/or quotient soundness without choice |",
        "| **Crimson** | `Classical.choice` (+ `propext`, `Quot.sound`) | Classical choice-dependent theorems |",
        "",
        "## 6. Two-Tier Honesty (`\\leanok` / `\\leanwitness`) & Five Honesty Invariants",
        "",
        "LaTeX rendering (`scripts/emit_tex.py`) distinguishes complete formalizations (`\\leanok` / `\\twolttok`) from scoped computational witnesses (`\\leanwitness` / `\\twolttwitness` with a mandatory `witness_scope` explaining which part is mechanized vs. proved in the monograph). `compile_db.py` enforces five hard honesty invariants across Cohorts I–IV:",
        "",
        "1. **1-to-1 Declaration Ownership (`decl_ownership`):** Every Lean declaration and 2LTT certificate path is owned by at most one node.",
        "2. **Two-Tier Blueprint Honesty:** `lean_ok` / `twoltt_ok` cannot be claimed on partial witnesses; `lean_witness` / `twoltt_witness` requires a non-empty `witness_scope`; `Proved by Lean code` / `Proved by 2LTT certificate` requires full `*_ok` status.",
        "3. **Citation-Locator Non-Vacuity:** Every `external_theorem`, `folklore`, or `standard_def` node must cite a verified BibTeX key from Volume I/II `.bib` files with an explicit theorem/section/page locator.",
        "4. **Conjecture Quarantine:** No unflagged proved node may depend transitively along `logical_dep` on an `unfounded_conjecture` or `open_problem` without `spec.conditional_on_conjecture = true`.",
        "5. **Cohort IV Paraphrase Completeness:** Every `prose_block` and `summary_table` must carry at least one incoming `prose_paraphrase` edge.",
        "",
        "## 7. Pass A / B / C Taint Drill Verification & Publication Impact Graph",
        "",
        "During Phase 0 (`logs/drill_report.json`), the three-pass adversarial drill verified the taint and isolation guarantees end-to-end:",
        "",
        "- **Pass A (Clean Baseline):** `10/10 CLEAN`, `0 TAINTED`, `0` cycles, `0` TCB violations, `6` audited formal nodes, `3/3` Royal Octavo PDFs clean.",
        "- **Pass B (Clause 3 Spec Injection):** Injecting Clause 3 into `ch01:def:probe-suite` changed its `spec_hash`, producing `7 TAINTED` nodes, mapping the missing-field Lean error (`ProbeSuite.lean:274`) directly back to `ch01:cex:flow-f1-frontier-nonmonotone` via sourcemaps, and flagging `PROSE_LOCK_MISMATCH` on both Cohort IV nodes.",
        "- **Pass C (Remediation + Body Isolation):** Remediating Clause 3 restored `10/10 CLEAN`; `harvest_body.py` accepted `-- BEGIN_BODY` edits and rejected out-of-bounds signature edits; mutating `lean_body` produced `BODY_DIRTY=1 / TAINTED=0 / CLEAN=9`, proving statement-vs-proof hash isolation.",
        "",
        "For publication, each out-degree-0 `pub_target` (`nodes/pub/*.toml`) computes a deterministic `cone_hash` in DuckDB scoped to its `sensitivity` (`spec_and_metrics`, `spec_and_body`, `spec_body_and_grounding`, `lean_only`, or `plan_and_problems`) and compares it against `manifest/publication_lock.json` (`CLEAN`, `ARTIFACT_DIRTY`, or `TAINTED` — which hard-blocks `gatekeeper.py --publish`):",
        "",
        "```mermaid",
        "flowchart LR",
        "  N[\"Core Nodes (TOML)\"] --> DB[\"DuckDB 5-Fiber Network\"]",
        "  P[\"14 Work Items (nodes/plan)\"] --> DB",
        "  DB --> G[\"Gatekeeper (KernelArena + AuditEnv + TeX)\"]",
        "  G -->|\"spec_hash + issues\"| P1[\"pub:doc:repo-frontdoor (main Docs)\"]",
        "  G -->|\"full graph + groundings\"| P2[\"pub:web:observatory (gh-pages)\"]",
        "  G -->|\"spec_and_body\"| P3[\"pub:pdf:* (Monograph, Ledger, Course Pack)\"]",
        "  G -->|\"lean_only\"| P4[\"pub:branch:lean-export (Standalone Lean)\"]",
        "  G -->|\"plan_and_problems\"| P5[\"pub:gh:issues-board (GitHub Issues)\"]",
        "```",
        "",
        "## 8. Cross-Volume Precision Guardrails & Portable Fence",
        "",
        "The Volume I repository (`" + m["vol1_root_default"] + "`, pinned HEAD `" + m["vol1_pinned_head"] + "`) is **strictly read-only**, verified before and after local builds by `scripts/fence_check.py --verify` (and logged as `SKIPPED_REMOTE_CI` on GitHub Actions where the sibling Volume I clone is absent). Every Volume II slice enforces the five Volume I guardrails (`manifest/guardrails.toml`):",
        "",
    ]
    for idx, g in enumerate(ctx["guardrails"], 1):
        lines.append(f"{idx}. **`{g['id']}` — {g['title']}** (Volume I anchor `{g['vol1_anchor']}`): {g['statement']}")
    lines.append("")
    return "\n".join(lines)


def render_roadmap(ctx: dict[str, Any]) -> str:
    m = ctx["manifest"]
    pub_lock = ctx["pub_lock"]
    gh_repo = pub_lock.get("github_repo") or m.get("github_repo", "tryggth/categorical-reverse-mathematics-vol2")
    repo_url = f"https://github.com/{gh_repo}"
    issues_map = pub_lock.get("issues", {})
    wis = ctx["work_items"]
    counts = Counter(w["status"] for w in wis)

    lines = [
        "# Volume II Project Roadmap — 14-Slice Blueprint (`ROADMAP.md`)",
        "",
        f"Generated deterministically from `build/vol2.duckdb` (`work_items` table) and `manifest/publication_lock.json` for **{m['working_title']}** (`{m['phase']}`).",
        "",
        "## Progress Summary",
        "",
        f"- **Total Slices:** `{len(wis)}` (Chapters 1–9 + 3 `KernelArena` 2LTT TCB Rungs)",
        f"- **Verified (`VERIFIED`):** `{counts.get('VERIFIED', 0)}` (all listed `deliverable_nodes` exist and are `CLEAN` in `vol2.duckdb`)",
        f"- **Active (`ACTIVE`):** `{counts.get('ACTIVE', 0)}` (lowest `seq_order` unverified slice)",
        f"- **Planned (`PLANNED`):** `{counts.get('PLANNED', 0)}`",
        "",
        "## 14-Slice Master Schedule",
        "",
        "| # | Slice | Milestone | Status | Deliverables | Target Modules | Guardrails | Issue |",
        "|---|---|---|---|---|---|---|---|",
    ]
    for w in wis:
        nid = w["id"]
        badge = STATUS_BADGES.get(w["status"], w["status"])
        deliv_str = f"`{w['verified_deliverables']}/{w['total_deliverables']}`"
        mods_str = ", ".join(f"`{mod}`" for mod in w["target_modules"]) if w["target_modules"] else "—"
        gr_str = ", ".join(f"`{g}`" for g in w["guardrails"]) if w["guardrails"] else "—"
        irec = issues_map.get(nid)
        if irec and irec.get("number"):
            inum = irec["number"]
            iurl = irec.get("url") or f"{repo_url}/issues/{inum}"
            issue_cell = f"[#{inum}]({iurl})"
        elif w["status"] == "VERIFIED":
            issue_cell = "Done"
        else:
            issue_cell = "Pending sync"
        lines.append(
            f"| {w['seq_order']} | `{w['slice_code']}` (`{nid}`) | {w['milestone']} | {badge} | {deliv_str} | {mods_str} | {gr_str} | {issue_cell} |"
        )

    lines.extend(["", "## Detailed Slice Specifications", ""])
    for w in wis:
        nid = w["id"]
        irec = issues_map.get(nid)
        issue_note = ""
        if irec and irec.get("number"):
            iurl = irec.get("url") or f"{repo_url}/issues/{irec['number']}"
            issue_note = f" · Issue [#{irec['number']}]({iurl})"
        lines.extend(
            [
                f"### {w['seq_order']}. {w['title']} (`{nid}`)",
                f"- **Status:** {STATUS_BADGES.get(w['status'], w['status'])} (`{w['verified_deliverables']}/{w['total_deliverables']}` deliverables `CLEAN`){issue_note}",
                f"- **Milestone {w['milestone_num']}:** {w['milestone']} (`{w['slice_code']}`)",
                f"- **Target Modules:** {', '.join(f'`{x}`' for x in w['target_modules'])}",
                f"- **Deliverable Nodes:** {', '.join(f'`{x}`' for x in w['deliverable_nodes'])}",
                f"- **Guardrails:** {', '.join(f'`{x}`' for x in w['guardrails']) if w['guardrails'] else 'None'}",
                f"- **Scope:** {w['summary']}",
                "",
            ]
        )
    return "\n".join(lines)


def render_citation(ctx: dict[str, Any]) -> str:
    m = ctx["manifest"]
    pub_lock = ctx["pub_lock"]
    gh_repo = pub_lock.get("github_repo") or m.get("github_repo", "tryggth/categorical-reverse-mathematics-vol2")
    repo_url = f"https://github.com/{gh_repo}"
    owner, rname = gh_repo.split("/", 1) if "/" in gh_repo else ("tryggth", gh_repo)
    pages_url = pub_lock.get("pages_url") or f"https://{owner}.github.io/{rname}/"
    author_parts = m["author"].split()
    family = author_parts[-1]
    given = " ".join(author_parts[:-1])
    cdate = m.get("citation_date", "2026-11-25")

    return "\n".join(
        [
            "cff-version: 1.2.0",
            'message: "If you cite this formalization or monograph draft, please note that the working title is unlocked (title_locked = false) and also cite Volume I."',
            f'title: "{m["working_title"]}: {m["working_subtitle"]} (Working Title, title_locked = false)"',
            "type: software",
            "authors:",
            f'  - family-names: "{family}"',
            f'    given-names: "{given}"',
            f'date-released: "{cdate}"',
            'license: "CC-BY-4.0"',
            f'repository-code: "{repo_url}"',
            f'url: "{pages_url}"',
            "keywords:",
            '  - "categorical reverse mathematics"',
            '  - "lean4"',
            '  - "two-level type theory"',
            '  - "topos theory"',
            '  - "constructive mathematics"',
            "references:",
            "  - type: book",
            '    title: "Categorical Reverse Mathematics — Volume I"',
            "    authors:",
            f'      - family-names: "{family}"',
            f'        given-names: "{given}"',
            f'    doi: "{m["vol1_zenodo_doi"]}"',
            f'    notes: "Pinned companion repository at {m["vol1_root_default"]} (HEAD {m["vol1_pinned_head"]}); Volume II working title_locked = false."',
            "",
        ]
    )


def render_all_docs() -> dict[Path, str]:
    ctx = load_public_doc_context()
    return {
        REPO_ROOT / "README.md": render_readme(ctx),
        REPO_ROOT / "PROCESS.md": render_process(ctx),
        REPO_ROOT / "ROADMAP.md": render_roadmap(ctx),
        REPO_ROOT / "CITATION.cff": render_citation(ctx),
    }


def check_docs_fresh() -> tuple[bool, list[str]]:
    rendered = render_all_docs()
    stale: list[str] = []
    for path, expected in rendered.items():
        if not path.exists():
            stale.append(str(path.relative_to(REPO_ROOT)))
            continue
        actual = path.read_text(encoding="utf-8")
        if actual != expected:
            stale.append(str(path.relative_to(REPO_ROOT)))
    return len(stale) == 0, stale


def emit_docs() -> list[str]:
    rendered = render_all_docs()
    written: list[str] = []
    for path, content in rendered.items():
        path.write_text(content, encoding="utf-8")
        written.append(str(path.relative_to(REPO_ROOT)))
    return written


def main() -> int:
    parser = argparse.ArgumentParser(description="Emit or verify tracked front-door public docs.")
    parser.add_argument(
        "--check",
        action="store_true",
        help="Verify README.md, PROCESS.md, ROADMAP.md, and CITATION.cff match generated output byte-for-byte.",
    )
    args = parser.parse_args()
    if args.check:
        fresh, stale = check_docs_fresh()
        if not fresh:
            sys.stderr.write(f"EMIT_PUBLIC_DOCS_STALE files={stale}\n")
            return 1
        print("EMIT_PUBLIC_DOCS_CHECK_OK files=['README.md', 'PROCESS.md', 'ROADMAP.md', 'CITATION.cff']")
        return 0
    written = emit_docs()
    print(f"EMIT_PUBLIC_DOCS_OK files={written}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
