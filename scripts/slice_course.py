#!/usr/bin/env python3
"""Slice a standalone Royal Octavo Course Pack from the backward `curriculum` cone."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

import duckdb

from emit_tex import BUILD_TEX_DIR, DB_PATH, REPO_ROOT, SOURCEMAPS_DIR, load_context, render_node_tex, tex_escape

COURSE_PACKS: dict[str, dict[str, str]] = {
    "ch01:tab:epistemic-probe-regimes": {
        "stem": "course_pack_ch01_probe_calibration",
        "subtitle": r"Standalone Course Pack: Chapter~1 Probe Calibration",
        "chapter_title": r"Epistemic Probe Calibration (Standalone Course Pack)",
        "chapter_label": "ch:course-probe",
        "section_title": r"Curriculum Cone and Probe Thresholds",
        "extra_note": r" (excluding out-of-slice nodes such as \texttt{ch01:rem:trident-mode3-2ltt-bootstrap})",
    },
    "ch02:tab:vertical-class-spectrum": {
        "stem": "course_pack_ch02_class_set_kaleidoscope",
        "subtitle": r"Standalone Course Pack: Chapter~2 Class--Set Adjunction \& Fixed-Set Kaleidoscope",
        "chapter_title": r"Minimal Definability, Fixed-Set Kaleidoscopes, and \texorpdfstring{$\mathrm{Def} \dashv \pi_{\mathrm{Set}}$}{Def -| pi\_Set} (Standalone Course Pack)",
        "chapter_label": "ch:course-ch02-kaleidoscope",
        "section_title": r"Curriculum Cone and Vertical Class Spectrum",
        "extra_note": r" (sliced directly from Table~2.1 across \S\S 2.1--2.4)",
    },
    "ch03:tab:piset-four-quadrant-ledger": {
        "stem": "course_pack_ch03_piset_transgression",
        "subtitle": r"Standalone Course Pack: Chapter~3 Leray Transgression Along $\pi_{\mathrm{Set}}$ \& Two-Valve Dichotomy",
        "chapter_title": r"Leray Transgression Along \texorpdfstring{$\pi_{\mathrm{Set}}$}{pi\_Set} and Horizontal Conservativity Breakdown (Standalone Course Pack)",
        "chapter_label": "ch:course-ch03-transgression",
        "section_title": r"Curriculum Cone and Four-Quadrant Transgression Ledger",
        "extra_note": r" (sliced directly from Table~3.1 across \S\S 3.1--3.4)",
    },
    "ch04:tab:ast-valves-and-scheme-solvents": {
        "stem": "course_pack_ch04_smallness_and_schemes",
        "subtitle": r"Standalone Course Pack: Chapter~4 Smallness Ideals, Pointillist Continua, \& Scheme Solvents",
        "chapter_title": r"Smallness Ideals, Scheme Solvents, and Pointillist Continua (Standalone Course Pack)",
        "chapter_label": "ch:course-ch04-smallness-schemes",
        "section_title": r"Curriculum Cone and AST/Scheme Solvents Ledger",
        "extra_note": r" (sliced directly from Table~4.1 across \S\S 4.1--4.4)",
    },
}


def compute_curriculum_cone(target_id: str) -> list[str]:
    con = duckdb.connect(str(DB_PATH), read_only=True)
    exists = con.execute("SELECT COUNT(*) FROM nodes WHERE id = ?", [target_id]).fetchone()[0]
    if not exists:
        raise ValueError(f"Target node '{target_id}' not found in DuckDB.")

    cone_rows = con.execute(
        """
        WITH RECURSIVE cone(id, depth) AS (
          SELECT ?, 0
          UNION ALL
          SELECT e.src_id, c.depth + 1
          FROM cone c
          JOIN edges e ON e.dst_id = c.id AND e.fiber = 'curriculum'
          WHERE c.depth < 100
        )
        SELECT DISTINCT id FROM cone
        """,
        [target_id],
    ).fetchall()
    cone_ids = {r[0] for r in cone_rows}

    seq_rows = con.execute("SELECT id, seq_order FROM nodes").fetchall()
    seq_map = {r[0]: int(r[1]) for r in seq_rows}

    edges = con.execute(
        """
        SELECT DISTINCT src_id, dst_id
        FROM edges
        WHERE fiber IN ('curriculum', 'logical_dep', 'lean_dep')
        """
    ).fetchall()
    con.close()

    indeg: dict[str, int] = {nid: 0 for nid in cone_ids}
    adj: dict[str, list[str]] = {nid: [] for nid in cone_ids}
    for src, dst in edges:
        if src in cone_ids and dst in cone_ids and src != dst:
            adj[src].append(dst)
            indeg[dst] += 1

    queue = sorted([nid for nid, d in indeg.items() if d == 0], key=lambda x: (seq_map.get(x, 1000), x))
    ordered: list[str] = []
    while queue:
        curr = queue.pop(0)
        ordered.append(curr)
        for nxt in sorted(adj[curr]):
            indeg[nxt] -= 1
            if indeg[nxt] == 0:
                queue.append(nxt)
        queue.sort(key=lambda x: (seq_map.get(x, 1000), x))
    if len(ordered) != len(cone_ids):
        raise RuntimeError("Cycle detected while sorting curriculum cone.")
    return ordered


def emit_course_pack(target_id: str) -> Path:
    if target_id not in COURSE_PACKS:
        raise ValueError(f"Unknown course pack target '{target_id}'. Registered: {sorted(COURSE_PACKS)}")
    cfg = COURSE_PACKS[target_id]
    manifest, _, nodes_meta, symbols, _ = load_context()
    ordered_ids = compute_curriculum_cone(target_id)
    allowed_set = set(ordered_ids)
    excluded_ids = sorted(set(nodes_meta.keys()) - allowed_set)

    cone_payload = sorted(
        [[nid, nodes_meta[nid]["spec_hash"], nodes_meta[nid]["body_hash"]] for nid in ordered_ids],
        key=lambda row: row[0],
    )
    cone_hash = hashlib.sha256(
        b"VOL2_COURSE_CONE_V1\x00" + json.dumps(cone_payload, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    ).hexdigest()

    target_title = tex_escape(nodes_meta[target_id]["title"])
    target_tex = target_id.replace("_", "\\_")
    lines: list[str] = [
        r"\documentclass[10pt,twoside,openany]{book}",
        r"\input{preamble_vol2}",
        f"\\title{{Course Pack: {target_title}}}",
        f"\\author{{{manifest['author']}}}",
        r"\begin{document}",
        r"\frontmatter",
        r"\thispagestyle{empty}",
        r"\vspace*{0.12\textheight}",
        r"\begin{center}",
        r"  {\LARGE\bfseries Categorical Reverse Mathematics --- Volume~II\par}",
        r"  \vspace{0.4em}",
        f"  {{\\large\\itshape\\color{{CRMBlue}} {cfg['subtitle']}\\par}}",
        r"  \vspace{0.8em}",
        f"  {{\\normalsize Sliced from backward \\texttt{{curriculum}} cone of \\texttt{{{target_tex}}}\\par}}",
        r"\end{center}",
        r"\clearpage",
        r"\mainmatter",
        r"\setcounter{secnumdepth}{2}",
        f"\\chapter{{{cfg['chapter_title']}}}\\label{{{cfg['chapter_label']}}}",
        f"\\section{{{cfg['section_title']}}}",
        f"This standalone pack extracts the {len(ordered_ids)}-node backward \\texttt{{curriculum}} cone terminating at \\ref{{{target_id}}}{cfg['extra_note']}.",
        "",
    ]

    intervals: list[dict[str, Any]] = []
    for nid in ordered_ids:
        node = nodes_meta[nid]
        if node["kind"] == "symbol":
            continue
        rendered = render_node_tex(node, symbols, nodes_meta, allowed_ids=allowed_set)
        start_line = len(lines) + 1
        lines.append(f"% BEGIN_NODE {nid}")
        lines.extend(rendered.splitlines())
        lines.append(f"% END_NODE {nid}")
        end_line = len(lines)
        lines.append("")
        intervals.append({"node_id": nid, "start_line": start_line, "end_line": end_line})

    lines.extend(
        [
            r"\bibliographystyle{plain}",
            r"\bibliography{references_vol2}",
            r"\end{document}",
            "",
        ]
    )

    BUILD_TEX_DIR.mkdir(parents=True, exist_ok=True)
    SOURCEMAPS_DIR.mkdir(parents=True, exist_ok=True)
    stem = cfg["stem"]
    out_tex = BUILD_TEX_DIR / f"{stem}.tex"
    out_tex.write_text("\n".join(lines), encoding="utf-8")

    map_payload = json.dumps(
        {"tex_file": str(out_tex.relative_to(REPO_ROOT)), "intervals": intervals},
        indent=2,
    ) + "\n"
    (SOURCEMAPS_DIR / f"{stem}.tex.map.json").write_text(map_payload, encoding="utf-8")
    if target_id == "ch01:tab:epistemic-probe-regimes":
        (SOURCEMAPS_DIR / "course_pack.tex.map.json").write_text(map_payload, encoding="utf-8")

    manifest_path = REPO_ROOT / "build" / "course_pack_manifest.json"
    manifest_data: dict[str, Any] = {}
    if manifest_path.exists():
        try:
            manifest_data = json.loads(manifest_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            manifest_data = {}
    packs = manifest_data.setdefault("packs", {})
    pack_rec = {
        "target_id": target_id,
        "stem": stem,
        "cone_hash": cone_hash,
        "included_nodes": ordered_ids,
        "excluded_nodes": excluded_ids,
    }
    packs[target_id] = pack_rec
    if target_id == "ch01:tab:epistemic-probe-regimes" or "target_id" not in manifest_data:
        manifest_data["target_id"] = target_id
        manifest_data["cone_hash"] = cone_hash
        manifest_data["included_nodes"] = ordered_ids
        manifest_data["excluded_nodes"] = excluded_ids
    manifest_path.write_text(json.dumps(manifest_data, indent=2) + "\n", encoding="utf-8")
    return out_tex


def main() -> int:
    parser = argparse.ArgumentParser(description="Emit standalone Course Pack PDF source.")
    parser.add_argument(
        "--target",
        default="ch01:tab:epistemic-probe-regimes",
        help="Terminal curriculum target node id.",
    )
    parser.add_argument(
        "--all",
        action="store_true",
        help="Emit all registered Chapter Course Packs.",
    )
    args = parser.parse_args()
    targets = list(COURSE_PACKS.keys()) if args.all else [args.target]
    for tid in targets:
        out_tex = emit_course_pack(tid)
        print(f"SLICE_COURSE_OK target={tid} tex={out_tex.relative_to(REPO_ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
