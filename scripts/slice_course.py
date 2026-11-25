#!/usr/bin/env python3
"""Slice a standalone Royal Octavo Course Pack from the backward `curriculum` cone."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

import duckdb

from emit_tex import BUILD_TEX_DIR, DB_PATH, REPO_ROOT, SOURCEMAPS_DIR, load_context, render_node_tex


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

    queue = sorted([nid for nid, d in indeg.items() if d == 0])
    ordered: list[str] = []
    while queue:
        curr = queue.pop(0)
        ordered.append(curr)
        for nxt in sorted(adj[curr]):
            indeg[nxt] -= 1
            if indeg[nxt] == 0:
                queue.append(nxt)
        queue.sort()
    if len(ordered) != len(cone_ids):
        raise RuntimeError("Cycle detected while sorting curriculum cone.")
    return ordered


def emit_course_pack(target_id: str) -> Path:
    manifest, _, nodes_meta, symbols, _ = load_context()
    ordered_ids = compute_curriculum_cone(target_id)
    allowed_set = set(ordered_ids)
    excluded_ids = sorted(set(nodes_meta.keys()) - allowed_set)

    target_title = nodes_meta[target_id]["title"]
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
        r"  {\large\itshape\color{CRMBlue} Standalone Course Pack: Chapter~1 Probe Calibration\par}",
        r"  \vspace{0.8em}",
        f"  {{\\normalsize Sliced from backward \\texttt{{curriculum}} cone of \\texttt{{{target_tex}}}\\par}}",
        r"\end{center}",
        r"\clearpage",
        r"\mainmatter",
        r"\setcounter{secnumdepth}{2}",
        r"\chapter{Epistemic Probe Calibration (Standalone Course Pack)}\label{ch:course-probe}",
        r"\section{Curriculum Cone and Probe Thresholds}",
        f"This standalone pack extracts the {len(ordered_ids)}-node backward \\texttt{{curriculum}} cone terminating at \\ref{{{target_id}}} (excluding orthogonal out-of-slice nodes such as \\texttt{{ch01:rem:trident-mode3-2ltt-bootstrap}}).",
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

    out_tex = BUILD_TEX_DIR / "course_pack_ch01_probe_calibration.tex"
    out_tex.write_text("\n".join(lines), encoding="utf-8")
    (SOURCEMAPS_DIR / "course_pack.tex.map.json").write_text(
        json.dumps(
            {"tex_file": str(out_tex.relative_to(REPO_ROOT)), "intervals": intervals},
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    (REPO_ROOT / "build" / "course_pack_manifest.json").write_text(
        json.dumps(
            {
                "target_id": target_id,
                "included_nodes": ordered_ids,
                "excluded_nodes": excluded_ids,
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    return out_tex


def main() -> int:
    parser = argparse.ArgumentParser(description="Emit standalone Course Pack PDF source.")
    parser.add_argument(
        "--target",
        default="ch01:tab:epistemic-probe-regimes",
        help="Terminal curriculum target node id.",
    )
    args = parser.parse_args()
    out_tex = emit_course_pack(args.target)
    print(f"SLICE_COURSE_OK target={args.target} tex={out_tex.relative_to(REPO_ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
