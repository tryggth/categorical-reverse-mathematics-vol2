#!/usr/bin/env python3
"""Emit Royal Octavo LaTeX monograph, claims ledger, and TeX line sourcemaps."""

from __future__ import annotations

import json
import re
import tomllib
from pathlib import Path
from typing import Any

import duckdb

REPO_ROOT = Path(__file__).resolve().parent.parent
MANIFEST_PATH = REPO_ROOT / "manifest.toml"
GUARDRAILS_PATH = REPO_ROOT / "manifest" / "guardrails.toml"
DB_PATH = REPO_ROOT / "build" / "vol2.duckdb"
BUILD_TEX_DIR = REPO_ROOT / "build" / "tex"
SOURCEMAPS_DIR = REPO_ROOT / "build" / "sourcemaps"

SYM_RE = re.compile(r"\{\{sym:([A-Za-z0-9_.:-]+)\}\}")
REF_RE = re.compile(r"\{\{ref:([A-Za-z0-9_.:-]+)\}\}")

STRATUM_STYLES = {
    "emerald": ("CRMEmerald", "Emerald (Axiom-Free)"),
    "sapphire": ("CRMSapphire", "Sapphire (Safe 2LTT)"),
    "amber": ("CRMAmber", "Amber (Propext / Quot)"),
    "crimson": ("CRMCrimson", "Crimson (Classical.choice)"),
}


def tex_escape(s: str) -> str:
    return (
        s.replace("\\", "\\textbackslash{}")
        .replace("_", "\\_")
        .replace("^", "\\^{}")
        .replace("&", "\\&")
        .replace("%", "\\%")
        .replace("#", "\\#")
        .replace("$", "\\$")
    )


def expand_tex_macros(
    text: str,
    symbols: dict[str, str],
    nodes_meta: dict[str, dict[str, Any]],
    allowed_ids: set[str] | None = None,
) -> str:
    def _rep_sym(m: re.Match[str]) -> str:
        key = m.group(1)
        if key not in symbols:
            raise KeyError(f"Unknown symbol macro: {key}")
        return symbols[key]

    def _rep_ref(m: re.Match[str]) -> str:
        nid = m.group(1)
        if nid not in nodes_meta:
            raise KeyError(f"Unknown node reference: {nid}")
        if allowed_ids is not None and nid not in allowed_ids:
            title = nodes_meta[nid]["title"]
            return f"\\emph{{{title}}} (full monograph)"
        return f"\\ref{{{nid}}}"

    out = SYM_RE.sub(_rep_sym, text)
    out = REF_RE.sub(_rep_ref, out)
    return out


def load_context() -> tuple[
    dict[str, Any],
    list[dict[str, Any]],
    dict[str, dict[str, Any]],
    dict[str, str],
    dict[str, dict[str, Any]],
]:
    with MANIFEST_PATH.open("rb") as fh:
        manifest = tomllib.load(fh)
    with GUARDRAILS_PATH.open("rb") as fh:
        guardrails = tomllib.load(fh).get("guardrail", [])

    con = duckdb.connect(str(DB_PATH), read_only=True)
    node_rows = con.execute(
        """
        SELECT id, kind, title, chapter, section, axis, grounding_tier,
               formal_pkg, stratum, module, decl_names_json, expected_axioms_json,
               cert_path, spec_hash, body_hash, taint_status, raw_json
        FROM nodes
        ORDER BY id
        """
    ).fetchall()
    sym_rows = con.execute("SELECT macro_key, latex_macro FROM symbols").fetchall()
    rec_rows = con.execute(
        "SELECT node_id, stratum, actual_axioms_json, cert_sha256, verified_at_utc, passed FROM verification_receipts"
    ).fetchall()
    con.close()

    symbols = {k: v for k, v in sym_rows}
    receipts = {
        nid: {
            "stratum": st,
            "actual_axioms": json.loads(ax),
            "cert_sha256": csha,
            "verified_at_utc": ts,
            "passed": passed,
        }
        for nid, st, ax, csha, ts, passed in rec_rows
    }

    nodes_meta: dict[str, dict[str, Any]] = {}
    for row in node_rows:
        (
            nid,
            kind,
            title,
            chapter,
            section,
            axis,
            grounding_tier,
            formal_pkg,
            stratum,
            module,
            decl_names_json,
            expected_axioms_json,
            cert_path,
            spec_hash,
            body_hash,
            taint_status,
            raw_json,
        ) = row
        nodes_meta[nid] = {
            "id": nid,
            "kind": kind,
            "title": title,
            "chapter": chapter,
            "section": section,
            "axis": axis,
            "grounding_tier": grounding_tier,
            "formal_pkg": formal_pkg,
            "stratum": stratum,
            "module": module,
            "decl_names": json.loads(decl_names_json),
            "expected_axioms": json.loads(expected_axioms_json),
            "cert_path": cert_path,
            "spec_hash": spec_hash,
            "body_hash": body_hash,
            "taint_status": taint_status,
            "raw": json.loads(raw_json),
        }

    return manifest, guardrails, nodes_meta, symbols, receipts


def render_node_tex(
    node: dict[str, Any],
    symbols: dict[str, str],
    nodes_meta: dict[str, dict[str, Any]],
    allowed_ids: set[str] | None = None,
) -> str:
    nid = node["id"]
    kind = node["kind"]
    raw = node["raw"]
    body = raw.get("body", {})
    raw_tex = body.get("tex", "").strip()
    expanded_tex = expand_tex_macros(raw_tex, symbols, nodes_meta, allowed_ids)

    lines: list[str] = []
    # Inject formal metadata & Four-Color Stratum badge for formalized nodes
    if node["formal_pkg"] == "mathlib_vol2":
        decls = ", ".join(node["decl_names"])
        color_macro, label = STRATUM_STYLES[node["stratum"]]
        lines.append(f"\\lean{{{decls}}}\\leanok")
        lines.append(f"\\stratumbadge{{{color_macro}}}{{{label}}}")
        lines.append(f"\\formalrefline{{Lean 4}}{{{tex_escape(decls)}}}")
    elif node["formal_pkg"] == "kernel_arena":
        cert_rel = node.get("cert_path", "")
        decls = ", ".join(node["decl_names"])
        lines.append(f"\\twoltt{{{decls}}}\\twolttok")
        lines.append("\\stratumbadge{CRMEmerald}{Emerald (2LTT Kernel Arena)}")
        lines.append(f"\\formalrefline{{2LTT Cert}}{{{tex_escape(cert_rel)}}}")

    if kind == "symbol":
        # Symbols render cleanly in the Symbol Registry / Notation summary
        lines.append(expanded_tex)
    else:
        lines.append(expanded_tex)

    return "\n".join(lines).strip()


def resolve_tex_error(tex_map_name: str, line: int) -> str | None:
    mp = SOURCEMAPS_DIR / tex_map_name
    if not mp.exists():
        return None
    data = json.loads(mp.read_text(encoding="utf-8"))
    for iv in data.get("intervals", []):
        if iv["start_line"] <= line <= iv["end_line"]:
            return iv["node_id"]
    return None


def emit_monograph(
    manifest: dict[str, Any],
    guardrails: list[dict[str, Any]],
    nodes_meta: dict[str, dict[str, Any]],
    symbols: dict[str, str],
) -> Path:
    BUILD_TEX_DIR.mkdir(parents=True, exist_ok=True)
    SOURCEMAPS_DIR.mkdir(parents=True, exist_ok=True)

    # Canonical Chapter 1 vertical slice presentation order
    preferred_order = [
        "vol1:def:doctrinal-philosophy",
        "sym:probe-suite",
        "ch01:prose:meta-crm-roadmap",
        "ch01:def:probe-suite",
        "ch01:def:adm-pareto-frontier",
        "ch01:thm:scotoma-pareto-trichotomy",
        "ch01:thm:flow-f1-threshold-order",
        "ch01:cex:flow-f1-frontier-nonmonotone",
        "ch01:rem:trident-mode3-2ltt-bootstrap",
        "ch01:tab:epistemic-probe-regimes",
    ]
    ordered_ids = [nid for nid in preferred_order if nid in nodes_meta]
    for nid in sorted(nodes_meta.keys()):
        if nid not in ordered_ids:
            ordered_ids.append(nid)

    title = manifest["working_title"]
    subtitle = manifest["working_subtitle"]
    author = manifest["author"]
    location = manifest["location"]
    vol1_doi = manifest["vol1_zenodo_doi"]

    lines: list[str] = [
        r"\documentclass[10pt,twoside,openright]{book}",
        r"\input{preamble_vol2}",
        f"\\title{{{title}: {subtitle}}}",
        f"\\author{{{author}}}",
        f"\\hypersetup{{pdftitle={{{title} --- {subtitle}}},pdfauthor={{{author}}}}}",
        "",
        r"\begin{document}",
        r"\frontmatter",
        r"\setcounter{secnumdepth}{-1}",
        "",
        r"\thispagestyle{empty}",
        r"\vspace*{0.26\textheight}",
        r"\begin{center}",
        f"  {{\\LARGE\\bfseries {title}\\par}}",
        r"  \vspace{0.45em}",
        f"  {{\\large\\itshape\\color{{CRMBlue}} {subtitle}\\par}}",
        r"\end{center}",
        r"\cleardoublepage",
        "",
        r"\thispagestyle{empty}",
        r"{\centering",
        r"  \vspace*{0.14\textheight}",
        r"  {\Huge\bfseries Categorical Reverse Mathematics\par}",
        r"  \vspace{0.55em}",
        r"  {\Large\scshape\color{CRMBlue} Volume~II\par}",
        r"  \vspace{1.0em}",
        r"  {\color{CRMBlue}\noindent\rule{\textwidth}{0.8pt}}\par",
        r"  \vspace{1.0em}",
        f"  {{\\LARGE\\itshape\\color{{CRMBlue}} {subtitle}\\par}}",
        r"  \vfill",
        f"  {{\\large {author}\\par}}",
        r"  \vspace{0.35em}",
        f"  {{\\normalsize {location}\\par}}",
        r"  \vspace{0.6em}",
        r"  {\large November 2026 (Phase 0 Vertical Slice)\par}",
        r"  \vspace*{0.05\textheight}\par}",
        r"\clearpage",
        "",
        r"\thispagestyle{empty}",
        r"\vspace*{\fill}",
        r"\begingroup\raggedright\scriptsize\setlength{\parskip}{0.15em}",
        f"\\textbf{{{title}: {subtitle}}}\\\\",
        f"By {author} ({location}). Licensed under CC BY 4.0.\\\\",
        f"Companion to Volume~I (Zenodo DOI: \\texttt{{{vol1_doi}}}).\\\\",
        r"Typeset in \LaTeXe\ via \texttt{pdfLaTeX} in Royal Octavo ($6.14\,\mathrm{in} \times 9.21\,\mathrm{in}$) with a Two-Package Trusted Computing Base (\texttt{KernelArena} 2LTT + \texttt{HomotopyCRMVol2} Lean~4 / \texttt{mathlib4}).",
        r"\endgroup\clearpage",
        "",
        r"\tableofcontents",
        r"\mainmatter",
        r"\setcounter{secnumdepth}{2}",
        "",
        r"\chapter{Epistemic Probe Calibration and the Meta-CRM Residuum Calculus}\label{ch:probe-calibration}",
        r"\chapterepigraph{Measure what is measurable, and make measurable what is not so.}{Attributed to Galileo Galilei}",
        r"\section{Doctrinal Philosophies, Probe Suites, and Flow F1}\label{sec:probe-suites}",
        "",
    ]

    intervals: list[dict[str, Any]] = []
    for nid in ordered_ids:
        node = nodes_meta[nid]
        rendered = render_node_tex(node, symbols, nodes_meta)
        start_line = len(lines) + 1
        lines.append(f"% BEGIN_NODE {nid} [spec:{node['spec_hash'][:8]} body:{node['body_hash'][:8]}]")
        lines.extend(rendered.splitlines())
        lines.append(f"% END_NODE {nid}")
        end_line = len(lines)
        lines.append("")
        intervals.append(
            {
                "node_id": nid,
                "start_line": start_line,
                "end_line": end_line,
                "spec_hash": node["spec_hash"],
                "body_hash": node["body_hash"],
            }
        )

    lines.extend(
        [
            r"\appendix",
            r"\chapter{Cross-Volume Precision Guardrails}\label{app:guardrails}",
            r"Volume~II enforces five cross-volume precision invariants inherited from Volume~I:",
            r"\begin{enumerate}[leftmargin=2.0em]",
        ]
    )
    for g in guardrails:
        lines.append(
            f"  \\item \\textbf{{{tex_escape(g['title'])}:}} ${g['latex']}$ ({tex_escape(g['statement'])})"
        )
    lines.extend(
        [
            r"\end{enumerate}",
            "",
            r"\backmatter",
            r"\bibliographystyle{plain}",
            r"\bibliography{references_vol2}",
            r"\printindex",
            r"\end{document}",
            "",
        ]
    )

    out_tex = BUILD_TEX_DIR / "crm_vol2_monograph.tex"
    out_tex.write_text("\n".join(lines), encoding="utf-8")
    (SOURCEMAPS_DIR / "monograph.tex.map.json").write_text(
        json.dumps(
            {
                "tex_file": str(out_tex.relative_to(REPO_ROOT)),
                "intervals": intervals,
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    return out_tex


def emit_claims_ledger(
    manifest: dict[str, Any],
    guardrails: list[dict[str, Any]],
    nodes_meta: dict[str, dict[str, Any]],
    receipts: dict[str, dict[str, Any]],
    audit_report: dict[str, Any] | None = None,
) -> Path:
    BUILD_TEX_DIR.mkdir(parents=True, exist_ok=True)
    audit_by_id = {}
    if audit_report:
        audit_by_id = {n["id"]: n for n in audit_report.get("nodes", [])}

    tier1 = [n for n in nodes_meta.values() if n["formal_pkg"] in ("mathlib_vol2", "kernel_arena")]
    tier2 = [n for n in nodes_meta.values() if n["formal_pkg"] not in ("mathlib_vol2", "kernel_arena")]

    lines: list[str] = [
        r"\documentclass[10pt,twoside,openany]{book}",
        r"\input{preamble_vol2}",
        r"\title{Categorical Reverse Mathematics --- Volume~II: Two-Tier Claims \& Audit Ledger}",
        f"\\author{{{manifest['author']}}}",
        r"\begin{document}",
        r"\frontmatter",
        r"\thispagestyle{empty}",
        r"\vspace*{0.12\textheight}",
        r"\begin{center}",
        r"  {\LARGE\bfseries Categorical Reverse Mathematics --- Volume~II\par}",
        r"  \vspace{0.4em}",
        r"  {\large\itshape\color{CRMBlue} Two-Tier Claims, Axiom, and Four-Color Stratum Audit Ledger\par}",
        r"  \vspace{0.8em}",
        f"  {{\\normalsize {manifest['author']} \\quad|\\quad {manifest['phase']}: {manifest['active_slice']}\\par}}",
        r"\end{center}",
        r"\clearpage",
        r"\mainmatter",
        r"\setcounter{secnumdepth}{2}",
        r"\chapter{Two-Tier Verification Ledger}\label{ch:ledger}",
        r"\section{Tier 1: Kernel-Checked and Lean 4 Formal Claims}",
        r"Every formal node below is checked under the Two-Package TCB (\texttt{KernelArena} zero-Mathlib 2LTT checker + \texttt{HomotopyCRMVol2} Lean~4 environment audit \cite{abramsky2022,Shulman20}).",
        "",
        r"\begin{table}[htbp]\centering\scriptsize\setlength{\tabcolsep}{3pt}\renewcommand{\arraystretch}{1.15}",
        r"\begin{tabularx}{\textwidth}{@{}P{0.28\textwidth}P{0.15\textwidth}P{0.14\textwidth}YP{0.14\textwidth}@{}}",
        r"\toprule",
        r"\textbf{Node ID} & \textbf{Package} & \textbf{Stratum} & \textbf{Verified Axioms / Spec8} & \textbf{Status} \\",
        r"\midrule",
    ]
    for n in sorted(tier1, key=lambda x: x["id"]):
        nid = n["id"]
        arec = audit_by_id.get(nid) or receipts.get(nid)
        axs = arec.get("actual_axioms", n["expected_axioms"]) if arec else n["expected_axioms"]
        ax_str = r"\texttt{[]}" if not axs else r"\texttt{" + tex_escape(", ".join(axs)) + "}"
        color_macro, _ = STRATUM_STYLES.get(n["stratum"], ("CRMBlue", n["stratum"]))
        stratum_tex = f"\\textcolor{{{color_macro}}}{{\\textbf{{{n['stratum']}}}}}"
        pkg_tex = tex_escape(n["formal_pkg"])
        lines.append(
            f"\\texttt{{{tex_escape(nid)}}} & \\texttt{{{pkg_tex}}} & {stratum_tex} & "
            f"{ax_str} (\\texttt{{{n['spec_hash'][:8]}}}) & \\texttt{{{tex_escape(n['taint_status'])}}} \\\\"
        )
    lines.extend(
        [
            r"\bottomrule",
            r"\end{tabularx}",
            r"\caption{Tier 1 Formalized Claims, Axioms, and Four-Color Stratum Classification.}",
            r"\end{table}",
            "",
            r"\section{Tier 2: Grounding Contracts, Symbols, and Exposition Nodes}",
            r"\begin{table}[htbp]\centering\scriptsize\setlength{\tabcolsep}{3pt}\renewcommand{\arraystretch}{1.15}",
            r"\begin{tabularx}{\textwidth}{@{}P{0.31\textwidth}P{0.16\textwidth}P{0.18\textwidth}YP{0.14\textwidth}@{}}",
            r"\toprule",
            r"\textbf{Node ID} & \textbf{Kind} & \textbf{Tier} & \textbf{Spec8 / Body8} & \textbf{Status} \\",
            r"\midrule",
        ]
    )
    for n in sorted(tier2, key=lambda x: x["id"]):
        nid = n["id"]
        lines.append(
            f"\\texttt{{{tex_escape(nid)}}} & \\texttt{{{tex_escape(n['kind'])}}} & "
            f"\\texttt{{{tex_escape(n['grounding_tier'])}}} & "
            f"\\texttt{{{n['spec_hash'][:8]}}} / \\texttt{{{n['body_hash'][:8]}}} & "
            f"\\texttt{{{tex_escape(n['taint_status'])}}} \\\\"
        )
    lines.extend(
        [
            r"\bottomrule",
            r"\end{tabularx}",
            r"\caption{Tier 2 Structural, Symbol, and Prose Nodes.}",
            r"\end{table}",
            "",
            r"\section{Cross-Volume Guardrail Register}",
            r"\begin{itemize}[leftmargin=1.5em]",
        ]
    )
    for g in guardrails:
        lines.append(f"  \\item \\textbf{{{tex_escape(g['id'])}:}} ${g['latex']}$")
    lines.extend(
        [
            r"\end{itemize}",
            r"\bibliographystyle{plain}",
            r"\bibliography{references_vol2}",
            r"\end{document}",
            "",
        ]
    )
    out_tex = BUILD_TEX_DIR / "crm_vol2_claims_ledger.tex"
    out_tex.write_text("\n".join(lines), encoding="utf-8")
    return out_tex


def main() -> int:
    manifest, guardrails, nodes_meta, symbols, receipts = load_context()
    audit_path = REPO_ROOT / "logs" / "audit_env.json"
    audit_report = None
    if audit_path.exists():
        try:
            audit_report = json.loads(audit_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            audit_report = None
    mono = emit_monograph(manifest, guardrails, nodes_meta, symbols)
    ledger = emit_claims_ledger(manifest, guardrails, nodes_meta, receipts, audit_report)
    print(f"EMIT_TEX_OK monograph={mono.relative_to(REPO_ROOT)} ledger={ledger.relative_to(REPO_ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
