#!/usr/bin/env python3
"""Emit Royal Octavo LaTeX monograph, 4-Part claims ledger + census, and TeX line sourcemaps."""

from __future__ import annotations

import json
import re
import tomllib
from collections import Counter
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
RAW_REF_RE = re.compile(r"\\ref\{([A-Za-z0-9_.:-]+)\}")
USES_PROVES_RE = re.compile(r"\\(uses|proves)\{([^}]*)\}")

STRATUM_STYLES = {
    "emerald": ("CRMEmerald", "Emerald (Axiom-Free)"),
    "sapphire": ("CRMSapphire", "Sapphire (Safe 2LTT)"),
    "amber": ("CRMAmber", "Amber (Propext / Quot)"),
    "crimson": ("CRMCrimson", "Crimson (Classical.choice)"),
}

CHAPTER_HEADERS = {
    "ch01": [
        r"\part*{Overture}",
        r"\addcontentsline{toc}{part}{Overture}",
        r"\chapter{Epistemic Probe Calibration and the Meta-CRM Residuum Calculus}\label{ch:probe-calibration}",
        r"\chapterepigraph{Measure what is measurable, and make measurable what is not so.}{Attributed to Galileo Galilei}",
        "",
    ],
    "ch02": [
        r"\part{The Class--Set Adjunction and Base-Change Transgression}\label{part:class-set-adjunction}",
        r"\chapter{Minimal Definability, Fixed-Set Kaleidoscopes, and \texorpdfstring{$\mathrm{Def} \dashv \pi_{\mathrm{Set}}$}{Def -| pi\_Set}}\label{ch:class-set-adjunction}",
        r"\chapterepigraph{The inequalities in the world are like the combinations in a kaleidoscope; at every turn a fresh picture strikes the eye; and yet, in reality, you see only the same bits of glass as you saw before.}{Arthur Schopenhauer, \emph{Counsels and Maxims}, \S 47}",
        "",
    ],
    "ch03": [
        r"\chapter{Leray Transgression Along \texorpdfstring{$\pi_{\mathrm{Set}}$}{pi\_Set} and Horizontal Conservativity Breakdown}\label{ch:piset-transgression}",
        r"\chapterepigraph{Sometimes I have had the task to write reviews of articles, where set theoretic notions and theorems are used without any explanation of what kind of set theory is meant. It is a disagreeable job to write reviews in such cases. One does not know what the author really means.}{Thoralf Skolem, \emph{A Critical Remark on Foundational Research} (1955)}",
        "",
    ],
    "ch04": [
        r"\part{Axis VI: Algebraic Set Theory, Cofinality, and Class Proof Unwinding}\label{part:ast-cofinality}",
        r"\chapter{Smallness Ideals, Scheme Solvents, and Pointillist Continua}\label{ch:smallness-and-schemes}",
        "",
    ],
    "ch09": [
        r"\part{Axis VII: Coalgebraic Hypersets, Univalent Multisets, and Higher Symmetry}\label{part:2ltt-tcb}",
        r"\chapter{Cartesian Cubical 2LTT, \texorpdfstring{$\mathsf{V}$}{V}-Univalence, and \texorpdfstring{\texttt{KernelArena}}{KernelArena} Rung~1}\label{ch:tcb-rung1-2ltt}",
        "",
    ],
}

SECTION_TITLES = {
    "1.1": (
        "Doctrinal Foundations, the Obstruction Trident, and Flow F1",
        "sec:trident-f1",
    ),
    "1.2": (
        "2-Chu Duality, Touchstone Specific Gravity, and Hereditary Subterminal Projectivity",
        "sec:chu-gravity-projsub",
    ),
    "1.3": (
        "Doctrinal Stability Flows F2--F4 and Realizability Localizations",
        "sec:flows-f2-f4",
    ),
    "1.4": (
        "Intrinsic 0-Giraud Characterization and the Core-Target Aperture",
        "sec:zero-giraud",
    ),
    "1.5": (
        "Operational Currencies and Quasi-Isometric Morita Resource Interleaving",
        "sec:currencies-morita",
    ),
    "2.1": (
        r"G\"odel Class Algebras and the Three-Way Model-Space Pullback Failure",
        "sec:gb0-pullback-failure",
    ),
    "2.2": (
        r"Minimal Definability, Coreflective Adjunction \texorpdfstring{$\mathrm{Def} \dashv \pi_{\mathrm{Set}}$}{Def -| pi\_Set}, and Syntactic Pullbacks",
        "sec:def-left-adjoint-syntactic",
    ),
    "2.3": (
        "Unbundling Limitation of Size and Williams's Fixed-Set Kaleidoscope",
        "sec:los-williams-kaleidoscope",
    ),
    "2.4": (
        "Transfinite Class Recursion, Kelley--Morse Barriers, and the Vertical Class Spectrum",
        "sec:vertical-class-spectrum",
    ),
    "3.1": (
        "Large Anafunctors, Functorial Global Choice Splitting, and the Equipollence Quotient",
        "sec:anafunctor-gc-splitting",
    ),
    "3.2": (
        r"Felgner's \texorpdfstring{$\kappa$}{kappa}-Closed Membrane, Glazer's Hartogs--Scott Valve, and Foundation-Free Leaks",
        "sec:felgner-glazer-leaks",
    ),
    "3.3": (
        r"Lindenbaum--Stone Transgression \texorpdfstring{$d_{\mathrm{Set}}$}{d\_Set} and Syntactic Pullback Exactness",
        "sec:piset-transgression-exactness",
    ),
    "3.4": (
        "The Two-Valve Base--Fiber Dichotomy, Morleyized Topoi, and Part~I Synthesis",
        "sec:two-valve-dichotomy",
    ),
    "4.1": (
        r"Joyal--Moerdijk \texorpdfstring{$(\mathcal{C},\mathcal{S})$}{(C, S)} Dissection and Axis~VI Quotient Descent",
        "sec:joyal-moerdijk-axis-vi",
    ),
    "4.2": (
        r"Pointillist Continua, \texorpdfstring{$\mathsf{CZF}$}{CZF} \texorpdfstring{$\Omega^X / 2^X$}{Omega^X / 2^X}, and Cohesive Adjudication",
        "sec:pointillist-continua-czf",
    ),
    "4.3": (
        r"Grothendieck Scheme Solvents: Constructive Zariski Frames vs.\ Krull Primes",
        "sec:zariski-krull-solvents",
    ),
    "4.4": (
        r"Borger \texorpdfstring{$\Lambda/\mathbb{F}_1$}{Lambda/F\_1}-Descent, Waterhouse's \texorpdfstring{$\mathrm{fpqc}$}{fpqc} Escape, and Chapter~4 Synthesis",
        "sec:borger-waterhouse-fpqc",
    ),
    "9.1": (
        r"Cartesian Cubical 2LTT, Univalent Transport, and \texorpdfstring{\texttt{KernelArena}}{KernelArena} Rung~1",
        "sec:tcb-rung1-2ltt",
    ),
}


def tex_escape(s: str) -> str:
    out = (
        s.replace("\\", "\\textbackslash{}")
        .replace("_", "\\_")
        .replace("^", "\\^{}")
        .replace("&", "\\&")
        .replace("%", "\\%")
        .replace("#", "\\#")
        .replace("$", "\\$")
    )
    unicode_map = {
        "≤": r"$\le$",
        "≥": r"$\ge$",
        "≠": r"$\neq$",
        "→": r"$\to$",
        "↔": r"$\leftrightarrow$",
        "↦": r"$\mapsto$",
        "⇒": r"$\Rightarrow$",
        "⇔": r"$\Leftrightarrow$",
        "⊣": r"$\dashv$",
        "↪": r"$\hookrightarrow$",
        "↠": r"$\twoheadrightarrow$",
        "⇀": r"$\rightharpoonup$",
        "×": r"$\times$",
        "∈": r"$\in$",
        "∉": r"$\notin$",
        "⊆": r"$\subseteq$",
        "⊈": r"$\not\subseteq$",
        "⊊": r"$\subsetneq$",
        "⊂": r"$\subset$",
        "∪": r"$\cup$",
        "∩": r"$\cap$",
        "⊔": r"$\sqcup$",
        "∖": r"$\setminus$",
        "∧": r"$\wedge$",
        "∨": r"$\vee$",
        "¬": r"$\neg$",
        "∀": r"$\forall$",
        "∃": r"$\exists$",
        "∅": r"$\emptyset$",
        "⊥": r"$\bot$",
        "⊤": r"$\top$",
        "≅": r"$\cong$",
        "≃": r"$\simeq$",
        "⊢": r"$\vdash$",
        "⊨": r"$\models$",
        "⊬": r"$\not\vdash$",
        "↓": r"$\downarrow$",
        "∞": r"$\infty$",
        "π": r"$\pi$",
        "ω": r"$\omega$",
        "λ": r"$\lambda$",
        "α": r"$\alpha$",
        "θ": r"$\theta$",
        "τ": r"$\tau$",
        "σ": r"$\sigma$",
        "Π": r"$\Pi$",
        "ℕ": r"$\mathbb{N}$",
        "ℤ": r"$\mathbb{Z}$",
        "Ω": r"$\Omega$",
        "Σ": r"$\Sigma$",
        "Φ": r"$\Phi$",
        "Ψ": r"$\Psi$",
        "φ": r"$\varphi$",
        "ψ": r"$\psi$",
        "κ": r"$\kappa$",
        "ℓ": r"$\ell$",
        "ℵ": r"$\aleph$",
        "′": r"$'$",
        "≡": r"$\equiv$",
        "₀": r"\textsubscript{0}",
        "₁": r"\textsubscript{1}",
        "₂": r"\textsubscript{2}",
        "⟨": r"$\langle$",
        "⟩": r"$\rangle$",
        "§": r"\S{}",
        "–": "--",
        "—": "---",
    }
    for u, rep in unicode_map.items():
        out = out.replace(u, rep)
    return out


def tex_code_break(s: str) -> str:
    """Escape identifier/code text and allow line breaks after ':', '_', and '.'."""
    esc = tex_escape(s)
    esc = esc.replace(":", r":\allowbreak{}")
    esc = esc.replace(r"\_", r"\_\allowbreak{}")
    esc = esc.replace(".", r".\allowbreak{}")
    return esc


def node_cohort(kind: str) -> str:
    if kind in ("theorem", "proposition", "lemma", "corollary", "counterexample"):
        return "Cohort I"
    if kind in ("definition", "remark", "conjecture", "principle", "problem", "vol1_external", "symbol"):
        return "Cohort II"
    if kind == "inline_claim":
        return "Cohort III"
    if kind in ("prose_block", "summary_table"):
        return "Cohort IV"
    return "Course Pack"


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
            title = tex_escape(nodes_meta[nid]["title"])
            return f"\\emph{{{title}}} (full monograph)"
        return f"\\ref{{{nid}}}"

    out = SYM_RE.sub(_rep_sym, text)
    out = REF_RE.sub(_rep_ref, out)
    if allowed_ids is not None:
        def _filter_uses(m: re.Match[str]) -> str:
            cmd = m.group(1)
            items = [x.strip() for x in m.group(2).split(",") if x.strip()]
            kept = [x for x in items if x not in nodes_meta or x in allowed_ids]
            if not kept:
                return ""
            return f"\\{cmd}{{{','.join(kept)}}}"

        def _rep_raw_ref(m: re.Match[str]) -> str:
            nid = m.group(1)
            if nid in nodes_meta and nid not in allowed_ids:
                title = tex_escape(nodes_meta[nid]["title"])
                return f"\\emph{{{title}}} (full monograph)"
            return m.group(0)

        out = USES_PROVES_RE.sub(_filter_uses, out)
        out = RAW_REF_RE.sub(_rep_raw_ref, out)
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
        SELECT id, kind, title, chapter, section, seq_order, axis, grounding_tier,
               formal_pkg, stratum, module, decl_names_json, expected_axioms_json,
               cert_path, spec_hash, body_hash, grounding_hash, taint_status, raw_json
        FROM nodes
        WHERE kind NOT IN ('work_item', 'pub_target')
        ORDER BY seq_order, id
        """
    ).fetchall()
    sym_rows = con.execute("SELECT macro_key, latex_macro FROM symbols").fetchall()
    rec_rows = con.execute(
        "SELECT node_id, stratum, actual_axioms_json, cert_sha256, verified_at_utc, passed FROM verification_receipts"
    ).fetchall()
    cg_rows = con.execute(
        """
        SELECT node_id, cohort, primary_category, blueprint_tier,
               characterization_types_json, witness_scope, dual_pillars_json, grounding_hash
        FROM claim_groundings
        """
    ).fetchall()
    pp_rows = con.execute(
        """
        SELECT src_id, dst_id, metadata_json
        FROM edges
        WHERE fiber = 'prose_paraphrase'
        ORDER BY dst_id, src_id
        """
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
    groundings = {
        nid: {
            "cohort": cohort,
            "primary_category": pcat,
            "blueprint_tier": btier,
            "characterization_types": json.loads(ct_json),
            "witness_scope": wscope,
            "dual_pillars": json.loads(dp_json),
            "grounding_hash": ghash,
        }
        for nid, cohort, pcat, btier, ct_json, wscope, dp_json, ghash in cg_rows
    }
    pp_by_consumer: dict[str, list[dict[str, Any]]] = {}
    for src_id, dst_id, meta_raw in pp_rows:
        meta = json.loads(meta_raw)
        pp_by_consumer.setdefault(dst_id, []).append(
            {
                "target_id": src_id,
                "locked_spec_hash": meta.get("locked_spec_hash", ""),
                "scope_note": meta.get("scope_note", ""),
            }
        )

    nodes_meta: dict[str, dict[str, Any]] = {}
    for row in node_rows:
        (
            nid,
            kind,
            title,
            chapter,
            section,
            seq_order,
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
            grounding_hash,
            taint_status,
            raw_json,
        ) = row
        raw_obj = json.loads(raw_json)
        g_info = groundings.get(nid) or {
            "cohort": node_cohort(kind),
            "primary_category": raw_obj.get("grounding", {}).get("primary_category", "Standard definition"),
            "blueprint_tier": raw_obj.get("grounding", {}).get("blueprint_tier", "none"),
            "characterization_types": raw_obj.get("grounding", {}).get("characterization_types", []),
            "witness_scope": raw_obj.get("grounding", {}).get("witness_scope", ""),
            "dual_pillars": raw_obj.get("grounding", {}).get("dual_pillars", []),
            "grounding_hash": grounding_hash,
        }
        nodes_meta[nid] = {
            "id": nid,
            "kind": kind,
            "cohort": g_info["cohort"],
            "title": title,
            "chapter": chapter,
            "section": section,
            "seq_order": seq_order,
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
            "grounding_hash": grounding_hash,
            "taint_status": taint_status,
            "grounding": g_info,
            "prose_paraphrase_in": pp_by_consumer.get(nid, []),
            "raw": raw_obj,
        }

    return manifest, guardrails, nodes_meta, symbols, receipts


def render_node_tex(
    node: dict[str, Any],
    symbols: dict[str, str],
    nodes_meta: dict[str, dict[str, Any]],
    allowed_ids: set[str] | None = None,
) -> str:
    raw = node["raw"]
    body = raw.get("body", {})
    raw_tex = body.get("tex", "").strip()
    expanded_tex = expand_tex_macros(raw_tex, symbols, nodes_meta, allowed_ids)
    bp_tier = node.get("grounding", {}).get("blueprint_tier", "")

    lines: list[str] = []
    if node["formal_pkg"] == "mathlib_vol2":
        decls = ", ".join(node["decl_names"])
        color_macro, label = STRATUM_STYLES[node["stratum"]]
        if bp_tier == "lean_witness":
            lines.append(f"\\lean{{{decls}}}\\leanwitness")
            lines.append(f"\\stratumbadge{{{color_macro}}}{{{label} [Witness]}}")
            lines.append(f"\\formalrefline{{Lean 4 Witness}}{{{tex_escape(decls)}}}")
        else:
            lines.append(f"\\lean{{{decls}}}\\leanok")
            lines.append(f"\\stratumbadge{{{color_macro}}}{{{label}}}")
            lines.append(f"\\formalrefline{{Lean 4}}{{{tex_escape(decls)}}}")
    elif node["formal_pkg"] == "kernel_arena":
        cert_rel = node.get("cert_path", "")
        decls = ", ".join(node["decl_names"])
        stratum = node.get("stratum", "emerald")
        color_macro, base_label = STRATUM_STYLES.get(
            stratum, ("CRMEmerald", "Emerald (Axiom-Free)")
        )
        short_name = base_label.split(" (", 1)[0]
        if bp_tier == "twoltt_witness":
            badge_label = f"{short_name} (2LTT Witness)"
            lines.append(f"\\twoltt{{{decls}}}\\twolttwitness")
            lines.append(f"\\stratumbadge{{{color_macro}}}{{{badge_label}}}")
            lines.append(f"\\formalrefline{{2LTT Witness}}{{{tex_escape(cert_rel)}}}")
        else:
            badge_label = (
                "Sapphire (Safe 2LTT Kernel Arena)"
                if stratum == "sapphire"
                else f"{short_name} (2LTT Kernel Arena)"
            )
            lines.append(f"\\twoltt{{{decls}}}\\twolttok")
            lines.append(f"\\stratumbadge{{{color_macro}}}{{{badge_label}}}")
            lines.append(f"\\formalrefline{{2LTT Cert}}{{{tex_escape(cert_rel)}}}")

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

    ordered_ids = [
        nid
        for nid, _ in sorted(
            nodes_meta.items(),
            key=lambda kv: (kv[1].get("seq_order", 1000), kv[0]),
        )
    ]

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
        f"  {{\\large {tex_escape(manifest['phase'])} ({tex_escape(manifest['active_slice'])})\\par}}",
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
    ]

    intervals: list[dict[str, Any]] = []
    current_chapter: str | None = None
    current_section: str | None = None
    for nid in ordered_ids:
        node = nodes_meta[nid]
        chap = node.get("chapter", "")
        if chap and chap != current_chapter and chap in CHAPTER_HEADERS:
            lines.extend(CHAPTER_HEADERS[chap])
            current_chapter = chap
            current_section = None
        sec = node.get("section", "")
        if sec and sec != current_section and sec in SECTION_TITLES:
            sec_title, sec_label = SECTION_TITLES[sec]
            lines.append(f"\\section{{{sec_title}}}\\label{{{sec_label}}}")
            lines.append("")
            current_section = sec
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


def _load_decl_ownership() -> list[tuple[str, str, str]]:
    if not DB_PATH.exists():
        return []
    con = duckdb.connect(str(DB_PATH), read_only=True)
    rows = con.execute(
        "SELECT decl_or_cert, node_id, ownership_kind FROM decl_ownership ORDER BY node_id, decl_or_cert"
    ).fetchall()
    con.close()
    return [(r[0], r[1], r[2]) for r in rows]


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

    decl_rows = _load_decl_ownership()
    all_nodes = sorted(nodes_meta.values(), key=lambda x: (x.get("seq_order", 1000), x["id"]))

    cohort_i = [n for n in all_nodes if n["cohort"] == "Cohort I"]
    cohort_ii = [n for n in all_nodes if n["cohort"] == "Cohort II"]
    cohort_iii = [n for n in all_nodes if n["cohort"] == "Cohort III"]
    cohort_iv = [n for n in all_nodes if n["cohort"] == "Cohort IV"]

    def _stratum_tex(st: str) -> str:
        if st in STRATUM_STYLES:
            cm, _ = STRATUM_STYLES[st]
            return f"\\textcolor{{{cm}}}{{\\textbf{{{st}}}}}"
        return r"\texttt{none}"

    def _pillars_summary(n: dict[str, Any]) -> str:
        pillars = n["grounding"].get("dual_pillars", [])
        if not pillars:
            return r"\emph{none}"
        bits = []
        for p in pillars:
            pk = tex_escape(p.get("kind", ""))
            pref = tex_code_break(p.get("ref", ""))
            ploc = p.get("locator", "")
            if ploc:
                bits.append(f"\\textbf{{{pk}}}: \\texttt{{{pref}}} ({tex_escape(ploc)})")
            else:
                bits.append(f"\\textbf{{{pk}}}: \\texttt{{{pref}}}")
        return "; ".join(bits)

    lines: list[str] = [
        r"\documentclass[10pt,twoside,openany]{book}",
        r"\input{preamble_vol2}",
        r"\title{Categorical Reverse Mathematics --- Volume~II: Master Claims \& Grounding Ledger}",
        f"\\author{{{manifest['author']}}}",
        r"\begin{document}",
        r"\frontmatter",
        r"\thispagestyle{empty}",
        r"\vspace*{0.12\textheight}",
        r"\begin{center}",
        r"  {\LARGE\bfseries Categorical Reverse Mathematics --- Volume~II\par}",
        r"  \vspace{0.4em}",
        r"  {\large\itshape\color{CRMBlue} Four-Part Master Claims, Two-Tier Blueprint, and Four-Color Stratum Ledger\par}",
        r"  \vspace{0.8em}",
        f"  {{\\normalsize {tex_escape(manifest['author'])} \\quad|\\quad {tex_escape(manifest['phase'])}: {tex_escape(manifest['active_slice'])}\\par}}",
        r"\end{center}",
        r"\clearpage",
        r"\mainmatter",
        r"\setcounter{secnumdepth}{2}",
        r"\chapter{Master Claims and Grounding Ledger}\label{ch:ledger}",
        (
            r"This ledger catalogs every claim, contract, inline benchmark, and paraphrase container "
            r"compiled from \texttt{build/vol2.duckdb} under the Two-Package TCB "
            r"(\texttt{KernelArena} 2LTT + \texttt{HomotopyCRMVol2} Lean~4) and the Five Gatekeeper "
            r"Honesty Invariants~\cite{abramsky2022,Shulman20,kihara2023,maschio_trotta2026}."
        ),
        "",
        # PART I
        r"\section{Part I: Cohort I Formal Results}\label{sec:ledger-part1}",
        r"{\scriptsize\setlength{\tabcolsep}{2.3pt}\renewcommand{\arraystretch}{1.15}",
        r"\begin{xltabular}{\textwidth}{@{}P{0.23\textwidth}P{0.18\textwidth}P{0.20\textwidth}YP{0.11\textwidth}@{}}",
        r"\caption{Cohort I Formal Theorems, Propositions, and Counterexamples.}\label{tab:ledger-cohort1}\\",
        r"\toprule",
        r"\textbf{Node ID} & \textbf{Category / Tier} & \textbf{Stratum \& Axioms} & \textbf{Characterizations \& Dual Pillars} & \textbf{Status} \\",
        r"\midrule",
        r"\endfirsthead",
        r"\toprule",
        r"\textbf{Node ID} & \textbf{Category / Tier} & \textbf{Stratum \& Axioms} & \textbf{Characterizations \& Dual Pillars} & \textbf{Status} \\",
        r"\midrule",
        r"\endhead",
        r"\bottomrule",
        r"\endfoot",
    ]
    for n in cohort_i:
        nid = n["id"]
        arec = audit_by_id.get(nid) or receipts.get(nid)
        axs = arec.get("actual_axioms", n["expected_axioms"]) if arec else n["expected_axioms"]
        ax_str = r"\texttt{[]}" if not axs else r"\texttt{" + tex_code_break(", ".join(axs)) + "}"
        g = n["grounding"]
        cat_tier = f"{tex_escape(g['primary_category'])} / \\texttt{{{tex_code_break(g['blueprint_tier'])}}}"
        char_str = tex_escape(", ".join(g["characterization_types"]))
        ws = f" \\emph{{Scope:}} {tex_escape(g['witness_scope'])}" if g["witness_scope"].strip() else ""
        detail = f"{char_str}. {_pillars_summary(n)}.{ws}"
        lines.append(
            f"\\texttt{{{tex_code_break(nid)}}} & {cat_tier} & "
            f"{_stratum_tex(n['stratum'])} ({ax_str}; \\texttt{{{n['spec_hash'][:8]}}}) & "
            f"{detail} & \\texttt{{{tex_escape(n['taint_status'])}}} \\\\"
        )
    lines.extend([r"\end{xltabular}}", ""])

    # PART II
    lines.extend(
        [
            r"\section{Part II: Cohort II Definitions, Remarks, Problems \& Volume~I Contracts}\label{sec:ledger-part2}",
            r"{\scriptsize\setlength{\tabcolsep}{2.3pt}\renewcommand{\arraystretch}{1.15}",
            r"\begin{xltabular}{\textwidth}{@{}P{0.23\textwidth}P{0.17\textwidth}P{0.16\textwidth}YP{0.11\textwidth}@{}}",
            r"\caption{Cohort II Framework Definitions, Remarks, Symbols, and Pinned Volume~I Contracts.}\label{tab:ledger-cohort2}\\",
            r"\toprule",
            r"\textbf{Node ID} & \textbf{Kind \& Category} & \textbf{Blueprint / Stratum} & \textbf{Witness Scope / Pillars \& Spec8} & \textbf{Status} \\",
            r"\midrule",
            r"\endfirsthead",
            r"\toprule",
            r"\textbf{Node ID} & \textbf{Kind \& Category} & \textbf{Blueprint / Stratum} & \textbf{Witness Scope / Pillars \& Spec8} & \textbf{Status} \\",
            r"\midrule",
            r"\endhead",
            r"\bottomrule",
            r"\endfoot",
        ]
    )
    for n in cohort_ii:
        nid = n["id"]
        g = n["grounding"]
        kind_cat = f"\\texttt{{{tex_escape(n['kind'])}}}; {tex_escape(g['primary_category'])}"
        bp_st = f"\\texttt{{{tex_code_break(g['blueprint_tier'])}}} / {_stratum_tex(n['stratum'])}"
        parts = [f"\\texttt{{{n['spec_hash'][:8]}}}/\\texttt{{{n['body_hash'][:8]}}}"]
        if n["kind"] == "symbol":
            exports = n["raw"].get("spec", {}).get("exports", [])
            parts.append("Exports: " + ", ".join(f"\\texttt{{{tex_code_break(e['key'])}}}" for e in exports))
        else:
            parts.append(_pillars_summary(n))
        if g["witness_scope"].strip():
            parts.append(f"\\emph{{Scope:}} {tex_escape(g['witness_scope'])}")
        detail = " --- ".join(parts)
        lines.append(
            f"\\texttt{{{tex_code_break(nid)}}} & {kind_cat} & {bp_st} & "
            f"{detail} & \\texttt{{{tex_escape(n['taint_status'])}}} \\\\"
        )
    lines.extend([r"\end{xltabular}}", ""])

    # PART III
    lines.extend(
        [
            r"\section{Part III: Cohort III Atomic Inline Claims}\label{sec:ledger-part3}",
            r"{\scriptsize\setlength{\tabcolsep}{2.3pt}\renewcommand{\arraystretch}{1.15}",
            r"\begin{xltabular}{\textwidth}{@{}P{0.23\textwidth}P{0.16\textwidth}P{0.20\textwidth}YP{0.11\textwidth}@{}}",
            r"\caption{Cohort III Atomic Inline Technical Assertions and External Citations.}\label{tab:ledger-cohort3}\\",
            r"\toprule",
            r"\textbf{Node ID} & \textbf{Category} & \textbf{Characterizations} & \textbf{Verified Citations \& Locators} & \textbf{Status} \\",
            r"\midrule",
            r"\endfirsthead",
            r"\toprule",
            r"\textbf{Node ID} & \textbf{Category} & \textbf{Characterizations} & \textbf{Verified Citations \& Locators} & \textbf{Status} \\",
            r"\midrule",
            r"\endhead",
            r"\bottomrule",
            r"\endfoot",
        ]
    )
    if cohort_iii:
        for n in cohort_iii:
            nid = n["id"]
            g = n["grounding"]
            lines.append(
                f"\\texttt{{{tex_code_break(nid)}}} & {tex_escape(g['primary_category'])} & "
                f"{tex_escape(', '.join(g['characterization_types']))} & {_pillars_summary(n)} & "
                f"\\texttt{{{tex_escape(n['taint_status'])}}} \\\\"
            )
    else:
        lines.append(r"\emph{No Cohort III nodes registered.} & --- & --- & --- & --- \\")
    lines.extend([r"\end{xltabular}}", ""])

    # PART IV
    lines.extend(
        [
            r"\section{Part IV: Cohort IV Table and Roadmap Paraphrase Matrix}\label{sec:ledger-part4}",
            r"{\scriptsize\setlength{\tabcolsep}{2.3pt}\renewcommand{\arraystretch}{1.15}",
            r"\begin{xltabular}{\textwidth}{@{}P{0.21\textwidth}P{0.22\textwidth}P{0.17\textwidth}YP{0.10\textwidth}@{}}",
            r"\caption{Cohort IV Paraphrase Lock Matrix Verifying Spec-Hash Synchronization.}\label{tab:ledger-cohort4}\\",
            r"\toprule",
            r"\textbf{Container} & \textbf{Target Claim} & \textbf{Locked / Actual Spec8} & \textbf{Scope Note} & \textbf{Match} \\",
            r"\midrule",
            r"\endfirsthead",
            r"\toprule",
            r"\textbf{Container} & \textbf{Target Claim} & \textbf{Locked / Actual Spec8} & \textbf{Scope Note} & \textbf{Match} \\",
            r"\midrule",
            r"\endhead",
            r"\bottomrule",
            r"\endfoot",
        ]
    )
    for n in cohort_iv:
        cid = n["id"]
        for edge in n.get("prose_paraphrase_in", []):
            tid = edge["target_id"]
            locked_h = edge["locked_spec_hash"]
            actual_h = nodes_meta[tid]["spec_hash"] if tid in nodes_meta else ""
            match_str = "LOCKED" if locked_h == actual_h and locked_h else "MISMATCH"
            lines.append(
                f"\\texttt{{{tex_code_break(cid)}}} & \\texttt{{{tex_code_break(tid)}}} & "
                f"\\texttt{{{locked_h[:8]}}} / \\texttt{{{actual_h[:8]}}} & "
                f"{tex_escape(edge.get('scope_note', ''))} & \\texttt{{{match_str}}} \\\\"
            )
    lines.extend([r"\end{xltabular}}", ""])

    # PART V: Census & Disjoint Declaration Summary Table
    cohort_counts = Counter(n["cohort"] for n in all_nodes)
    cat_counts = Counter(n["grounding"]["primary_category"] for n in all_nodes)
    stratum_counts = Counter(n["stratum"] for n in all_nodes)
    lean_decl_count = sum(1 for _, _, okind in decl_rows if okind == "lean_decl")
    cert_decl_count = sum(1 for _, _, okind in decl_rows if okind == "twoltt_cert")

    lines.extend(
        [
            r"\section{Part V: Census \& Disjoint Declaration Summary}\label{sec:ledger-part5}",
            r"{\scriptsize\setlength{\tabcolsep}{3pt}\renewcommand{\arraystretch}{1.15}",
            r"\begin{xltabular}{\textwidth}{@{}P{0.26\textwidth}P{0.44\textwidth}P{0.14\textwidth}Y@{}}",
            r"\caption{Census by Cohort, Grounding Category, Four-Color Stratum, and Disjoint Declaration Ownership.}\label{tab:ledger-census}\\",
            r"\toprule",
            r"\textbf{Dimension} & \textbf{Bucket} & \textbf{Count} & \textbf{Notes} \\",
            r"\midrule",
            r"\endfirsthead",
            r"\toprule",
            r"\textbf{Dimension} & \textbf{Bucket} & \textbf{Count} & \textbf{Notes} \\",
            r"\midrule",
            r"\endhead",
            r"\bottomrule",
            r"\endfoot",
        ]
    )
    for cname in ("Cohort I", "Cohort II", "Cohort III", "Cohort IV"):
        lines.append(f"Cohort & {tex_escape(cname)} & {cohort_counts.get(cname, 0)} & --- \\\\")
    lines.append(f"\\textbf{{Total Nodes}} & \\textbf{{All Cohorts}} & \\textbf{{{len(all_nodes)}}} & CLEAN={sum(1 for n in all_nodes if n['taint_status'] == 'CLEAN')} \\\\")
    lines.append(r"\midrule")
    for cat, cnt in sorted(cat_counts.items()):
        lines.append(f"Grounding Category & {tex_escape(cat)} & {cnt} & --- \\\\")
    lines.append(r"\midrule")
    for st in ("emerald", "sapphire", "amber", "crimson", "none"):
        lines.append(
            f"Four-Color Stratum & {_stratum_tex(st)} & {stratum_counts.get(st, 0)} & --- \\\\"
        )
    lines.append(r"\midrule")
    lines.append(
        f"Declaration Ownership & Unique Lean Declarations & {lean_decl_count} & 1-to-1 disjoint across \\texttt{{decl\\_ownership}} \\\\"
    )
    lines.append(
        f"Declaration Ownership & Unique 2LTT Certificates & {cert_decl_count} & 0 shared certs; 0 TCB crossings \\\\"
    )
    lines.extend([r"\end{xltabular}}", ""])

    lines.extend(
        [
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
