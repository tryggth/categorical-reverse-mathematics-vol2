# Categorical Reverse Mathematics — Volume II
### *Universes, Classes, and Higher Fixed Points*

> **Glass-Box 5-Fiber Formalization & Monograph Network (`Phase 1A-Pub`)**  
> **Author:** James F. Walters (Port Townsend, Washington) · **License:** CC BY 4.0 · **Working Title Locked:** `false`  
> **Companion to Volume I:** `../categorical-reverse-mathematics (HEAD b849be75)` · Zenodo Concept DOI [`10.5281/zenodo.24238086`](https://doi.org/10.5281/zenodo.24238086)

Volume II is developed as a **single-network, machine-checked mathematical and monograph architecture**. Every mathematical definition, theorem, counterexample, 2LTT certificate, LaTeX section, roadmap slice, and publication sink compiles into `build/vol2.duckdb` across five orthogonal fibers (`logical_dep`, `lean_dep`, `prose_paraphrase`, `notation`, `curriculum`) with zero cycles, disjoint 1-to-1 declaration ownership, and strict separation between **formal statement integrity (`spec_hash`)** and **proof/exposition edits (`body_hash`, `grounding_hash`)**.

## Live Public Surfaces

| Surface | Channel | Location |
|---|---|---|
| **Source Repository (`main`)** | GitHub | [tryggth/categorical-reverse-mathematics-vol2](https://github.com/tryggth/categorical-reverse-mathematics-vol2) |
| **Glass-Box Interactive Observatory** | `gh-pages` | [https://tryggth.github.io/categorical-reverse-mathematics-vol2/](https://tryggth.github.io/categorical-reverse-mathematics-vol2/) |
| **Standalone Lean 4 + KernelArena Workspace** | `lean-export` | [branch `lean-export`](https://github.com/tryggth/categorical-reverse-mathematics-vol2/tree/lean-export) |
| **Royal Octavo Monograph PDF** | Observatory PDF | [crm_vol2_monograph.pdf](https://tryggth.github.io/categorical-reverse-mathematics-vol2/pdfs/crm_vol2_monograph.pdf) |
| **4-Part Master Claims & Grounding Ledger PDF** | Observatory PDF | [crm_vol2_claims_ledger.pdf](https://tryggth.github.io/categorical-reverse-mathematics-vol2/pdfs/crm_vol2_claims_ledger.pdf) |
| **Standalone Ch. 1 Course Pack PDF** | Observatory PDF | [course_pack_ch01_probe_calibration.pdf](https://tryggth.github.io/categorical-reverse-mathematics-vol2/pdfs/course_pack_ch01_probe_calibration.pdf) |
| **Glass-Box Methodology & Taint Engine Guide** | Repository Doc | [PROCESS.md](PROCESS.md) |
| **14-Slice Volume II Project Plan** | Repository Doc | [ROADMAP.md](ROADMAP.md) |

## Current Verification Telemetry

- **Core Mathematical, Prose, & Symbol Nodes:** `22` (`22` CLEAN, `0` TAINTED across `164` directed edges)
- **14-Slice Blueprint (`nodes/plan/*.toml`):** `2 VERIFIED`, `1 ACTIVE`, `11 PLANNED` — active slice: `plan:ch01-p1b` (Phase 1B: Ch. 1 §§1.4–1.5 Zero-Giraud Axioms, Currencies, & Morita Interleaving)
- **Publication Sinks (`nodes/pub/*.toml`):** `7` out-degree-0 sinks (`main_docs`, `gh_pages`, `lean_export`, `gh_issues`)
- **Two-Package TCB (`leanprover/lean4:v4.28.0`):** `157` disjoint Lean 4 declarations (`HomotopyCRMVol2` + `AuditEnv`) + `1` zero-`Mathlib` `KernelArena` 2LTT certificates (`0` cross-package `lean_dep` edges)
- **Four-Color Stratum Spectrometer:** Emerald=15, Sapphire=0, Amber=1, Crimson=1, Prose/Symbol=5
- **Four-Part Grounding Cohorts:** Cohort I=9, Cohort II=10, Cohort III=1, Cohort IV=2

## Headline Verified Nodes (Locked via `prose_paraphrase`)

| Node ID | Title | Stratum | Blueprint Tier | Spec8 |
|---|---|---|---|---|
| `ch01:thm:mode3-orbit-stabilizer-exactness` | Mode (iii) Orbit-Stabilizer Exactness and (R_{2,2}, phi_aug) Decomposition | Amber (`propext` / `Quot.sound`) | `lean_ok` | `8dbdf070` |
| `ch01:rem:trident-mode3-2ltt-bootstrap` | Mode (iii) Obstruction Trident Preview: Zero-Mathlib 2LTT Bootstrap | Emerald (Axiom-Free) | `twoltt_ok` | `789da10e` |
| `ch01:def:probe-suite` | Doctrinal Problem and Calibrated Probe Suite (Clauses 1–3) | Emerald (Axiom-Free) | `lean_witness` | `069b4c14` |
| `ch01:thm:scotoma-pareto-trichotomy` | Epistemic Trichotomy: Scotoma, Unique Residuum, or Pareto Schism | Crimson (`Classical.choice`) | `lean_ok` | `73d0580b` |
| `ch01:thm:flow-f1-threshold-order` | Flow F1 Threshold Ordering (t_wake <= t_dogma) | Emerald (Axiom-Free) | `lean_ok` | `d8f9b2fd` |
| `ch01:cex:flow-f1-frontier-nonmonotone` | Finite 5-Point Counterexample: Non-Monotone Pareto Cardinality (1 -> 2 -> 1) | Emerald (Axiom-Free) | `lean_ok` | `08bfdee1` |
| `ch01:prop:extent-transversal-galois` | 2-Chu Extent-Transversal Galois Duality and Maximal-vs.-Minimal Reconciliation | Emerald (Axiom-Free) | `lean_ok` | `8e07cdaa` |
| `ch01:thm:flow-f2-four-rung-escalation` | Flow F2 Strict Four-Rung Stability Escalation and Etale Slice Collapse | Emerald (Axiom-Free) | `lean_witness` | `ad78ce8e` |
| `ch01:prop:flow-f3-lt-partition-and-schism` | Flow F3 Reflective Localization Partition (3^k 2^m) and Realizability Pareto Schism | Emerald (Axiom-Free) | `lean_witness` | `20719a85` |
| `ch01:thm:flow-f4-split-polarity-transport` | Flow F4 Split-Polarity Transport Law Along Mixed-Variance Conversions | Emerald (Axiom-Free) | `lean_ok` | `8127e3cb` |

## Quickstart & Local Verification

```bash
# 1. Compile the 5-fiber DuckDB network and run structural/honesty gates
python3 scripts/compile_db.py

# 2. Verify generated front-door documentation freshness
python3 scripts/emit_public_docs.py --check

# 3. Emit Lean 4 sources and run zero-Mathlib 2LTT KernelArena self-tests + cert checks
python3 scripts/emit_lean.py
lake --dir kernel_arena build
lake --dir kernel_arena exe kernel-arena --self-test
lake --dir kernel_arena exe kernel-arena verify certs/ch01_bool_id_bootstrap.2ltt.json

# 4. Build Mathlib Vol II modules and run AuditEnv axiom/stratum/hidden-edge checks
(cd mathlib_vol2 && lake exe cache get && lake build HomotopyCRM audit_env && lake exe audit_env ../build/audit_nodes_manifest.json)

# 5. Run the complete verification gatekeeper (including Royal Octavo PDFs locally)
python3 scripts/gatekeeper.py
```

> **Note on Standalone Lean Use:** If you only want the generated Lean 4 + `KernelArena` codebase without compiling DuckDB or LaTeX, switch to or clone the standalone [`lean-export`](https://github.com/tryggth/categorical-reverse-mathematics-vol2/tree/lean-export) branch.
