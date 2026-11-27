# Volume II Project Roadmap — 14-Slice Blueprint (`ROADMAP.md`)

Generated deterministically from `build/vol2.duckdb` (`work_items` table) and `manifest/publication_lock.json` for **Categorical Reverse Mathematics — Volume II** (`Phase 3`).

## Progress Summary

- **Total Slices:** `14` (Chapters 1–9 + 3 `KernelArena` 2LTT TCB Rungs)
- **Verified (`VERIFIED`):** `5` (all listed `deliverable_nodes` exist and are `CLEAN` in `vol2.duckdb`)
- **Active (`ACTIVE`):** `1` (lowest `seq_order` unverified slice)
- **Planned (`PLANNED`):** `8`

## 14-Slice Master Schedule

| # | Slice | Milestone | Status | Deliverables | Target Modules | Guardrails | Issue |
|---|---|---|---|---|---|---|---|
| 1 | `Phase 0` (`plan:ch00-bootstrap`) | Chapter 1: Epistemic Probe Calibration & Meta-CRM Residuum | `VERIFIED` | `10/10` | `HomotopyCRM.Vol2.ProbeSuite`, `HomotopyCRM.Vol2.CertChecks`, `KernelArena.Check` | `ltt_eff_muchnik_meets` | Done |
| 2 | `Phase 1A` (`plan:ch01-p1a`) | Chapter 1: Epistemic Probe Calibration & Meta-CRM Residuum | `VERIFIED` | `12/12` | `HomotopyCRM.Vol2.ObstructionTrident`, `HomotopyCRM.Vol2.DoctrinalFlows` | `ltt_eff_muchnik_meets` | Done |
| 3 | `Phase 1B` (`plan:ch01-p1b`) | Chapter 1: Epistemic Probe Calibration & Meta-CRM Residuum | `VERIFIED` | `11/11` | `HomotopyCRM.Vol2.ZeroGiraud`, `HomotopyCRM.Vol2.MoritaInterleaving` | `ltt_eff_muchnik_meets` | [#1](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/1) |
| 4 | `Ch. 2` (`plan:ch02-class-set-adjunction`) | Chapter 2: Class-Set Adjunction & Mod(GB_0) | `VERIFIED` | `14/14` | `HomotopyCRM.Vol2.ClassSetAdjunction`, `HomotopyCRM.Vol2.VerticalKaleidoscope` | — | [#2](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/2) |
| 5 | `Ch. 3` (`plan:ch03-piset-transgression`) | Chapter 3: Leray Transgression Along pi_Set | `VERIFIED` | `15/15` | `HomotopyCRM.Vol2.EquivSplittingGC`, `HomotopyCRM.Vol2.ForcingMembrane`, `HomotopyCRM.Vol2.PiSetTransgression` | `global_section_dc` | [#3](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/3) |
| 6 | `TCB Rung 1` (`plan:tcb-rung1-cubical-kan`) | TCB: KernelArena 2LTT | `ACTIVE` | `0/3` | `KernelArena.AST`, `KernelArena.Check`, `HomotopyCRM.Vol2.CertChecks` | — | [#4](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/4) |
| 7 | `Ch. 4` (`plan:ch04-smallness-and-schemes`) | Chapter 4: Smallness Valves & Scheme Residuum | `PLANNED` | `0/4` | `HomotopyCRM.Vol2.SmallnessValves`, `HomotopyCRM.Vol2.SchemeResiduum` | `cumulative_hierarchy_strict_inclusion` | [#5](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/5) |
| 8 | `Ch. 5` (`plan:ch05-borel-unraveling`) | Chapter 5: Arboreal Comonads & Borel Unraveling | `PLANNED` | `0/3` | `HomotopyCRM.Vol2.ArborealGameComonads`, `HomotopyCRM.Vol2.BorelUnraveling` | — | [#6](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/6) |
| 9 | `Ch. 6` (`plan:ch06-large-doctrines-vopenka`) | Chapter 6: Large Doctrines & Vopenka Localization Wall | `PLANNED` | `0/3` | `HomotopyCRM.Vol2.LargeDoctrines`, `HomotopyCRM.Vol2.VopenkaLocalizationWall` | — | [#7](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/7) |
| 10 | `Ch. 7` (`plan:ch07-inf-inf-calibration`) | Chapter 7: Class-Theoretic Calibration of the (infty,infty)-Ladder | `PLANNED` | `0/3` | `HomotopyCRM.Vol2.InfInfLadder`, `HomotopyCRM.Vol2.CatOmegaStabilization` | `ordinal_rank_base` | [#8](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/8) |
| 11 | `TCB Rung 2` (`plan:tcb-rung2-nu-anima`) | TCB: KernelArena 2LTT | `PLANNED` | `0/3` | `KernelArena.AST`, `KernelArena.Check`, `HomotopyCRM.Vol2.CertChecks` | — | [#9](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/9) |
| 12 | `Ch. 8` (`plan:ch08-boffa-nu-anima`) | Chapter 8: Aczel-Boffa Coalgebras & nuP_Anima | `PLANNED` | `0/3` | `HomotopyCRM.Vol2.BoffaNuAnima`, `HomotopyCRM.Vol2.NominalDecalage` | `nom_not_iac` | [#10](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/10) |
| 13 | `TCB Rung 3` (`plan:tcb-rung3-presheaf-soundness`) | TCB: KernelArena 2LTT | `PLANNED` | `0/2` | `HomotopyCRM.Vol2.TwoLTTSoundness` | — | [#11](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/11) |
| 14 | `Ch. 9` (`plan:ch09-cic-vs-2ltt-horizons`) | Chapter 9: CIC vs. 2LTT Obstructions & Volume II Horizons | `PLANNED` | `0/3` | `HomotopyCRM.Vol2.CICvsTwoLTTObstruction` | `nom_not_iac`, `ordinal_rank_base`, `ltt_eff_muchnik_meets`, `global_section_dc`, `cumulative_hierarchy_strict_inclusion` | [#12](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/12) |

## Detailed Slice Specifications

### 1. Phase 0 Bootstrap: 5-Fiber Network Compiler, Two-Package TCB, & Ch. 1 §1.1 Core (`plan:ch00-bootstrap`)
- **Status:** `VERIFIED` (`10/10` deliverables `CLEAN`)
- **Milestone 1:** Chapter 1: Epistemic Probe Calibration & Meta-CRM Residuum (`Phase 0`)
- **Target Modules:** `HomotopyCRM.Vol2.ProbeSuite`, `HomotopyCRM.Vol2.CertChecks`, `KernelArena.Check`
- **Deliverable Nodes:** `vol1:def:doctrinal-philosophy`, `sym:probe-suite`, `ch01:def:probe-suite`, `ch01:def:adm-pareto-frontier`, `ch01:thm:scotoma-pareto-trichotomy`, `ch01:thm:flow-f1-threshold-order`, `ch01:cex:flow-f1-frontier-nonmonotone`, `ch01:rem:trident-mode3-2ltt-bootstrap`, `ch01:prose:meta-crm-roadmap`, `ch01:tab:epistemic-probe-regimes`
- **Guardrails:** `ltt_eff_muchnik_meets`
- **Scope:** Initialize DuckDB 5-fiber compiler, two-hash taint engine, zero-Mathlib KernelArena 2LTT checker, Royal Octavo LaTeX pipeline, and Ch. 1 §1.1 10-node vertical slice with Pass A/B/C taint drills.

### 2. Phase 1A: Ch. 1 §§1.1–1.3 Obstruction Trident, 2-Chu Duality, & Flows F2–F4 (`plan:ch01-p1a`)
- **Status:** `VERIFIED` (`12/12` deliverables `CLEAN`)
- **Milestone 1:** Chapter 1: Epistemic Probe Calibration & Meta-CRM Residuum (`Phase 1A`)
- **Target Modules:** `HomotopyCRM.Vol2.ObstructionTrident`, `HomotopyCRM.Vol2.DoctrinalFlows`
- **Deliverable Nodes:** `vol1:def:comparison-triple`, `vol1:def:residuum`, `sym:trident-flows`, `ch01:def:essential-fiber-trident`, `ch01:thm:mode3-orbit-stabilizer-exactness`, `ch01:prop:extent-transversal-galois`, `ch01:def:touchstone-specific-gravity`, `ch01:prop:lt-stability-projsub`, `ch01:thm:flow-f2-four-rung-escalation`, `ch01:claim:kihara-ew-weihrauch-ltt-duality`, `ch01:prop:flow-f3-lt-partition-and-schism`, `ch01:thm:flow-f4-split-polarity-transport`
- **Guardrails:** `ltt_eff_muchnik_meets`
- **Scope:** Upgrade 4-part claim grounding ledger with 5 honesty invariants and mechanize the Obstruction Trident, 2-Chu extent-transversal duality, Touchstone specific gravity, Flow F2 4-rung escalation, Flow F3 3^k 2^m partition, and Flow F4 transport.

### 3. Phase 1B: Ch. 1 §§1.4–1.5 Zero-Giraud Axioms, Currencies, & Morita Interleaving (`plan:ch01-p1b`)
- **Status:** `VERIFIED` (`11/11` deliverables `CLEAN`) · Issue [#1](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/1)
- **Milestone 1:** Chapter 1: Epistemic Probe Calibration & Meta-CRM Residuum (`Phase 1B`)
- **Target Modules:** `HomotopyCRM.Vol2.ZeroGiraud`, `HomotopyCRM.Vol2.MoritaInterleaving`
- **Deliverable Nodes:** `sym:giraud-morita`, `ch01:prop:topological-no-schism`, `ch01:thm:zero-giraud-representation`, `ch01:thm:zero-giraud-living-zone-zorn`, `ch01:cex:p0-independent-of-p1-p5`, `ch01:prob:two-giraud-prototopos-nerve`, `ch01:def:operational-currencies`, `ch01:claim:abramsky-arboreal-coalgebra-numbers`, `ch01:thm:morita-resource-interleaving`, `ch01:cex:russells-socks-levelwise-morita-failure`, `ch01:tab:currencies-morita-ledger`
- **Guardrails:** `ltt_eff_muchnik_meets`
- **Scope:** Formalize ZeroGiraud.lean (Topological No-Schism, constructive 0-Giraud (P1)+(P3)+(P4)+(P5) representation + Dogma/Casuistry banishment, Crimson Zorn Living-Zone existence with (P0)+(P2), and 4-element (P0) independence witness), register Open Problem two-giraud-prototopos-nerve, define Operational Currencies, formalize MoritaInterleaving.lean (two-sided (a,b)/(a',b') quasi-isometric resource interleaving and finite Russell's Socks k=1 failure witness), and refresh Ch. 1 Cohort IV containers.

### 4. Ch. 2 (Part I): Class-Set Adjunction, Mod(GB_0), & Williams Kaleidoscope (`plan:ch02-class-set-adjunction`)
- **Status:** `VERIFIED` (`14/14` deliverables `CLEAN`) · Issue [#2](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/2)
- **Milestone 2:** Chapter 2: Class-Set Adjunction & Mod(GB_0) (`Ch. 2`)
- **Target Modules:** `HomotopyCRM.Vol2.ClassSetAdjunction`, `HomotopyCRM.Vol2.VerticalKaleidoscope`
- **Deliverable Nodes:** `vol1:def:set-projection-fibration`, `vol1:prop:los-smuggles-gc`, `sym:class-set`, `ch02:prose:part1-ch02-roadmap`, `ch02:def:gb0-model-category`, `ch02:thm:three-way-pullback-failure`, `ch02:thm:def-left-adjoint-coreflection`, `ch02:prop:syntactic-conservative-pullback`, `ch02:prop:los-unbundling-independence`, `ch02:claim:easton-hod-unsplit-card`, `ch02:thm:williams-fixed-set-kaleidoscope`, `ch02:claim:gitman-etr-ord-fujimoto-contrast`, `ch02:claim:kelley-morse-freyd-kan-barrier`, `ch02:tab:vertical-class-spectrum`
- **Guardrails:** None
- **Scope:** Construct the Mod(GB_0) doctrinal setting, prove the 3-way naive model-space pullback failure counterexample, establish the Def -| pi_Set class-set adjunction, and formalize Williams' fixed-set kaleidoscope of class theories over a fixed set universe.

### 5. Ch. 3 (Part I): Leray Transgression Along pi_Set & Felgner vs. DC_Ord (`plan:ch03-piset-transgression`)
- **Status:** `VERIFIED` (`15/15` deliverables `CLEAN`) · Issue [#3](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/3)
- **Milestone 3:** Chapter 3: Leray Transgression Along pi_Set (`Ch. 3`)
- **Target Modules:** `HomotopyCRM.Vol2.EquivSplittingGC`, `HomotopyCRM.Vol2.ForcingMembrane`, `HomotopyCRM.Vol2.PiSetTransgression`
- **Deliverable Nodes:** `vol1:prop:large-equiv-splitting`, `vol1:thm:glazer-nonconservativity`, `vol1:thm:quantitative-conservation`, `sym:piset-transgression`, `ch03:prose:ch03-transgression-roadmap`, `ch03:thm:anafunctor-vs-functorial-gc-splitting`, `ch03:prop:skeleton-quotient-choice-stratum`, `ch03:thm:felgner-kappa-closed-membrane`, `ch03:prop:glazer-hartogs-scott-surjection`, `ch03:claim:mathias-gb0-nonconservative-over-mac`, `ch03:claim:felgner76-foundation-free-dc-ord-leak`, `ch03:thm:piset-transgression-exactness`, `ch03:thm:two-valve-transgression-dichotomy`, `ch03:prob:morleyized-classifying-topos-transgression`, `ch03:tab:piset-four-quadrant-ledger`
- **Guardrails:** `global_section_dc`
- **Scope:** Formulate Leray spectral transgression along pi_Set and the Card -> Set splitting, separating Felgner's 1971 global-choice conservation membrane from Glazer (2023) and Felgner (1976) DC_Ord leakage under Guardrail 4.

### 6. TCB Rung 1: Cubical Kan KernelArena DSL, Cofibrations, & V-Univalence ua(not) (`plan:tcb-rung1-cubical-kan`)
- **Status:** `ACTIVE` (`0/3` deliverables `CLEAN`) · Issue [#4](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/4)
- **Milestone 10:** TCB: KernelArena 2LTT (`TCB Rung 1`)
- **Target Modules:** `KernelArena.AST`, `KernelArena.Check`, `HomotopyCRM.Vol2.CertChecks`
- **Deliverable Nodes:** `tcb:tool:arena-builder-dsl`, `tcb:cert:cubical-coe-hcom`, `tcb:cert:v-univalence-ua-not`
- **Guardrails:** None
- **Scope:** Implement scripts/arena_builder.py high-level DSL and extend zero-Mathlib kernel_arena/ with Cartesian interval Psi, union-find cofibrations F, Path types, coe/hcom Kan operations, and V-Univalence certificate ua(not).

### 7. Ch. 4 (Part II): Joyal-Moerdijk (C,S) Valves, Mac != ZC, & SchemeResiduum (`plan:ch04-smallness-and-schemes`)
- **Status:** `PLANNED` (`0/4` deliverables `CLEAN`) · Issue [#5](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/5)
- **Milestone 4:** Chapter 4: Smallness Valves & Scheme Residuum (`Ch. 4`)
- **Target Modules:** `HomotopyCRM.Vol2.SmallnessValves`, `HomotopyCRM.Vol2.SchemeResiduum`
- **Deliverable Nodes:** `ch04:def:joyal-moerdijk-cs-valve`, `ch04:prop:h-aleph1-czf-subobject-stratification`, `ch04:thm:mathias-mac-strict-zc`, `ch04:thm:waterhouse-fpqc-smallness-escape`
- **Guardrails:** `cumulative_hierarchy_strict_inclusion`
- **Scope:** Calibrate Joyal-Moerdijk (C, S) Stratum II smallness valves across H(aleph_1), CZF Omega^X / 2^X, and Mathias's Mac subsetneq ZC separation (Guardrail 5), culminating in SchemeResiduum.lean up to Waterhouse's fpqc smallness escape.

### 8. Ch. 5 (Part II): Arboreal Game Comonads & Martin's Borel Unraveling (Vol. I Prob. 15) (`plan:ch05-borel-unraveling`)
- **Status:** `PLANNED` (`0/3` deliverables `CLEAN`) · Issue [#6](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/6)
- **Milestone 5:** Chapter 5: Arboreal Comonads & Borel Unraveling (`Ch. 5`)
- **Target Modules:** `HomotopyCRM.Vol2.ArborealGameComonads`, `HomotopyCRM.Vol2.BorelUnraveling`
- **Deliverable Nodes:** `ch05:def:arboreal-comonads-ek-pk-mk`, `ch05:thm:martin-unraveling-coalgebra-cs`, `ch05:thm:vol1-problem15-borel-determinacy-residuum`
- **Guardrails:** None
- **Scope:** Develop Abramsky-Reggio arboreal game comonads E_k, P_k, M_k and Martin's proper-class unraveling coalgebras in C \ S to price Borel determinacy and resolve Volume I Problem 15.

### 9. Ch. 6 (Part III): GBC to KM Large Doctrines & Vopenka Sigma_2 Localization Wall (`plan:ch06-large-doctrines-vopenka`)
- **Status:** `PLANNED` (`0/3` deliverables `CLEAN`) · Issue [#7](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/7)
- **Milestone 6:** Chapter 6: Large Doctrines & Vopenka Localization Wall (`Ch. 6`)
- **Target Modules:** `HomotopyCRM.Vol2.LargeDoctrines`, `HomotopyCRM.Vol2.VopenkaLocalizationWall`
- **Deliverable Nodes:** `ch06:thm:gbc-nbg-etr-km-hierarchy`, `ch06:thm:cmr-vopenka-sigma2-wall`, `ch06:cor:large-2cat-localization-pricing`
- **Guardrails:** None
- **Scope:** Price large doctrines and 2-categories across the strict hierarchy GBC subsetneq NBG subsetneq ETR_Ord subsetneq KM up to the Casacuberta-Mathias-Rosicky / Vopenka Sigma_2 localization reflection wall.

### 10. Ch. 7 (Part III): Class Calibration of 4-Tier (infty,infty)-Ladder (Vol. I Prob. 16) (`plan:ch07-inf-inf-calibration`)
- **Status:** `PLANNED` (`0/3` deliverables `CLEAN`) · Issue [#8](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/8)
- **Milestone 7:** Chapter 7: Class-Theoretic Calibration of the (infty,infty)-Ladder (`Ch. 7`)
- **Target Modules:** `HomotopyCRM.Vol2.InfInfLadder`, `HomotopyCRM.Vol2.CatOmegaStabilization`
- **Deliverable Nodes:** `ch07:def:four-tier-inf-inf-ladder`, `ch07:thm:alpha0-gbc-stabilization-cat-omega`, `ch07:thm:vol1-problem16-inf-inf-calibration`
- **Guardrails:** `ordinal_rank_base`
- **Scope:** Calibrate the 4-tier (infty,infty)-ladder via class theories and prove alpha = 0 GBC stabilization on Cat_{<= omega} under Guardrail 2 (rank(D) = 0 iff D ~= D^simeq), resolving Volume I Problem 16.

### 11. TCB Rung 2: Container Fixed Points WSup / NuCoalg & Quine Double-Loop Cert (`plan:tcb-rung2-nu-anima`)
- **Status:** `PLANNED` (`0/3` deliverables `CLEAN`) · Issue [#9](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/9)
- **Milestone 10:** TCB: KernelArena 2LTT (`TCB Rung 2`)
- **Target Modules:** `KernelArena.AST`, `KernelArena.Check`, `HomotopyCRM.Vol2.CertChecks`
- **Deliverable Nodes:** `tcb:ast:wsup-mu-panima`, `tcb:ast:nucoalg-nu-panima`, `tcb:cert:quine-double-loop-zmod2`
- **Guardrails:** None
- **Scope:** Extend KernelArena with polynomial container fixed points WSup (mu P_Anima) and NuCoalg (nu P_Anima) and verify the coalgebraic bisimulation path certificate certs/quine_double_loop_zmod2.2ltt.json.

### 12. Ch. 8 (Part IV): Aczel-Boffa Coalgebras, nuP_Anima Z/2Z Loops, & Nominal Decalage (Vol. I Prob. 17) (`plan:ch08-boffa-nu-anima`)
- **Status:** `PLANNED` (`0/3` deliverables `CLEAN`) · Issue [#10](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/10)
- **Milestone 8:** Chapter 8: Aczel-Boffa Coalgebras & nuP_Anima (`Ch. 8`)
- **Target Modules:** `HomotopyCRM.Vol2.BoffaNuAnima`, `HomotopyCRM.Vol2.NominalDecalage`
- **Deliverable Nodes:** `ch08:thm:aczel-boffa-loop-zmod2`, `ch08:thm:decalage-q0-sym-cont`, `ch08:thm:vol1-problem17-boffa-resolution`
- **Guardrails:** `nom_not_iac`
- **Scope:** Connect Aczel-Boffa non-wellfounded coalgebras and Omega(nu P_Anima, [q,q]) ~= Z/2Z to decalage onto Q_0^{#(2)} ->> [Q_0]^2 and [T_odd(Q_0)] in Cont(Sym(Q_0)), enforcing Guardrail 1 and resolving Volume I Problem 17.

### 13. TCB Rung 3: TwoLTTSoundness.lean Presheaf Semantics & Loop Non-Collapse (`plan:tcb-rung3-presheaf-soundness`)
- **Status:** `PLANNED` (`0/2` deliverables `CLEAN`) · Issue [#11](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/11)
- **Milestone 10:** TCB: KernelArena 2LTT (`TCB Rung 3`)
- **Target Modules:** `HomotopyCRM.Vol2.TwoLTTSoundness`
- **Deliverable Nodes:** `tcb:thm:psh-box-cart-soundness`, `tcb:thm:quine-loop-non-collapse`
- **Guardrails:** None
- **Scope:** Mechanize TwoLTTSoundness.lean proving semantic soundness of the KernelArena 2LTT calculus inside PSh(Box_cart) at Type (u + k + 1) and establishing non-collapse of the Quine double-loop invariant.

### 14. Ch. 9 (Part IV): Four-Layer CIC vs. 2LTT Obstruction, Proof Tomography, & Horizons (`plan:ch09-cic-vs-2ltt-horizons`)
- **Status:** `PLANNED` (`0/3` deliverables `CLEAN`) · Issue [#12](https://github.com/tryggth/categorical-reverse-mathematics-vol2/issues/12)
- **Milestone 9:** Chapter 9: CIC vs. 2LTT Obstructions & Volume II Horizons (`Ch. 9`)
- **Target Modules:** `HomotopyCRM.Vol2.CICvsTwoLTTObstruction`
- **Deliverable Nodes:** `ch09:thm:four-layer-cic-vs-2ltt-obstruction`, `ch09:prose:proof-tomography-case-study`, `ch09:prob:volume2-open-horizons`
- **Guardrails:** `nom_not_iac`, `ordinal_rank_base`, `ltt_eff_muchnik_meets`, `global_section_dc`, `cumulative_hierarchy_strict_inclusion`
- **Scope:** Establish the four-layer CICvsTwoLTTObstruction.lean separation, present the genre-signposted Proof Tomography case study, and synthesize Volume II Open Horizons under all five cross-volume precision guardrails.
