# Categorical Reverse Mathematics — Volume II — Standalone `lean-export` Workspace

This branch is auto-generated from `main` by `scripts/export_lean_branch.py`.
It packages the complete, standalone Lean 4 (`leanprover/lean4:v4.28.0`) codebase without DuckDB, LaTeX, or `.lake/` caches:

- `kernel_arena/`: Zero-`Mathlib` two-level type theory (2LTT) checker + `certs/*.2ltt.json`
- `mathlib_vol2/`: Emitted `HomotopyCRM/Vol2/*.lean` modules + `AuditEnv.lean` + `audit_nodes_manifest.json`
- `EXPORT_MANIFEST.json`: Node-to-declaration ownership and hash manifest (`spec_hash`, `body_hash`)

## Quick Verification

```bash
# 1. Zero-Mathlib KernelArena 2LTT checks
lake --dir kernel_arena build
lake --dir kernel_arena exe kernel-arena --self-test
lake --dir kernel_arena exe kernel-arena verify certs/ch01_bool_id_bootstrap.2ltt.json
lake --dir kernel_arena exe kernel-arena verify certs/tcb_r1_path_sym_kan.2ltt.json
lake --dir kernel_arena exe kernel-arena verify certs/tcb_r1_univ_bool_ua_not_holonomy.2ltt.json

# 2. Mathlib Vol II build & AuditEnv (Four-Color Stratum + Hidden-Edge Gate)
cd mathlib_vol2
lake exe cache get
lake build HomotopyCRM audit_env
lake exe audit_env audit_nodes_manifest.json
```
