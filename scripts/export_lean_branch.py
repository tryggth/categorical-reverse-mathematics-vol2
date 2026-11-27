#!/usr/bin/env python3
"""Stage and commit standalone Lean 4 + KernelArena workspace onto branch `lean-export`."""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import tomllib
from pathlib import Path
from typing import Any

import duckdb

from emit_lean import emit_all

REPO_ROOT = Path(__file__).resolve().parent.parent
BUILD_DIR = REPO_ROOT / "build"
STAGE_DIR = BUILD_DIR / "lean_export_stage"
DB_PATH = BUILD_DIR / "vol2.duckdb"
MANIFEST_PATH = REPO_ROOT / "manifest.toml"
PUB_LOCK_PATH = REPO_ROOT / "manifest" / "publication_lock.json"
AUDIT_MANIFEST_PATH = BUILD_DIR / "audit_nodes_manifest.json"


def run_git(args: list[str], env: dict[str, str] | None = None, input_text: str | None = None) -> str:
    proc = subprocess.run(
        ["git", *args],
        cwd=str(REPO_ROOT),
        env=env,
        input=input_text,
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)} failed ({proc.returncode}): {proc.stderr.strip()}")
    return proc.stdout.strip()


def commit_stage_to_branch(stage_dir: Path, branch_name: str, commit_message: str) -> str:
    """Commit staged directory directly onto refs/heads/<branch_name> via GIT_INDEX_FILE without checkout."""
    files = sorted(p for p in stage_dir.rglob("*") if p.is_file() or p.is_symlink())
    for p in files:
        if ".lake" in p.parts:
            raise RuntimeError(f"Forbidden .lake path found in staging directory: {p}")

    tmp_index = BUILD_DIR / f"tmp_{branch_name.replace('/', '_')}.index"
    if tmp_index.exists():
        tmp_index.unlink()

    env = os.environ.copy()
    env["GIT_INDEX_FILE"] = str(tmp_index)
    try:
        rel_paths = [p.relative_to(stage_dir).as_posix() for p in files]
        abs_paths_input = "\n".join(str(p) for p in files) + "\n"
        blob_shas = run_git(["hash-object", "-w", "--stdin-paths"], env=env, input_text=abs_paths_input).splitlines()
        if len(blob_shas) != len(rel_paths):
            raise RuntimeError(f"hash-object count mismatch: {len(blob_shas)} != {len(rel_paths)}")

        index_lines = [
            f"100644 blob {sha}\t{rel}"
            for sha, rel in zip(blob_shas, rel_paths)
        ]
        run_git(["update-index", "--index-info"], env=env, input_text="\n".join(index_lines) + "\n")
        tree_sha = run_git(["write-tree"], env=env)

        parent_proc = subprocess.run(
            ["git", "rev-parse", "--verify", f"refs/heads/{branch_name}"],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            check=False,
        )
        if parent_proc.returncode == 0:
            parent_sha = parent_proc.stdout.strip()
            existing_tree = run_git(["rev-parse", f"{parent_sha}^{{tree}}"])
            if existing_tree == tree_sha:
                return parent_sha
            commit_sha = run_git(["commit-tree", tree_sha, "-p", parent_sha, "-m", commit_message])
        else:
            commit_sha = run_git(["commit-tree", tree_sha, "-m", commit_message])

        run_git(["update-ref", f"refs/heads/{branch_name}", commit_sha])
        return commit_sha
    finally:
        if tmp_index.exists():
            tmp_index.unlink()


def build_stage() -> dict[str, Any]:
    if not (REPO_ROOT / "mathlib_vol2" / "HomotopyCRM" / "Vol2" / "All.lean").exists():
        emit_all()

    manifest = tomllib.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    if STAGE_DIR.exists():
        shutil.rmtree(STAGE_DIR)
    STAGE_DIR.mkdir(parents=True, exist_ok=True)

    shutil.copy2(REPO_ROOT / "lean-toolchain", STAGE_DIR / "lean-toolchain")

    # Copy certs
    certs_dst = STAGE_DIR / "certs"
    certs_dst.mkdir(parents=True, exist_ok=True)
    cert_files: list[str] = []
    for p in sorted((REPO_ROOT / "certs").glob("*.2ltt.json")):
        shutil.copy2(p, certs_dst / p.name)
        cert_files.append(f"certs/{p.name}")

    # Copy kernel_arena (excluding .lake and Generated)
    ka_src = REPO_ROOT / "kernel_arena"
    ka_dst = STAGE_DIR / "kernel_arena"
    for rel in ("lakefile.toml", "lake-manifest.json", "lean-toolchain", "Main.lean", "KernelArena.lean"):
        src_p = ka_src / rel
        if src_p.exists():
            (ka_dst / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src_p, ka_dst / rel)
    for src_p in sorted((ka_src / "KernelArena").rglob("*.lean")):
        if "Generated" in src_p.parts or ".lake" in src_p.parts:
            continue
        dst_p = ka_dst / src_p.relative_to(ka_src)
        dst_p.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src_p, dst_p)

    # Copy mathlib_vol2 (excluding .lake)
    mv_src = REPO_ROOT / "mathlib_vol2"
    mv_dst = STAGE_DIR / "mathlib_vol2"
    for rel in ("lakefile.toml", "lake-manifest.json", "lean-toolchain", "AuditEnv.lean", "HomotopyCRM.lean"):
        src_p = mv_src / rel
        if src_p.exists():
            (mv_dst / rel).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(src_p, mv_dst / rel)
    emitted_modules: list[str] = []
    for src_p in sorted((mv_src / "HomotopyCRM").rglob("*.lean")):
        if ".lake" in src_p.parts:
            continue
        dst_p = mv_dst / src_p.relative_to(mv_src)
        dst_p.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src_p, dst_p)
        if src_p.parent.name == "Vol2" and src_p.stem != "All":
            emitted_modules.append(f"HomotopyCRM.Vol2.{src_p.stem}")
    if AUDIT_MANIFEST_PATH.exists():
        shutil.copy2(AUDIT_MANIFEST_PATH, mv_dst / "audit_nodes_manifest.json")

    # Query formal nodes from DuckDB
    con = duckdb.connect(str(DB_PATH), read_only=True)
    rows = con.execute(
        """
        SELECT id, kind, title, formal_pkg, stratum, module, decl_names_json,
               expected_axioms_json, cert_path, spec_hash, body_hash
        FROM nodes
        WHERE formal_pkg IN ('mathlib_vol2', 'kernel_arena')
        ORDER BY seq_order, id
        """
    ).fetchall()
    con.close()

    formal_nodes = [
        {
            "id": r[0],
            "kind": r[1],
            "title": r[2],
            "formal_pkg": r[3],
            "stratum": r[4],
            "module": r[5],
            "decl_names": json.loads(r[6]),
            "expected_axioms": json.loads(r[7]),
            "cert_path": r[8],
            "spec_hash": r[9],
            "body_hash": r[10],
        }
        for r in rows
    ]

    export_manifest = {
        "schema": "vol2.lean_export.v1",
        "working_title": manifest["working_title"],
        "working_subtitle": manifest["working_subtitle"],
        "lean_toolchain": manifest["lean_toolchain"],
        "vol1_zenodo_doi": manifest["vol1_zenodo_doi"],
        "emitted_modules": emitted_modules,
        "cert_files": cert_files,
        "formal_node_count": len(formal_nodes),
        "formal_nodes": formal_nodes,
    }
    (STAGE_DIR / "EXPORT_MANIFEST.json").write_text(
        json.dumps(export_manifest, indent=2) + "\n", encoding="utf-8"
    )

    readme_lines = [
        f"# {manifest['working_title']} — Standalone `lean-export` Workspace",
        "",
        "This branch is auto-generated from `main` by `scripts/export_lean_branch.py`.",
        "It packages the complete, standalone Lean 4 (`" + manifest["lean_toolchain"] + "`) codebase without DuckDB, LaTeX, or `.lake/` caches:",
        "",
        "- `kernel_arena/`: Zero-`Mathlib` two-level type theory (2LTT) checker + `certs/*.2ltt.json`",
        "- `mathlib_vol2/`: Emitted `HomotopyCRM/Vol2/*.lean` modules + `AuditEnv.lean` + `audit_nodes_manifest.json`",
        "- `EXPORT_MANIFEST.json`: Node-to-declaration ownership and hash manifest (`spec_hash`, `body_hash`)",
        "",
        "## Quick Verification",
        "",
        "```bash",
        "# 1. Zero-Mathlib KernelArena 2LTT checks",
        "lake --dir kernel_arena build",
        "lake --dir kernel_arena exe kernel-arena --self-test",
        "lake --dir kernel_arena exe kernel-arena verify certs/ch01_bool_id_bootstrap.2ltt.json",
        "lake --dir kernel_arena exe kernel-arena verify certs/tcb_r1_path_sym_kan.2ltt.json",
        "lake --dir kernel_arena exe kernel-arena verify certs/tcb_r1_univ_bool_ua_not_holonomy.2ltt.json",
        "",
        "# 2. Mathlib Vol II build & AuditEnv (Four-Color Stratum + Hidden-Edge Gate)",
        "cd mathlib_vol2",
        "lake exe cache get",
        "lake build HomotopyCRM audit_env",
        "lake exe audit_env audit_nodes_manifest.json",
        "```",
        "",
    ]
    (STAGE_DIR / "README_LEAN_EXPORT.md").write_text("\n".join(readme_lines), encoding="utf-8")
    return export_manifest


def main() -> int:
    parser = argparse.ArgumentParser(description="Stage and commit standalone lean-export branch.")
    parser.add_argument("--stage-only", action="store_true", help="Stage files without updating refs/heads/lean-export.")
    args = parser.parse_args()

    export_manifest = build_stage()
    if args.stage_only:
        print(
            f"EXPORT_LEAN_STAGE_OK modules={len(export_manifest['emitted_modules'])} "
            f"formal_nodes={export_manifest['formal_node_count']}"
        )
        return 0

    main_sha = run_git(["rev-parse", "--short=8", "HEAD"])
    commit_msg = f"chore(lean-export): export standalone Vol II Lean 4 + KernelArena workspace (from main {main_sha})"
    commit_sha = commit_stage_to_branch(STAGE_DIR, "lean-export", commit_msg)

    pub_lock: dict[str, Any] = {}
    if PUB_LOCK_PATH.exists():
        pub_lock = json.loads(PUB_LOCK_PATH.read_text(encoding="utf-8"))
    pub_lock.setdefault("schema", "vol2.publication_lock.v1")
    pub_lock["lean_export_commit"] = commit_sha
    PUB_LOCK_PATH.write_text(json.dumps(pub_lock, indent=2) + "\n", encoding="utf-8")

    print(
        f"EXPORT_LEAN_BRANCH_OK branch=lean-export commit={commit_sha} "
        f"modules={len(export_manifest['emitted_modules'])} "
        f"formal_nodes={export_manifest['formal_node_count']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
