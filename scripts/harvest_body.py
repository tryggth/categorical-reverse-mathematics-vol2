#!/usr/bin/env python3
"""Harvest edited `-- BEGIN_BODY <id>` ... `-- END_BODY <id>` back into node TOML."""

from __future__ import annotations

import argparse
import re
import sys
import tomllib
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
NODES_DIR = REPO_ROOT / "nodes"


def find_node_toml(node_id: str) -> Path:
    for path in sorted(NODES_DIR.rglob("*.toml")):
        with path.open("rb") as fh:
            data = tomllib.load(fh)
        if data.get("id") == node_id:
            return path
    raise FileNotFoundError(f"Node TOML not found for id '{node_id}'")


def format_toml_multiline(text: str) -> str:
    escaped = text.replace('"""', '\\"\\"\\"')
    return f'"""\n{escaped}\n"""'


def update_lean_body_in_toml(toml_path: Path, new_body: str) -> None:
    src = toml_path.read_text(encoding="utf-8")
    # Match `lean_body = """ ... """` under [body]
    pattern = re.compile(r'(lean_body\s*=\s*""")(.*?)(""")', re.DOTALL)
    m = pattern.search(src)
    if not m:
        raise ValueError(f"Could not locate triple-quoted `lean_body` in {toml_path}")
    updated = src[: m.start(2)] + "\n" + new_body.rstrip("\n") + "\n" + src[m.end(2) :]
    # Validate TOML parses cleanly after rewrite
    tomllib.loads(updated)
    toml_path.write_text(updated, encoding="utf-8")


def harvest_node(lean_file: Path, node_id: str) -> int:
    text = lean_file.read_text(encoding="utf-8")
    node_pat = re.compile(
        rf"^-- BEGIN_NODE {re.escape(node_id)} \[spec:[0-9a-f]+ body:[0-9a-f]+\]\n(.*?)\n-- END_NODE {re.escape(node_id)}$",
        re.MULTILINE | re.DOTALL,
    )
    nm = node_pat.search(text)
    if not nm:
        sys.stderr.write(f"E_NODE_MARKERS_MISSING: could not locate BEGIN_NODE/END_NODE for {node_id}\n")
        return 1
    node_block = nm.group(1)

    body_pat = re.compile(
        rf"^[ \t]*-- BEGIN_BODY {re.escape(node_id)}\n(.*?)\n[ \t]*-- END_BODY {re.escape(node_id)}$",
        re.MULTILINE | re.DOTALL,
    )
    bm = body_pat.search(node_block)
    if not bm:
        sys.stderr.write(f"E_BODY_MARKERS_MISSING: could not locate BEGIN_BODY/END_BODY for {node_id}\n")
        return 1

    harvested_body = bm.group(1)
    toml_path = find_node_toml(node_id)
    with toml_path.open("rb") as fh:
        toml_data = tomllib.load(fh)

    mathlib_spec = toml_data.get("spec", {}).get("mathlib", {})
    signature = mathlib_spec.get("lean_signature", "").rstrip()
    guard_stanzas = mathlib_spec.get("guard_axiom_stanzas", [])
    guard_text = ("\n\n" + "\n\n".join(s.rstrip() for s in guard_stanzas)) if guard_stanzas else ""

    if "{{LEAN_BODY}}" not in signature:
        sys.stderr.write(f"E_NO_BODY_PLACEHOLDER: {node_id} signature has no {{{{LEAN_BODY}}}}\n")
        return 1

    expected_node_block = signature.replace(
        "{{LEAN_BODY}}",
        f"-- BEGIN_BODY {node_id}\n{harvested_body}\n-- END_BODY {node_id}",
    ) + guard_text

    if node_block != expected_node_block:
        sys.stderr.write(
            f"E_SIGNATURE_MUTATION: code outside BEGIN_BODY/END_BODY for {node_id} was modified.\n"
        )
        return 1

    update_lean_body_in_toml(toml_path, harvested_body)
    print(f"HARVEST_OK node_id={node_id} toml={toml_path.relative_to(REPO_ROOT)} bytes={len(harvested_body)}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Harvest Lean body edits back into node TOML.")
    parser.add_argument("lean_file", help="Path to generated Lean module.")
    parser.add_argument("--node", required=True, help="Node ID to harvest.")
    args = parser.parse_args()
    lp = Path(args.lean_file)
    if not lp.is_absolute():
        lp = (REPO_ROOT / lp).resolve()
    return harvest_node(lp, args.node)


if __name__ == "__main__":
    raise SystemExit(main())
