#!/usr/bin/env python3
"""Read-only fence enforcement for CRM Volume I."""

from __future__ import annotations

import argparse
import datetime as dt
import json
import subprocess
import sys
from pathlib import Path

VOL1_ROOT = "/home/tryggth2009/categorical-reverse-mathematics"
REPO_ROOT = Path(__file__).resolve().parent.parent
BASELINE_PATH = REPO_ROOT / "logs" / "vol1_fence_baseline.json"
FENCE_LOG_PATH = REPO_ROOT / "logs" / "vol1_fence.log"


def query_vol1_state() -> dict[str, str]:
    """Query Volume I HEAD SHA and working-tree status without taking git locks."""
    rev_proc = subprocess.run(
        ["git", "-C", VOL1_ROOT, "--no-optional-locks", "rev-parse", "HEAD"],
        capture_output=True,
        text=True,
        check=False,
    )
    if rev_proc.returncode != 0:
        raise RuntimeError(
            f"Failed to query Volume I HEAD ({rev_proc.returncode}): {rev_proc.stderr.strip()}"
        )
    status_proc = subprocess.run(
        ["git", "-C", VOL1_ROOT, "--no-optional-locks", "status", "--porcelain"],
        capture_output=True,
        text=True,
        check=False,
    )
    if status_proc.returncode != 0:
        raise RuntimeError(
            f"Failed to query Volume I status ({status_proc.returncode}): {status_proc.stderr.strip()}"
        )
    return {
        "vol1_root": VOL1_ROOT,
        "head_sha": rev_proc.stdout.strip(),
        "status_porcelain": status_proc.stdout,
    }


def cmd_init() -> int:
    """Record baseline snapshot of Volume I into logs/vol1_fence_baseline.json."""
    BASELINE_PATH.parent.mkdir(parents=True, exist_ok=True)
    state = query_vol1_state()
    payload = {
        **state,
        "recorded_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
    }
    BASELINE_PATH.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(f"FENCE_INIT_OK head_sha={payload['head_sha']} baseline={BASELINE_PATH}")
    return 0


def cmd_verify() -> int:
    """Verify current Volume I state matches the recorded baseline."""
    FENCE_LOG_PATH.parent.mkdir(parents=True, exist_ok=True)
    if not BASELINE_PATH.exists():
        msg = f"FENCE_VERIFY_FAIL missing baseline file: {BASELINE_PATH}\n"
        FENCE_LOG_PATH.write_text(msg, encoding="utf-8")
        sys.stderr.write(msg)
        return 1

    baseline = json.loads(BASELINE_PATH.read_text(encoding="utf-8"))
    current = query_vol1_state()
    checked_at = dt.datetime.now(dt.timezone.utc).isoformat()

    diffs: list[str] = []
    if current["head_sha"] != baseline.get("head_sha"):
        diffs.append(
            f"HEAD_MISMATCH expected={baseline.get('head_sha')} actual={current['head_sha']}"
        )
    if current["status_porcelain"] != baseline.get("status_porcelain"):
        diffs.append(
            "STATUS_MISMATCH\n"
            f"--- expected ---\n{baseline.get('status_porcelain', '')}"
            f"--- actual ---\n{current['status_porcelain']}"
        )

    if diffs:
        log_text = (
            f"[{checked_at}] FENCE_VERIFY_FAIL vol1_root={VOL1_ROOT}\n"
            + "\n".join(diffs)
            + "\n"
        )
        FENCE_LOG_PATH.write_text(log_text, encoding="utf-8")
        sys.stderr.write(log_text)
        return 1

    log_text = (
        f"[{checked_at}] FENCE_VERIFY_OK vol1_root={VOL1_ROOT} "
        f"head_sha={current['head_sha']} status_lines={len(current['status_porcelain'].splitlines())}\n"
    )
    FENCE_LOG_PATH.write_text(log_text, encoding="utf-8")
    sys.stdout.write(log_text)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Volume I read-only fence checker.")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--init", action="store_true", help="Record Volume I baseline snapshot.")
    group.add_argument("--verify", action="store_true", help="Verify Volume I matches baseline.")
    args = parser.parse_args()
    if args.init:
        return cmd_init()
    return cmd_verify()


if __name__ == "__main__":
    raise SystemExit(main())
