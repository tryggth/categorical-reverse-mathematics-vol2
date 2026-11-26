#!/usr/bin/env python3
"""Idempotent GitHub Label, Milestone, and Issue sync driven by DuckDB work_items & tainted/open nodes."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tomllib
from pathlib import Path
from typing import Any

import duckdb

REPO_ROOT = Path(__file__).resolve().parent.parent
MANIFEST_PATH = REPO_ROOT / "manifest.toml"
PUB_LOCK_PATH = REPO_ROOT / "manifest" / "publication_lock.json"
DB_PATH = REPO_ROOT / "build" / "vol2.duckdb"

NODE_MARKER_RE = re.compile(r"<!--\s*crm-vol2-node:\s*([^\s>]+)\s*-->")

LABELS = [
    ("slice:active", "0E8A16", "Currently active roadmap work item"),
    ("slice:planned", "1D76DB", "Planned roadmap work item"),
    ("slice:verified", "5319E7", "Verified roadmap work item (all deliverables CLEAN)"),
    ("tcb:kernel-arena", "0052CC", "Zero-Mathlib 2LTT KernelArena TCB deliverable"),
    ("taint:remediation", "D93F0B", "Tainted node or prose_paraphrase mismatch requiring remediation"),
    ("horizon:open-problem", "FBCA04", "Open mathematical or formalization problem"),
]


def run_gh(args: list[str], allow_fail: bool = False) -> tuple[int, str, str]:
    proc = subprocess.run(
        ["gh", *args],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0 and not allow_fail:
        raise RuntimeError(f"gh {' '.join(args)} failed ({proc.returncode}): {proc.stderr.strip()}")
    return proc.returncode, proc.stdout.strip(), proc.stderr.strip()


def load_sync_state() -> dict[str, Any]:
    manifest = tomllib.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    pub_lock: dict[str, Any] = {}
    if PUB_LOCK_PATH.exists():
        pub_lock = json.loads(PUB_LOCK_PATH.read_text(encoding="utf-8"))
    github_repo = pub_lock.get("github_repo") or manifest["github_repo"]

    con = duckdb.connect(str(DB_PATH), read_only=True)
    work_rows = con.execute(
        """
        SELECT w.node_id, n.title, n.seq_order, w.milestone, w.milestone_num, w.slice_code,
               w.target_modules_json, w.deliverable_nodes_json, w.guardrails_json,
               w.summary, w.status, w.verified_deliverables, w.total_deliverables
        FROM work_items w
        JOIN nodes n ON n.id = w.node_id
        ORDER BY n.seq_order, w.node_id
        """
    ).fetchall()
    open_prob_rows = con.execute(
        """
        SELECT id, kind, title, chapter, section, grounding_tier, taint_status, raw_json
        FROM nodes
        WHERE kind IN ('problem', 'conjecture') OR grounding_tier = 'open_problem'
        ORDER BY seq_order, id
        """
    ).fetchall()
    tainted_rows = con.execute(
        """
        SELECT id, kind, title, spec_hash, taint_reason
        FROM nodes
        WHERE taint_status = 'TAINTED'
        ORDER BY seq_order, id
        """
    ).fetchall()
    clean_core_ids = {
        r[0]
        for r in con.execute(
            "SELECT id FROM nodes WHERE kind NOT IN ('work_item', 'pub_target') AND taint_status = 'CLEAN'"
        ).fetchall()
    }
    con.close()

    work_items = [
        {
            "id": r[0],
            "title": r[1],
            "seq_order": r[2],
            "milestone": r[3],
            "milestone_num": r[4],
            "slice_code": r[5],
            "target_modules": json.loads(r[6]),
            "deliverable_nodes": json.loads(r[7]),
            "guardrails": json.loads(r[8]),
            "summary": r[9],
            "status": r[10],
            "verified_deliverables": r[11],
            "total_deliverables": r[12],
        }
        for r in work_rows
    ]
    open_problems = [
        {
            "id": r[0],
            "kind": r[1],
            "title": r[2],
            "chapter": r[3],
            "section": r[4],
            "grounding_tier": r[5],
            "taint_status": r[6],
            "raw": json.loads(r[7]),
        }
        for r in open_prob_rows
    ]
    tainted_nodes = [
        {"id": r[0], "kind": r[1], "title": r[2], "spec_hash": r[3], "taint_reason": r[4]}
        for r in tainted_rows
    ]

    # Collect unique milestones ordered by milestone_num
    ms_seen: dict[int, str] = {}
    for w in work_items:
        ms_seen.setdefault(w["milestone_num"], w["milestone"])
    milestones = [ms_seen[k] for k in sorted(ms_seen.keys())]

    return {
        "manifest": manifest,
        "pub_lock": pub_lock,
        "github_repo": github_repo,
        "work_items": work_items,
        "open_problems": open_problems,
        "tainted_nodes": tainted_nodes,
        "clean_core_ids": clean_core_ids,
        "milestones": milestones,
    }


def render_work_item_issue(w: dict[str, Any], clean_core_ids: set[str]) -> tuple[str, str, list[str], str]:
    title = f"[{w['slice_code']}] {w['title']}"
    labels = ["slice:active" if w["status"] == "ACTIVE" else "slice:planned"]
    if w["milestone_num"] == 10 or any("KernelArena" in m for m in w["target_modules"]):
        labels.append("tcb:kernel-arena")

    deliv_lines = []
    for d in w["deliverable_nodes"]:
        mark = "x" if d in clean_core_ids else " "
        deliv_lines.append(f"- [{mark}] `{d}`")

    mods_text = ", ".join(f"`{m}`" for m in w["target_modules"]) or "None"
    gr_text = ", ".join(f"`{g}`" for g in w["guardrails"]) or "None"
    body = "\n".join(
        [
            f"<!-- crm-vol2-node: {w['id']} -->",
            "",
            f"**Node ID:** `{w['id']}`  ",
            f"**Milestone:** {w['milestone']} (Milestone {w['milestone_num']})  ",
            f"**Slice Code:** `{w['slice_code']}` · **Status:** `{w['status']}` (`{w['verified_deliverables']}/{w['total_deliverables']}` deliverables `CLEAN`)  ",
            f"**Target Modules:** {mods_text}  ",
            f"**Guardrails:** {gr_text}",
            "",
            "### Scope",
            w["summary"],
            "",
            "### Deliverable Nodes",
            *deliv_lines,
            "",
            "---",
            "_Synced automatically from `nodes/plan/*.toml` and `build/vol2.duckdb` via `scripts/sync_gh_issues.py`._",
        ]
    )
    return title, body, labels, w["milestone"]


def render_problem_issue(p: dict[str, Any]) -> tuple[str, str, list[str]]:
    title = f"[Open Problem] {p['title']}"
    stmt = p["raw"].get("spec", {}).get("statement", "")
    body = "\n".join(
        [
            f"<!-- crm-vol2-node: {p['id']} -->",
            "",
            f"**Node ID:** `{p['id']}` (`{p['kind']}`, Ch. `{p['chapter']}` §`{p['section']}`)  ",
            f"**Grounding Tier:** `{p['grounding_tier']}`",
            "",
            "### Statement",
            stmt,
            "",
            "---",
            "_Synced automatically from `build/vol2.duckdb` via `scripts/sync_gh_issues.py`._",
        ]
    )
    return title, body, ["horizon:open-problem"]


def render_taint_issue(t: dict[str, Any]) -> tuple[str, str, list[str]]:
    title = f"[Taint Remediation] {t['id']}: {t['title']}"
    body = "\n".join(
        [
            f"<!-- crm-vol2-node: taint:{t['id']} -->",
            "",
            f"**Tainted Node ID:** `{t['id']}` (`{t['kind']}`)  ",
            f"**Spec Hash:** `{t['spec_hash']}`  ",
            f"**Taint Reason:** `{t['taint_reason']}`",
            "",
            "Resolve the upstream `spec_hash` change or `prose_paraphrase` lock mismatch and re-run `python3 scripts/gatekeeper.py --publish`.",
        ]
    )
    return title, body, ["taint:remediation"]


def main() -> int:
    parser = argparse.ArgumentParser(description="Sync Volume II milestones and issues to GitHub.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--dry-run", action="store_true", help="Print planned changes without mutating GitHub.")
    mode.add_argument("--apply", action="store_true", help="Apply labels, milestones, and issues on GitHub.")
    args = parser.parse_args()
    apply_mode = args.apply

    state = load_sync_state()
    repo = state["github_repo"]
    work_items = state["work_items"]
    open_problems = state["open_problems"]
    tainted_nodes = state["tainted_nodes"]
    clean_core_ids = state["clean_core_ids"]
    milestones_needed = state["milestones"]

    desired_open: list[dict[str, Any]] = []
    desired_close_ids: set[str] = set()

    for w in work_items:
        if w["status"] == "VERIFIED":
            desired_close_ids.add(w["id"])
        else:
            title, body, labels, ms_title = render_work_item_issue(w, clean_core_ids)
            desired_open.append(
                {
                    "key": w["id"],
                    "title": title,
                    "body": body,
                    "labels": labels,
                    "milestone": ms_title,
                }
            )

    for p in open_problems:
        title, body, labels = render_problem_issue(p)
        desired_open.append(
            {"key": p["id"], "title": title, "body": body, "labels": labels, "milestone": None}
        )

    for t in tainted_nodes:
        title, body, labels = render_taint_issue(t)
        desired_open.append(
            {"key": f"taint:{t['id']}", "title": title, "body": body, "labels": labels, "milestone": None}
        )

    if not apply_mode:
        print(f"SYNC_GH_DRY_RUN repo={repo}")
        print(f"LABELS ({len(LABELS)}): {[l[0] for l in LABELS]}")
        print(f"MILESTONES ({len(milestones_needed)}): {milestones_needed}")
        print(f"OPEN_ISSUES_PLANNED ({len(desired_open)}):")
        for idx, item in enumerate(desired_open, 1):
            print(f"  {idx:02d}. key={item['key']} labels={item['labels']} milestone={item['milestone']} title={item['title']}")
        print(f"VERIFIED_AUTO_CLOSE_KEYS: {sorted(desired_close_ids)}")
        return 0

    # 1. Ensure labels
    for lname, lcolor, ldesc in LABELS:
        run_gh(
            [
                "label",
                "create",
                lname,
                "--repo",
                repo,
                "--color",
                lcolor,
                "--description",
                ldesc,
                "--force",
            ]
        )

    # 2. Ensure milestones
    _, ms_raw, _ = run_gh(["api", f"repos/{repo}/milestones?state=all&per_page=100"])
    existing_ms = {m["title"]: m for m in json.loads(ms_raw)}
    milestones_map: dict[str, int] = {}
    for mtitle in milestones_needed:
        if mtitle in existing_ms:
            milestones_map[mtitle] = existing_ms[mtitle]["number"]
        else:
            _, created_raw, _ = run_gh(
                [
                    "api",
                    "--method",
                    "POST",
                    f"repos/{repo}/milestones",
                    "-f",
                    f"title={mtitle}",
                    "-f",
                    f"description=CRM Volume II roadmap milestone: {mtitle}",
                ]
            )
            created_ms = json.loads(created_raw)
            milestones_map[mtitle] = created_ms["number"]

    # 3. Fetch existing issues keyed by <!-- crm-vol2-node: ... -->
    _, issues_raw, _ = run_gh(
        [
            "issue",
            "list",
            "--repo",
            repo,
            "--state",
            "all",
            "--limit",
            "500",
            "--json",
            "number,title,body,state,url,labels,milestone",
        ]
    )
    existing_by_key: dict[str, dict[str, Any]] = {}
    for irec in json.loads(issues_raw):
        m = NODE_MARKER_RE.search(irec.get("body") or "")
        if m:
            existing_by_key[m.group(1)] = irec

    issues_lock: dict[str, Any] = {}
    desired_keys = {item["key"] for item in desired_open}

    # 4. Create or update desired open issues in strict seq_order
    for item in desired_open:
        key = item["key"]
        existing = existing_by_key.get(key)
        if existing is None:
            cmd = [
                "issue",
                "create",
                "--repo",
                repo,
                "--title",
                item["title"],
                "--body",
                item["body"],
            ]
            for lbl in item["labels"]:
                cmd.extend(["--label", lbl])
            if item["milestone"]:
                cmd.extend(["--milestone", item["milestone"]])
            _, out_url, _ = run_gh(cmd)
            url_line = out_url.splitlines()[-1].strip()
            num = int(url_line.rstrip("/").split("/")[-1])
            issues_lock[key] = {
                "number": num,
                "title": item["title"],
                "state": "OPEN",
                "url": url_line,
                "milestone": item["milestone"] or "",
                "labels": item["labels"],
            }
            print(f"ISSUE_CREATED #{num} key={key} url={url_line}")
        else:
            num = int(existing["number"])
            if existing["state"] != "OPEN":
                run_gh(["issue", "reopen", str(num), "--repo", repo])
            cur_labels = sorted(l["name"] for l in existing.get("labels", []))
            cur_ms = (existing.get("milestone") or {}).get("title")
            needs_edit = (
                existing["title"] != item["title"]
                or existing["body"].strip() != item["body"].strip()
                or cur_labels != sorted(item["labels"])
                or cur_ms != item["milestone"]
            )
            if needs_edit:
                # Use gh api PATCH for exact label/milestone replacement
                patch_cmd = [
                    "api",
                    "--method",
                    "PATCH",
                    f"repos/{repo}/issues/{num}",
                    "-f",
                    f"title={item['title']}",
                    "-f",
                    f"body={item['body']}",
                ]
                for lbl in item["labels"]:
                    patch_cmd.extend(["-f", f"labels[]={lbl}"])
                if item["milestone"] and item["milestone"] in milestones_map:
                    patch_cmd.extend(["-F", f"milestone={milestones_map[item['milestone']]}"])
                run_gh(patch_cmd)
                print(f"ISSUE_UPDATED #{num} key={key}")
            else:
                print(f"ISSUE_UNCHANGED #{num} key={key}")
            issues_lock[key] = {
                "number": num,
                "title": item["title"],
                "state": "OPEN",
                "url": existing["url"],
                "milestone": item["milestone"] or "",
                "labels": item["labels"],
            }

    # 5. Auto-close verified work items or cleared taint issues
    for key, existing in sorted(existing_by_key.items()):
        if key in desired_keys:
            continue
        num = int(existing["number"])
        if existing["state"] == "OPEN" and (key in desired_close_ids or key.startswith("taint:")):
            receipt = (
                f"Verification receipt: `{key}` transitioned to `VERIFIED` / `CLEAN` in `build/vol2.duckdb`."
            )
            run_gh(["issue", "comment", str(num), "--repo", repo, "--body", receipt])
            if key in desired_close_ids:
                run_gh(
                    [
                        "api",
                        "--method",
                        "PATCH",
                        f"repos/{repo}/issues/{num}",
                        "-f",
                        "state=closed",
                        "-f",
                        "state_reason=completed",
                        "-f",
                        "labels[]=slice:verified",
                    ]
                )
            else:
                run_gh(["issue", "close", str(num), "--repo", repo, "--reason", "completed"])
            print(f"ISSUE_CLOSED #{num} key={key}")
            issues_lock[key] = {
                "number": num,
                "title": existing["title"],
                "state": "CLOSED",
                "url": existing["url"],
                "milestone": (existing.get("milestone") or {}).get("title") or "",
                "labels": ["slice:verified"] if key in desired_close_ids else ["taint:remediation"],
            }
        elif existing["state"] != "OPEN":
            issues_lock[key] = {
                "number": num,
                "title": existing["title"],
                "state": existing["state"],
                "url": existing["url"],
                "milestone": (existing.get("milestone") or {}).get("title") or "",
                "labels": sorted(l["name"] for l in existing.get("labels", [])),
            }

    pub_lock = state["pub_lock"]
    pub_lock.setdefault("schema", "vol2.publication_lock.v1")
    pub_lock["github_repo"] = repo
    owner, rname = repo.split("/", 1) if "/" in repo else ("tryggth", repo)
    pub_lock.setdefault("pages_url", f"https://{owner}.github.io/{rname}/")
    pub_lock["milestones"] = milestones_map
    pub_lock["issues"] = issues_lock
    PUB_LOCK_PATH.write_text(json.dumps(pub_lock, indent=2) + "\n", encoding="utf-8")

    print(
        f"SYNC_GH_APPLY_OK repo={repo} milestones={len(milestones_map)} "
        f"tracked_issues={len(issues_lock)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
