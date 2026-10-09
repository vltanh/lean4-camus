#!/usr/bin/env python3
"""Account Codex JSONL sessions, excluding inherited fork histories.

Only accounting metadata is emitted; transcript text and local session IDs are
not copied. Input tokens include cache reads, reported separately below. The
counted tool calls are top-level transcript requests, not nested orchestration.
"""
import argparse
import datetime as dt
import json
from pathlib import Path


def time(value):
    return dt.datetime.fromisoformat(value.replace("Z", "+00:00")).timestamp()


def usage(row):
    data = row.get("payload", {})
    if row.get("type") == "event_msg" and data.get("type") == "token_count":
        return (data.get("info") or {}).get("total_token_usage")
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sessions", type=Path, required=True)
    parser.add_argument("--cwd", type=Path, default=Path.cwd())
    parser.add_argument("--start", required=True)
    parser.add_argument("--end", required=True)
    args = parser.parse_args()
    start, end = time(args.start), time(args.end)
    sessions = []
    for path in args.sessions.rglob("*.jsonl"):
        if path.stat().st_mtime < start:
            continue
        try:
            rows = [json.loads(line) for line in path.read_text().splitlines()]
        except (ValueError, OSError):
            continue
        meta = rows[0].get("payload", {})
        if meta.get("cwd") != str(args.cwd.resolve()) or time(meta["timestamp"]) > end:
            continue
        sessions.append((meta, rows))
    parent_turns = {
        r["payload"].get("turn_id")
        for m, rs in sessions if not isinstance(m.get("source"), dict)
        for r in rs if r.get("payload", {}).get("type") == "task_started"
    }
    results = []
    intervals = []
    for meta, rows in sessions:
        src = meta.get("source", {})
        agent = (src.get("subagent", {}).get("thread_spawn", {}).get("agent_path")
                 if isinstance(src, dict) else None)
        first = 0
        if agent:
            first = next(i for i, r in enumerate(rows)
                         if r.get("payload", {}).get("type") == "task_started"
                         and r["payload"].get("turn_id") not in parent_turns)
        baseline = {}
        latest = {}
        for r in rows[:first]:
            if usage(r):
                baseline = usage(r)
        own = rows[first:]
        models = set()
        tool_calls = 0
        reports = set()
        turns = {}
        for r in own:
            ts = time(r["timestamp"])
            if ts > end:
                break
            u = usage(r)
            if ts < start:
                if u:
                    baseline = u
                continue
            if u:
                latest = u
                reports.add(tuple(sorted(u.items())))
            data = r.get("payload", {})
            if r.get("type") == "turn_context" and data.get("model"):
                models.add(data["model"])
            if r.get("type") == "response_item" and data.get("type") in (
                    "function_call", "custom_tool_call"):
                tool_calls += 1
            tid = data.get("turn_id")
            if data.get("type") == "task_started" and tid not in parent_turns:
                turns[tid] = [max(start, ts), end]
            if data.get("type") == "task_complete" and tid in turns:
                turns[tid][1] = min(end, ts)
        counts = {k: latest.get(k, 0) - baseline.get(k, 0) for k in latest}
        if not models:
            models = {r["payload"]["model"] for r in rows
                      if r.get("type") == "turn_context" and r.get("payload", {}).get("model")}
        if agent:
            intervals.extend(turns.values())
        results.append({"agent": agent or "/root", "models": sorted(models),
                        "cli_version": meta.get("cli_version"), "tokens": counts,
                        "top_level_tool_calls": tool_calls,
                        "distinct_usage_reports": len(reports),
                        "own_turns": len(turns) if agent else 1,
                        "active_seconds": sum(b-a for a,b in turns.values()) if agent else end-start})
    points = [(a, 1) for a,b in intervals] + [(b, -1) for a,b in intervals]
    active = maximum = 0
    for _, delta in sorted(points):
        active += delta
        maximum = max(maximum, active)
    aggregate = {k: sum(r["tokens"].get(k, 0) for r in results)
                 for k in {k for r in results for k in r["tokens"]}}
    print(json.dumps({"start": args.start, "end": args.end,
                      "elapsed_seconds": end-start, "sessions": results,
                      "tokens": aggregate,
                      "top_level_tool_calls": sum(r["top_level_tool_calls"] for r in results),
                      "subagents": len(intervals) and sum(r["agent"] != "/root" for r in results),
                      "max_active_subagents": maximum,
                      "subagent_active_seconds": sum(b-a for a,b in intervals)}, indent=2))


if __name__ == "__main__":
    main()
