#!/usr/bin/env python3
"""Read-only Open Math Agents discovery and local transcript lookup."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from urllib.parse import quote, urlencode

REGISTRY = "https://lefttosolve.com"
ROOT = Path(__file__).resolve().parents[1]
ID = re.compile(r"[\w][\w.!'-]*")


def fetch(path):
    return subprocess.check_output(
        ["curl", "--fail", "--silent", "--show-error", "--location",
         "--max-time", "30", REGISTRY + path], encoding="utf-8",
    )


def discover(args):
    kind = "unformalized" if args.kind == "formalize" else args.kind
    params = {
        "kind": kind, "unsolved": 1, "full": 1,
        "sort": args.sort, "limit": args.limit, "offset": args.offset,
    }
    params.update({key: getattr(args, key) for key in ("q", "field", "source")
                   if getattr(args, key)})
    page = json.loads(fetch("/api/problems?" + urlencode(params)))
    candidates = []
    for item in page["items"]:
        problem = item["id"]
        if (item.get("solved") or item.get("claimed") or item.get("kind") != kind
                or not ID.fullmatch(problem)):
            continue
        candidate = {key: item.get(key) for key in (
            "id", "title", "kind", "statement", "lean", "decl", "file", "line",
            "ref", "source", "fields", "liveAgents",
        )}
        candidate["brief"] = f"{REGISTRY}/p/{quote(problem, safe='')}/agent.txt"
        candidates.append(candidate)
    print(json.dumps({
        "upstream": page["upstream"], "catalogue_total": page["total"],
        "offset": args.offset, "returned": len(page["items"]), "candidates": candidates,
    }, ensure_ascii=False, indent=2))


def problem_path(problem):
    if not ID.fullmatch(problem):
        raise ValueError("invalid problem ID")
    return quote(problem, safe="")


def brief(args):
    print(fetch(f"/p/{problem_path(args.id)}/agent.txt"), end="")


def steps(args):
    problem = json.loads(fetch(f"/api/problems/{problem_path(args.id)}"))
    print(json.dumps({
        "parent": problem["id"], "upstream_commit": problem.get("upstreamCommit"),
        "steps": [step for step in problem.get("steps", []) if not step.get("solved")],
    }, ensure_ascii=False, indent=2))


def local_messages(record):
    role = record.get("type")
    if role in ("user", "assistant"):
        message = record.get("message", {})
    elif role == "response_item" and record.get("payload", {}).get("type") == "message":
        message = record["payload"]
        role = message.get("role")
    else:
        return
    if role not in ("user", "assistant") or record.get("isMeta"):
        return
    content = message.get("content", [])
    if isinstance(content, str):
        yield role, content
    elif isinstance(content, list):
        for part in content:
            if isinstance(part, dict) and part.get("type") in ("text", "input_text", "output_text"):
                value = part.get("text")
                if isinstance(value, str):
                    yield role, value


def transcript_matches(path, scope, pattern):
    in_scope = False
    with path.open(encoding="utf-8", errors="replace") as stream:
        for number, line in enumerate(stream, 1):
            try:
                record = json.loads(line)
            except ValueError:
                continue
            if not isinstance(record, dict):
                continue
            cwd = record.get("cwd") or record.get("payload", {}).get("cwd")
            if isinstance(cwd, str) and Path(cwd).is_absolute():
                in_scope = Path(cwd).resolve().is_relative_to(scope)
            if in_scope:
                for role, message in local_messages(record):
                    match = pattern.search(message)
                    if match:
                        yield number, role, message[max(0, match.start() - 100):match.start() + 300]


def history(args):
    codex = Path(os.environ.get("CODEX_HOME", Path.home() / ".codex"))
    claude = Path(os.environ.get("CLAUDE_CONFIG_DIR", Path.home() / ".claude"))
    roots = args.logs or [claude / "projects", codex / "sessions", codex / "archived_sessions"]
    scope = args.scope.resolve()
    pattern = re.compile(re.escape(args.query), re.IGNORECASE)
    paths = set()
    for root in roots:
        if root.is_dir():
            paths.update(path for path in root.rglob("*.jsonl") if not path.is_symlink())
        elif root.is_file():
            paths.add(root)
    paths = sorted(paths, key=lambda path: (path.stat().st_mtime, str(path)), reverse=True)
    count = 0
    for path in paths:
        for line, role, excerpt in transcript_matches(path, scope, pattern):
            result = {"path": str(path), "line": line, "role": role}
            if args.excerpts:
                result["excerpt"] = excerpt
            print(json.dumps(result, ensure_ascii=False))
            count += 1
            if count == args.limit:
                return
    if not count:
        print(f"No matching messages in {len(paths)} transcript files for {scope}.", file=sys.stderr)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(required=True)
    search = commands.add_parser("discover", help="list candidates from the live registry")
    search.set_defaults(run=discover)
    search.add_argument("--kind", choices=("open", "formalize"), default="open")
    search.add_argument("--sort", choices=("easiest", "relevance", "famous", "hardest", "active"),
                        default="easiest")
    for key in ("q", "field", "source"):
        search.add_argument("--" + key)
    search.add_argument("--limit", type=int, default=10)
    search.add_argument("--offset", type=int, default=0)
    detail = commands.add_parser("brief", help="read a candidate's public brief")
    detail.set_defaults(run=brief)
    detail.add_argument("id")
    obligations = commands.add_parser("steps", help="list unsolved reduction obligations")
    obligations.set_defaults(run=steps)
    obligations.add_argument("id")
    logs = commands.add_parser("history", help="find local Claude Code and Codex messages")
    logs.set_defaults(run=history)
    logs.add_argument("query")
    default_scope = ROOT.parent.parent if ROOT.parent.name == "worktrees" else ROOT
    logs.add_argument("--scope", type=Path, default=default_scope)
    logs.add_argument("--logs", type=Path, action="append", help="override roots with a file or dir")
    logs.add_argument("--limit", type=int, default=20)
    logs.add_argument("--excerpts", action="store_true", help="include private text in local stdout")
    args = parser.parse_args()
    if (hasattr(args, "limit") and not 1 <= args.limit <= 100
            or hasattr(args, "offset") and args.offset < 0
            or hasattr(args, "query") and not args.query.strip()):
        parser.error("limit must be 1–100, offset must be nonnegative, and query must be nonempty")
    try:
        args.run(args)
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as exc:
        parser.exit(1, f"attack: {exc}\n")


if __name__ == "__main__":
    main()
