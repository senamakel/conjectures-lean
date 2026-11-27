#!/usr/bin/env python3
"""Rank Lean-open OMA targets by retrieved evidence for a small proof bridge."""

import argparse
from concurrent.futures import ThreadPoolExecutor
from contextlib import redirect_stdout
import io
import json
import re
from urllib.request import Request, urlopen

if __package__:
    from .attack import discover, fetch, problem_path
else:
    from attack import discover, fetch, problem_path

PREMISES = 32
QUALIFIED = re.compile(r"[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)+")
DECLARATION = re.compile(r"^\s*(?:theorem|lemma)\s+[^\s:(]+\s*:\s*")


class MCP:
    def __init__(self, url):
        self.url = url
        self.session = None

    def request(self, method, params, notification=False):
        message = {"jsonrpc": "2.0", "method": method, "params": params}
        headers = {"Accept": "application/json, text/event-stream",
                   "Content-Type": "application/json"}
        if not notification:
            message["id"] = 1
        if self.session:
            headers["Mcp-Session-Id"] = self.session
        request = Request(self.url, json.dumps(message).encode(), headers)
        with urlopen(request, timeout=45) as response:
            self.session = response.headers.get("Mcp-Session-Id", self.session)
            if notification:
                return None
            if response.headers.get_content_type() == "text/event-stream":
                reply = next(event for line in response if line.startswith(b"data:")
                             for event in [json.loads(line[5:])] if event.get("id") == 1)
            else:
                reply = json.load(response)
        if "error" in reply:
            raise ValueError(reply["error"].get("message", "MCP request failed"))
        return reply["result"]

    def __enter__(self):
        self.request("initialize", {
            "protocolVersion": "2025-03-26", "capabilities": {},
            "clientInfo": {"name": "oma-attack-scan", "version": "1"},
        })
        self.request("notifications/initialized", {}, notification=True)
        return self

    def __exit__(self, *_):
        if self.session:
            try:
                request = Request(self.url, method="DELETE",
                                  headers={"Mcp-Session-Id": self.session})
                with urlopen(request, timeout=5):
                    pass
            except OSError:
                pass

    def call(self, name, **arguments):
        result = self.request("tools/call", {"name": name, "arguments": arguments})
        if result.get("isError"):
            raise ValueError("MCP tool failed: " + name)
        return result


def proposition(statement):
    # Only strip a declaration header without binders. Preserve binder scope.
    return DECLARATION.sub("", statement, count=1)


def normalized(statement):
    return " ".join(proposition(statement).split())


def lemma_record(goal, hit):
    signature = hit.get("signature", "")
    shared = sorted(set(QUALIFIED.findall(goal)) & set(QUALIFIED.findall(signature)))
    return {**hit, "shared_symbols": shared,
            "same_printed_proposition": normalized(goal) == normalized(signature)}


def rows(result):
    if "structuredContent" in result:
        return result["structuredContent"]["result"]
    return [json.loads(block["text"]) for block in result["content"]
            if block["type"] == "text"]


def inspect_target(target, endpoint):
    goal = proposition(target["lean"])
    symbols = sorted(set(QUALIFIED.findall(goal)))
    with MCP(endpoint) as client:
        kwargs = {"symbols": symbols} if symbols else {}
        premises = rows(client.call("premises", goal=goal, k=PREMISES, **kwargs))
        neighbours = rows(client.call("search", query=goal, origin="oma/", k=12,
                                      kinds=["theorem"]))
    premises = [lemma_record(goal, hit) for hit in premises]
    neighbours = [lemma_record(goal, hit) for hit in neighbours
                  if hit.get("name") != target["id"]]
    proof_neighbours = [hit for hit in neighbours if hit.get("origin") == "oma/proofs"]
    best = sorted(premises + proof_neighbours, key=evidence_score, reverse=True)
    return {**target, "goal": goal, "symbols": symbols, "premises": premises,
            "neighbours": neighbours, "proposed_bridges": best[:5],
            "priority": evidence_score(best[0]) if best else (0, 0)}


def evidence_score(hit):
    return int(hit["same_printed_proposition"]), len(hit["shared_symbols"])


def lookup_prior_art(row, client):
    query = (
        f"Original statement, proofs, claimed solutions and partial bounds for "
        f"{row['title']} ({row['id']}), source {row.get('ref') or 'unknown'}. "
        f"Exact target: {row['goal']}"
    )
    row["exa_query"] = query
    row["exa_results"] = client.call(
        "web_search_exa", query=query, numResults=4,
        objective="Find primary sources for the exact claim and distinguish variants.",
    )["content"]


def candidates(args):
    if args.goals:
        with open(args.goals, encoding="utf-8") as stream:
            goals = json.load(stream)
        if not isinstance(goals, dict) or not all(
            isinstance(goal, str) and goal.strip() for goal in goals.values()
        ):
            raise ValueError("--goals expects an object mapping names to Lean propositions")
        return [{"id": name, "title": name, "lean": goal} for name, goal in
                list(goals.items())[args.offset:args.offset + args.limit]]
    if args.parent:
        parent = json.loads(fetch("/api/problems/" + problem_path(args.parent)))
        return [
            {"id": step["id"], "title": parent["id"] + " reduction step",
             "lean": step["statement"], "ref": step.get("reduction_pr"),
             "parent": parent["id"], "upstream": parent.get("upstreamCommit")}
            for step in parent.get("steps", []) if not step.get("solved")
        ][args.offset:args.offset + args.limit]
    output = io.StringIO()
    with redirect_stdout(output):
        discover(args)
    page = json.loads(output.getvalue())
    return [{**item, "upstream": page["upstream"]} for item in page["candidates"]
            if item.get("lean")]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--parent", help="scan open reduction leaves of this OMA ID")
    mode.add_argument("--goals", help="read named Lean propositions from a JSON object")
    for key in ("q", "field", "source"):
        parser.add_argument("--" + key)
    parser.add_argument("--limit", type=int, default=10)
    parser.add_argument("--offset", type=int, default=0)
    parser.add_argument("--workers", type=int, default=3)
    parser.add_argument("--exa-top", type=int, default=3)
    parser.add_argument("--lemmagraph-url", default="http://127.0.0.1:7340/mcp")
    parser.add_argument("--exa-url", default="https://mcp.exa.ai/mcp")
    parser.set_defaults(kind="open", sort="relevance")
    args = parser.parse_args()
    if not (1 <= args.limit <= 100 and 1 <= args.workers <= 8
            and args.offset >= 0 and args.exa_top >= 0):
        parser.error("use limit 1–100, workers 1–8 and nonnegative offset and exa-top")
    try:
        targets = candidates(args)
    except (OSError, ValueError, KeyError) as exc:
        parser.exit(1, f"attack-scan: {exc}\n")
    results = []
    errors = []
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        jobs = [(target, pool.submit(inspect_target, target, args.lemmagraph_url))
                for target in targets]
        for target, job in jobs:
            try:
                results.append(job.result())
            except (OSError, ValueError, KeyError, StopIteration) as exc:
                errors.append({"id": target["id"], "tool": "lemmagraph", "error": str(exc)})
    results.sort(key=lambda row: row["priority"], reverse=True)
    if args.exa_top and results:
        try:
            with MCP(args.exa_url) as exa:
                for row in results[:args.exa_top]:
                    try:
                        lookup_prior_art(row, exa)
                    except (OSError, ValueError, KeyError, StopIteration) as exc:
                        errors.append({"id": row["id"], "tool": "exa", "error": str(exc)})
        except (OSError, ValueError, KeyError, StopIteration) as exc:
            errors.append({"tool": "exa", "error": str(exc)})
    print(json.dumps({"premise_k": PREMISES, "scanned": len(targets),
                      "candidates": results, "errors": errors}, ensure_ascii=False, indent=2))
    return 1 if errors else 0


if __name__ == "__main__":
    raise SystemExit(main())
