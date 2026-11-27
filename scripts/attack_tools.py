#!/usr/bin/env python3
"""Filter scan reports and prepare evidence packets for OMA proof agents."""

import argparse
from collections import defaultdict
import json
from pathlib import Path

LANES = ("proofs/", "reductions/", "statements/")


def overlaps(target, pull_requests):
    matches = []
    for pr in pull_requests:
        paths = []
        for item in pr["files"]:
            path = item["path"]
            if not path.startswith(LANES) or not path.endswith(".lean"):
                continue
            stem = Path(path).stem
            if stem == target or stem.startswith(target + ".") or target.startswith(stem + "."):
                paths.append(path)
        if paths:
            matches.append({**pr, "matched_paths": paths})
    return matches


def link_targets(candidates):
    by_lemma = defaultdict(dict)
    for row in candidates:
        for hit in row["proposed_bridges"]:
            if hit["shared_symbols"] or hit["same_printed_proposition"]:
                key = (hit.get("origin"), hit["name"], hit.get("url"))
                by_lemma[key][row["id"]] = hit["shared_symbols"]
    links = [
        {"lemma": name, "origin": origin, "source": url, "targets": targets}
        for (origin, name, url), targets in by_lemma.items() if len(targets) > 1
    ]
    return sorted(links, key=lambda link: (-len(link["targets"]), link["lemma"]))


def packet(row, pull_requests):
    return {
        "candidate": row,
        "overlapping_prs": overlaps(row["id"], pull_requests) if pull_requests is not None else None,
        "questions": [
            "Does the source have the same quantifiers, hypotheses and conclusion?",
            "Which candidate lemma applies at the OMA pin, and what exact goal remains?",
            "Which sibling obligations are still open, and what would this proof close?",
            "What published proof, counterexample or active PR would change the decision?",
            "What small Lean check could confirm or rule out this route?",
        ],
    }


def load_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    shortlist = commands.add_parser("shortlist", help="show top candidates and path overlaps")
    shortlist.add_argument("--take", type=int, default=3)
    links = commands.add_parser("links", help="find proposed bridge lemmas shared by targets")
    handoff = commands.add_parser("packet", help="emit a proof-agent packet for one ID")
    collision = commands.add_parser("overlap", help="match one ID against a GitHub PR snapshot")
    collision.add_argument("id")
    collision.add_argument("--prs", type=Path, required=True)
    for command in (shortlist, links, handoff):
        command.add_argument("report", type=Path)
    handoff.add_argument("id")
    for command in (shortlist, handoff):
        command.add_argument("--prs", type=Path, help="GitHub open-PR snapshot")
    args = parser.parse_args()
    try:
        prs = load_json(args.prs) if getattr(args, "prs", None) else None
        if args.command == "overlap":
            result = overlaps(args.id, prs)
        else:
            report = load_json(args.report)
            candidates = report["candidates"]
            if args.command == "links":
                result = link_targets(candidates)
            elif args.command == "packet":
                row = next((row for row in candidates if row["id"] == args.id), None)
                if row is None:
                    parser.error(f"ID not found in report: {args.id}")
                result = packet(row, prs)
            else:
                if args.take < 1:
                    parser.error("--take must be positive")
                result = {
                    "prior_art_or_retrieval_errors": report["errors"],
                    "candidates": [
                        {"id": row["id"], "goal": row["goal"], "priority": row["priority"],
                         "lemmas": [hit["name"] for hit in row["proposed_bridges"]],
                         "overlapping_prs": overlaps(row["id"], prs) if prs is not None else None}
                        for row in candidates[:args.take]
                    ],
                }
    except (OSError, ValueError, KeyError, TypeError) as exc:
        parser.exit(1, f"attack-tools: {exc}\n")
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
