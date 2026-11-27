#!/usr/bin/env python3
"""Screen the residual length-eight Wilf blocks for justified window permutations."""

import argparse
import json
import pickle
import pickletools
from itertools import combinations, product
from pathlib import Path

PATTERN_LENGTH = 8
MIN_SEPARATION = 4
ARCHIVE_OPS = {
    "PROTO", "FRAME", "EMPTY_LIST", "MARK", "APPENDS",
    "SHORT_BINUNICODE", "MEMOIZE", "STOP",
}


def read_blocks(path: Path) -> list[list[str]]:
    data = path.read_bytes()
    if any(op.name not in ARCHIVE_OPS for op, _, _ in pickletools.genops(data)):
        raise ValueError("archive must encode only lists of rank strings")
    blocks = pickle.loads(data)
    ranks = set("12345678")
    if (
        not isinstance(blocks, list)
        or not all(
            isinstance(block, list)
            and len(block) >= 2
            and all(
                isinstance(pattern, str)
                and len(pattern) == PATTERN_LENGTH
                and set(pattern) == ranks
                for pattern in block
            )
            for block in blocks
        )
    ):
        raise ValueError("expected a list of length-eight rank blocks")
    return blocks


def overlaps(pattern: str) -> list[int]:
    return [
        shift for shift in range(1, PATTERN_LENGTH)
        if all(
            (pattern[i] < pattern[j]) == (pattern[i + shift] < pattern[j + shift])
            for i, j in combinations(range(PATTERN_LENGTH - shift), 2)
        )
    ]


def preserves_windows(source: str, target: str) -> bool:
    """Check the central window for every possible local neighbor configuration."""
    permutation = [source.index(rank) for rank in target]
    support = {i for i, j in enumerate(permutation) if i != j}
    shifts = overlaps(source)
    if any(shift < MIN_SEPARATION for shift in shifts):
        return False
    if any(support & {i + shift for i in support} for shift in shifts):
        return False

    # Separation by at least four permits at most one overlapping predecessor
    # and one overlapping successor of the central length-eight window.
    for prior, later in product([None, *shifts], repeat=2):
        starts = ([0] if prior is None else [-prior, 0])
        if later is not None:
            starts.append(later)
        first = min(starts)
        count = max(starts) - first + PATTERN_LENGTH
        reach = [0] * count
        image = list(range(count))
        for start in starts:
            offset = start - first
            for i in support:
                image[offset + i] = offset + permutation[i]
            for i, j in combinations(range(PATTERN_LENGTH), 2):
                smaller, larger = (i, j) if source[i] < source[j] else (j, i)
                reach[offset + smaller] |= 1 << (offset + larger)

        for k in range(count):
            for i in range(count):
                if reach[i] & (1 << k):
                    reach[i] |= reach[k]
        if any(row & (1 << i) for i, row in enumerate(reach)):
            continue  # No permutation can satisfy a cyclic system of comparisons.

        for i, j in combinations(range(PATTERN_LENGTH), 2):
            smaller, larger = (i, j) if target[i] < target[j] else (j, i)
            if not reach[image[smaller - first]] & (1 << image[larger - first]):
                return False
    return True


def scan(blocks: list[list[str]]) -> dict:
    matches = []
    closed = []
    for index, block in enumerate(blocks):
        adjacency = {p: set() for p in block}
        for p, q in combinations(block, 2):
            if preserves_windows(p, q) and preserves_windows(q, p):
                adjacency[p].add(q)
                adjacency[q].add(p)
                support_size = sum(a != b for a, b in zip(p, q))
                matches.append({"block": index, "patterns": [p, q], "moved_positions": support_size})
        reached = {block[0]}
        pending = [block[0]]
        while pending:
            new = adjacency[pending.pop()] - reached
            reached.update(new)
            pending.extend(new)
        if len(reached) == len(block):
            closed.append(index)
    return {
        "input_blocks": len(blocks),
        "input_pairs": sum(len(block) * (len(block) - 1) // 2 for block in blocks),
        "passing_pairs": matches,
        "connected_blocks": closed,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("archive", type=Path, help="path to the archive's left8.pkl")
    print(json.dumps(scan(read_blocks(parser.parse_args().archive)), indent=2))
