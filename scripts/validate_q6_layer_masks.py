#!/usr/bin/env python3
"""Independently validate the emitted normalized Q6 snakepit masks."""

import argparse
import struct
import sys
from pathlib import Path


def validate(path: Path, target_edges: int) -> int:
    data = path.read_bytes()
    if len(data) % 8:
        raise ValueError(f"{path}: byte length {len(data)} is not divisible by 8")

    masks = [mask for (mask,) in struct.iter_unpack("<Q", data)]
    seen: set[int] = set()
    for index, mask in enumerate(masks):
        if mask in seen:
            raise ValueError(f"{path}: duplicate mask at record {index}: {mask:#018x}")
        seen.add(mask)
        if mask & 0b111 != 0b111:
            raise ValueError(f"{path}: record {index} lacks normalized path vertices")

        vertices = [v for v in range(64) if (mask >> v) & 1]
        if len(vertices) < 27:
            raise ValueError(f"{path}: record {index} has only {len(vertices)} vertices")

        degrees = {v: 0 for v in vertices}
        adjacency = {v: [] for v in vertices}
        edges = 0
        for v in vertices:
            for bit in range(6):
                u = v ^ (1 << bit)
                if u in degrees:
                    degrees[v] += 1
                    adjacency[v].append(u)
                    if v < u:
                        edges += 1
        if any(degree > 2 for degree in degrees.values()):
            raise ValueError(f"{path}: record {index} has induced degree above two")
        if edges != target_edges:
            raise ValueError(f"{path}: record {index} has {edges} edges, expected {target_edges}")

        seen_vertices: set[int] = set()
        components = 0
        for start in vertices:
            if start in seen_vertices:
                continue
            components += 1
            stack = [start]
            seen_vertices.add(start)
            while stack:
                v = stack.pop()
                for u in adjacency[v]:
                    if u not in seen_vertices:
                        seen_vertices.add(u)
                        stack.append(u)
        if edges != len(vertices) - components:
            raise ValueError(f"{path}: record {index} contains a cycle")

    return len(masks)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--edges", type=int, required=True)
    parser.add_argument("mask_file", type=Path)
    args = parser.parse_args()
    if not 23 <= args.edges <= 26:
        parser.error("--edges must be between 23 and 26")
    try:
        count = validate(args.mask_file, args.edges)
    except (OSError, ValueError) as error:
        print(error, file=sys.stderr)
        return 1
    print(f"VALID records={count} target_edges={args.edges} file={args.mask_file}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
