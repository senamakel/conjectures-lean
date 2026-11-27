#!/usr/bin/env python3
"""Small Q4 checkpoint/resume equivalence and frontier completeness test."""

import struct
import subprocess
import sys
import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / ".lake/build/enumerate_q6_heavy_layers"
OUT = ROOT / ".lake/snakepit-checkpoint-test"
SEED = 0b111


def run(output: Path, checkpoint: Path, *, resume: bool, capped: bool) -> int:
    args = [str(BIN), "3", str(output), "--dimension", "4", "--min-vertices", "3",
            "--force-saturated", "--early-cycle", "--checkpoint", str(checkpoint)]
    if capped:
        args += ["--node-cap", "13"]
    if resume:
        args += ["--resume"]
    result = subprocess.run(args, cwd=ROOT, text=True, capture_output=True, check=False)
    if result.returncode not in (0, 1):
        raise AssertionError(f"enumerator failed ({result.returncode}): {result.stderr}")
    if result.stderr:
        raise AssertionError(f"enumerator wrote stderr: {result.stderr}")
    return result.returncode


def read_masks(path: Path) -> list[int]:
    data = path.read_bytes()
    if len(data) % 8:
        raise AssertionError(f"misaligned output {path}: {len(data)} bytes")
    masks = [x[0] for x in struct.iter_unpack("<Q", data)]
    if len(masks) != len(set(masks)):
        raise AssertionError(f"duplicate records in {path}")
    return masks


def frontier(path: Path) -> list[tuple[tuple[int, int], ...]]:
    lines = path.read_text().splitlines()
    if not lines or not lines[0].startswith("SNAKECP1 "):
        raise AssertionError("missing checkpoint header")
    count = int(lines[1])
    if len(lines) != count + 2:
        raise AssertionError("checkpoint frontier count mismatch")
    paths = []
    for line in lines[2:]:
        values = list(map(int, line.split()))
        size, values = values[0], values[1:]
        if len(values) != 2 * size:
            raise AssertionError("malformed checkpoint prefix")
        paths.append(tuple(zip(values[::2], values[1::2])))
    for i, left in enumerate(paths):
        for j, right in enumerate(paths):
            if i != j and len(left) <= len(right) and right[:len(left)] == left:
                raise AssertionError("frontier is not prefix-free")
    if len(paths) != len(set(paths)):
        raise AssertionError("duplicate frontier prefix")
    return paths


def exhaustive_q4() -> set[int]:
    result = set()
    for mask in range(1 << 16):
        if mask & SEED != SEED or mask.bit_count() < 3:
            continue
        deg = {}
        edge_count = 0
        for v in range(16):
            if mask >> v & 1:
                deg[v] = sum(bool(mask >> (v ^ (1 << b)) & 1) for b in range(4))
                edge_count += deg[v]
        edge_count //= 2
        if edge_count != 3 or any(d > 2 for d in deg.values()):
            continue
        seen = set()
        components = 0
        for start in deg:
            if start in seen:
                continue
            components += 1
            stack = [start]
            seen.add(start)
            while stack:
                v = stack.pop()
                for b in range(4):
                    u = v ^ (1 << b)
                    if u in deg and u not in seen:
                        seen.add(u)
                        stack.append(u)
        if edge_count == len(deg) - components:
            result.add(mask)
    return result


def main() -> int:
    if not BIN.is_file():
        raise SystemExit(f"compile enumerator first: {BIN}")
    OUT.mkdir(parents=True, exist_ok=True)
    plain, cp_plain = OUT / "plain.bin", OUT / "plain.chk"
    resumed, cp = OUT / "resumed.bin", OUT / "resume.chk"
    for path in (plain, cp_plain, resumed, cp):
        path.unlink(missing_ok=True)
    run(plain, cp_plain, resume=False, capped=False)
    if run(resumed, cp, resume=False, capped=True) != 1:
        raise AssertionError("13-node capped invocation unexpectedly completed")
    first_frontier = frontier(cp)
    if not first_frontier:
        raise AssertionError("capped run did not record a resumable frontier")
    duplicate_cp, duplicate_out = OUT / "duplicate.chk", OUT / "duplicate.bin"
    duplicate_out.write_bytes(resumed.read_bytes())
    lines = cp.read_text().splitlines()
    lines[1] = str(int(lines[1]) + 1)
    lines.append(lines[2])
    duplicate_cp.write_text("\n".join(lines) + "\n")
    bad = subprocess.run([str(BIN), "3", str(duplicate_out), "--dimension", "4", "--min-vertices", "3",
                          "--force-saturated", "--early-cycle", "--checkpoint", str(duplicate_cp), "--resume"],
                         cwd=ROOT, text=True, capture_output=True, check=False)
    if bad.returncode != 2:
        raise AssertionError("resume accepted a duplicate/overlapping frontier")
    overlong_cp = OUT / "overlong.chk"
    overlong_out = OUT / "overlong.bin"
    overlong_out.write_bytes(b"")
    overlong_cp.write_text("SNAKECP1 4 3 3 0 0 0 0 0 0 0\n1\n2 3 1 15 0\n")
    bad = subprocess.run([str(BIN), "3", str(overlong_out), "--dimension", "4", "--min-vertices", "3",
                          "--checkpoint", str(overlong_cp), "--resume"], cwd=ROOT,
                         text=True, capture_output=True, check=False)
    if bad.returncode != 2:
        raise AssertionError("resume silently completed an overlong prefix pruned before replay ended")
    rounds = 1
    while frontier(cp):
        if rounds >= 1000:
            raise AssertionError("resume invocation cap exceeded")
        run(resumed, cp, resume=True, capped=True)
        read_masks(resumed)
        frontier(cp)
        rounds += 1
    got = set(read_masks(resumed))
    expected_uninterrupted = set(read_masks(plain))
    expected_exhaustive = exhaustive_q4()
    if got != expected_uninterrupted:
        raise AssertionError(f"resumed/uninterrupted mismatch: {len(got)} vs {len(expected_uninterrupted)}")
    if got != expected_exhaustive:
        raise AssertionError(f"DFS/exhaustive mismatch: {len(got)} vs {len(expected_exhaustive)}")
    corrupt = OUT / "corrupt.bin"
    corrupt.write_bytes(resumed.read_bytes()[:-8])
    bad = subprocess.run([str(BIN), "3", str(corrupt), "--dimension", "4", "--min-vertices", "3",
                          "--force-saturated", "--early-cycle", "--checkpoint", str(cp), "--resume"],
                         cwd=ROOT, text=True, capture_output=True, check=False)
    if bad.returncode != 2:
        raise AssertionError("resume accepted output shorter than saved byte offset")
    bad_cp = OUT / "bad.chk"
    bad_cp.write_text("not-a-checkpoint\n")
    bad = subprocess.run([str(BIN), "3", str(resumed), "--dimension", "4", "--min-vertices", "3",
                          "--checkpoint", str(bad_cp), "--resume"], cwd=ROOT, text=True,
                         capture_output=True, check=False)
    if bad.returncode != 2:
        raise AssertionError("resume accepted corrupted checkpoint")
    fields = cp.read_text().splitlines()
    header = fields[0].split()
    header[7] = str(int(header[7]) + 1)
    bad_cp.write_text(" ".join(header) + "\n" + "\n".join(fields[1:]) + "\n")
    bad = subprocess.run([str(BIN), "3", str(resumed), "--dimension", "4", "--min-vertices", "3",
                          "--force-saturated", "--early-cycle", "--checkpoint", str(bad_cp), "--resume"],
                         cwd=ROOT, text=True, capture_output=True, check=False)
    if bad.returncode != 2:
        raise AssertionError("resume accepted a non-record-aligned output offset")
    header[7] = str(int(cp.read_text().splitlines()[0].split()[7]))
    header[9] = str(int(header[9]) + 1)
    bad_cp.write_text(" ".join(header) + "\n" + "\n".join(fields[1:]) + "\n")
    bad = subprocess.run([str(BIN), "3", str(resumed), "--dimension", "4", "--min-vertices", "3",
                          "--force-saturated", "--early-cycle", "--checkpoint", str(bad_cp), "--resume"],
                         cwd=ROOT, text=True, capture_output=True, check=False)
    if bad.returncode != 2:
        raise AssertionError("resume accepted an output offset/count mismatch")
    bad = subprocess.run([str(BIN), "3", str(OUT / "same.bin"), "--dimension", "4",
                          "--checkpoint", str(OUT / "same.bin")], cwd=ROOT,
                         text=True, capture_output=True, check=False)
    if bad.returncode != 2:
        raise AssertionError("enumerator accepted identical output/checkpoint paths")
    marker = OUT / "alias-marker.bin"
    marker.write_bytes(b"preserve-me")
    dotted = subprocess.run([str(BIN), "3", str(marker), "--dimension", "4", "--min-vertices", "3",
                            "--checkpoint", str(OUT) + "/./alias-marker.bin"], cwd=ROOT,
                           text=True, capture_output=True, check=False)
    if dotted.returncode != 2 or marker.read_bytes() != b"preserve-me":
        raise AssertionError("enumerator did not reject normalized output/checkpoint alias safely")
    symlink = OUT / "alias-symlink.chk"
    symlink.unlink(missing_ok=True)
    symlink.symlink_to(marker)
    linked = subprocess.run([str(BIN), "3", str(marker), "--dimension", "4", "--min-vertices", "3",
                             "--checkpoint", str(symlink)], cwd=ROOT, text=True,
                            capture_output=True, check=False)
    if linked.returncode != 2 or marker.read_bytes() != b"preserve-me":
        raise AssertionError("enumerator did not reject symlink output/checkpoint alias safely")
    hardlink = OUT / "alias-hardlink.chk"
    hardlink.unlink(missing_ok=True)
    hardlink.hardlink_to(marker)
    linked = subprocess.run([str(BIN), "3", str(marker), "--dimension", "4", "--min-vertices", "3",
                             "--checkpoint", str(hardlink)], cwd=ROOT, text=True,
                            capture_output=True, check=False)
    if linked.returncode != 2 or marker.read_bytes() != b"preserve-me":
        raise AssertionError("enumerator did not reject hardlink output/checkpoint alias safely")
    temp_alias = OUT / "temp-alias.chk"
    temp_alias.unlink(missing_ok=True)
    temp_alias.with_name(temp_alias.name + ".tmp").unlink(missing_ok=True)
    temp_alias.with_name(temp_alias.name + ".tmp").symlink_to(marker)
    separate_output = OUT / "separate-output.bin"
    temp_result = subprocess.run([str(BIN), "3", str(separate_output), "--dimension", "4",
                                  "--min-vertices", "3", "--checkpoint", str(temp_alias), "--node-cap", "1"],
                                 cwd=ROOT, text=True, capture_output=True, check=False)
    if temp_result.returncode != 2 or marker.read_bytes() != b"preserve-me":
        raise AssertionError("checkpoint temporary alias damaged mask output")
    before = hashlib.sha256(resumed.read_bytes()).hexdigest()
    run(resumed, cp, resume=True, capped=True)
    after = hashlib.sha256(resumed.read_bytes()).hexdigest()
    if after != before:
        raise AssertionError("repeated resume from an empty frontier changed output")
    print(f"PASS q4_masks={len(got)} resume_invocations={rounds} frontier_final=0")
    return 0


if __name__ == "__main__":
    sys.exit(main())
