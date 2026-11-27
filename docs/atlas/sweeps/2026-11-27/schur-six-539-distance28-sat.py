#!/usr/bin/env python3
"""SAT-search the fixed distance-28 extension of McKenna's Schur-538 word.

The input files and unique minimum support are pinned and checked. Run with
``--preflight-only`` to count the local tuple universe before formula emission.
The default run builds a DIMACS CNF, invokes CaDiCaL, checks SAT witnesses
directly, and requires DRAT-trim to certify any UNSAT result.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import itertools
import resource
import subprocess
import urllib.request
from pathlib import Path


ROOT = Path(__file__).resolve().parents[4]
OUT = ROOT / "target" / "schur-six-539-distance28"
EVOLVED_URL = (
    "https://raw.githubusercontent.com/jeffchen006/Schur-Number-6/"
    "5148494527df1e61e199bad21018e9a0bebbf0e0/evolve538/evolved_words.txt.gz"
)
EVOLVED_SHA256 = "bbcb8f39937278c34426caed972274493f410021d0bf40f78e0730ebe0936d19"
MCKENNA_URL = (
    "https://raw.githubusercontent.com/mysticflounder/schur-538/"
    "47c01b341b74ef5620c5e3f858c527cd266e212b/schur6-538.word"
)
MCKENNA_SHA256 = "9e149c007b778655afd199685ebcc76260604a44f4c322d8aa9a1d96afb71d20"
MCKENNA_ALT_URL = (
    "https://raw.githubusercontent.com/mysticflounder/schur-538/"
    "47c01b341b74ef5620c5e3f858c527cd266e212b/schur6-538-b.word"
)
MCKENNA_ALT_SHA256 = "00824bdd056da8543aa66878d3e1a86b123c7a814c701978e8d3c169226c4f58"
EXPECTED_NORMALIZED_SHA256 = "9be24a8e408a0d531aaa77596c7123c44a68d2c6725627f284dd2bc96df12c41"
EXPECTED_SUPPORT = (
    (6, 533), (24, 515), (28, 511), (37, 502), (39, 500), (42, 497),
    (55, 484), (57, 482), (59, 480), (68, 471), (72, 467), (73, 466),
    (77, 462), (86, 453), (88, 451), (91, 448), (103, 436), (106, 433),
    (108, 431), (117, 422), (121, 418), (126, 413), (137, 402), (138, 401),
    (151, 388), (170, 369), (200, 339), (249, 290),
)
N = 538
K = 6
APPEND_COLOUR = 4  # first-occurrence canonical; raw McKenna label is 3
REPLACEMENT_COLOURS = tuple(c for c in range(K) if c != APPEND_COLOUR)
MAX_LOCAL_TUPLES = 20_000_000
MAX_CONFLICT_CLAUSES = 10_000_000
MAX_CNF_BYTES = 1 << 30
SOLVER_CPU_SECONDS = 300
SOLVER_MEMORY_BYTES = 8 << 30
PROOF_BYTES = 2 << 30
SOLVER = ROOT / "target" / "solvers" / "cadical" / "build" / "cadical"
DRAT_TRIM = ROOT / "target" / "solvers" / "drat-trim" / "drat-trim"


class SearchLimit(RuntimeError):
    """Raised when a predeclared safety cap prevents a complete run."""


def fetch_checked(url: str, expected_sha256: str) -> bytes:
    with urllib.request.urlopen(url, timeout=60) as response:
        data = response.read()
    actual = hashlib.sha256(data).hexdigest()
    if actual != expected_sha256:
        raise RuntimeError(f"SHA-256 mismatch for {url}: {actual}")
    return data


def canonical(word: str) -> tuple[int, ...]:
    names: dict[str, int] = {}
    result = []
    for symbol in word:
        if symbol not in names:
            names[symbol] = len(names)
        result.append(names[symbol])
    if not result or len(names) > K:
        raise ValueError("word must be nonempty and use at most six colors")
    return tuple(result)


def word_digest(word: tuple[int, ...]) -> str:
    return hashlib.sha256(bytes(word)).hexdigest()


def is_sum_free(word: tuple[int, ...] | list[int]) -> bool:
    """Check all same-color x+y=z triples, with x=y permitted."""
    masks = [0] * K
    for value, colour in enumerate(word, 1):
        masks[colour] |= 1 << value
    for mask in masks:
        remaining = mask
        while remaining:
            bit = remaining & -remaining
            x = bit.bit_length() - 1
            if (mask << x) & mask:
                return False
            remaining ^= bit
    return True


def triples_538() -> list[tuple[int, int, int]]:
    return [
        (a, b, a + b)
        for a in range(1, N // 2 + 1)
        for b in range(a, N + 1 - a)
    ]


def bad_endpoint_pairs(word: tuple[int, ...], colour: int) -> tuple[tuple[int, int], ...]:
    return tuple(
        (a, 539 - a)
        for a in range(1, 270)
        if word[a - 1] == word[538 - a] == colour
    )


def load_and_freeze_support() -> tuple[tuple[int, ...], tuple[tuple[int, int], ...]]:
    evolved_raw = gzip.decompress(fetch_checked(EVOLVED_URL, EVOLVED_SHA256))
    evolved_words: dict[tuple[int, ...], set[str]] = {}
    raw_count = 0
    for line in evolved_raw.decode("ascii").splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        ident, size, word = line.split()
        if int(size) == N:
            raw_count += 1
            evolved_words.setdefault(canonical(word), set()).add(ident)
    if raw_count != 1021 or len(evolved_words) != 995:
        raise RuntimeError("pinned evolved-word corpus counts changed")

    all_words = {word: set(ids) for word, ids in evolved_words.items()}
    mckenna = canonical(fetch_checked(MCKENNA_URL, MCKENNA_SHA256).decode("ascii").strip())
    mckenna_alt = canonical(
        fetch_checked(MCKENNA_ALT_URL, MCKENNA_ALT_SHA256).decode("ascii").strip()
    )
    if len(mckenna) != N or len(mckenna_alt) != N:
        raise RuntimeError("a published McKenna word has the wrong length")
    if mckenna in evolved_words or mckenna_alt in evolved_words:
        raise RuntimeError("baseline membership changed; recheck the support inventory")
    if mckenna == mckenna_alt:
        raise RuntimeError("the two published McKenna words unexpectedly coincide")
    all_words.setdefault(mckenna, set()).add("mckenna-main")
    all_words.setdefault(mckenna_alt, set()).add("mckenna-b")
    if len(all_words) != 997:
        raise RuntimeError("unexpected number of normalized input words")

    best = N + 1
    winners: list[tuple[tuple[int, ...], set[str], int, tuple[tuple[int, int], ...]]] = []
    for word, labels in all_words.items():
        if not is_sum_free(word):
            raise RuntimeError(f"invalid length-538 input: {sorted(labels)}")
        for colour in range(K):
            pairs = bad_endpoint_pairs(word, colour)
            if len(pairs) < best:
                best = len(pairs)
                winners = [(word, labels, colour, pairs)]
            elif len(pairs) == best:
                winners.append((word, labels, colour, pairs))
    if best != 28 or len(winners) != 1:
        raise RuntimeError(f"unique minimum changed: minimum={best}, ties={len(winners)}")
    word, labels, colour, pairs = winners[0]
    if labels != {"mckenna-main"} or colour != APPEND_COLOUR:
        raise RuntimeError("the unique minimizing word/color changed")
    if word_digest(word) != EXPECTED_NORMALIZED_SHA256 or pairs != EXPECTED_SUPPORT:
        raise RuntimeError("fixed 28-pair support does not match the recorded protocol")
    if not is_sum_free(word) or len(pairs) != 28:
        raise RuntimeError("fixed base word/support failed validation")
    print("evolved_raw_records", raw_count)
    print("evolved_color_renaming_classes", len(evolved_words))
    print("normalized_words_in_inventory", len(all_words))
    print("unique_minimum_conflicts", best)
    print("unique_minimum_word", sorted(labels))
    print("canonical_append_colour", colour)
    print("normalized_word_sha256", word_digest(word))
    print("fixed_conflict_pairs", pairs)
    return word, pairs


def choice_options(pair: tuple[int, int]) -> tuple[tuple[int, int], ...]:
    return tuple(
        (endpoint, colour)
        for endpoint in pair
        for colour in REPLACEMENT_COLOURS
    )


def support_groups_for_triple(
    triple: tuple[int, int, int], position_to_group: dict[int, int]
) -> tuple[int, ...]:
    return tuple(sorted({position_to_group[p] for p in triple if p in position_to_group}))


def preflight(
    triples: list[tuple[int, int, int]], position_to_group: dict[int, int]
) -> tuple[int, Counter[int]]:
    counts: Counter[int] = Counter()
    tuples = 0
    for triple in triples:
        groups = support_groups_for_triple(triple, position_to_group)
        if not groups:
            continue
        counts[len(groups)] += 1
    # Each pair has 10 choices; K is kept as the palette size for clarity.
    tuples = sum((10**k) * count for k, count in counts.items())
    if tuples > MAX_LOCAL_TUPLES:
        raise SearchLimit(
            f"preflight tuple count {tuples} exceeds cap {MAX_LOCAL_TUPLES}; no CNF emitted"
        )
    return tuples, counts


def variable(group: int, option: int) -> int:
    return group * 10 + option + 1


def group_assignments(groups: tuple[int, ...]):
    return itertools.product(range(10), repeat=len(groups))


def conflict_clauses(
    word: tuple[int, ...],
    pairs: tuple[tuple[int, int], ...],
    triples: list[tuple[int, int, int]],
    position_to_group: dict[int, int],
) -> tuple[set[tuple[int, ...]], int]:
    options = [choice_options(pair) for pair in pairs]
    clauses: set[tuple[int, ...]] = set()
    tuples_checked = 0
    for triple in triples:
        groups = support_groups_for_triple(triple, position_to_group)
        if not groups:
            continue
        for assigned in group_assignments(groups):
            tuples_checked += 1
            changes = {
                options[group][option][0]: options[group][option][1]
                for group, option in zip(groups, assigned)
            }
            colours = tuple(changes.get(position, word[position - 1]) for position in triple)
            if colours[0] == colours[1] == colours[2]:
                clause = tuple(-variable(group, option) for group, option in zip(groups, assigned))
                clauses.add(clause)
                if len(clauses) > MAX_CONFLICT_CLAUSES:
                    raise SearchLimit(
                        f"conflict clauses exceeded cap {MAX_CONFLICT_CLAUSES}; no solver run"
                    )
    return clauses, tuples_checked


def exactly_one_clauses(groups: int = 28) -> list[tuple[int, ...]]:
    result = []
    for group in range(groups):
        variables = [variable(group, option) for option in range(10)]
        result.append(tuple(variables))
        result.extend((-variables[i], -variables[j]) for i in range(10) for j in range(i + 1, 10))
    assert len(result) == 28 * 46 == 1288
    return result


def dimacs_size(clauses: list[tuple[int, ...]]) -> int:
    header = f"p cnf 280 {len(clauses)}\n"
    size = len(header.encode("ascii"))
    for clause in clauses:
        line = " ".join(map(str, clause)) + " 0\n"
        size += len(line.encode("ascii"))
    return size


def write_dimacs(path: Path, clauses: list[tuple[int, ...]]) -> str:
    size = dimacs_size(clauses)
    if size > MAX_CNF_BYTES:
        raise SearchLimit(f"DIMACS size {size} exceeds cap {MAX_CNF_BYTES}; no solver run")
    digest = hashlib.sha256()
    with path.open("wb") as output:
        header = f"p cnf 280 {len(clauses)}\n".encode("ascii")
        output.write(header)
        digest.update(header)
        for clause in clauses:
            line = (" ".join(map(str, clause)) + " 0\n").encode("ascii")
            output.write(line)
            digest.update(line)
    return digest.hexdigest()


def set_child_limits() -> None:
    resource.setrlimit(resource.RLIMIT_CPU, (SOLVER_CPU_SECONDS, SOLVER_CPU_SECONDS + 5))
    resource.setrlimit(resource.RLIMIT_AS, (SOLVER_MEMORY_BYTES, SOLVER_MEMORY_BYTES))
    resource.setrlimit(resource.RLIMIT_FSIZE, (PROOF_BYTES, PROOF_BYTES))


def run_limited(command: list[str], stdout_path: Path, timeout: int) -> int:
    with stdout_path.open("wb") as output:
        try:
            result = subprocess.run(
                command,
                stdout=output,
                stderr=subprocess.STDOUT,
                preexec_fn=set_child_limits,
                timeout=timeout,
                check=False,
            )
        except subprocess.TimeoutExpired as error:
            raise SearchLimit(f"process exceeded wall cap ({timeout}s): {command[0]}") from error
    return result.returncode


def read_solver_status(path: Path) -> str:
    text = path.read_text(errors="replace")
    if "s SATISFIABLE" in text:
        return "SAT"
    if "s UNSATISFIABLE" in text:
        return "UNSAT"
    return "UNKNOWN"


def parse_model(path: Path) -> dict[int, bool]:
    model: dict[int, bool] = {}
    for line in path.read_text(errors="replace").splitlines():
        if line.startswith("v "):
            for token in line.split()[1:]:
                literal = int(token)
                if literal:
                    model[abs(literal)] = literal > 0
    return model


def validate_model(
    word: tuple[int, ...],
    pairs: tuple[tuple[int, int], ...],
    model: dict[int, bool],
) -> list[int]:
    options = [choice_options(pair) for pair in pairs]
    changes = {}
    for group in range(len(pairs)):
        selected = [option for option in range(10) if model.get(variable(group, option), False)]
        if len(selected) != 1:
            raise RuntimeError(f"model has {len(selected)} choices for group {group}")
        position, colour = options[group][selected[0]]
        changes[position] = colour
    if len(changes) != 28:
        raise RuntimeError(f"model changes {len(changes)} positions, expected 28")
    candidate = list(word) + [APPEND_COLOUR]
    for position, colour in changes.items():
        candidate[position - 1] = colour
    if not is_sum_free(candidate):
        raise RuntimeError("SAT model failed the independent full sum-free checker")
    for a in range(1, 270):
        b = 539 - a
        if candidate[a - 1] == candidate[b - 1] == APPEND_COLOUR:
            raise RuntimeError(f"SAT model leaves append-color conflict at {(a, b)}")
    return candidate


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--preflight-only", action="store_true")
    parser.add_argument("--cadical", type=Path, default=SOLVER)
    parser.add_argument("--drat-trim", type=Path, default=DRAT_TRIM)
    args = parser.parse_args()

    word, pairs = load_and_freeze_support()
    triples = triples_538()
    if len(triples) != 72_361:
        raise RuntimeError(f"unexpected old-triple count: {len(triples)}")
    position_to_group = {
        position: group
        for group, pair in enumerate(pairs)
        for position in pair
    }
    local_tuples, by_group_count = preflight(triples, position_to_group)
    print("old_triples", len(triples))
    print("support_triples_by_group_count", dict(sorted(by_group_count.items())))
    print("local_option_tuples", local_tuples)
    print("local_tuple_cap", MAX_LOCAL_TUPLES)
    if args.preflight_only:
        return

    if not args.cadical.is_file() or not args.drat_trim.is_file():
        raise RuntimeError("pinned CaDiCaL and DRAT-trim binaries are required")
    OUT.mkdir(parents=True, exist_ok=True)
    cnf = OUT / "schur-six-539-distance28.cnf"
    proof = OUT / "schur-six-539-distance28.drat"
    solver_log = OUT / "cadical.log"
    checker_log = OUT / "drat-trim.log"
    clauses_set, generated_tuples = conflict_clauses(
        word, pairs, triples, position_to_group
    )
    if generated_tuples != local_tuples:
        raise AssertionError("formula tuple count disagrees with preflight")
    base = exactly_one_clauses()
    conflict = sorted(clauses_set)
    clauses = base + conflict
    if len(conflict) > MAX_CONFLICT_CLAUSES:
        raise SearchLimit("conflict-clause cap exceeded")
    formula_hash = write_dimacs(cnf, clauses)
    print("variables", 280)
    print("exactly_one_clauses", len(base))
    print("conflict_clauses", len(conflict))
    print("total_clauses", len(clauses))
    print("dimacs_bytes", cnf.stat().st_size)
    print("dimacs_sha256", formula_hash)

    solver_rc = run_limited(
        [str(args.cadical), str(cnf), str(proof)], solver_log, SOLVER_CPU_SECONDS + 5
    )
    status = read_solver_status(solver_log)
    print("cadical_return_code", solver_rc)
    print("cadical_log", solver_log)
    print("solver_status", status)
    if status == "SAT":
        candidate = validate_model(word, pairs, parse_model(solver_log))
        print("SAT_WITNESS_VERIFIED")
        print("canonical_word_539", "".join(map(str, candidate)))
        return
    if status != "UNSAT":
        raise SearchLimit("solver did not return SAT or UNSAT within the declared cap")
    if not proof.is_file() or proof.stat().st_size > PROOF_BYTES:
        raise SearchLimit("UNSAT result lacks a proof within the declared proof-size cap")

    checker_rc = run_limited(
        [str(args.drat_trim), str(cnf), str(proof), "-t", str(SOLVER_CPU_SECONDS)],
        checker_log,
        SOLVER_CPU_SECONDS + 5,
    )
    checker_text = checker_log.read_text(errors="replace")
    print("drat_trim_return_code", checker_rc)
    print("drat_trim_log", checker_log)
    if checker_rc != 0 or "VERIFIED" not in checker_text.upper():
        raise RuntimeError("UNSAT proof did not pass DRAT-trim")
    print("UNSAT_PROOF_VERIFIED")
    print("drat_sha256", hashlib.sha256(proof.read_bytes()).hexdigest())


if __name__ == "__main__":
    main()
