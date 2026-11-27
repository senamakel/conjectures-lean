#!/usr/bin/env python3
"""Bounded radius-two extension search for six-colour Schur words of length 538.

Run with ``--inventory`` to count the candidate neighborhood without searching,
or with ``--max-candidates N`` to enumerate it. Inputs are fetched from pinned
public GitHub revisions and checked by SHA-256 before use.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import urllib.request
from collections import Counter


EVOLVED_URL = (
    "https://raw.githubusercontent.com/jeffchen006/Schur-Number-6/"
    "5148494527df1e61e199bad21018e9a0bebbf0e0/evolve538/evolved_words.txt.gz"
)
EVOLVED_SHA256 = "bbcb8f39937278c34426caed972274493f410021d0bf40f78e0730ebe0936d19"
BASE_URLS = {
    "mckenna-main": (
        "https://raw.githubusercontent.com/mysticflounder/schur-538/"
        "47c01b341b74ef5620c5e3f858c527cd266e212b/schur6-538.word",
        "9e149c007b778655afd199685ebcc76260604a44f4c322d8aa9a1d96afb71d20",
    ),
    "mckenna-b": (
        "https://raw.githubusercontent.com/mysticflounder/schur-538/"
        "47c01b341b74ef5620c5e3f858c527cd266e212b/schur6-538-b.word",
        "00824bdd056da8543aa66878d3e1a86b123c7a814c701978e8d3c169226c4f58",
    ),
}
N = 538
K = 6


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
        raise ValueError("word must be nonempty and use at most six colours")
    return tuple(result)


def is_sum_free(word: tuple[int, ...] | list[int]) -> bool:
    """Check no same-colour x,y,z in [1,n] have x+y=z (x=y allowed)."""
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


def single_conflict_counts(
    word: tuple[int, ...], triples: list[tuple[int, int, int]]
) -> list[list[int]]:
    """Count old Schur triples made monochromatic by each one-site recolour."""
    counts = [[0] * K for _ in range(N + 1)]
    for a, b, z in triples:
        ca, cb, cz = word[a - 1], word[b - 1], word[z - 1]
        if a == b:
            counts[a][cz] += 1
            counts[z][ca] += 1
        else:
            if cb == cz:
                counts[a][cb] += 1
            if ca == cz:
                counts[b][ca] += 1
            if ca == cb:
                counts[z][ca] += 1
    return counts


def bad_endpoint_pairs(word: tuple[int, ...]) -> list[list[tuple[int, int]]]:
    """Pairs x,539-x with equal old colours, grouped by their colour."""
    result: list[list[tuple[int, int]]] = [[] for _ in range(K)]
    for a in range(1, 270):
        b = 539 - a
        if word[a - 1] == word[b - 1]:
            result[word[a - 1]].append((a, b))
    return result


def shared_old_triples(p: int, q: int) -> list[tuple[int, int, int]]:
    """All old triples containing two distinct changed positions p < q."""
    triples = []
    if p + q <= N:
        triples.append((p, q, p + q))
    difference = q - p
    triples.append((min(p, difference), max(p, difference), q))
    return triples


def triple_colours(
    word: tuple[int, ...],
    triple: tuple[int, int, int],
    changes: dict[int, int],
) -> tuple[int, int, int]:
    return tuple(changes.get(position, word[position - 1]) for position in triple)


def two_recolours_preserve_old_sum_freeness(
    word: tuple[int, ...],
    single_counts: list[list[int]],
    p: int,
    cp: int,
    q: int,
    cq: int,
) -> bool:
    """Check every old triple affected by changes at p and q in constant time."""
    if p > q:
        p, q, cp, cq = q, p, cq, cp
    removed_p = 0
    removed_q = 0
    for triple in shared_old_triples(p, q):
        if len(set(triple_colours(word, triple, {p: cp}))) == 1:
            removed_p += 1
        if len(set(triple_colours(word, triple, {q: cq}))) == 1:
            removed_q += 1
        if len(set(triple_colours(word, triple, {p: cp, q: cq}))) == 1:
            return False
    assert removed_p <= single_counts[p][cp]
    assert removed_q <= single_counts[q][cq]
    return (
        single_counts[p][cp] == removed_p
        and single_counts[q][cq] == removed_q
    )


def endpoint_extension_is_legal(
    word: tuple[int, ...],
    conflicts: list[list[tuple[int, int]]],
    append_colour: int,
    changes: dict[int, int],
) -> bool:
    """Check only x+(539-x)=539 pairs touched by the changed positions."""
    bad = len(conflicts[append_colour])
    affected = {min(position, 539 - position) for position in changes}
    for a in affected:
        b = 539 - a
        old_a, old_b = word[a - 1], word[b - 1]
        if old_a == old_b == append_colour:
            bad -= 1
        new_a = changes.get(a, old_a)
        new_b = changes.get(b, old_b)
        if new_a == new_b == append_colour:
            bad += 1
    return bad == 0


def make_witness(
    word: tuple[int, ...], changes: dict[int, int], append_colour: int
) -> list[int]:
    candidate = list(word) + [append_colour]
    for position, colour in changes.items():
        candidate[position - 1] = colour
    if not is_sum_free(candidate):
        raise AssertionError("incremental checks accepted an invalid witness")
    return candidate


def load_words() -> tuple[dict[tuple[int, ...], set[str]], int, int, dict[str, bool]]:
    evolved_compressed = fetch_checked(EVOLVED_URL, EVOLVED_SHA256)
    evolved_lines = gzip.decompress(evolved_compressed).decode("ascii").splitlines()
    evolved_words: dict[tuple[int, ...], set[str]] = {}
    raw_count = 0
    for line in evolved_lines:
        if not line.strip() or line.startswith("#"):
            continue
        ident, size, word = line.split()
        if int(size) != N:
            continue
        raw_count += 1
        evolved_words.setdefault(canonical(word), set()).add(ident)
    if raw_count != 1021 or len(evolved_words) != 995:
        raise RuntimeError(
            f"unexpected evolved corpus counts: {raw_count} raw, "
            f"{len(evolved_words)} up to colour renaming"
        )

    all_words = {word: set(ids) for word, ids in evolved_words.items()}
    baseline_keys = {}
    baseline_present = {}
    for label, (url, digest) in BASE_URLS.items():
        text = fetch_checked(url, digest).decode("ascii").strip()
        key = canonical(text)
        if len(key) != N:
            raise RuntimeError(f"{label} has length {len(key)}, expected {N}")
        baseline_keys[label] = key
        baseline_present[label] = key in evolved_words
        all_words.setdefault(key, set()).add(label)
    if baseline_keys["mckenna-main"] == baseline_keys["mckenna-b"]:
        raise RuntimeError("McKenna's two supplied baseline words are not distinct")
    return all_words, raw_count, len(evolved_words), baseline_present


def candidate_count(
    words: dict[tuple[int, ...], set[str]],
) -> tuple[int, Counter[str]]:
    """Count the additional exactly-two-recolour candidates after radius one."""
    total = 0
    distribution: Counter[str] = Counter()
    for word in words:
        conflicts = bad_endpoint_pairs(word)
        for pairs in conflicts:
            if len(pairs) == 0:
                distribution["zero-pair-colours"] += 1
            elif len(pairs) == 1:
                # Radius one has already covered the 10 one-site edits.
                total += 1073 * 25
                distribution["one-pair-colours"] += 1
            elif len(pairs) == 2:
                # Choose one endpoint and one replacement colour in each pair.
                total += 2 * 5 * 2 * 5
                distribution["two-pair-colours"] += 1
            else:
                distribution["more-than-two-pair-colours"] += 1
    return total, distribution


def search_radius_one(
    words: dict[tuple[int, ...], set[str]],
    triples: list[tuple[int, int, int]],
) -> tuple[int, Counter[str]]:
    """Test every append colour and every zero/one old-coordinate recolour."""
    checked = 0
    distribution: Counter[str] = Counter()
    for word, labels in sorted(words.items(), key=lambda item: min(item[1])):
        if len(word) != N or not is_sum_free(word):
            raise RuntimeError(f"invalid input word: {sorted(labels)}")
        single_counts = single_conflict_counts(word, triples)
        for position in range(1, N + 1):
            if single_counts[position][word[position - 1]]:
                raise AssertionError("input word has an old monochromatic triple")
        conflicts = bad_endpoint_pairs(word)
        for append_colour in range(K):
            changes: dict[int, int] = {}
            checked += 1
            distribution["zero-recolour"] += 1
            if endpoint_extension_is_legal(word, conflicts, append_colour, changes):
                witness = make_witness(word, changes, append_colour)
                print("WITNESS", sorted(labels), append_colour, changes)
                print("word", "".join(map(str, witness)))
                return checked, distribution | Counter({"witness": 1})
            for position in range(1, N + 1):
                old = word[position - 1]
                for replacement in range(K):
                    if replacement == old:
                        continue
                    changes = {position: replacement}
                    checked += 1
                    distribution["one-recolour"] += 1
                    if (
                        single_counts[position][replacement] == 0
                        and endpoint_extension_is_legal(
                            word, conflicts, append_colour, changes
                        )
                    ):
                        witness = make_witness(word, changes, append_colour)
                        print("WITNESS", sorted(labels), append_colour, changes)
                        print("word", "".join(map(str, witness)))
                        return checked, distribution | Counter({"witness": 1})
    return checked, distribution


def search_radius_two(
    words: dict[tuple[int, ...], set[str]],
    triples: list[tuple[int, int, int]],
) -> tuple[int, Counter[str]]:
    """Test the additional exactly-two-recolour candidates using pair counts."""
    checked = 0
    distribution: Counter[str] = Counter()
    for word, labels in sorted(words.items(), key=lambda item: min(item[1])):
        if len(word) != N or not is_sum_free(word):
            raise RuntimeError(f"invalid input word: {sorted(labels)}")
        single_counts = single_conflict_counts(word, triples)
        for position in range(1, N + 1):
            if single_counts[position][word[position - 1]]:
                raise AssertionError("input word has an old monochromatic triple")
        conflicts = bad_endpoint_pairs(word)

        for append_colour, pairs in enumerate(conflicts):
            if len(pairs) == 0:
                raise AssertionError("radius-one search should have found this extension")

            if len(pairs) > 2:
                distribution["skipped-more-than-two-pairs"] += 1
                continue

            if len(pairs) == 1:
                (a, b) = pairs[0]
                # Every two-site support meeting {a,b}, with each unordered
                # support generated once. It has 2*537 - 1 = 1,073 members.
                supports = set()
                for endpoint in (a, b):
                    for other in range(1, N + 1):
                        if other != endpoint:
                            supports.add(tuple(sorted((endpoint, other))))
                assert len(supports) == 1073
                for p, q in sorted(supports):
                    for cp in range(K):
                        if cp == word[p - 1]:
                            continue
                        for cq in range(K):
                            if cq == word[q - 1]:
                                continue
                            changes = {p: cp, q: cq}
                            checked += 1
                            distribution["two-recolour-one-pair"] += 1
                            if (
                                two_recolours_preserve_old_sum_freeness(
                                    word, single_counts, p, cp, q, cq
                                )
                                and endpoint_extension_is_legal(
                                    word, conflicts, append_colour, changes
                                )
                            ):
                                witness = make_witness(word, changes, append_colour)
                                print("WITNESS", sorted(labels), append_colour, changes)
                                print("word", "".join(map(str, witness)))
                                return checked, distribution | Counter({"witness": 1})
                continue

            # Two disjoint bad endpoint pairs require a recolour in each.
            (a1, b1), (a2, b2) = pairs
            for p in (a1, b1):
                for cp in range(K):
                    if cp == word[p - 1]:
                        continue
                    for q in (a2, b2):
                        for cq in range(K):
                            if cq == word[q - 1]:
                                continue
                            changes = {p: cp, q: cq}
                            checked += 1
                            distribution["two-recolour-two-pairs"] += 1
                            if (
                                two_recolours_preserve_old_sum_freeness(
                                    word, single_counts, p, cp, q, cq
                                )
                                and endpoint_extension_is_legal(
                                    word, conflicts, append_colour, changes
                                )
                            ):
                                witness = make_witness(word, changes, append_colour)
                                print("WITNESS", sorted(labels), append_colour, changes)
                                print("word", "".join(map(str, witness)))
                                return checked, distribution | Counter({"witness": 1})

    return checked, distribution


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--inventory", action="store_true")
    parser.add_argument("--max-candidates", type=int, default=100_000_000)
    args = parser.parse_args()

    words, raw_count, evolved_unique, baseline_present = load_words()
    baseline_unique = len({canonical("".join(map(str, word))) for word in words})
    assert baseline_unique == len(words)
    assert all(is_sum_free(word) for word in words)
    one_recolour_total = len(words) * K * (1 + N * (K - 1))
    radius_two_total, distribution = candidate_count(words)
    total = one_recolour_total + radius_two_total
    print("evolved_raw_words", raw_count)
    print("evolved_up_to_renaming", evolved_unique)
    print("unique_words_including_McKenna_baselines", len(words))
    print("McKenna_baseline_already_in_evolved_corpus", baseline_present)
    print("append_colours_by_endpoint_conflict_count", dict(sorted(distribution.items())))
    print("candidate_assignments_radius_zero_or_one", one_recolour_total)
    print("additional_candidate_assignments_radius_two", radius_two_total)
    print("total_candidate_assignments_in_search", total)
    print("hard_candidate_cap", args.max_candidates)
    if args.inventory:
        return
    if total > args.max_candidates:
        raise SystemExit("candidate cap exceeded before search; no partial search run")
    triples = triples_538()
    if len(triples) != 72_361:
        raise AssertionError(f"unexpected old-triple count: {len(triples)}")
    checked_one, result_one = search_radius_one(words, triples)
    print("candidate_assignments_checked_radius_zero_or_one", checked_one)
    print("radius_zero_or_one_outcomes", dict(sorted(result_one.items())))
    if "witness" in result_one:
        return
    if checked_one != one_recolour_total:
        raise AssertionError(
            f"incomplete radius-one enumeration: checked {checked_one}, "
            f"expected {one_recolour_total}"
        )
    checked_two, result_two = search_radius_two(words, triples)
    print("additional_candidate_assignments_checked_radius_two", checked_two)
    print("radius_two_outcomes", dict(sorted(result_two.items())))
    if "witness" not in result_two:
        if checked_two != radius_two_total:
            raise AssertionError(
                f"incomplete radius-two enumeration: checked {checked_two}, "
                f"expected {radius_two_total}"
            )
        print("NO_WITNESS_WITH_AT_MOST_TWO_RECOLOURS")


if __name__ == "__main__":
    main()
