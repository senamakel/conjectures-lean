#!/usr/bin/env python3
"""Bound extensions of the pinned 538-word corpus by disjoint witnesses."""

from __future__ import annotations

import gzip
import hashlib
import urllib.request
from collections import defaultdict

EVOLVED_URL = (
    "https://raw.githubusercontent.com/jeffchen006/Schur-Number-6/"
    "5148494527df1e61e199bad21018e9a0bebbf0e0/evolve538/evolved_words.txt.gz"
)
EVOLVED_SHA256 = "bbcb8f39937278c34426caed972274493f410021d0bf40f78e0730ebe0936d19"
PUBLISHED = {
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
MAX_INCIDENCE_VISITS = 50_000_000


def fetch(url: str, expected: str) -> bytes:
    with urllib.request.urlopen(url, timeout=60) as response:
        data = response.read()
    digest = hashlib.sha256(data).hexdigest()
    if digest != expected:
        raise RuntimeError(f"pinned input digest mismatch: {url}: {digest}")
    return data


def canonical(text: str) -> tuple[int, ...]:
    names: dict[str, int] = {}
    result = []
    for char in text:
        names.setdefault(char, len(names))
        result.append(names[char])
    if len(result) != N or len(names) > K:
        raise ValueError("expected a 538-position word with at most six colors")
    return tuple(result)


def triples() -> list[tuple[int, int, int]]:
    return [
        (x, y, x + y)
        for x in range(1, N // 2 + 1)
        for y in range(x, N + 1 - x)
    ]


def incidence_index(ts: list[tuple[int, int, int]]) -> list[list[int]]:
    result = [[] for _ in range(N + 1)]
    for ti, triple in enumerate(ts):
        for position in set(triple):
            result[position].append(ti)
    return result


def sum_free(word: tuple[int, ...], ts: list[tuple[int, int, int]]) -> bool:
    return all(not (word[x - 1] == word[y - 1] == word[z - 1]) for x, y, z in ts)


def load_corpus() -> dict[tuple[int, ...], set[str]]:
    raw = gzip.decompress(fetch(EVOLVED_URL, EVOLVED_SHA256)).decode("ascii")
    corpus: dict[tuple[int, ...], set[str]] = {}
    raw_538 = 0
    for line in raw.splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        ident, size, text = line.split()
        if int(size) == N:
            raw_538 += 1
            corpus.setdefault(canonical(text), set()).add(ident)
    if raw_538 != 1021 or len(corpus) != 995:
        raise RuntimeError(f"unexpected evolved corpus counts {raw_538}, {len(corpus)}")
    for label, (url, digest) in PUBLISHED.items():
        word = canonical(fetch(url, digest).decode("ascii").strip())
        if word in corpus:
            raise RuntimeError(f"published baseline {label} unexpectedly already present")
        corpus[word] = {label}
    if len(corpus) != 997:
        raise RuntimeError(f"unexpected total normalized corpus size {len(corpus)}")
    return corpus


def conflicts(word: tuple[int, ...], colour: int) -> tuple[tuple[int, int], ...]:
    return tuple(
        (a, 539 - a)
        for a in range(1, 270)
        if word[a - 1] == word[538 - a] == colour
    )


def option_witness(
    word: tuple[int, ...],
    position: int,
    colour: int,
    forbidden_positions: set[int],
    ts: list[tuple[int, int, int]],
    incident: list[list[int]],
) -> tuple[tuple[int, int, int], tuple[int, ...]] | None:
    """Lexicographically first triple witness with other positions outside P."""
    for ti in incident[position]:
        triple = ts[ti]
        others = tuple(sorted({p for p in triple if p != position}))
        if any(p in forbidden_positions for p in others):
            continue
        if all(word[p - 1] == colour for p in others):
            if all(colour == word[p - 1] for p in triple if p == position):
                return triple, others
    return None


def analyze(
    word: tuple[int, ...],
    append_colour: int,
    pairs: tuple[tuple[int, int], ...],
    ts: list[tuple[int, int, int]],
    incident: list[list[int]],
) -> tuple[list[tuple[tuple[int, int], tuple[int, ...]]], int]:
    support = {position for pair in pairs for position in pair}
    qualifying = []
    visits = 0
    for pair in pairs:
        chosen_witnesses: list[tuple[int, int, int]] = []
        witness_positions: set[int] = set()
        robust = True
        for endpoint in pair:
            for colour in range(K):
                if colour == append_colour:
                    continue
                visits += len(incident[endpoint])
                if visits > MAX_INCIDENCE_VISITS:
                    raise RuntimeError(
                        f"witness incidence cap {MAX_INCIDENCE_VISITS} exceeded"
                    )
                found = option_witness(
                    word, endpoint, colour, support, ts, incident
                )
                if found is None:
                    robust = False
                else:
                    triple, other_positions = found
                    chosen_witnesses.append(triple)
                    witness_positions.update(other_positions)
        if robust:
            if not witness_positions or witness_positions & support:
                raise AssertionError("robust union must be nonempty and outside support")
            qualifying.append((pair, tuple(sorted(witness_positions))))
    return qualifying, visits


def greedy_pack(
    candidates: list[tuple[tuple[int, int], tuple[int, ...]]]
) -> list[tuple[tuple[int, int], tuple[int, ...]]]:
    packed = []
    used: set[int] = set()
    for item in sorted(candidates, key=lambda x: (len(x[1]), x[0])):
        positions = set(item[1])
        if not positions & used:
            packed.append(item)
            used.update(positions)
    return packed


def main() -> None:
    corpus = load_corpus()
    ts = triples()
    if len(ts) != 72_361:
        raise RuntimeError(f"unexpected triple count {len(ts)}")
    incident = incidence_index(ts)
    best_counts: list[tuple[int, str, int]] = []
    low = []
    for word, labels in sorted(corpus.items(), key=lambda item: sorted(item[1])):
        if not sum_free(word, ts):
            raise RuntimeError(f"input is not sum-free: {sorted(labels)}")
        for colour in range(K):
            pairs = conflicts(word, colour)
            m = len(pairs)
            best_counts.append((m, sorted(labels)[0], colour))
            if m <= 29:
                low.append((word, labels, colour, pairs))

    print("evolved_raw_words", 1021)
    print("evolved_renaming_classes", 995)
    print("normalized_words_including_published_baselines", len(corpus))
    print("word_append_color_pairs", len(corpus) * K)
    print("cases_with_m_le_29", len(low))
    print("minimum_m", min(best_counts))

    incidence_total = sum(
        len(incident[position])
        for word, labels, colour, pairs in low
        for pair in pairs
        for position in pair
        for _alt_colour in range(K - 1)
    )
    print("precomputed_witness_incidence_visits", incidence_total)
    print("witness_incidence_cap", MAX_INCIDENCE_VISITS)
    if incidence_total > MAX_INCIDENCE_VISITS:
        print("STOP_CAP_EXCEEDED_NO_WITNESS_ENUMERATION")
        return

    cases = []
    total_visits = 0
    for word, labels, colour, pairs in low:
        witnesses, visits = analyze(word, colour, pairs, ts, incident)
        total_visits += visits
        packed = greedy_pack(witnesses)
        q = len(packed)
        bound = len(pairs) + q
        cases.append((bound, len(pairs), q, sorted(labels)[0], colour, pairs, packed))
    print("witness_enumeration_visits", total_visits)
    print("bound_distribution_m_q", end=" ")
    from collections import Counter
    print(dict(sorted(Counter((m, q) for _, m, q, *_ in cases).items())))
    print("cases_below_30_lower_bound", sum(bound < 30 for bound, *_ in cases))
    print("minimum_combined_bound", min(bound for bound, *_ in cases))
    print("worst_cases")
    for bound, m, q, label, colour, pairs, packed in sorted(cases)[:20]:
        print({
            "bound": bound,
            "m": m,
            "q": q,
            "word": label,
            "append_colour": colour,
            "conflict_pairs": pairs,
            "packed_unions": packed,
        })
    if any(bound < 30 for bound, *_ in cases):
        print("CONCLUSION: this packing does not exclude distance 29 for every pinned input")
    else:
        print("CONCLUSION: every pinned input needs at least 30 old-position changes")


if __name__ == "__main__":
    main()
