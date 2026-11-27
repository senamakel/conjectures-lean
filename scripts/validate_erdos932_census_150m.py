#!/usr/bin/env python3
"""Independent, exact validation of every row in the A387864 extension table.

This deliberately uses trial division for primality and factorization, separate
from the byte-array Eratosthenes scan that produced the census.
"""

import csv
import sys


def is_prime_trial(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def largest_prime_factor_trial(n: int) -> int:
    assert n >= 2
    largest = 1
    d = 2
    while d * d <= n:
        if n % d == 0:
            largest = d
            while n % d == 0:
                n //= d
        d = 3 if d == 2 else d + 2
    return max(largest, n)


def main(path: str) -> None:
    with open(path, newline="", encoding="ascii") as f:
        rows = list(csv.DictReader(f, delimiter="\t"))
    assert len(rows) == 1197, len(rows)
    previous_r = 6_386_830
    for row in rows:
        r, p, q, gap, n1, n2 = (int(row[k]) for k in
                               ("r", "p_r", "p_next", "gap", "n1", "n2"))
        assert r > previous_r and q - p == gap
        assert p <= 150_000_000
        assert is_prime_trial(p) and is_prime_trial(q), (r, p, q)
        # Exact trial-division proof that no prime lies strictly inside (p,q).
        assert all(not is_prime_trial(n) for n in range(p + 1, q)), (r, p, q)
        assert p < n1 < n2 < q
        lpf1 = largest_prime_factor_trial(n1)
        lpf2 = largest_prime_factor_trial(n2)
        assert lpf1 < gap and lpf2 < gap, (r, gap, n1, lpf1, n2, lpf2)
        previous_r = r
    print(f"exactly_validated_extension_rows={len(rows)}")
    print(f"last_r={previous_r}")
    print(f"last_gap={rows[-1]['p_r']} {rows[-1]['p_next']}")
    print(f"last_hits={rows[-1]['n1']} {rows[-1]['n2']}")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit(f"usage: {sys.argv[0]} EXTENSION_TSV")
    main(sys.argv[1])
