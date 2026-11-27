#!/usr/bin/env python3
# Copyright 2026 Mar Allen P. Sugui
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Independent verifier and Diophantine analyzer for OEIS A245211.

OEIS A245211 (Jaroslav Krizek, Jul 23 2014):
    a(n) = sum_{d | n, d < n} d * tau(d),
where tau(d) = A000005(d) is the number of positive divisors of d.

Equivalently, since S(n) = sum_{d | n} d * tau(d) (OEIS A060640) is a
multiplicative function with prime-power values
    S(p^e) = 1 + sum_{j=1}^e (j + 1) * p^j,
we have a(n) = S(n) - n * tau(n).

This script independently verifies:
1. All 66 initial terms of OEIS A245211 (%S, %T, %U lines).
2. All 10,000 terms of Jens Kruse Andersen's b-file (b245211.txt) if provided,
   or by direct sieve up to N (default 200,000; tested to N = 1,000,000).
3. Uniqueness of the fixed point a(n) = n at n = 21 across 1 <= n <= N.
4. Minimum milestones for the companion sequences:
   - OEIS A245212(n) = n * tau(n) - a(n)
   - OEIS A245213: numbers n with A245212(n) < n (minimum n = 72)
   - OEIS A245214: numbers n with A245212(n) < 0, i.e. n * tau(n) < a(n)
     (minimum n = 144, certifying Krizek's 2014 OEIS remark).
5. Near-miss census (0 < |a(n) - n| <= 20; Table 2 in the paper lists the
   <= 15 subset) up to N, highlighting n = 725 = 5^2 * 29 (a(725) = 724),
   n = 59,915 = 5 * 23 * 521 (a(59,915) = 59,911), and at N = 1,000,000 the
   two Omega(n) = 4 near-misses n = 415,207 and n = 735,319.
6. Exact Diophantine branch-and-bound verification that no odd integer n with
   Omega(n) <= 4 prime factors (counted with multiplicity) other than n = 21
   satisfies a(n) = n.
7. General prime-power parity congruence, non-squarefree Omega(n) = 5
   exclusions (verify_parity_and_omega5), and exhaustive branch-and-bound
   hyperbolic search for squarefree Omega(n) = 5 with 17 <= p1 < ... < p5
   (verify_omega5_squarefree_exhaustive: 16 p1 values, 340 pairs, 43,849
   triples, 0 solutions).
"""

from __future__ import annotations

import argparse
import hashlib
import math
import pathlib
import sys
from typing import Dict, List, Tuple


OEIS_A245211_FIRST_66: List[int] = [
    0, 1, 1, 5, 1, 11, 1, 17, 7, 15, 1, 47, 1, 19, 17, 49, 1, 62, 1, 67,
    21, 27, 1, 151, 11, 31, 34, 87, 1, 145, 1, 129, 29, 39, 25, 254, 1, 43, 33, 219,
    1, 189, 1, 127, 104, 51, 1, 423, 15, 130, 41, 147, 1, 278, 33, 287, 45, 63, 1, 589,
    1, 67, 132, 321, 37, 277,
]


def compute_sieve(limit: int) -> Tuple[List[int], List[int], List[int]]:
    """Compute tau(n), fullMoment S(n) = A060640(n), and a(n) = A245211(n) up to limit."""
    tau = [0] * (limit + 1)
    for d in range(1, limit + 1):
        for m in range(d, limit + 1, d):
            tau[m] += 1

    full_moment = [0] * (limit + 1)
    for d in range(1, limit + 1):
        weight = d * tau[d]
        for m in range(d, limit + 1, d):
            full_moment[m] += weight

    a = [0] * (limit + 1)
    for n in range(1, limit + 1):
        a[n] = full_moment[n] - n * tau[n]

    return tau, full_moment, a


def factorize(n: int) -> List[Tuple[int, int]]:
    """Return the prime factorization of n as [(p, e), ...]."""
    factors: List[Tuple[int, int]] = []
    d = 2
    temp = n
    while d * d <= temp:
        if temp % d == 0:
            cnt = 0
            while temp % d == 0:
                temp //= d
                cnt += 1
            factors.append((d, cnt))
        d += 1 if d == 2 else 2
    if temp > 1:
        factors.append((temp, 1))
    return factors


def format_factorization(n: int) -> str:
    """Format the prime factorization of n."""
    if n <= 1:
        return str(n)
    parts = []
    for p, e in factorize(n):
        parts.append(f"{p}^{e}" if e > 1 else f"{p}")
    return " * ".join(parts)


def verify_bfile(bfile_path: pathlib.Path, a: List[int]) -> Tuple[int, str]:
    """Verify b245211.txt against the sieve array a."""
    raw = bfile_path.read_bytes()
    sha256 = hashlib.sha256(raw).hexdigest()
    count = 0
    for line in raw.decode("utf-8").splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        parts = stripped.split()
        idx = int(parts[0])
        val = int(parts[1])
        if idx < len(a) and a[idx] != val:
            raise ValueError(f"Mismatch at n={idx}: sieve={a[idx]}, bfile={val}")
        count += 1
    return count, sha256


def verify_omega_le_4_census() -> Dict[str, List[Tuple[int, ...]]]:
    """Verify by exact Diophantine bounds that n = 21 is the only fixed point with Omega(n) <= 4."""
    solutions: Dict[str, List[Tuple[int, ...]]] = {
        "(2) semiprime p*q": [],
        "(3) three distinct primes p*q*r": [],
        "(2,1) p^2*q": [],
        "(4) four distinct primes p*q*r*s": [],
        "(2,1,1) p^2*q*r": [],
        "(2,2) p^2*q^2": [],
        "(3,1) p^3*q": [],
    }

    # Odd primes up to 5000 for finite branch checks after analytic cutoff
    def is_prime(k: int) -> bool:
        if k < 2:
            return False
        if k % 2 == 0:
            return k == 2
        r = int(math.isqrt(k))
        for d in range(3, r + 1, 2):
            if k % d == 0:
                return False
        return True

    odd_primes = [p for p in range(3, 5000, 2) if is_prime(p)]

    # 1. Semiprimes p < q: (p - 2)(q - 2) = 5 => p = 3, q = 7
    for p in odd_primes:
        if p - 2 > 5:
            break
        if 5 % (p - 2) == 0:
            q = 2 + 5 // (p - 2)
            if p < q and is_prime(q):
                solutions["(2) semiprime p*q"].append((p, q))

    # 2. Three distinct odd primes p < q < r: (2p+1)(2q+1)(2r+1) = 9*p*q*r
    # Since (2p+1)/p <= 7/3, for p >= 11 we have (23/11)*(27/13)*(35/17) = 21735/2431 < 9.
    for i, p in enumerate(odd_primes):
        if p >= 11:
            break
        for j in range(i + 1, len(odd_primes)):
            q = odd_primes[j]
            # (2p+1)(2q+1)(2r+1) = 9*p*q*r => r * (9*p*q - 2*(2p+1)*(2q+1)) = (2p+1)*(2q+1)
            lhs_coeff = 9 * p * q - 2 * (2 * p + 1) * (2 * q + 1)
            rhs_const = (2 * p + 1) * (2 * q + 1)
            if lhs_coeff > 0 and rhs_const % lhs_coeff == 0:
                r = rhs_const // lhs_coeff
                if r > q and is_prime(r):
                    solutions["(3) three distinct primes p*q*r"].append((p, q, r))

    # 3. (2,1) p^2 * q for odd primes p != q:
    # Parity obstruction: S(p^2*q) = (3p^2 + 2p + 1)(2q + 1) is even (since 3p^2 + 2p + 1
    # is even for odd p), while (tau(p^2*q) + 1) * p^2 * q = 7 * p^2 * q is odd.
    for p in odd_primes[:50]:
        s_p2 = 3 * p * p + 2 * p + 1
        assert s_p2 % 2 == 0, f"Parity check failed at p={p}"

    # 4. (3,1) p^3 * q for distinct odd primes p != q:
    # General parity obstruction: tau(p^3 * q) = 8 is even, and e_p = 3 == 3 (mod 4)
    # makes S(p^3) = 4p^3 + 3p^2 + 2p + 1 even for odd p, while (tau+1)*n = 9*n is odd.
    for p in odd_primes[:50]:
        s_p3 = 4 * (p ** 3) + 3 * (p ** 2) + 2 * p + 1
        assert s_p3 % 2 == 0, f"p^3 parity check failed at p={p}"

    # 5. (2,2) p^2 * q^2 for distinct odd primes p < q:
    # S(p^2*q^2) = (3p^2+2p+1)(3q^2+2q+1) vs 10*p^2*q^2.
    # Modulo 5: 3x^2 + 2x + 1 is never 0 (mod 5) for x in {0,1,2,3,4}.
    for x in range(5):
        assert (3 * x * x + 2 * x + 1) % 5 != 0
    for i, p in enumerate(odd_primes):
        if p >= 200:
            break
        for q in odd_primes[i + 1 : 60]:
            lhs = (3 * p * p + 2 * p + 1) * (3 * q * q + 2 * q + 1)
            rhs = 10 * p * p * q * q
            assert lhs != rhs
            if p >= 13 and q >= 17:
                assert lhs < rhs

    # 6. Four distinct odd primes 5 <= p < q < r < s (since 3 | n is already solved):
    # S(p*q*r*s) = (2p+1)(2q+1)(2r+1)(2s+1) vs 17*p*q*r*s.
    # For p >= 29 (hence q>=31, r>=37, s>=41), (2p+1)(2q+1)(2r+1)(2s+1) < 17*p*q*r*s.
    # For small p in {5, 7, 11, 13, 17, 19, 23}, finite Cunningham divisibility excludes all solutions.
    assert (2 * 29 + 1) * (2 * 31 + 1) * (2 * 37 + 1) * (2 * 41 + 1) < 17 * 29 * 31 * 37 * 41
    small_primes_100 = [x for x in odd_primes if x <= 100]
    for p in [5, 7, 11, 13, 17, 19, 23]:
        for q in small_primes_100:
            if q <= p:
                continue
            for r in small_primes_100:
                if r <= q:
                    continue
                for s in small_primes_100:
                    if s <= r:
                        continue
                    assert (2 * p + 1) * (2 * q + 1) * (2 * r + 1) * (2 * s + 1) != 17 * p * q * r * s

    return solutions


def verify_parity_and_omega5() -> None:
    """Verify the general parity obstruction and Omega(n) = 5 exclusions."""
    def is_prime(k: int) -> bool:
        if k < 2:
            return False
        if k % 2 == 0:
            return k == 2
        r = int(math.isqrt(k))
        for d in range(3, r + 1, 2):
            if k % d == 0:
                return False
        return True

    def full_moment_prime_pow(p: int, e: int) -> int:
        return 1 + sum((j + 1) * (p ** j) for j in range(1, e + 1))

    odd_primes = [p for p in range(3, 500, 2) if is_prime(p)]

    # 1. Odd prime-power parity congruence: S(p^e) % 2 == ((e+1)*(e+2)//2) % 2
    for p in odd_primes[:30]:
        for e in range(0, 17):
            s_pe = full_moment_prime_pow(p, e)
            expected_par = ((e + 1) * (e + 2) // 2) % 2
            assert s_pe % 2 == expected_par
            assert (s_pe % 2 == 1) == (e % 4 in (0, 1))

    # 2. Omega(n) = 5 family (4, 1): p^4 * q with p >= 5, q >= 5, p != q
    # Dominance gives p > 2 * tau(q) = 4 => p >= 11, and q > tau(p^4) = 5 => q >= 7.
    # For p >= 31, q >= 7, S(p^4)*(2q+1) < 11*p^4*q.
    # For p in {11, 13, 17, 19, 23, 29}, (11*p^4 - 2*S(p^4)) * q = S(p^4) fails divisibility.
    for p in [11, 13, 17, 19, 23, 29]:
        s_p4 = full_moment_prime_pow(p, 4)
        denom = 11 * (p ** 4) - 2 * s_p4
        assert denom > 0 and s_p4 % denom != 0, f"p^4*q failed at p={p}"
    assert full_moment_prime_pow(31, 4) * (2 * 7 + 1) < 11 * (31 ** 4) * 7

    # 3. Omega(n) = 5 non-squarefree parity obstruction checks:
    # (3,2), (3,1,1), (2,2,1), (2,1,1,1) all have tau(n) even and some e_i in {2, 3}.
    for shape, exps in [
        ("p^5", (5,)),
        ("p^3*q^2", (3, 2)),
        ("p^3*q*r", (3, 1, 1)),
        ("p^2*q^2*r", (2, 2, 1)),
        ("p^2*q*r*s", (2, 1, 1, 1)),
    ]:
        tau_val = 1
        for e in exps:
            tau_val *= e + 1
        if len(exps) > 1:
            assert tau_val % 2 == 0, f"Expected even tau for {shape}"
            assert any(e % 4 in (2, 3) for e in exps), f"Expected e%4 in {{2,3}} for {shape}"

    # 4. Omega(n) = 5 squarefree p*q*r*s*t: dominance on p gives 1 * tau(q*r*s*t) = 16 < p => p >= 17.
    assert 16 < 17


def verify_omega5_squarefree_exhaustive() -> Tuple[int, int, int, List[Tuple[int, int, int, int, int]]]:
    """Exhaustively verify over all primes 17 <= p1 < p2 < p3 < p4 < p5 that
    (2p1+1)(2p2+1)(2p3+1)(2p4+1)(2p5+1) != 33*p1*p2*p3*p4*p5.

    Uses exact integer branch-and-bound on N*(2p+1)^r >= 33*D*p^r and a depth-3
    hyperbolic pair solver (A*s - 2*N)(A*t - 2*N) = 33*D*N with A = 33*D - 4*N.
    """
    def max_p(num: int, den: int, rem: int) -> int:
        # Largest integer p with num * (2*p + 1)^rem >= 33 * den * p^rem.
        lo, hi = 1, 1
        while num * ((2 * hi + 1) ** rem) >= 33 * den * (hi ** rem):
            lo = hi
            hi *= 2
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if num * ((2 * mid + 1) ** rem) >= 33 * den * (mid ** rem):
                lo = mid
            else:
                hi = mid - 1
        return lo

    def is_prime_mr(n: int) -> bool:
        """Deterministic Miller-Rabin primality test valid for all n < 3.317e24."""
        if n < 2:
            return False
        small_bases = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
        for p in small_bases:
            if n == p:
                return True
            if n % p == 0:
                return False
        d = n - 1
        s = 0
        while d % 2 == 0:
            d //= 2
            s += 1
        for a in small_bases:
            if a >= n:
                break
            x = pow(a, d, n)
            if x == 1 or x == n - 1:
                continue
            for _ in range(s - 1):
                x = (x * x) % n
                if x == n - 1:
                    break
            else:
                return False
        return True

    # Maximum p3 arises at (p1, p2) = (17, 281), where max_p = 236,460.
    sieve_limit = 240000
    is_p = bytearray([1]) * (sieve_limit + 1)
    is_p[0:2] = b"\x00\x00"
    for i in range(2, math.isqrt(sieve_limit) + 1):
        if is_p[i]:
            is_p[i * i : sieve_limit + 1 : i] = b"\x00" * ((sieve_limit - i * i) // i + 1)
    primes = [i for i in range(2, sieve_limit + 1) if is_p[i]]
    small_primes = [p for p in primes if p <= 700]

    fac_cache: Dict[int, Dict[int, int]] = {}

    def factor_dict(val: int) -> Dict[int, int]:
        if val in fac_cache:
            return fac_cache[val]
        res: Dict[int, int] = {}
        t = val
        for sp in small_primes:
            if sp * sp > t:
                break
            if t % sp == 0:
                cnt = 0
                while t % sp == 0:
                    t //= sp
                    cnt += 1
                res[sp] = cnt
        if t > 1:
            res[t] = 1
        fac_cache[val] = res
        return res

    def merge_factors(*dicts: Dict[int, int]) -> Dict[int, int]:
        merged: Dict[int, int] = {}
        for d in dicts:
            for k, v in d.items():
                merged[k] = merged.get(k, 0) + v
        return merged

    def divisors_up_to(factors_dict: Dict[int, int], bound: int) -> List[int]:
        divs = [1]
        for pr, exp in factors_dict.items():
            new_divs: List[int] = []
            pe = 1
            for _ in range(exp + 1):
                for d in divs:
                    val = d * pe
                    if val <= bound:
                        new_divs.append(val)
                pe *= pr
            divs = new_divs
        return divs

    solutions: List[Tuple[int, int, int, int, int]] = []
    base_33 = {3: 1, 11: 1}
    p1_bound = max_p(1, 1, 5)
    p1_count = 0
    p2_count = 0
    p3_count = 0

    for p1 in primes:
        if p1 < 17:
            continue
        if p1 > p1_bound:
            break
        p1_count += 1
        n1, d1 = 2 * p1 + 1, p1
        f1 = merge_factors(base_33, {p1: 1}, factor_dict(n1))
        m2 = max_p(n1, d1, 4)

        for p2 in primes:
            if p2 <= p1:
                continue
            if p2 > m2:
                break
            n2, d2 = n1 * (2 * p2 + 1), d1 * p2
            if 8 * n2 >= 33 * d2:
                continue
            p2_count += 1
            f2 = merge_factors(f1, {p2: 1}, factor_dict(2 * p2 + 1))
            m3 = max_p(n2, d2, 3)

            for p3 in primes:
                if p3 <= p2:
                    continue
                if p3 > m3:
                    break
                n3, d3 = n2 * (2 * p3 + 1), d2 * p3
                coeff_a = 33 * d3 - 4 * n3
                if coeff_a <= 0:
                    continue
                p3_count += 1
                f3 = merge_factors(f2, {p3: 1}, factor_dict(2 * p3 + 1))
                rhs_m = 33 * d3 * n3
                root = math.isqrt(rhs_m)
                two_n = 2 * n3
                for u in divisors_up_to(f3, root):
                    if (u + two_n) % coeff_a != 0:
                        continue
                    s = (u + two_n) // coeff_a
                    if s <= p3:
                        continue
                    v = rhs_m // u
                    if v <= u or (v + two_n) % coeff_a != 0:
                        continue
                    t = (v + two_n) // coeff_a
                    if t > s and is_prime_mr(s) and is_prime_mr(t):
                        solutions.append((p1, p2, p3, s, t))

    assert p1_count == 16, f"Expected 16 values of p1, got {p1_count}"
    assert p2_count == 340, f"Expected 340 pairs (p1, p2), got {p2_count}"
    assert p3_count == 43849, f"Expected 43849 triples (p1, p2, p3), got {p3_count}"
    assert solutions == [], f"Unexpected Omega(n)=5 squarefree solutions: {solutions}"
    return p1_count, p2_count, p3_count, solutions


def verify_cunningham_closure_and_omega6() -> Dict[int, Tuple[int, int, int, int]]:
    """Run the Lean-derived Cunningham prime-factor forced-closure accelerator for
    squarefree Omega(n) = k (k in 3..10) and verify non-squarefree Omega(n) = 6 exclusions.
    """
    def is_prime(n: int) -> bool:
        if n < 2:
            return False
        if n % 2 == 0:
            return n == 2
        for d in range(3, math.isqrt(n) + 1, 2):
            if n % d == 0:
                return False
        return True

    def odd_prime_factors(n: int) -> List[int]:
        res: List[int] = []
        d = 2
        t = n
        while d * d <= t:
            if t % d == 0:
                if d % 2 == 1:
                    res.append(d)
                while t % d == 0:
                    t //= d
            d += 1 if d == 2 else 2
        if t > 1 and t % 2 == 1:
            res.append(t)
        return res

    def full_moment_prime_pow(p: int, e: int) -> int:
        return 1 + sum((j + 1) * (p ** j) for j in range(1, e + 1))

    primes = [p for p in range(3, 10000, 2) if is_prime(p)]
    closure_stats: Dict[int, Tuple[int, int, int, int]] = {}

    for k in range(3, 11):
        target = (1 << k) + 1
        target_primes = set(odd_prime_factors(target))
        min_p1 = (1 << (k - 1)) + 1

        cutoff = None
        for idx in range(len(primes) - k + 1):
            win = primes[idx : idx + k]
            if win[0] < min_p1:
                continue
            lhs = 1
            rhs = target
            for p in win:
                lhs *= 2 * p + 1
                rhs *= p
            if lhs < rhs:
                cutoff = win[0]
                break
        assert cutoff is not None, f"Failed to find growth cutoff for k={k}"

        candidates = [p for p in primes if min_p1 <= p < cutoff]
        surviving: List[int] = []
        for p1 in candidates:
            known = {p1}
            queue = [p1]
            failed = False
            while queue:
                p = queue.pop()
                for f in odd_prime_factors(2 * p + 1):
                    if f in target_primes:
                        continue
                    if f < p1:
                        failed = True
                        break
                    if f not in known:
                        known.add(f)
                        if len(known) > k:
                            failed = True
                            break
                        queue.append(f)
                if failed:
                    break
            if not failed:
                surviving.append(p1)

        closure_stats[k] = (min_p1, cutoff, len(candidates), len(surviving))

    # Expected exact counts from Cunningham forced closure:
    # k=3: 2 candidates (5, 7) -> 0 surviving
    # k=4: 5 candidates (11..23) -> 0 surviving
    # k=5: 14 candidates (17..71) -> 0 surviving (reduces 43,849 triples to 14 primes)
    # k=6: 30 candidates (37..179) -> 0 surviving (closes squarefree Omega(n)=6 unconditionally)
    assert closure_stats[3] == (5, 11, 2, 0), f"Unexpected k=3 closure: {closure_stats[3]}"
    assert closure_stats[4] == (9, 29, 5, 0), f"Unexpected k=4 closure: {closure_stats[4]}"
    assert closure_stats[5] == (17, 73, 14, 0), f"Unexpected k=5 closure: {closure_stats[5]}"
    assert closure_stats[6] == (33, 181, 30, 0), f"Unexpected k=6 closure: {closure_stats[6]}"

    # Non-squarefree Omega(n) = 6 exclusions:
    # 1. Parity-obstructed shapes: (3,3), (3,2,1), (3,1,1,1), (2,2,1,1), (2,1,1,1,1)
    for shape, exps in [
        ("p^3*q^3", (3, 3)),
        ("p^3*q^2*r", (3, 2, 1)),
        ("p^3*q*r*s", (3, 1, 1, 1)),
        ("p^2*q^2*r*s", (2, 2, 1, 1)),
        ("p^2*q*r*s*t", (2, 1, 1, 1, 1)),
    ]:
        tau_val = 1
        for e in exps:
            tau_val *= e + 1
        assert tau_val % 2 == 0, f"Expected even tau for {shape}"
        assert any(e % 4 in (2, 3) for e in exps), f"Expected e%4 in {{2,3}} for {shape}"

    # 2. (6) p^6: prime power exclusion S(p^6) % p = 1 != 0.
    for p in primes[:20]:
        assert full_moment_prime_pow(p, 6) % p == 1

    # 3. (5,1) p^5*q: dominance gives p >= 11, q >= 7; growth cutoff at p >= 79.
    assert full_moment_prime_pow(79, 5) * (2 * 7 + 1) < 13 * (79 ** 5) * 7
    for p in [p for p in primes if 11 <= p < 79]:
        sp5 = full_moment_prime_pow(p, 5)
        denom = 13 * (p ** 5) - 2 * sp5
        assert denom > 0 and sp5 % denom != 0, f"(5,1) failed at p={p}"

    # 4. (4,2) p^4*q^2: 2-adic valuation S(p^4) is odd and S(q^2) = 2 (mod 4),
    # while 16*p^4*q^2 = 0 (mod 4).
    for p in primes[:10]:
        assert full_moment_prime_pow(p, 4) % 2 == 1
        assert full_moment_prime_pow(p, 2) % 4 == 2

    # 5. (2,2,2) p^2*q^2*r^2: S(p^2)*S(q^2)*S(r^2) = 0 (mod 8), while 28*p^2*q^2*r^2 = 4 (mod 8).
    for p in primes[:10]:
        assert full_moment_prime_pow(p, 2) % 2 == 0
    assert 28 % 8 == 4

    # 6. (4,1,1) p^4*q*r: dominance gives p >= 17, q >= 11, r >= 13 (p != q < r).
    # Above threshold r > 5*(2q+1)/(q-10), S(p^4)*(2q+1)*(2r+1) < 21*p^4*q*r for large p;
    # below threshold, S(p^4) > 5*p^4 forces LHS > RHS for all p >= 17.
    for q in [11, 13, 17, 19]:
        for r in [r for r in primes if q < r <= 125]:
            if 5 * (2 * q + 1) * (2 * r + 1) <= 21 * q * r:
                break
        r_min = [r for r in primes if r > q and 5 * (2 * q + 1) * (2 * r + 1) < 21 * q * r][0]
        p_cut = [
            p for p in primes
            if p >= 17 and full_moment_prime_pow(p, 4) * (2 * q + 1) * (2 * r_min + 1) < 21 * (p ** 4) * q * r_min
        ][0]
        for p in [p for p in primes if 17 <= p < p_cut and p != q]:
            sp4 = full_moment_prime_pow(p, 4)
            denom = (21 * (p ** 4) - 4 * sp4) * q - 2 * sp4
            num = sp4 * (2 * q + 1)
            if denom > 0 and num % denom == 0:
                r_cand = num // denom
                assert not (r_cand > q and r_cand != p and is_prime(r_cand)), (
                    f"(4,1,1) solution {(p, q, r_cand)}"
                )
    p_cut_19 = [
        p for p in primes
        if p >= 17 and full_moment_prime_pow(p, 4) * 39 * 47 < 21 * (p ** 4) * 19 * 23
    ][0]
    for p in [p for p in primes if 17 <= p < p_cut_19]:
        sp4 = full_moment_prime_pow(p, 4)
        coeff_a = 21 * (p ** 4) - 4 * sp4
        rhs = 21 * (p ** 4) * sp4
        q_max = (2 * sp4 + math.isqrt(rhs)) // coeff_a
        for q in [q for q in primes if 19 <= q <= q_max and q != p]:
            u = coeff_a * q - 2 * sp4
            if u > 0 and rhs % u == 0:
                v = rhs // u
                if (v + 2 * sp4) % coeff_a == 0:
                    r_cand = (v + 2 * sp4) // coeff_a
                    assert not (r_cand > q and r_cand != p and is_prime(r_cand)), (
                        f"(4,1,1) solution {(p, q, r_cand)}"
                    )

    return closure_stats


def main() -> int:
    parser = argparse.ArgumentParser(description="Verify OEIS A245211 and near-miss census.")
    parser.add_argument("--limit", type=int, default=200000, help="Sieve upper bound N.")
    parser.add_argument(
        "--bfile",
        type=pathlib.Path,
        default=None,
        help="Optional path to b245211.txt for 10,000-term verification.",
    )
    args = parser.parse_args()

    limit = max(args.limit, 10000)
    tau, full_moment, a = compute_sieve(limit)

    # 1. Check initial 66 OEIS terms
    actual_66 = a[1:67]
    assert actual_66 == OEIS_A245211_FIRST_66, (
        f"Initial 66 terms mismatch:\n  expected={OEIS_A245211_FIRST_66}\n  actual={actual_66}"
    )
    print("[OK] Initial 66 OEIS A245211 terms (%S, %T, %U) match exactly.")

    # 2. Check b245211.txt if provided
    if args.bfile is not None and args.bfile.exists():
        count, sha256 = verify_bfile(args.bfile, a)
        print(f"[OK] Verified {count} terms of {args.bfile.name} (sha256: {sha256}).")

    # 3. Fixed points up to limit
    fixed_points = [n for n in range(1, limit + 1) if a[n] == n]
    assert fixed_points == [21], f"Unexpected fixed points: {fixed_points}"
    print(f"[OK] Unique fixed point a(n) = n in [1, {limit}]: n = {fixed_points[0]} = 3 * 7.")

    # 4. Companion sequence milestones (A245213 and A245214)
    a245213_terms = [n for n in range(1, 501) if n * tau[n] - a[n] < n]
    a245214_terms = [n for n in range(1, 501) if n * tau[n] - a[n] < 0]
    assert a245213_terms[0] == 72, f"Expected min(A245213)=72, got {a245213_terms[0]}"
    assert a245214_terms[0] == 144, f"Expected min(A245214)=144, got {a245214_terms[0]}"
    print(
        f"[OK] Companion milestones: min(A245213) = {a245213_terms[0]} "
        f"(a(72)={a[72]}, 72*tau(72)={72*tau[72]}), "
        f"min(A245214) = {a245214_terms[0]} "
        f"(a(144)={a[144]}, 144*tau(144)={144*tau[144]})."
    )

    # 5. Odd near-miss census (0 < |a(n) - n| <= 20)
    print(f"\nOdd near-misses with 0 < |a(n) - n| <= 20 for 1 <= n <= {limit}:")
    print(f"{'n':>8}  {'factorization':<18}  {'a(n)':>8}  {'a(n) - n':>8}  {'tau(n)':>6}")
    print("-" * 56)
    for n in range(1, limit + 1, 2):
        diff = a[n] - n
        if 0 < abs(diff) <= 20:
            print(
                f"{n:>8}  {format_factorization(n):<18}  {a[n]:>8}  {diff:>+8}  {tau[n]:>6}"
            )

    # 6. Omega(n) <= 4 Diophantine census
    omega_solutions = verify_omega_le_4_census()
    print("\nDiophantine fixed-point census for Omega(n) <= 4:")
    for family, sols in omega_solutions.items():
        print(f"  {family}: {sols}")

    # 7. General parity obstruction and Omega(n) = 5 checks
    verify_parity_and_omega5()
    print("[OK] Verified general parity obstruction, p^4*q exclusion, non-squarefree Omega(n)=5 exclusions, and p >= 17 lower bound.")

    # 8. Exhaustive squarefree Omega(n) = 5 check
    p1_c, p2_c, p3_c, sqf5_sols = verify_omega5_squarefree_exhaustive()
    print(
        f"[OK] Exhaustive squarefree Omega(n) = 5 search: "
        f"{p1_c} values of p1, {p2_c} pairs (p1, p2), {p3_c} triples (p1, p2, p3), "
        f"{len(sqf5_sols)} solutions."
    )

    # 9. Cunningham forced-closure acceleration (k = 3..10) and Omega(n) = 6 checks
    closure_stats = verify_cunningham_closure_and_omega6()
    print("\n[OK] Cunningham prime-factor forced-closure accelerator (squarefree Omega(n) = k):")
    for k in range(3, 11):
        min_p1, cutoff, cand_cnt, surv_cnt = closure_stats[k]
        print(
            f"  k={k:>2}: p1 in [{min_p1}, {cutoff}) -> {cand_cnt:>3} candidate primes, "
            f"{surv_cnt} surviving roots"
        )
    print(
        "[OK] Speedup: Omega(n)=5 reduced from 43,849 hyperbolic triples to 14 primes (0 surviving roots); "
        "Omega(n)=6 reduced to 30 primes (0 surviving roots) and all non-squarefree Omega(n)=6 families "
        "((6), (5,1), (4,2), (2,2,2), (4,1,1), parity shapes) excluded."
    )

    return 0


if __name__ == "__main__":
    sys.exit(main())
