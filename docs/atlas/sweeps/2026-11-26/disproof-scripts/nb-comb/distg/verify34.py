# Independent verification for Carraher-Galvin-Hartke-Radcliffe-Stolee (arXiv:1401.7183v1) Conjecture 34:
#   alpha({1,8,k}) = piecewise formula, k>8, k not in {9,10,14,16,18,23,25,32}.
# (1) Lower bounds: explicit periodic independent sets (checked by brute force on Z/P, no kappa code).
# (2) Exact alpha for small k: maximum cycle mean (Karp) over the de Bruijn-type automaton of
#     D-avoiding binary words of length max(D); alpha(D) equals the max cycle mean (every avoiding
#     sequence is a walk; every cycle gives a periodic avoiding set).
from fractions import Fraction as Fr
import sys

def conj34(k):
    r = k % 9
    return {0: Fr(4*k, 9*k+9), 1: Fr(4, 9), 2: Fr(4*k+1, 9*k+9), 3: Fr(4*k+24, 9*k+72),
            4: Fr(4*k+2, 9*k+9), 5: Fr(4*k+1, 9*k+16), 6: Fr(4*k+3, 9*k+9),
            7: Fr(4*k-1, 9*k+9), 8: Fr(4, 9)}[r]

def periodic_set_density(D, P, a, h):
    S = [x for x in range(P) if (a*x) % P < h]
    Sset = set(S)
    for x in S:
        for d in D:
            if (x + d) % P in Sset:
                return None  # not independent
    return Fr(len(S), P)

def exact_alpha(D):
    # states: words w of length L=max(D) (bit i = position i), with no two ones at distance in D inside
    L = max(D)
    def ok_word(w):
        for i in range(L):
            if (w >> i) & 1:
                for d in D:
                    if i + d < L and (w >> (i+d)) & 1:
                        return False
        return True
    states = [w for w in range(1 << L) if ok_word(w)]
    idx = {w: i for i, w in enumerate(states)}
    n = len(states)
    # transition: shift out bit 0, append new bit b at position L-1 ; new bit conflicts with bit L-1-d+? :
    # positions after shift: old bit j moves to j-1; new bit at L-1 ; conflict if old bit at L-d (now L-1-d) is 1, i.e. distance d.
    adj = [[] for _ in range(n)]
    for w in states:
        for b in (0, 1):
            nw = (w >> 1) | (b << (L-1))
            if b:
                # new bit sits at absolute position L of the old word; it conflicts with old bit L-d
                if any((w >> (L - d)) & 1 for d in D):
                    continue
            if nw in idx:
                adj[idx[w]].append((idx[nw], b))
    # Karp max mean cycle with integer DP: F[k][v] = max weight of walk of length k ending at v (from any start)
    NEG = -10**9
    F = [[0]*n]
    for step in range(1, n+1):
        prev = F[-1]; cur = [NEG]*n
        for u in range(n):
            pu = prev[u]
            if pu == NEG: continue
            for v, wgt in adj[u]:
                if pu + wgt > cur[v]: cur[v] = pu + wgt
        F.append(cur)
    best = None
    for v in range(n):
        if F[n][v] == NEG: continue
        worst = None
        for kk in range(n):
            if F[kk][v] == NEG: continue
            val = Fr(F[n][v] - F[kk][v], n - kk)
            if worst is None or val < worst: worst = val
        if worst is not None and (best is None or worst > best): best = worst
    return best, n

if __name__ == "__main__":
    # (1) lower-bound witnesses: k=50 (k%9=5) and k=57 (k%9=3), plus the general branches checked up to K
    for k, P, a, h in [(50, 51, 22, 22), (57, 58, 25, 25)]:
        dens = periodic_set_density((1, 8, k), P, a, h)
        c = conj34(k)
        print(f"k={k}: periodic set {{x: {a}x mod {P} < {h}}} independent, density {dens} ; Conjecture 34 value {c} ; excess {dens - c}")
    K = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    viol = []
    for k in range(50, K+1):
        r = k % 9
        if r == 5:
            P = k+1; h = (4*P-6)//9; assert (4*P-6) % 9 == 0
        elif r == 3 and k >= 57:
            P = k+1; h = (4*P-7)//9; assert (4*P-7) % 9 == 0
        else:
            continue
        dens = None
        for a in (h, h+1, P-h):
            dens = periodic_set_density((1, 8, k), P, a, h)
            if dens is not None: break
        if dens is not None and dens > conj34(k):
            viol.append(k)
    print(f"lower-bound violations of Conj 34 for 50<=k<={K}: {len(viol)} values; first {viol[:12]}")
    # (2) exact alpha for small k
    for k in range(11, 20):
        al, n = exact_alpha((1, 8, k))
        excluded = k in (9, 10, 14, 16, 18, 23, 25, 32)
        print(f"k={k}: exact alpha={al} (states {n}); Conj 34 value {conj34(k)}{' [excluded]' if excluded else ''}{'  <-- CONTRADICTS' if (not excluded and al != conj34(k)) else ''}")
