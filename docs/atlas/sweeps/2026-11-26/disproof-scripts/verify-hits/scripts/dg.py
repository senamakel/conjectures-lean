import sys
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from conjf import conj
from fractions import Fraction as F
def indep_periodic(A, P, S):
    A = set(a % P for a in A)
    return all((a + d) % P not in A for a in A for d in S)
# witness
for k, h, c in [(50,22,22),(59,26,26),(68,30,30),(57,25,25)]:
    P = k+1; A = [x for x in range(P) if (h*x) % P < c]
    print(k, "indep:", indep_periodic(A, P, {1,8,k}), "density", F(len(A),P), "conj", conj(k), ">" if F(len(A),P) > conj(k) else "<=")
# best cyclic rotation sets h*x mod P < c for P in a range, k in 9..130
hits = []
for k in range(9, 131):
    best = F(0)
    for P in range(2, 2*k+20):
        for h in range(1, P):
            for c in range(P//2, 0, -1):
                if F(c,P) <= best: break
                A = [x for x in range(P) if (h*x) % P < c]
                if indep_periodic(A, P, {1,8,k}): best = F(c,P); break
    if best > conj(k): hits.append((k, k%9, best, conj(k)))
print("k where a 'h x mod P < c' set beats the formula:", hits)
