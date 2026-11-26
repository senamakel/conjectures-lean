import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from conjf import conj
from fractions import Fraction as F
j = 8
out = []
for k in range(9, 200):
    n, r = divmod(k, j+1)
    if r in (1, j): mu = F(j, 2*(j+1)); valid = True
    else:
        mu = F(n*j//2 + r//2, k+1)
        valid = n >= ((j-r-2)/2 if r % 2 == 0 else (2*j-r-3)/2)
    if valid and mu != conj(k): out.append((k, k%9, mu, conj(k), 'H>C' if mu > conj(k) else 'H<C'))
    if k <= 68 and valid: pass
print(out)
