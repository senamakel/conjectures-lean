# primes q with o2(q) | L2 and o3(q) | L3: for each, list o2, o3, |<2,3>|
import sys, math
sys.path.insert(0,'/tmp/claude-1000/-home-ubuntu-work-personal-conjectures/e6c3a6a3-3702-43d3-8640-5f8f102b5329/scratchpad/hunt-large/py')
from sympy import primerange, n_order, divisors, factorint
L2=int(sys.argv[1]); L3=int(sys.argv[2]); B=int(sys.argv[3])
# candidates: q dividing 2^d-1 for d | L2 -> use cypari factoring of cyclotomic values would be best; here brute primes < B
import cypari2; pari=cypari2.Pari(); pari.allocatemem(2*10**9)
cand=set()
for d in divisors(L2):
    v=pari.polcyclo(d,2)
    f=pari.factor(v, 10**7)   # partial factorisation, small factors
    for p in f[0]:
        p=int(p)
        if p<B and pari.isprime(p): cand.add(p)
out=[]
for q in sorted(cand):
    if q in (2,3): continue
    o2=n_order(2,q); o3=n_order(3,q)
    if L2%o2 or L3%o3: continue
    # |<2,3>| = o2*o3/|<2> cap <3>| ; <2> cap <3> has order gcd-structure: compute directly via subgroup of cyclic group
    # in cyclic group of order q-1: <2> = index (q-1)/o2 subgroup; <2,3> = subgroup of order lcm(o2,o3)
    g=o2*o3//math.gcd(o2,o3)
    out.append((q,o2,o3,g))
s=sum(1/g for q,o2,o3,g in out)
print(len(out),'sum 1/g =',round(s,4))
for t in out[:80]: print(t)
