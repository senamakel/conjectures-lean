import math, sys
N = int(sys.argv[1])
s = bytearray([1])*(N+1); s[0]=s[1]=0
for i in range(2, int(N**0.5)+1):
    if s[i]: s[i*i::i] = bytearray(len(range(i*i, N+1, i)))
P = [i for i in range(N+1) if s[i]]
print("primes:", len(P), "up to", P[-1])
print("small n (0-indexed p_n = Nat.nth Nat.Prime n):")
for n in range(0, 10):
    p, q = P[n], P[n+1]; g = q-p; L = math.log(p)
    print(f" n={n} p={p} g={g} ratio={g/L**2:.4f}  strict(<1)={g/L**2<1}  firoozCons g<L^2-L: {g < L*L-L}")
viol_sb = [n for n in range(4, len(P)-1) if (P[n+1]-P[n]) >= math.log(P[n])**2]
viol_fc = [n for n in range(4, len(P)-1) if (P[n+1]-P[n]) >= math.log(P[n])**2 - math.log(P[n])]
print("StrictBound violations n>=4:", viol_sb[:10], len(viol_sb))
print("FiroozbakhtConsequence violations n>=4:", viol_fc[:10], len(viol_fc))
best = max(range(4, len(P)-1), key=lambda n: (P[n+1]-P[n])/math.log(P[n])**2)
print("max ratio n>=4:", best, P[best], P[best+1]-P[best], (P[best+1]-P[best])/math.log(P[best])**2)
# Firoozbakht conjecture itself on range: p_{n+1}^(1/(n+2)) < p_n^(1/(n+1)), 0-indexed as fc's firoozbakhtSeq
vf = [n for n in range(len(P)-1) if math.log(P[n+1])/(n+2) >= math.log(P[n])/(n+1)]
print("Firoozbakht violations (fc indexing):", vf[:10])
# record gaps: G(x)/log^2 x just above record start
rec=0; out=[]
for n in range(len(P)-1):
    g=P[n+1]-P[n]
    if g>rec:
        rec=g; x=P[n]+1; out.append((P[n],g,g/math.log(x)**2))
print("record gaps (p, g, G(p+1)/log^2(p+1)) last 6:", [(a,b,round(c,4)) for a,b,c in out[-6:]])
print("2e^-gamma =", 2*math.exp(-0.5772156649015329))
