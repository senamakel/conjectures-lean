import sys
sys.path.insert(0,'.')
from nt import spf_sieve,factor
N=int(sys.argv[1])
s=spf_sieve(N+5)
isp=lambda n: n>1 and s[n]==n
exp={}; first={}; gk={}
for k in range(2,N+1):
    g=1
    for p,e in factor(k,s).items(): g*=p**min(e,exp.get(p,0))
    gk[k]=g; f=2+k//g
    for p,e in factor(f,s).items():
        exp[p]=exp.get(p,0)+e
        first.setdefault(p,k)
bad=[p for p in range(5,N) if isp(p) and not isp(p-2) and first.get(p,10**18)<=p-1]
print("bad",bad[:20])
qs=[q for q in sorted(first) if q>2]
print([(q,first[q],gk.get(q-2)) for q in qs[:30]])
print("max first[q]/q", max((first[q]/q,q) for q in qs if q< N//3))
miss=[q for q in range(3,N//3) if isp(q) and q not in first]
print("primes never dividing", miss[:20])
