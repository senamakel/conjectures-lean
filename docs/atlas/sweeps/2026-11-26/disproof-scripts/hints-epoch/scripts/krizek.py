# A245211: find n with sum_{d|n} d*tau(d) = n*(tau(n)+1). Multiplicative DFS with exact fractions.
from fractions import Fraction as F
import sys
def isprime(n):
    if n<2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%p==0: return n==p
    d=n-1;s=0
    while d%2==0: d//=2;s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(s-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True
def u(p,e): return F(sum((i+1)*p**i for i in range(e+1)), p**e)
def nextprime(p):
    p+=1
    while not isprime(p): p+=1
    return p
sols=set(); nodes=0
MAXK=int(sys.argv[1]); MAXE=int(sys.argv[2]); PCAP=int(sys.argv[3])
def dfs(rho,T,last,fac,k):
    global nodes; nodes+=1
    # close with one more prime exponent 1: rho*(2p+1)/(2p) = 1+1/(2T)
    tgt=1+F(1,2*T); den = 2*tgt-2*rho
    if den>0:
        pv = rho/den
        if pv.denominator==1 and pv.numerator>last and isprime(pv.numerator):
            sols.add(tuple(fac+[(pv.numerator,1)]))
    if k>=MAXK: return
    if rho >= 1+F(1,2*T): return
    p=nextprime(last)
    while True:
        # minimal gain with exponent 1 is (2p+1)/(2p); if rho*that >= 1+1/(2T), stop (larger p gives smaller gain, need smaller... ) 
        # gain decreases in p, so need rho*gain(p) < target for recursion; target for recursion must allow further growth: need rho*gain < 1+1/(2T)
        g1 = F(2*p+1,2*p)
        if p>PCAP: break
        any_ok=False
        for e in range(1,MAXE+1):
            r2 = rho*u(p,e)/(e+1); T2=T*(e+1)
            if r2 == 1+F(1,T2): sols.add(tuple(fac+[(p,e)]))
            if r2 < 1+F(1,T2):
                any_ok=True
                dfs(r2,T2,p,fac+[(p,e)],k+1)
        # bound: for recursion we need rho*g1 < 1 + 1/(2T)... but closure for larger p handled exactly above. If rho*(1+1/(2p))*... further primes need at least 2 more primes; stop when even two more primes with min gain can't... use crude: stop when p > 4*k*T/(...)
        # Need ((1+1/(2T))/rho) - 1 >= gain-1 of each future prime >= 1/(2p)*(something); with remaining m primes total gain <= (1+1/p)^m
        m=MAXK-k
        if rho*(1+F(1,p))**m < 1+F(1,2*T) and p>2:  # even m primes at p can't reach: but larger p gives less; so all larger p fail to reach target... only if closure needed exactly at the end; closure is exact solve; so break
            pass
        # need rho * (gain from future) reaching ~ target; the remaining primes are >= p so gain <= (1+1/p)^m ; if that < required, deeper search futile EXCEPT last-prime closure solved exactly in child -> child requires its own primes too. Actually closure step in child handles last prime >= p. So the child needs rho*g(p)*(closing gain) = target: closing gain >1 always fine. Hence no pruning by this. Use PCAP.
        p=nextprime(p)
dfs(F(1),1,1,[],0)
for s in sorted(sols, key=lambda s: eval('*'.join(str(p**e) for p,e in s))):
    n=1
    for p,e in s: n*=p**e
    print(n, s)
print('nodes',nodes, file=sys.stderr)
