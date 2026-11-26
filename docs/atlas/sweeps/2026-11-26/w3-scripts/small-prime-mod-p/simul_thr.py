import math
def B(x,N): return (math.sqrt(x)+2+3/x)*(2/3)*(math.log(N)+5/3)+math.log(x)+1.6
def ok(P,Om,Nf): # Nf: N = Nf*P^2
    return (2**Om-1)*B(P,Nf*P*P) < P/2-math.sqrt(P)/20-3
def from_(Om,Nf):
    lo,hi=10.0,1e80
    for _ in range(400):
        mid=math.sqrt(lo*hi)
        if ok(mid,Om,Nf): hi=mid
        else: lo=mid
    return hi
# omega_max(m): largest k with primorial(k) <= m
pr=[]; n=2
while len(pr)<60:
    if all(n%q for q in pr): pr.append(n)
    n+=1
def wmax(m):
    prod=1;k=0
    for q in pr:
        if prod*q>m: break
        prod*=q;k+=1
    return k
print('Om : P from which sieve-free bound holds (A243847, N=2P^2)')
for Om in range(4,48,4): print(Om, '%.2e'%from_(Om,2))
# worst case closing: smallest P0 with ok for Om = wmax(P)+wmax(2P) for all P>=P0 (scan)
P=1e6; last=None
while P<1e60:
    Om=wmax(P)+wmax(2.2*P)
    if not ok(P,Om,2.2): last=P
    P*=1.05
print('sieve-free closing point (worst-case omega both moduli) ~ %.1e'%last)
