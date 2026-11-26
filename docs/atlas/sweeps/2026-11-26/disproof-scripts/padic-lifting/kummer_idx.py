# find level-j indices for irregular pair (37,32): k with 37^j | B_k/k, via B_k = S_k(p^J)/p^J mod p^(2J-1)
p=37
def vp(x):
    if x==0: return 99
    v=0
    while x%p==0: x//=p; v+=1
    return v
def Bk_mod(k,J):
    PJ=p**J; mod=p**(3*J)
    s=0
    for i in range(1,PJ):
        if i%p: s=(s+pow(i,k,mod))%mod
    # terms with p|i contribute p^k*... negligible for k>=3J
    assert s%PJ==0
    return (s//PJ)%(p**(2*J-1)), 2*J-1
# check against flint for known: 284 -> 2, 37580 -> 3
for k in [32,284,37580]:
    b,prec=Bk_mod(k,3); print(k, "v(B_k/k)=", min(vp(b),prec)-vp(k))
k3=37580; step=36*p**2
for t in range(p):
    k=k3+step*t
    b,prec=Bk_mod(k,3)
    v=vp(b)-vp(k)
    if v>=4: print("level4 index", k, "v>=", v, "prec", prec); k4=k
step4=36*p**3
for t in range(p):
    k=k4+step4*t
    b,prec=Bk_mod(k,4)
    v=vp(b)-vp(k)
    if v>=5: print("level5 index", k, "v>=", v, "prec", prec)
