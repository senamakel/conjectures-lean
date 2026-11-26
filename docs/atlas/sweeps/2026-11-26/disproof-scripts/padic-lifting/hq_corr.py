import sys
sys.argv=[sys.argv[0],'12']
exec(open('hq_check.py').read().split("E = int")[0])
kj={2:284,3:37580,4:1072544,5:55777784}
def vB(ke):  # v_37(B_ke/ke) for ke = 32 mod 36
    v=1
    for j,kk in kj.items():
        if (ke-kk)%(36*37**(j-1))==0: v+=1
    return v
bad=0;tot=0
for line in sys.stdin:
    p,a,n,k,v=map(int,line.split())
    pr=pred(p,a,n,k)
    ke=k-(k&1)
    if ke%36==32: pr+= vB(ke)-1
    if v>=12: v=None
    tot+=1
    if v is not None and v!=pr:
        bad+=1
        if bad<10: print("still off",n,k,v,pr)
print("corrected formula: total",tot,"off",bad)
