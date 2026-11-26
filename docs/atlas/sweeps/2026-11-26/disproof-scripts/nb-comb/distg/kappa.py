# kappa(D)=max_t min_{d in D} ||d t|| (Haralambis / lonely-runner value), exact; kappa(D) <= alpha(D) always
# (rational t=a/P gives the periodic independent set {x: a x mod P in [0,h)} of density h/P).
# Compare with Carraher-Galvin-Hartke-Radcliffe-Stolee (arXiv:1401.7183) Conjectures 26, 29, 33, 34.
from fractions import Fraction as Fr
import sys
def kappa(D):
    best=Fr(0); bt=None
    qs=set()
    for a in D:
        qs.add(2*a)
        for b in D:
            if a<b: qs.add(a+b); qs.add(b-a)
    for q in qs:
        for j in range(0,q//2+1):
            # t=j/q ; value = min_d dist(d*j mod q)/q
            v=min(min((d*j)%q, q-(d*j)%q) for d in D)
            if v*best.denominator > best.numerator*q:
                best=Fr(v,q); bt=Fr(j,q)
    return best,bt
def conj33(k):
    r=k%7
    return {0:Fr(3*k,7*k+7),1:Fr(3,7),2:Fr(3*k+1,7*k+7),3:Fr(3*k-2,7*k+7),4:Fr(3*k+2,7*k+7),5:Fr(3*k-1,7*k+7),6:Fr(3,7)}[r]
def conj34(k):
    r=k%9
    return {0:Fr(4*k,9*k+9),1:Fr(4,9),2:Fr(4*k+1,9*k+9),3:Fr(4*k+24,9*k+72),4:Fr(4*k+2,9*k+9),5:Fr(4*k+1,9*k+16),6:Fr(4*k+3,9*k+9),7:Fr(4*k-1,9*k+9),8:Fr(4,9)}[r]
if __name__=="__main__":
    which=sys.argv[1]; lo=int(sys.argv[2]); hi=int(sys.argv[3])
    for k in range(lo,hi+1):
        if which=="33":
            if k<=6 or k in (7,10,12,17): continue
            D=(1,6,k); c=conj33(k)
        elif which=="34":
            if k<=8 or k in (9,10,14,16,18,23,25,32): continue
            D=(1,8,k); c=conj34(k)
        kp,t=kappa(D)
        tag = "KAPPA>CONJ (refutes)" if kp>c else ("kappa<conj" if kp<c else "eq")
        if tag!="eq": print(which,k,k%(7 if which=='33' else 9),"kappa=",kp,"t=",t,"conj=",c,tag,flush=True)
    print("done",which,lo,hi)
