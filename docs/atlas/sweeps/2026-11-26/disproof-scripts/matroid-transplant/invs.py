from flags import *
from compalg import *
from math import comb
def build(nmax=9):
    A=Alg(nmax)
    chi=A.chi(); P=A.right_kls(chi); Q=A.inverse(A.sgn(P)); Z=A.conv(A.tpow(),P)
    mu=A.mobius()
    Tmu={c:(T**sum(c))*p for c,p in mu.items()}
    Yhat=A.conv(A.sgn(Q),Tmu)
    Y={c:(p if sum(c)%2==0 else -p) for c,p in Yhat.items()}
    return dict(A=A,chi=chi,P=P,Q=Q,Z=Z,Y=Y)
