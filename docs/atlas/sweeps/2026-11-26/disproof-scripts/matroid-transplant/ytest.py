from lattices import *
from invs import *
from fractions import Fraction as Fr
I=build(9)
def coeffs(name,L):
    n,al=L; p=evaluate(I[name],al,n); co=[int(x) for x in p.coeffs()]; return co+[0]*(n+1-len(co))
def ycj(L):
    y=coeffs('Y',L); n=L[0]
    return [y[0]]+[y[j]-y[j-1] for j in range(1,n//2+1)]
def lcmin(co):
    r=[Fr(co[i]**2,co[i-1]*co[i+1]) for i in range(1,len(co)-1) if co[i-1]*co[i+1]>0]
    return min(r) if r else None
if __name__=="__main__":
    assert prod(boolean(2),boolean(3))[1]==boolean(5)[1]
    assert prod(pg(3,3),boolean(2))[1]==Dlat(3,2,3)[1]
    print("prod ok")
    for s in [3,5,10,30,100]:
        for m in [3,4,5]:
            L=line(s)
            for _ in range(m-1): L=prod(L,line(s))
            for r in range(4,min(2*m,9)):
                T=truncate(L,r); c=ycj(T)
                print('lines',s,'x',m,'trunc',r,'c_j',c,'Ylc %.5f'%float(lcmin(coeffs('Y',T))))
