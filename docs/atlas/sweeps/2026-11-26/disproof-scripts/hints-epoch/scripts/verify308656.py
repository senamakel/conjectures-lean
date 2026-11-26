import sys
from math import isqrt
def reps(n, fx):
    out=[]
    t=1
    while t*t<=n:
        u=t
        while u*u<=n:
            s=u*u; m=n-s
            # enumerate integers x with f(x)<=m
            X=isqrt(m)+2
            for x in range(-X, X+1):
                f=fx(x)
                if f<0 or f>m: continue
                r=m-f  # need r = y(3y+1)/2, y integer  <=> 24r+1 = (6y+1)^2
                D=24*r+1; z=isqrt(D)
                if z*z==D and (z%6 in (1,5)):
                    y=(z-1)//6 if z%6==1 else -(z+1)//6
                    assert y*(3*y+1)//2==r
                    out.append((s,x,y))
            u*=9
        t*=2
    return out
n=int(sys.argv[1])
forms={'x(4x+1)':lambda x:x*(4*x+1),'x(5x+2)':lambda x:x*(5*x+2),'x(5x+4)':lambda x:x*(5*x+4),'x(7x+3)/2':lambda x:x*(7*x+3)//2,'x(7x+5)/2':lambda x:x*(7*x+5)//2}
for k,f in forms.items():
    r=reps(n,f); print(k, len(r), r[:3])
