import sympy as sp
from fractions import Fraction as F
t,v=sp.symbols('t v',positive=True)
R=sp.Rational
GD=R(1099511627776); D0=R(1048576)
a1=R(4252035564110250469740648)/(GD*D0); a1e=R(760852761666848834989)/(D0*D0)
a2p=R(463585232095674405339284)/(GD*D0); a2pe=R(5587348473184294079485)/(D0*D0)
a2n=R(44601726036410213767724532)/(GD*D0)
V0=(R(13182834354755211737)+20625534903171+15568535259931704074)/GD
Ve=(R(72271341813760)+639958350772+1207134689330252)/D0
l2u=R('0.6931471808'); l2l=R('0.6931471803')
S=R(11989718)
piL=R('3.141592')  # pi lower: 1/(0.055 pi t) upper uses pi lower
piU=R('3.141593')
L=R('2.89')
u=29*t**2; u3=R('3.3')*(t-12)
rU=(1+R('0.024')/t)/(R('0.055')*piL*t)
hU=R('0.0019')/t
XU=(t/2-L+R('1.063')+R('0.05')/t)*(a1+hU*a1e)+l2u/4*(a2p+hU*a2pe)-l2l/4*a2n
M=rU*XU
EV=2*(t+7)*(V0+hU*Ve)/u
# C = 2*740648/120 * pi*rU*1.005*((t/2+5)/pi+0.31) = 2*740648/120*rU*1.005*((t/2+5)+0.31 pi)
C=2*R(740648)/120*rU*R('1.005')*((t/2+5)+R('0.31')*piU)
BT=R(18838744)*(t+R('0.001'))/(64*(t/4+L/2-R('2.886')-R('0.01')))
PP=131072*(t+R('0.001'))*(R('128.1')/u+R('147.4')/(u3*t))
Err=R(11)
g=S-M-EV-C-BT-PP-Err
for tv in [18,19,20,30,100,1000,10**6]:
    print(tv, float(g.subs(t,tv)))
num,den=sp.fraction(sp.together(g))
P=sp.Poly(sp.expand(num.subs(t,v+18)),v)
print([float(c) for c in P.all_coeffs()])
print(sp.factor_list(den))
