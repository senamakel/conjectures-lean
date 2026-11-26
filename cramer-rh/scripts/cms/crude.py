from mpmath import mp, mpf, log, sqrt, pi, exp
mp.dps=30
c=mpf(22)/25; GD=mpf(1099511627776); D0=mpf(1048576)
a1=mpf(4252035564110250469740648)/(GD*D0); a1e=mpf(760852761666848834989)/(D0*D0)
a2p=mpf(463585232095674405339284)/(GD*D0); a2pe=mpf(5587348473184294079485)/(D0*D0)
a2n=mpf(44601726036410213767724532)/(GD*D0); a2ne=mpf(1037532018656752372080)/(D0*D0)
V0=(mpf(13182834354755211737)+20625534903171+15568535259931704074)/GD
Ve=(mpf(72271341813760)+639958350772+1207134689330252)/D0
l2u=mpf('0.6931471808'); l2l=mpf('0.6931471803')
S=mpf(11989718)
def bounds(t):
    u=exp(t/2); q=c*u*t
    yL=q/128-mpf('1.02'); yU=q/128
    mU=u**2+1+q/2; mL=u**2
    rhoU=sqrt(mU)/(8*yL)
    hU=8*yU/mL; hL=8*yL/mU
    LamU=log(mU/(16*pi*yL))
    M=(1/pi)*rhoU*(LamU*(a1+hU*a1e)+l2u/4*(a2p+hU*a2pe)-l2l/4*(a2n+0*a2ne))
    TU=120/hL
    Ero=mpf('0.137')*log(TU)+mpf('0.443')*log(log(TU))+mpf('1.588')
    EV=2/sqrt(mL)*Ero*(V0+hU*Ve)
    tau=(log(TU)-log(2*pi))/pi+mpf('2.613')/(120/hU)+mpf('0.3')*log(TU)/(120/hU)
    C=(2*740648/mpf(120))*(1+16*hU)**mpf(1.5)*tau*rhoU
    R=sqrt(2*yL/3); W=log(R-1)+mpf(1)/2-log(2)
    bU=mU+128*yU; aL=mL+64*yL-128*yU
    BT=18838744*log(bU)/(64*W)
    PP=8388608*log(bU)*((sqrt(bU)-sqrt(aL)+1)+(bU**(mpf(1)/3)+1))/(64*yL)
    Err=1.5*740648/(64*yL**2)
    tot=M+EV+C+BT+PP+Err
    return (S-tot)/2**20, [float(v/2**20) for v in (M,EV,C,BT,PP,Err)]
for t in [18.42,19,20,22,25,30,40,60,100,200,500,1000,1e4,1e5]:
    mg,parts=bounds(mpf(t)); print(t, float(mg), [round(p,4) for p in parts])
