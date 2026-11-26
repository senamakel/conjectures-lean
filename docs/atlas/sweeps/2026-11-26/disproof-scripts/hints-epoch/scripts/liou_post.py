import struct, sys, math, glob, os
d=sys.argv[1]; files=sorted(glob.glob(d+'/c*.bin'), key=lambda f:int(os.path.basename(f)[1:-4]))
A0=0; B0=0.0
rec=struct.Struct('<3q2q16s16s16s')
def ld(b):
    # x87 80-bit long double in 16 bytes
    mant=int.from_bytes(b[:8],'little'); se=int.from_bytes(b[8:10],'little')
    s=-1 if se>>15 else 1; e=se&0x7fff
    if e==0 and mant==0: return 0.0
    return s*mant*2.0**(e-16383-63)
mx_nb=-9; mn_gap=9; mn_a=9; mx_a=-9; flags=[]
for f in files:
    data=open(f,'rb').read()
    for off in range(0,len(data),rec.size):
        st,en,A,Amin,Amax,Bb,Bmn,Bmx=rec.unpack_from(data,off)
        B=ld(Bb); Bmin=ld(Bmn); Bmax=ld(Bmx)
        if st>10**8:
            ll=math.log(math.log(st))
            ub=math.sqrt(st)*(B0+Bmax)   # upper bound of sqrt(n) b(n) (since negative)
            lb=math.sqrt(en)*(B0+Bmin)
            mx_nb=max(mx_nb,ub); mn_gap=min(mn_gap, lb+math.log(math.log(en)))
            alo=(A0+Amin)/math.sqrt(en); ahi=(A0+Amax)/(math.sqrt(st)*ll)
            mn_a=min(mn_a,alo); mx_a=max(mx_a,ahi)
            if ub>=-1 or lb<=-math.log(math.log(en)) or alo<=1 or ahi>=1: flags.append((st,en,ub,lb,alo,ahi))
        A0+=A; B0+=B
print('final n', en-1, 'A', A0, 'B', B0, 'sqrt(n)B', math.sqrt(en-1)*B0, 'A/sqrt', A0/math.sqrt(en-1))
print('bounds over n>1e8: max sqrt(n)b <=', mx_nb, ' min(sqrt(n)b+loglog) >=', mn_gap, ' min a/sqrt >=', mn_a, ' max a/(sqrt loglog) <=', mx_a)
print('flagged blocks', len(flags))
for x in flags[:20]: print(x)
