import struct, sys, math, glob, os
d=sys.argv[1]; files=sorted(glob.glob(d+'/c*.bin'), key=lambda f:int(os.path.basename(f)[1:-4]))
rec=struct.Struct('<3q2q16s16s16s')
def ld(b):
    mant=int.from_bytes(b[:8],'little'); se=int.from_bytes(b[8:10],'little')
    s=-1 if se>>15 else 1; e=se&0x7fff
    return 0.0 if (e==0 and mant==0) else s*mant*2.0**(e-16383-63)
A0=0;B0=0.0; cur=None
for f in files:
    data=open(f,'rb').read()
    for off in range(0,len(data),rec.size):
        st,en,A,Amin,Amax,Bb,Bmn,Bmx=rec.unpack_from(data,off)
        B=ld(Bb);Bmin=ld(Bmn);Bmax=ld(Bmx)
        dec=int(math.log10(st)*2)/2
        if cur is None or cur[0]!=dec:
            if cur: print('10^%.1f: min a/sqrt %.4f at ~%d ; max sqrt(n)b %.4f at ~%d ; min sqrt(n)b %.4f'%tuple(cur))
            cur=[dec,9,0,-9,0,9]
        alo=(A0+Amin)/math.sqrt(en); ub=math.sqrt(st)*(B0+Bmax); lb=math.sqrt(en)*(B0+Bmin)
        if alo<cur[1]: cur[1]=alo; cur[2]=st
        if ub>cur[3]: cur[3]=ub; cur[4]=st
        if lb<cur[5]: cur[5]=lb
        A0+=A;B0+=B
print('10^%.1f: min a/sqrt %.4f at ~%d ; max sqrt(n)b %.4f at ~%d ; min sqrt(n)b %.4f'%tuple(cur))
