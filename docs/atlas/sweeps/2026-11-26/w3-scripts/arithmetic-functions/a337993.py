import sys; sys.path.insert(0,'.')
from ca import *
# margin(N)/N for Lagarias: H/N + e^H log H / N - sigma/N ; H = lnN + gamma (+1/(2N) negligible for N huge; handle small N separately)
rows=[]; cnt=0; first=None; prev=None; mono_fail=[]; minratio=None
for p,k,eps,logN,logS in ca_stream(int(sys.argv[1])):
    cnt+=1
    if logN < 60: continue   # small ones done exactly elsewhere
    H=logN+G
    sN=logS.exp()
    marg = EG*H.ln() - sN          # e^H/N ~ e^gamma (1+1/(2N)) ; H/N negligible
    D_over = EG*logN.ln() - sN      # Robin margin / N
    # monotonicity of F: log F = logN + log(marg)
    logF = logN + marg.ln()
    if prev is not None:
        r=float(logF-prev)
        if minratio is None or r<minratio[0]: minratio=(r,p,k,float(logN))
        if r<=0: mono_fail.append((p,k,float(logN)))
    prev=logF
    term = marg < 1/PI2
    if term and first is None: first=(cnt,p,k,float(logN),float(marg))
    if cnt%2000==0 or (term and cnt<first[0]+3):
        print(cnt,p,k,"logN=%.4g"%float(logN),"marg/N=%.6g"%float(marg),"D/N*sqrt(logN)=%.5f"%float(D_over*logN.sqrt()),"term" if term else "")
print("count",cnt,"first CA term of A337993 beyond data:",first)
print("min log(F_{j+1}/F_j):",minratio,"failures:",mono_fail[:5])
