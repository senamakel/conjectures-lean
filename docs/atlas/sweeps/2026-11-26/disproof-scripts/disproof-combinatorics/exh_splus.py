"""Akbari-Kumar-Mohar-Pragada-Zhang (arXiv:2506.07264) Conjecture 1.2: connected G, m >= n+1
=> s+(G) = sum of squares of positive adjacency eigenvalues >= n. Exhaustive over geng -c n res/mod.
Prints the minimum of s+ - n over graphs with m >= n+1 (negative = counterexample)."""
import sys, subprocess
import numpy as np
geng, n, res, mod = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4]
out = subprocess.run([geng, '-cq', str(n), f'{n+1}:0', f'{res}/{mod}'], capture_output=True, check=True).stdout
lines = out.split(b'\n')[:-1]
nbits = n*(n-1)//2; nch=(nbits+5)//6
iu=[(i,j) for j in range(n) for i in range(j)]; I=np.array([p[0] for p in iu]); J=np.array([p[1] for p in iu])
best=(1e9,''); CH=200000
for s in range(0,len(lines),CH):
    L6=lines[s:s+CH]; N=len(L6)
    raw=np.frombuffer(b''.join(l[1:1+nch] for l in L6),dtype=np.uint8).reshape(N,nch)-63
    bits=np.unpackbits(raw[:,:,None],axis=2)[:,:,2:].reshape(N,-1)[:,:nbits]
    A=np.zeros((N,n,n)); A[:,I,J]=bits; A[:,J,I]=bits
    ea=np.linalg.eigvalsh(A); sp=(np.where(ea>1e-9,ea,0)**2).sum(1)
    v=sp-n; i=int(v.argmin())
    if v[i]<best[0]: best=(float(v[i]),L6[i].decode())
print(n,res,mod,len(lines),best,flush=True)
