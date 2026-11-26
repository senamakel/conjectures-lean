# fraction of (k,m) pairs left "allowed" (N could be a prime with (11/N)=-1) by choosing 2n mod 44
def leg(a,p):
    a%=p
    if a==0: return 0
    return 1 if pow(a,(p-1)//2,p)==1 else -1
def chi(N):  # (11/N) for odd prime N != 11, via reciprocity: (N/11)*(-1)^((N-1)/2)
    return leg(N,11)*(1 if N%4==1 else -1)
for a in (0,2):
  for b in range(11):
    # 2n == x mod 44 with x%4==a, x%11==b
    x=[x for x in range(44) if x%4==a and x%11==b][0]
    bad=[]
    for k in range(1,11):      # k=1 special, k>=2 periodic mod 10 (rep 2..11)
      kk = k if k>1 else 1
      for m in range(10):
        ks=[kk] if kk==1 else [kk, kk+10]
        N=(x-pow(2,kk,44)-pow(3,m,44))%44
        if N%2==0 or N%11==0: continue
        if chi(N)==1: continue
        bad.append((kk,m))
    print(a,b,x,len(bad))
