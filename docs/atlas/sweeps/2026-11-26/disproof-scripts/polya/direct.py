import sys
N=int(sys.argv[1])
mu=[1]*(N+1); lam=[1]*(N+1); spf=list(range(N+1))
for p in range(2,int(N**.5)+1):
    if spf[p]==p:
        for j in range(p*p,N+1,p):
            if spf[j]==j: spf[j]=p
M=0;L=0
for n in range(1,N+1):
    m=n; e=0; mm=1; ll=1
    while m>1:
        p=spf[m]; k=0
        while m%p==0: m//=p; k+=1
        mm = 0 if k>1 else -mm; ll*= (-1)**k
    M+=mm; L+=ll
print(N,M,L)
