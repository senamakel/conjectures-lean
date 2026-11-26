// Hong-Qiu Conjecture (cnj2): v_p(s(ap^n, ap^n-k)) for 2<=k<=a(p-1)p^{n-1}+1.
// s(N, N-k) = e_k(1,...,N-1) (unsigned Stirling first kind). Compute mod M = p^E (M < 2^63).
// Output: one line per k: p a n k v  (v = E means >= E)
// usage: hq p a n E
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128;
int main(int argc,char**argv){
  long p=atol(argv[1]), a=atol(argv[2]), n=atol(argv[3]); int E=atoi(argv[4]);
  uint64_t M=1; for(int i=0;i<E;i++) M*=p;
  long pn=1; for(int i=0;i<n;i++) pn*=p;
  long N=a*pn; long K=a*(p-1)*(pn/p)+1; if(K>N-2) K=N-2; if(argc>5 && atol(argv[5])<K) K=atol(argv[5]);
  uint64_t *e=calloc(K+1,8); e[0]=1;
  for(long x=1;x<=N-1;x++){
    uint64_t xm=x%M;
    long top = x<K? x:K;
    for(long j=top;j>=1;j--){
      e[j]=(uint64_t)(((u128)e[j-1]*xm + e[j])%M);
    }
  }
  for(long k=2;k<=K;k++){
    uint64_t v=e[k]; int val=0; while(val<E && v%p==0){v/=p;val++;}
    printf("%ld %ld %ld %ld %d\n",p,a,n,k,val);
  }
  return 0;
}
