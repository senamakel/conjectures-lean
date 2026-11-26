// A245211: g(n)=sum_{d|n} d tau(d) == n(tau(n)+1) ?  A245212: 2 n tau(n) - g(n) == sigma(n) ?
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#define SEG (1<<22)
typedef unsigned __int128 u128;
int main(int argc,char**argv){ uint64_t lo=strtoull(argv[1],0,10),hi=strtoull(argv[2],0,10);
  uint64_t sq=(uint64_t)sqrtl((long double)hi)+2; char*isc=calloc(sq+1,1); uint32_t*pr=malloc(4*(sq/2+10)); int np=0;
  for(uint64_t i=2;i<=sq;i++) if(!isc[i]){pr[np++]=i; for(uint64_t j=i*i;j<=sq;j+=i) isc[j]=1;}
  uint64_t*rem=malloc(8*SEG); u128*g=malloc(16*SEG),*sg=malloc(16*SEG); uint32_t*tau=malloc(4*SEG);
  for(uint64_t L=lo;L<hi;L+=SEG){ uint64_t n=SEG; if(L+n>hi)n=hi-L;
    for(uint64_t i=0;i<n;i++){rem[i]=L+i;g[i]=1;sg[i]=1;tau[i]=1;}
    for(int k=0;k<np;k++){ uint64_t p=pr[k]; if(p*p>=L+n)break; uint64_t s=((L+p-1)/p)*p;
      for(uint64_t m=s;m<L+n;m+=p){ uint64_t i=m-L; int e=0; do{rem[i]/=p;e++;}while(rem[i]%p==0);
        u128 gp=0,sp=0,pw=1; for(int j=0;j<=e;j++){ gp+=pw*(j+1); sp+=pw; pw*=p; } g[i]*=gp; sg[i]*=sp; tau[i]*=(e+1); } }
    for(uint64_t i=0;i<n;i++){ uint64_t N=L+i; if(N<2) continue; u128 G=g[i],Sg=sg[i]; uint32_t T=tau[i];
      if(rem[i]>1){ u128 p=rem[i]; G*=(1+2*p); Sg*=(1+p); T*=2; }
      if(G==(u128)N*(T+1)) printf("A245211 hit n=%lu\n",N);
      if((u128)2*N*T == G+Sg && (N&(N-1))) printf("A245212 hit n=%lu\n",N); } }
  fprintf(stderr,"done %lu %lu\n",lo,hi); }
