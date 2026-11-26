// A000224 Ordowski: n>1, n^2 == 1 mod a(n)(a(n)-1) iff n odd prime. search composite n in [lo,hi)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#define SEG (1<<22)
typedef unsigned __int128 u128;
static uint64_t spp(uint64_t p,int e){ // squares mod p^e
  u128 pe1=1; for(int i=0;i<e+1;i++) pe1*=p;
  if(p==2){ u128 q=pe1/2; return (uint64_t)((e%2==0)? (q+10)/6 : (q+11)/6); }
  return (uint64_t)((e%2==0)? (pe1+p+2)/(2*(p+1)) : (pe1+2*p+1)/(2*(p+1)));
}
static uint64_t brute(uint64_t n){ char*s=calloc(n,1); uint64_t c=0; for(uint64_t x=0;x<n;x++){uint64_t r=x*x%n; if(!s[r]){s[r]=1;c++;}} free(s); return c;}
int main(int argc,char**argv){
  uint64_t lo=strtoull(argv[1],0,10), hi=strtoull(argv[2],0,10);
  if(argc>3){ // selftest
    for(uint64_t n=1;n<3000;n++){ uint64_t m=n,a=1; for(uint64_t p=2;p<=m;p++){int e=0; while(m%p==0){m/=p;e++;} if(e)a*=spp(p,e);} if(a!=brute(n)){printf("mismatch %lu %lu %lu\n",n,a,brute(n));return 1;} }
    printf("selftest ok\n"); return 0; }
  uint64_t sq=(uint64_t)sqrtl((long double)hi)+2;
  char*isc=calloc(sq+1,1); uint32_t*pr=malloc(4*(sq/2+10)); int np=0;
  for(uint64_t i=2;i<=sq;i++) if(!isc[i]){pr[np++]=i; for(uint64_t j=i*i;j<=sq;j+=i) isc[j]=1;}
  uint64_t*rem=malloc(8*SEG),*a=malloc(8*SEG); unsigned char*comp=malloc(SEG);
  long hits=0;
  for(uint64_t L=lo;L<hi;L+=SEG){ uint64_t n=SEG; if(L+n>hi)n=hi-L;
    for(uint64_t i=0;i<n;i++){rem[i]=L+i;a[i]=1;comp[i]=0;}
    for(int k=0;k<np;k++){ uint64_t p=pr[k]; if(p*p>=L+n)break; uint64_t s=((L+p-1)/p)*p;
      for(uint64_t m=s;m<L+n;m+=p){ uint64_t i=m-L; int e=0; do{rem[i]/=p;e++;}while(rem[i]%p==0); a[i]*=spp(p,e); if(m!=p) comp[i]=1; } }
    for(uint64_t i=0;i<n;i++){ uint64_t N=L+i; if(N<2)continue; uint64_t A=a[i]; if(rem[i]>1){ A*=spp(rem[i],1); }
      int isprime = !comp[i]; // N prime iff no small prime factor < N (rem==N)

      u128 M=(u128)A*(A-1); if(M==0) continue;
      u128 r=((u128)N*N-1)%M;
      int cond=(r==0);
      int pred = isprime && (N&1);
      if(cond!=pred && hits++<20){ printf("MISMATCH n=%lu a=%lu cond=%d prime=%d\n",N,A,cond,isprime); fflush(stdout);} }
  }
  fprintf(stderr,"done %lu %lu hits %ld\n",lo,hi,hits); return 0; }
