// Segmented sieve of mu and lambda. Usage: sieve N mode(0=lambda,1=mu)
// Prints S(N)=sum_{n<=N} f(n), and the first n (>=2 for lambda, >200 for mu) violating the conjecture.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#define SEG (1<<20)
static uint32_t *primes; static int np;
static void small_primes(uint64_t lim){ char*c=calloc(lim+1,1); primes=malloc(sizeof(uint32_t)*(lim+1)); np=0;
 for(uint64_t i=2;i<=lim;i++){ if(!c[i]){primes[np++]=i; for(uint64_t j=i*i;j<=lim;j+=i)c[j]=1;} } free(c);}
// compute f on [lo,hi) into out (int8)
static void segment(uint64_t lo, uint64_t hi, int mode, int8_t*out, uint64_t*prod){
 uint64_t len=hi-lo; for(uint64_t i=0;i<len;i++){prod[i]=1; out[i]=1;}
 for(int t=0;t<np;t++){ uint64_t p=primes[t]; if(p*p>=hi) break;
   uint64_t pk=p; int k=1;
   while(pk<hi){
     uint64_t s=(lo+pk-1)/pk*pk;
     for(uint64_t m=s;m<hi;m+=pk){ uint64_t i=m-lo; prod[i]*=p;
        if(mode==0) out[i]=-out[i]; else { if(k==1) out[i]=-out[i]; else out[i]=0; } }
     if(pk> hi/p) break; pk*=p; k++;
   }
 }
 for(uint64_t i=0;i<len;i++){ uint64_t n=lo+i; if(prod[i]!=n){ out[i]=-out[i]; } }
}
int main(int argc,char**argv){ uint64_t N=strtoull(argv[1],0,10); int mode=atoi(argv[2]);
 small_primes((uint64_t)sqrtl((long double)N)+2);
 uint64_t nseg=(N+SEG)/SEG; // covers [1, N]
 int64_t *ssum=calloc(nseg,8),*smax=calloc(nseg,8),*smin=calloc(nseg,8);
 #pragma omp parallel
 { int8_t*out=malloc(SEG); uint64_t*prod=malloc(8*SEG);
 #pragma omp for schedule(dynamic,4)
 for(uint64_t s=0;s<nseg;s++){ uint64_t lo=1+s*SEG, hi=lo+SEG; if(hi>N+1)hi=N+1;
   segment(lo,hi,mode,out,prod); int64_t acc=0,mx=INT64_MIN,mn=INT64_MAX;
   for(uint64_t i=0;i<hi-lo;i++){acc+=out[i]; if(acc>mx)mx=acc; if(acc<mn)mn=acc;}
   ssum[s]=acc; smax[s]=mx; smin[s]=mn; }
 free(out);free(prod);}
 int64_t off=0; uint64_t first=0; int8_t*out=malloc(SEG); uint64_t*prod=malloc(8*SEG);
 for(uint64_t s=0;s<nseg;s++){ uint64_t lo=1+s*SEG, hi=lo+SEG; if(hi>N+1)hi=N+1;
   int cand=0;
   if(mode==0) cand = (off+smax[s]>0);
   else { int64_t a=off+smax[s], b=off+smin[s]; __int128 m=(__int128)(a>-b?a:-b); cand = (4*m*m >= (__int128)lo) && hi>201; }
   if(cand && !first){ segment(lo,hi,mode,out,prod); int64_t acc=off;
     for(uint64_t i=0;i<hi-lo;i++){ acc+=out[i]; uint64_t n=lo+i;
       if(mode==0 && n>=2 && acc>0){first=n; printf("first violation n=%llu S=%lld\n",(unsigned long long)n,(long long)acc);break;}
       if(mode==1 && n>200 && 4*(__int128)acc*acc>=n){first=n; printf("first violation x=%llu M=%lld\n",(unsigned long long)n,(long long)acc);break;} } }
   off+=ssum[s]; }
 printf("N=%llu S(N)=%lld\n",(unsigned long long)N,(long long)off); return 0; }
