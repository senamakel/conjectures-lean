// segmented Omega sieve over [lo,hi); per block of 2^16 output: block start, local prefix min/max of A and B, block totals
// usage: liou lo hi outfile
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <string.h>
#define SEG (1<<22)
#define BLK (1<<16)
int main(int argc,char**argv){
  uint64_t lo=strtoull(argv[1],0,10), hi=strtoull(argv[2],0,10);
  FILE*f=fopen(argv[3],"wb");
  uint64_t sq=(uint64_t)sqrtl((long double)hi)+2;
  char*isc=calloc(sq+1,1); uint32_t*pr=malloc(sizeof(uint32_t)*(sq/2+10)); int np=0;
  for(uint64_t i=2;i<=sq;i++){ if(!isc[i]){pr[np++]=i; for(uint64_t j=i*i;j<=sq;j+=i)isc[j]=1;} }
  uint64_t*rem=malloc(8*SEG); unsigned char*om=malloc(SEG);
  for(uint64_t L=lo; L<hi; L+=SEG){
    uint64_t n=SEG; if(L+n>hi)n=hi-L;
    for(uint64_t i=0;i<n;i++){rem[i]=L+i;om[i]=0;}
    for(int k=0;k<np;k++){ uint64_t p=pr[k]; if(p*p>=L+n) break;
      uint64_t s=((L+p-1)/p)*p;
      for(uint64_t m=s;m<L+n;m+=p){ uint64_t i=m-L; do{rem[i]/=p;om[i]++;}while(rem[i]%p==0); }
    }
    // blocks
    for(uint64_t b0=0;b0<n;b0+=BLK){
      uint64_t e=b0+BLK; if(e>n)e=n;
      long long A=0,Amin=0,Amax=0; long double B=0,Bmin=0,Bmax=0,c=0;
      for(uint64_t i=b0;i<e;i++){
        uint64_t k=L+i; if(k==0) continue;
        int O=om[i]+(rem[i]>1);
        int s=((k+O)&1)?-1:1;
        A+=s; if(A<Amin)Amin=A; if(A>Amax)Amax=A;
        long double y=(long double)s/(long double)k - c; long double t=B+y; c=(t-B)-y; B=t;
        if(B<Bmin)Bmin=B; if(B>Bmax)Bmax=B;
      }
      uint64_t st=L+b0, en=L+e; long long rec[3]={(long long)st,(long long)en,A}; long long r2[2]={Amin,Amax};
      long double r3[3]={B,Bmin,Bmax};
      fwrite(rec,8,3,f); fwrite(r2,8,2,f); fwrite(r3,sizeof(long double),3,f);
    }
  }
  fclose(f); return 0;
}
