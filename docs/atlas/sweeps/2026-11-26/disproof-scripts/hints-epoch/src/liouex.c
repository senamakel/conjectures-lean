// exact per-n scan: liouex lo hi A0 B0(long double as string)
// checks: b(n)<0 ; sqrt(n)b(n) < -1 (n>1) ; sqrt(n)b(n) > -loglog n (n>2008); a(n)>sqrt n (n>324); a(n)<sqrt(n)loglog n (n>5892); a(n)>0 (n>4)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#define SEG (1<<22)
int main(int argc,char**argv){
  uint64_t lo=strtoull(argv[1],0,10), hi=strtoull(argv[2],0,10);
  long long A=atoll(argv[3]); long double B=strtold(argv[4],0), c=0;
  uint64_t sq=(uint64_t)sqrtl((long double)hi)+2;
  char*isc=calloc(sq+1,1); uint32_t*pr=malloc(sizeof(uint32_t)*(sq/2+10)); int np=0;
  for(uint64_t i=2;i<=sq;i++){ if(!isc[i]){pr[np++]=i; for(uint64_t j=i*i;j<=sq;j+=i)isc[j]=1;} }
  uint64_t*rem=malloc(8*SEG); unsigned char*om=malloc(SEG);
  long double mxb=-1e9, mnbl=1e9, mna=1e9, mxa=-1e9; uint64_t amxb=0,amnbl=0,amna=0,amxa=0; long cnt[6]={0};
  for(uint64_t L=lo; L<hi; L+=SEG){
    uint64_t n=SEG; if(L+n>hi)n=hi-L;
    for(uint64_t i=0;i<n;i++){rem[i]=L+i;om[i]=0;}
    for(int k=0;k<np;k++){ uint64_t p=pr[k]; if(p*p>=L+n) break;
      uint64_t s=((L+p-1)/p)*p;
      for(uint64_t m=s;m<L+n;m+=p){ uint64_t i=m-L; do{rem[i]/=p;om[i]++;}while(rem[i]%p==0); } }
    for(uint64_t i=0;i<n;i++){ uint64_t k=L+i; if(!k)continue;
      int O=om[i]+(rem[i]>1); int s=((k+O)&1)?-1:1;
      A+=s; long double y=(long double)s/(long double)k - c; long double t=B+y; c=(t-B)-y; B=t;
      long double r=sqrtl((long double)k); long double ll= k>15? logl(logl((long double)k)):0;
      long double nb=B*r; // normalized b
      if(B>=0){ if(cnt[0]++<5) printf("b>=0 at %lu\n",k);}
      if(k>1 && nb>=-1){ if(cnt[1]++<10) printf("sqrt(n)b>=-1 at %lu val %.9Lf\n",k,nb);}
      if(k>2008 && nb<=-ll){ if(cnt[2]++<10) printf("sqrt(n)b<=-loglog at %lu val %.9Lf ll %.6Lf\n",k,nb,ll);}
      if(k>324 && (long double)A<=r){ if(cnt[3]++<10) printf("a<=sqrt at %lu a=%lld\n",k,A);}
      if(k>5892 && (long double)A>=r*ll){ if(cnt[4]++<10) printf("a>=sqrt*loglog at %lu a=%lld\n",k,A);}
      if(k>4 && A<=0){ if(cnt[5]++<5) printf("a<=0 at %lu\n",k);}
      if(k>2008){ if(nb>mxb){mxb=nb;amxb=k;} long double q=nb+ll; if(q<mnbl){mnbl=q;amnbl=k;} }
      if(k>5892){ long double q=A/r; if(q<mna){mna=q;amna=k;} long double q2=A/(r*ll); if(q2>mxa){mxa=q2;amxa=k;} }
    }
  }
  printf("END A=%lld B=%.21Le\n",A,B);
  printf("max sqrt(n)b=%.9Lf at %lu; min sqrt(n)b+loglog=%.9Lf at %lu; min a/sqrt=%.6Lf at %lu; max a/(sqrt loglog)=%.6Lf at %lu\n",mxb,amxb,mnbl,amnbl,mna,amna,mxa,amxa);
  printf("counts %ld %ld %ld %ld %ld %ld\n",cnt[0],cnt[1],cnt[2],cnt[3],cnt[4],cnt[5]);
}
