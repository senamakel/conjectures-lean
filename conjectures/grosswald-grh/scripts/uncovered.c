// Sizing only, not part of the proof. Build: gcc -O2 -o uncovered uncovered.c -lm
// Fraction of primes in [lo, lo+len) not covered by the GRH sieve inequality with the
// constants of Grosswald/Analytic.lean (best S = s largest prime factors of p-1, 2 never needed).
// usage: frac lo len
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <stdint.h>
#include <string.h>
typedef unsigned long long u64;
typedef unsigned __int128 u128;
static int cmpd(const void*a,const void*b){u64 x=*(u64*)a,y=*(u64*)b;return x<y?-1:x>y;}
double bachC(double p,double x){return (2.0/3)*(1+2/sqrt(x)+3/pow(x,1.5))*(1+(5.0/3)/log(p))+(log(x)+2)/(sqrt(x)*log(p));}
int main(int argc,char**argv){
  u64 lo=strtoull(argv[1],0,10), len=strtoull(argv[2],0,10);
  u64 hi=lo+len; u64 B=(u64)sqrtl((long double)hi)+2;
  char*isc=calloc(B+1,1); u64*pr=malloc(sizeof(u64)*(B/2+10)); int np=0;
  for(u64 i=2;i<=B;i++){ if(!isc[i]){pr[np++]=i; for(u64 j=i*i;j<=B;j+=i) isc[j]=1;} }
  // rem[i] = (lo+i)-1 = m; factor lists
  u64*rem=malloc(8*len); unsigned char*isP=malloc(len); unsigned char*nf=calloc(len,1);
  u64 (*fac)[16]=malloc(sizeof(u64)*16*len);
  for(u64 i=0;i<len;i++){rem[i]=lo+i-1; isP[i]=1;}
  for(int k=0;k<np;k++){u64 q=pr[k];
    // primality sieve on lo+i
    u64 s=((lo+q-1)/q)*q; if(s<q*q) s=q*q;
    for(u64 j=s;j<hi;j+=q) isP[j-lo]=0;
    // factor m=lo+i-1
    u64 t=((lo-1+q-1)/q)*q;
    for(u64 j=t;j<hi-1;j+=q){u64 i=j-(lo-1); if(nf[i]<16) fac[i][nf[i]++]=q; while(rem[i]%q==0) rem[i]/=q;}
  }
  u64 nprime=0,unc=0; double sumg=0; int maxg=0; u64 hist[64]={0}, unch[64]={0};
  for(u64 i=0;i<len;i++){ u64 p=lo+i; if(p<3||!isP[i]) continue; nprime++;
    int n=nf[i]; u64 F[17]; memcpy(F,fac[i],8*n); if(rem[i]>1) F[n++]=rem[i];
    qsort(F,n,8,cmpd); hist[n]++;
    double x=floor(sqrtl((long double)p))-2; double A=bachC(p,x)*sqrt(x)*log((double)p); double R=x/2-(sqrt(x)/20+3);
    int cov=0;
    for(int s=0;s<n && !cov;s++){ double d=1; for(int j=n-s;j<n;j++) d-=1.0/F[j]; if(d<=0) continue;
      double K=pow(2,n-s)*(2+(s-1)/d)-1; if(K*A<R) cov=1; }
    if(!cov){unc++; unch[n]++;}
  }
  printf("lo=%llu len=%llu primes=%llu uncovered=%llu frac=%.4f\n",lo,len,nprime,unc,(double)unc/nprime);
  for(int n=1;n<20;n++) if(hist[n]) printf("  w=%d: %llu (unc %llu)\n",n,hist[n],unch[n]);
}
