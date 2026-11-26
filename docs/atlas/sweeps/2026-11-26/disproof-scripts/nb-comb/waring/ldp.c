// min number of generators (m^k-1)/d, m>=2, d | m^k-1, for all n<=N. Reports max length, argmax, window maxima.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128;
int main(int argc,char**argv){
  int k=atoi(argv[1]); long long N=atoll(argv[2]); long long d=argc>3?atoll(argv[3]):1;
  static long long gens[1<<20]; int ng=0;
  for(long long m=2;;m++){ u128 p=1; for(int i=0;i<k;i++){p*=m; if(p>(u128)N*d+1) break;}
    if(p>(u128)N*d+1) break; u128 g=p-1; if(g%d) continue; gens[ng++]=(long long)(g/d);}
  fprintf(stderr,"k=%d d=%lld N=%lld ngens=%d first=%lld\n",k,d,N,ng,gens[0]);
  uint16_t *L=malloc((N+1)*sizeof(uint16_t)); const uint16_t INF=65535;
  L[0]=0;
  for(long long n=1;n<=N;n++){ uint16_t b=INF; for(int i=0;i<ng&&gens[i]<=n;i++){uint16_t v=L[n-gens[i]]; if(v<b)b=v;} L[n]=(b==INF)?INF:b+1; }
  uint16_t mx=0; long long cnt=0, last=0; long long gaps=0, F=0;
  for(long long n=1;n<=N;n++){ if(L[n]==INF){gaps++;F=n;continue;} if(L[n]>mx){mx=L[n];cnt=0;} if(L[n]==mx){cnt++;last=n;} }
  printf("k=%d d=%lld N=%lld gaps(<=N)=%lld largestgap=%lld maxlen=%u count=%lld lastargmax=%lld\n",k,d,N,gaps,F,mx,cnt,last);
  if(cnt<=20){ printf(" argmax:"); for(long long n=1;n<=N;n++) if(L[n]==mx) printf(" %lld",n); printf("\n"); }
  // window maxima over dyadic-ish windows
  for(long long a=1;a<=N;a*=2){ long long b=a*2-1; if(b>N)b=N; uint16_t w=0; for(long long n=a;n<=b;n++) if(L[n]!=INF&&L[n]>w)w=L[n]; printf(" [%lld,%lld] max=%u\n",a,b,w);}
  return 0;}
