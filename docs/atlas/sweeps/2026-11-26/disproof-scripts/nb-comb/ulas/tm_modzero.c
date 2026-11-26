// GMU Conj 3.15 screen: t_m(n) mod p for two 61/62-bit primes; report n<=N with t_m(n)≡0 mod both.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static const uint64_t P1=2305843009213693951ULL; // 2^61-1
static const uint64_t P2=4611686018427387847ULL; // prime < 2^62
static uint64_t mulm(uint64_t a,uint64_t b,uint64_t p){return (uint64_t)((u128)a*b%p);}
int main(int argc,char**argv){
  int m=atoi(argv[1]); long N=atol(argv[2]);
  uint64_t *t1=malloc((N+1)*8),*t2=malloc((N+1)*8);
  uint64_t C1[300],C2[300]; // signed binomials (-1)^i C(m,i) mod p
  // binomials via Pascal mod p
  uint64_t row1[300]={0},row2[300]={0}; row1[0]=row2[0]=1;
  for(int r=1;r<=m;r++) for(int i=r;i>=1;i--){ row1[i]=(row1[i]+row1[i-1])%P1; row2[i]=(row2[i]+row2[i-1])%P2; }
  for(int i=0;i<=m;i++){ C1[i]=(i&1)?(P1-row1[i])%P1:row1[i]; C2[i]=(i&1)?(P2-row2[i])%P2:row2[i]; }
  t1[0]=t2[0]=1; long hits=0;
  for(long n=1;n<=N;n++){ u128 s1=0,s2=0;
    for(int i=n&1;i<=m&&i<=n;i+=2){ long j=(n-i)/2; s1+=(u128)C1[i]*t1[j]; s2+=(u128)C2[i]*t2[j]; }
    t1[n]=(uint64_t)(s1%P1); t2[n]=(uint64_t)(s2%P2);
    if(t1[n]==0&&t2[n]==0){ hits++; if(hits<=20) printf("m=%d candidate zero n=%ld\n",m,n); } }
  printf("m=%d N=%ld zero-candidates=%ld\n",m,N,hits); return 0;}
