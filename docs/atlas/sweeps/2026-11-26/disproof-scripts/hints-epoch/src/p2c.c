// Find odd N in [lo,hi) NOT representable as p + 2^x + c*2^y, x,y>=1, p prime with p%6==r (r=0: any odd prime)
// usage: p2c c r lo hi   (lo,hi odd-aligned automatically)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
typedef unsigned __int128 u128;
static uint64_t mulmod(uint64_t a,uint64_t b,uint64_t m){return (u128)a*b%m;}
static uint64_t powmod(uint64_t a,uint64_t e,uint64_t m){uint64_t r=1;a%=m;while(e){if(e&1)r=mulmod(r,a,m);a=mulmod(a,a,m);e>>=1;}return r;}
static int isprime(uint64_t n){ if(n<2)return 0; static const uint64_t sp[]={2,3,5,7,11,13,17,19,23,29,31,37};
  for(int i=0;i<12;i++){ if(n%sp[i]==0) return n==sp[i]; }
  uint64_t d=n-1; int s=0; while(!(d&1)){d>>=1;s++;}
  for(int i=0;i<12;i++){ uint64_t x=powmod(sp[i],d,n); if(x==1||x==n-1) continue; int ok=0; for(int j=1;j<s;j++){x=mulmod(x,x,n); if(x==n-1){ok=1;break;}} if(!ok) return 0;} return 1; }
#define B (1ULL<<27)          /* odd numbers per block */
#define SH (1ULL<<25)         /* max s/2 handled by bitmap */
int main(int argc,char**argv){
  uint64_t c=strtoull(argv[1],0,10); int r=atoi(argv[2]); uint64_t lo=strtoull(argv[3],0,10), hi=strtoull(argv[4],0,10);
  if(!(lo&1))lo++;
  // s list
  uint64_t S[4096]; int ns=0;
  for(int x=1;x<63;x++) for(int y=1;y<60;y++){ u128 s=((u128)1<<x)+(u128)c*((u128)1<<y); if(s<((u128)1<<62)) S[ns++]=(uint64_t)s; }
  // sort
  for(int i=1;i<ns;i++){uint64_t v=S[i];int j=i-1;while(j>=0&&S[j]>v){S[j+1]=S[j];j--;}S[j+1]=v;}
  uint64_t sq=(uint64_t)sqrtl((long double)hi)+2; char*isc=calloc(sq+1,1); uint32_t*pr=malloc(4*(sq/2+10)); int np=0;
  for(uint64_t i=2;i<=sq;i++) if(!isc[i]){pr[np++]=i; for(uint64_t j=i*i;j<=sq;j+=i) isc[j]=1;}
  uint64_t W=(B+SH)/64+2; uint64_t*P=malloc(8*W); uint64_t*R=malloc(8*(B/64+2));
  long found=0;
  for(uint64_t L=lo; L<hi; L+=2*B){
    // bitmap P over odd v in [L-2SH, L+2B): bit j <-> v = L - 2*SH + 2j
    int64_t base=(int64_t)L-2*(int64_t)SH;
    memset(P,0xff,8*W);
    uint64_t nb=W*64;
    // mark v<3 non-prime
    for(uint64_t j=0;j<nb;j++){ int64_t v=base+2*(int64_t)j; if(v>=3) break; P[j>>6]&=~(1ULL<<(j&63)); }
    for(int k=1;k<np;k++){ uint64_t p=pr[k]; int64_t top=base+2*(int64_t)nb; if((int64_t)(p*p)>=top) break;
      int64_t st = base<=(int64_t)(p*p)? (int64_t)(p*p) : ((base+ (int64_t)p-1)/(int64_t)p)*(int64_t)p;
      if(!(st&1)) st+=p;
      for(int64_t v=st; v<top; v+=2*p){ uint64_t j=(v-base)/2; P[j>>6]&=~(1ULL<<(j&63)); } }
    if(r){ // keep only v%6==r. v = base+2j ; mask by residue pattern period 3 in j
      for(uint64_t j=0;j<nb;j++){ int64_t v=base+2*(int64_t)j; if(((v%6)+6)%6!=r) P[j>>6]&=~(1ULL<<(j&63)); } }
    memset(R,0,8*(B/64+2));
    // R bit i <-> N = L+2i ; N - s = L + 2i - s -> j = i + SH - s/2
    for(int t=0;t<ns;t++){ uint64_t h=S[t]/2; if(h>SH) break; uint64_t off=SH-h; // R[i] |= P[i+off]
      uint64_t wq=off>>6, bq=off&63;
      for(uint64_t w=0; w<B/64; w++){ uint64_t v = bq? (P[w+wq]>>bq)|(P[w+wq+1]<<(64-bq)) : P[w+wq]; R[w]|=v; } }
    for(uint64_t w=0; w<B/64; w++) if(~R[w]) for(int b=0;b<64;b++) if(!((R[w]>>b)&1)){
      uint64_t N=L+2*(w*64+b); if(N>=hi) continue;
      int ok=0; for(int t=0;t<ns;t++){ uint64_t s=S[t]; if(s>=N) break; if(s/2<=SH) continue; uint64_t p=N-s; if(r && p%6!=(uint64_t)r) continue; if(isprime(p)){ok=1;break;} }
      if(!ok){ printf("UNREP N=%lu n=%lu\n",N,(N+1)/2); fflush(stdout); found++; } }
  }
  fprintf(stderr,"c=%lu r=%d [%lu,%lu) unrep=%ld\n",c,r,lo,hi,found); return 0; }
