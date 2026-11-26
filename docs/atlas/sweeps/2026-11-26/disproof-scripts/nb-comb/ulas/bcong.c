// b_M(n) mod 2^64 (M-coloured binary partitions) for n<=N; for each k print min over 1<=n<=N/2^(k+1)
// of nu_2(b(2^(k+1)n)-b(2^(k-1)n)) (capped at 64) and the first n attaining it.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc,char**argv){
  int M=atoi(argv[1]); long N=atol(argv[2]);
  uint64_t *b=calloc(N+1,8); b[0]=1; long len=1; // b[0..len-1] valid
  while(len<=N){ long nl=2*len; if(nl>N+1) nl=N+1;
    for(long n=nl-1;n>=0;n--) b[n]=(n&1)?0:b[n/2];
    for(int r=0;r<M;r++){ uint64_t s=0; for(long n=0;n<nl;n++){ s+=b[n]; b[n]=s; } }
    len=nl; if(nl==N+1) break; }
  for(int k=1;k<40;k++){ long lim=N>>(k+1); if(lim<1) break; int mv=64; long at=-1; long cnt=0;
    for(long n=1;n<=lim;n++){ uint64_t d=b[n<<(k+1)]-b[n<<(k-1)]; int v=d?__builtin_ctzll(d):64; if(v<mv){mv=v;at=n;cnt=0;} if(v==mv)cnt++; }
    printf("M=%d k=%d nmax=%ld minval=%d first_n=%ld count=%ld\n",M,k,lim,mv,at,cnt); }
  // also print b(1..10) for sanity
  printf("M=%d b(0..9):",M); for(int i=0;i<10;i++) printf(" %llu",(unsigned long long)b[i]); printf("\n");
  return 0;}
