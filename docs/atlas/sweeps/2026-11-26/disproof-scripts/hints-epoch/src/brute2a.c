// independent brute: n = (2^a 9^b)^2 + x(4x+1) + y(3y+1)/2 ; test via 24r+1 square, early exit
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
static int pent(int64_t r){ int64_t D=24*r+1; int64_t z=(int64_t)sqrtl((long double)D); while(z*z>D) z--; while((z+1)*(z+1)<=D) z++; return z*z==D && (z%6==1||z%6==5); }
int main(int argc,char**argv){ int64_t lo=atoll(argv[1]),hi=atoll(argv[2]); int64_t sv[64];int ns=0;
  for(int64_t t=1;t*t<=hi;t*=2) for(int64_t u=t;u*u<=hi;u*=9) sv[ns++]=u*u;
  for(int64_t n=lo;n<hi;n++){ int ok=0;
    for(int k=0;k<ns&&!ok;k++){ int64_t s=sv[k]; if(s>n) continue; int64_t m=n-s;
      // x ordering: 0,-1,1,-2,2,...  x(4x+1) <= m
      for(int64_t j=0;;j++){ int64_t x = (j&1)? -(j+1)/2 : j/2; int64_t f=x*(4*x+1); if(f>m){ if(j>3) break; else continue;} if(pent(m-f)){ok=1;break;} } }
    if(!ok) printf("UNREP %ld\n",(long)n); }
  fprintf(stderr,"done %ld %ld\n",(long)lo,(long)hi); }
