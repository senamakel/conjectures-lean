// S(n,k) mod 2^64 by the row recurrence; test Adelberg-Lengyel conjecture con:a+2 and Thm th:+1+2.
// usage: st2 H CMAX
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static int v2u(uint64_t x){ return x? __builtin_ctzll(x) : 64; }
static int s2(long x){ return __builtin_popcountl(x); }
// v2(binom(m, r)) = s2(r)+s2(m-r)-s2(m)
static int v2binom(long m, long r){ if(r<0||r>m) return 999; return s2(r)+s2(m-r)-s2(m); }
int main(int argc,char**argv){
  int H=atoi(argv[1]); int CMAX=atoi(argv[2]);
  long N=(long)CMAX<<H; N+=3;
  uint64_t *row=calloc(N+2,8);
  row[0]=1; // S(0,0)
  long fails=0, checks=0, val=0;
  for(long n=1;n<=N;n++){
    for(long k=n;k>=1;k--) row[k]=row[k-1]+(uint64_t)k*row[k];
    row[0]=0;
    // rows of form c 2^h + 2 (and +0 for validation)
    for(int h=3;h<=H;h++){
      long m=1L<<h;
      if(n>=2*m && (n-2)%m==0){
        long c=(n-2)/m;
        if(c<2||c>CMAX) continue;
        for(long b=1;b<c;b++){
          int f=s2(b)-s2(c)+v2binom(2*c-b-1,c);
          for(long a=3;a<=m/2;a++){
            long k=b*m+a;
            int got=v2u(row[k]);
            int pred=s2(a)+f+v2binom(a+1,2)-1;
            if((a&3)==3){
              checks++;
              if(got!=pred){ fails++; if(fails<200) printf("FAIL h=%d c=%ld b=%ld a=%ld n=%ld k=%ld got=%d pred=%d condThm=%d\n",h,c,b,a,n,k,got,pred, (m/4)>=v2binom(2*c-b-1,c)); fflush(stdout);}
            } else if((m/4)>=v2binom(2*c-b-1,c)){
              val++;
              if(got!=pred){ printf("THMFAIL?? h=%d c=%ld b=%ld a=%ld got=%d pred=%d\n",h,c,b,a,got,pred);}
            }
          }
        }
      }
    }
  }
  printf("done checks=%ld fails=%ld thmchecks=%ld\n",checks,fails,val);
}
