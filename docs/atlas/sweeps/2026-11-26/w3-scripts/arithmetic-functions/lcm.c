// margin/N for N = lcm(1..x): Lagarias margin  M(N)/N ~ e^g*log(H) - sigma(N)/N (+H/N), H = log N + g ; also d(N) = e^g loglog N - sigma/N
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
int main(int argc,char**argv){
  long X=atol(argv[1]);
  char *c=calloc(X+1,1); for(long i=2;i*i<=X;i++) if(!c[i]) for(long j=i*i;j<=X;j+=i) c[j]=1;
  long double g=0.5772156649015328606065120900824024L, eg=expl(g), pi2=9.8696044010893586188344909998762L;
  long double logN=0, logS=0; long last_nonterm=0; long first_term=0; long double maxm=0;
  // iterate x upward: when x = p^a (prime power), N gains a factor p
  for(long x=2;x<=X;x++){
    long p=0, a=0, y=x;
    // test prime power
    for(long q=2;q*q<=y;q++){ if(y%q==0){ p=q; while(y%q==0){y/=q;a++;} break; } }
    if(p==0){ p=x; a=1; y=1; }
    if(y!=1) continue; // not a prime power
    logN+=logl((long double)p);
    // sigma ratio factor: (1-p^{-a-1})/(1-p^{-a}) for a>=2; for a=1: (1-p^{-2})/(1-p^{-1}) = 1+1/p
    long double num=1.0L-powl((long double)p,-(long double)(a+1)), den=1.0L-powl((long double)p,-(long double)a);
    logS+=logl(num/den);
    if(logN<20) continue;
    long double H=logN+g, sN=expl(logS);
    long double marg = eg*logl(H) - sN;   // + H/N + O(1/N): negligible
    int term = marg < 1.0L/pi2;
    if(!term) last_nonterm=x; else if(!first_term) first_term=x;
    if((x & (x-1))==0 || x==X) printf("x=%ld logN=%.1Lf marg/N=%.6Lf d=%.6Lf term=%d\n",x,logN,marg,eg*logl(logN)-sN,term);
  }
  printf("first x with lcm(1..x) a term: %ld ; last prime power x<=%ld with lcm(1..x) NOT a term: %ld\n",first_term,X,last_nonterm);
  return 0;
}
