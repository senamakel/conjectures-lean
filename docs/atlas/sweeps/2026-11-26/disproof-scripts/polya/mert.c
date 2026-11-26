#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll;
/* block algorithm, same shape as the Lean checker; small[y]=M(y) for y<=T, big[a]=M(X/a) */
static ll X,T; static ll *sm,*bg;
static ll f(ll q){ return q<=T? sm[q] : bg[X/q]; }
static ll blocksum2(ll y){ /* sum_{k=2}^{y} f(y/k) */
  ll s=0,n=2; while(n<=y){ ll q=y/n, n2=y/q; s+=(n2+1-n)*f(q); n=n2+1;} return s; }
int main(int argc,char**argv){ X=atoll(argv[1]); T=(ll)sqrtl((long double)X); while(T*T>X)T--; while((T+1)*(T+1)<=X)T++;
  ll A=X/(T+1); sm=calloc(T+2,8); bg=calloc(A+2,8);
  /* independent Mobius sieve for small values */
  signed char *mu=malloc(T+2); for(ll i=0;i<=T;i++)mu[i]=1; char*comp=calloc(T+2,1);
  for(ll p=2;p<=T;p++) if(!comp[p]){ for(ll j=p;j<=T;j+=p){ if(j>p)comp[j]=1; mu[j]=-mu[j];} for(ll j=p*p;j<=T;j+=p*p) mu[j]=0; }
  sm[0]=0; for(ll y=1;y<=T;y++) sm[y]=sm[y-1]+mu[y];
  for(ll a=A;a>=1;a--){ ll y=X/a; bg[a]=1-blocksum2(y); }
  ll M=f(X); ll L=0; for(ll d=1;d*d<=X;d++) L+=f(X/(d*d));
  /* verify the identity at every point like the Lean checker */
  ll bad=0; for(ll y=1;y<=T;y++) if(f(y)+blocksum2(y)!=1) bad++;
  for(ll a=1;a<=A;a++) if(f(X/a)+blocksum2(X/a)!=1) bad++;
  printf("X=%lld T=%lld A=%lld M=%lld L=%lld bad=%lld 4M^2-X=%lld\n",X,T,A,M,L,bad,4*M*M-X); }
