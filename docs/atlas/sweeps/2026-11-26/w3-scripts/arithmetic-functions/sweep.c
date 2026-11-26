// sigma, Omega up to N; checks: A337993 terms, Gerasimova (A008578), Robin margin D(n) minima, Lagarias margin
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
int main(int argc,char**argv){
  long N=atol(argv[1]);
  unsigned long *sig=calloc(N+1,8); unsigned char *Om=calloc(N+1,1);
  for(long d=1;d<=N;d++) for(long m=d;m<=N;m+=d) sig[m]+=d;
  // Omega via smallest prime factor sieve
  int *spf=calloc(N+1,4);
  for(long i=2;i<=N;i++) if(!spf[i]) for(long j=i;j<=N;j+=i) if(!spf[j]) spf[j]=i;
  for(long i=2;i<=N;i++) Om[i]=Om[i/spf[i]]+1;
  long double g=0.5772156649015328606065120900824024L, eg=expl(g), pi2=9.8696044010893586188344909998762L;
  long double H=0; long gerfail=0, a337=0; long double minD=1e300L; long argminD=0;
  long double minDtail[8]; for(int i=0;i<8;i++) minDtail[i]=1e300L;
  long double sgD=0;
  for(long n=1;n<=N;n++){
    H+=1.0L/n;
    long double L=floorl(H+expl(H)*logl(H));
    long double s=(long double)sig[n];
    if(L < s + n/pi2){ a337++; printf("A337993 term %ld\n",n);} 
    // Gerasimova: sigma(n) > n*Omega(n) iff n is 1 or prime
    int isp = (n>1 && spf[n]==n);
    int cond = (sig[n] > (unsigned long)n*Om[n]);
    if(cond != (n==1||isp)) { gerfail++; if(gerfail<10) printf("Gerasimova fail %ld\n",n);} 
    if(n>5040){ long double D=eg*n*logl(logl((long double)n)) - s; if(D<minD){minD=D;argminD=n;}
      // min D over n in [10^k,10^{k+1})
      int k=(int)floorl(log10l((long double)n)); if(k<8 && D<minDtail[k]) minDtail[k]=D; }
  }
  printf("A337993 count<=%ld: %ld ; Gerasimova failures: %ld ; min D(n) n>5040: %Lf at %ld\n",N,a337,gerfail,minD,argminD);
  for(int k=3;k<8;k++) printf("min D on [1e%d,1e%d): %Lf\n",k,k+1,minDtail[k]);
  return 0;
}
