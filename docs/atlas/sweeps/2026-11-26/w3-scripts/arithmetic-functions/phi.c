#include <stdio.h>
#include <stdlib.h>
#include <math.h>
int main(int argc,char**argv){
  long M=atol(argv[1]); unsigned *ph=malloc((M+1)*sizeof(unsigned));
  for(long i=0;i<=M;i++) ph[i]=i;
  for(long p=2;p<=M;p++) if(ph[p]==p) for(long j=p;j<=M;j+=p) ph[j]-=ph[j]/p;
  long double eg=1.7810724179901979852365041031L; long cnt=0; long maxn=0;
  for(long m=3;m<=M;m++){ long n=ph[m]; if(n<=2) continue; long double L=logl(logl((long double)n));
     long double f=eg*L+2.5L/L; if((long double)m >= n*f){ cnt++; if(n>maxn) maxn=n; if(cnt<=40) printf("counterexample: m=%ld phi(m)=n=%ld  m/(n f(n))=%.6Lf\n",m,n,(long double)m/(n*f)); } }
  printf("total pairs (m<=%ld) with m >= phi(m) f(phi(m)): %ld ; largest such n: %ld\n",M,cnt,maxn);
}
