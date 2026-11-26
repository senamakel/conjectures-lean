#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
int main(int argc,char**argv){
  long N=atol(argv[1]); int M=atoi(argv[2]);
  unsigned char *s=calloc(N+1,1);
  for(long i=2;i*i<=N;i++) if(!s[i]) for(long j=i*i;j<=N;j+=i) s[j]=1;
  long best[64]; long argk[64], argp[64];
  for(int m=1;m<=M;m++){best[m]=-1000000000L;}
  long k=0;
  for(long p=2;p<=N;p++) if(!s[p]){ k++;
    for(int m=1;m<=M;m++){ long v=k*(long)m-p; if(v>best[m]){best[m]=v;argk[m]=k;argp[m]=p;} } }
  for(int m=1;m<=M;m++){ int ok = exp(m+1) < (double)N; printf("%d %ld k=%ld p=%ld complete=%d\n",m,best[m],argk[m],argp[m],ok);}
}
