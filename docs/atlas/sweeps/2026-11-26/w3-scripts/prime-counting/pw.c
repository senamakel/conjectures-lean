#include <stdio.h>
#include <stdlib.h>
#include <math.h>
/* check (1/n) sum_{k<=n} p_k^a < p_n^a/(a+1), track last failure and min relative margin*log p_n */
int main(int argc,char**argv){ long N=atol(argv[1]);
 unsigned char*s=calloc(N+1,1); for(long i=2;i*i<=N;i++) if(!s[i]) for(long j=i*i;j<=N;j+=i) s[j]=1;
 for(int a=2;a<=10;a++){ long double S=0; long n=0,lastfail=0; long double minm=1e9; long atn=0;
   for(long p=2;p<=N;p++) if(!s[p]){ n++; long double pa=powl((long double)p,a); S+=pa;
     /* compare S/n vs pa/(a+1): ratio r = S*(a+1)/(n*pa) */
     long double r=S*(a+1)/(n*pa); if(r>=1) lastfail=n;
     if(n>1000){ long double m=(1-r)*logl((long double)p)*(a+1)/a; if(m<minm){minm=m;atn=n;} } }
   printf("a=%d last failure n=%ld (Sun's N_a predicted thresholds 9,15,31,47,62,92,92,122,122) ; min (1-r)*log p*(a+1)/a over n>1000: %.4Lf at n=%ld; n_max=%ld\n",a,lastfail,minm,atn,n); }
}
