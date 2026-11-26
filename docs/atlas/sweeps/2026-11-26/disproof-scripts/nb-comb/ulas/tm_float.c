// long double screening of GMU Conj 5.9 / 3.15 for t_m(n), n<=N.
// t(n)=sum_{i≡n mod 2,0<=i<=m} (-1)^i C(m,i) t((n-i)/2)
// err[n]: running relative error bound in units of eps (first-order).
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
int main(int argc,char**argv){
  int m=atoi(argv[1]); long N=atol(argv[2]);
  long double *t=malloc((N+2)*sizeof(long double)); float *err=malloc((N+2)*sizeof(float));
  long double C[200]; C[0]=1; for(int i=1;i<=m;i++) C[i]=C[i-1]*(m-i+1)/i;
  t[0]=1; err[0]=0;
  double worst=0; long worstn=0;
  for(long n=1;n<=N+1;n++){ long double s=0; long double ea=0;
    for(int i=n&1;i<=m && i<=n;i+=2){ long j=(n-i)/2; long double term=((i&1)?-C[i]:C[i])*t[j]; s+=term; ea+= fabsl(term)*(err[j]+m+2); }
    t[n]=s; double e = (s==0)?1e30:(double)(ea/fabsl(s)); if(e>1e30)e=1e30; err[n]=(float)e; if(e>worst){worst=e;worstn=n;} }
  long nss=0, nlc=0, nz=0; long double minr=1e300L; long minn=0; long first_ss=-1, first_lc=-1;
  long exc0=0, exc1=0;
  for(long n=1;n<=N;n++){
    if(t[n]==0 || err[n]>1e15) {nz++; if(nz<5) printf("m=%d near-zero/illcond n=%ld err=%g\n",m,n,err[n]);}
    if((t[n-1]>0&&t[n]>0&&t[n+1]>0)||(t[n-1]<0&&t[n]<0&&t[n+1]<0)){ nss++; if(first_ss<0)first_ss=n; }
    long double p=t[n-1]*t[n+1];
    if(p>0){ long double r=t[n]*t[n]/p; if(r<minr){minr=r;minn=n;} if(r<=1){nlc++; if(first_lc<0)first_lc=n;} }
    if(n%3==0 && t[n]<0) exc0++;
    if(n%3==1 && t[n]>0) exc1++;
  }
  printf("m=%d N=%ld samesign3=%ld first=%ld notLC=%ld first=%ld minLCratio=%.6Lg at n=%ld worst_err_eps=%g at %ld exc0=%ld exc1=%ld (of %ld) illcond=%ld\n",
    m,N,nss,first_ss,nlc,first_lc,minr,minn,worst,worstn,exc0,exc1,N/3,nz);
  return 0;}
