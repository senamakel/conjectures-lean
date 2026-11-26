// Sun Conj. 3.27 family (arXiv:1211.1588; OEIS A234451, A236358, A234504):
// n = k + m, k,m >= 1, e = phi(k)/a + phi(m)/b must be an integer in the set P
// (exponents for which the special form is prime, read from a list file).
// Usage: phirep a b listfile N0 N1 [full]
//   prints every n in [N0,N1] with no representation; with "full" prints a(n) for all n.
// Only exponents e <= EMAX (largest list entry) are trusted; n whose every
// attainable e is below EMAX are "decided"; we report the first n where max e >= EMAX.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int gcd(int a,int b){while(b){int t=a%b;a=b;b=t;}return a;}
int main(int argc,char**argv){
  int a=atoi(argv[1]),b=atoi(argv[2]); const char*lf=argv[3];
  long N0=atol(argv[4]),N1=atol(argv[5]); int full=argc>6;
  int L=a/gcd(a,b)*b, ca=L/a, cb=L/b;
  // read list
  FILE*f=fopen(lf,"r"); long v, emax=0; long cap=1<<24; char*P=calloc(cap,1);
  while(fscanf(f,"%ld",&v)==1){ if(v<cap){P[v]=1; if(v>emax)emax=v;} }
  fclose(f);
  long N=N1+1; int*phi=malloc(sizeof(int)*N);
  for(long i=0;i<N;i++)phi[i]=i;
  for(long i=2;i<N;i++) if(phi[i]==i) for(long j=i;j<N;j+=i) phi[j]-=phi[j]/i;
  long nz=0, undecided_from=-1;
  #pragma omp parallel for schedule(dynamic,64) reduction(+:nz)
  for(long n=N0;n<=N1;n++){
    long cnt=0, maxe=0;
    for(long k=1;k<n;k++){
      long num=(long)phi[k]*ca+(long)phi[n-k]*cb;
      if(num%L) continue;
      long e=num/L; if(e>maxe)maxe=e;
      if(e<cap && P[e]){ cnt++; if(!full) break; }
    }
    if(cnt==0){
      // recompute maxe fully
      maxe=0; for(long k=1;k<n;k++){long num=(long)phi[k]*ca+(long)phi[n-k]*cb; if(num%L==0 && num/L>maxe) maxe=num/L;}
      #pragma omp critical
      { printf("ZERO n=%ld maxe=%ld %s\n",n,maxe, maxe<emax?"decided":"UNDECIDED"); fflush(stdout);}
      nz++;
    } else if(full){
      #pragma omp critical
      printf("%ld %ld\n",n,cnt);
    }
  }
  fprintf(stderr,"done a=%d b=%d [%ld,%ld] zeros=%ld emax=%ld\n",a,b,N0,N1,nz,emax);
  return 0;
}
