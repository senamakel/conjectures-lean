#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
typedef unsigned long long u64; typedef unsigned __int128 u128;
static u64 pw(u64 a,u64 e,u64 m){u64 r=1;a%=m;while(e){if(e&1)r=(u128)r*a%m;a=(u128)a*a%m;e>>=1;}return r;}
int main(int argc,char**argv){
  u64 lo0=strtoull(argv[1],0,10), N=strtoull(argv[2],0,10);
  u64 R=(u64)sqrt((double)N)+2; char*b=calloc(R+1,1); u64*bp=malloc(sizeof(u64)*R); long nb=0;
  for(u64 i=2;i<=R;i++) if(!b[i]){bp[nb++]=i; for(u64 j=i*i;j<=R;j+=i)b[j]=1;}
  u64 S=1<<24; char*seg=malloc(S); long cnt=0; u64 last=0,lastr=0; u64 maxr=0,maxrp=0;
  for(u64 lo=lo0; lo<=N; lo+=S){ u64 hi=lo+S-1; if(hi>N)hi=N; memset(seg,1,hi-lo+1);
    for(long k=0;k<nb;k++){u64 q=bp[k]; if(q*q>hi)break; u64 st=((lo+q-1)/q)*q; if(st<q*q)st=q*q; for(u64 j=st;j<=hi;j+=q)seg[j-lo]=0;}
    for(u64 p=(lo<3?3:lo); p<=hi; p++){ if(!seg[p-lo]) continue; if(p<2)continue;
      u64 e=(p-1)/2,r=0; for(long k=1;k<nb;k++){u64 q=bp[k]; if(q==p)continue; if(pw(q,e,p)==1){r=q;break;}}
      if(r>maxr){maxr=r;maxrp=p;}
      double c=cbrt((double)p); if((double)r>=c){cnt++;last=p;lastr=r;} }
  }
  printf("range [%llu,%llu]: count rho>=p^(1/3): %ld, last p=%llu rho=%llu; max rho %llu at %llu\n",lo0,N,cnt,last,lastr,maxr,maxrp);
}
