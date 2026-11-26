#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <stdint.h>
typedef unsigned long long u64; typedef unsigned __int128 u128;
static u64 pw(u64 a,u64 e,u64 m){u64 r=1;a%=m;while(e){if(e&1)r=(u128)r*a%m;a=(u128)a*a%m;e>>=1;}return r;}
int main(int argc,char**argv){
  u64 N=strtoull(argv[1],0,10);
  char*s=calloc(N+1,1); for(u64 i=2;i<=N;i++)s[i]=1;
  for(u64 i=2;i*i<=N;i++) if(s[i]) for(u64 j=i*i;j<=N;j+=i)s[j]=0;
  int sm[3000],ns=0; for(u64 i=3;ns<3000;i++) if(s[i]) sm[ns++]=i;
  double cs[4]={1.0/3,0.3,0.27,0.25}; long cnt[4]={0}; u64 last[4]={0},lastr[4]={0};
  double best=0; u64 bp=0,br=0; long nexc=0;
  /* also least prime QNR == 3 mod 4 and == 1 mod 4 below sqrt p */
  long n3fail=0,n1fail=0; u64 n3last=0,n1last=0;
  for(u64 p=3;p<=N;p++){ if(!s[p])continue;
    u64 e=(p-1)/2,r=0; int got3=0,got1=0; u64 q3=0,q1=0;
    for(int k=0;k<ns;k++){u64 q=sm[k]; if(q==p)continue; u64 v=pw(q,e,p);
      if(v==1 && !r) r=q;
      if(v==p-1){ if(q%4==3&&!q3)q3=q; if(q%4==1&&!q1)q1=q; }
      if(r&&q3&&q1)break;}
    if(r==0){printf("no r for %llu\n",p);continue;}
    if(r*r>=p){printf("exc %llu %llu\n",p,r);nexc++;}
    if(q3==0||q3*q3>=p){n3fail++;n3last=p;}
    if(q1==0||q1*q1>=p){n1fail++;n1last=p;}
    double lp=log((double)p);
    if(p>1000 && r/(lp*lp)>best){best=r/(lp*lp);bp=p;br=r;}
    for(int c=0;c<4;c++) if((double)r>=pow((double)p,cs[c])){cnt[c]++;last[c]=p;lastr[c]=r;}
  }
  printf("max rho/log^2 p (p>1000): %.4f at p=%llu rho=%llu\n",best,bp,br);
  for(int c=0;c<4;c++) printf("c=%.3f count=%ld last p=%llu rho=%llu\n",cs[c],cnt[c],last[c],lastr[c]);
  printf("QNR==3mod4 not < sqrt p: count %ld last %llu\nQNR==1mod4 not < sqrt p: count %ld last %llu\n",n3fail,n3last,n1fail,n1last);
}
