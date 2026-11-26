#include <stdlib.h>
// recompute the budget for each listed q with its own x = floor(c log^2 q) and log q
#include <stdio.h>
#include <math.h>
typedef unsigned long long u64;
int pr[3000],npr; double ces[4000];
double lam(int n){for(int i=0;i<npr&&pr[i]<=n;i++)if(n%pr[i]==0){int m=n;while(m%pr[i]==0)m/=pr[i];return m==1?log(pr[i]):0;}return 0;}
int main(int argc,char**argv){double CC=argc>1?atof(argv[1]):1.657;
for(int n=2;n<4000;n++){int ok=1;for(int d=2;d*d<=n;d++)if(n%d==0){ok=0;break;}if(ok)pr[npr++]=n;}
for(int x=1;x<4000;x++){double s=0;for(int n=1;n<=x;n++)s+=lam(n)*(1.0/n)*(1-(double)n/x);ces[x]=s;}
const double g=0.5772156649015329,lpi=log(M_PI);u64 q,cnt=0,mx=0;double sq=0;
while(scanf("%llu",&q)==1){double L=log((double)q);int x=(int)floor(CC*L*L);double s=sqrt(x),l=log(x);
double K=(s+1+l/2)/(1+1.0/x-2/s),kap=K*(1-1.0/x)+l/2;double Es=-0.5*(1-1.0/x)*lpi-g/2*(1-1.0/x)+(l+2)/x;double Et=M_PI*M_PI/6-g/2*l;
double Pc=x<2000?ces[x]:l-2;double B=x-0.15*s-3*l-3+2*K*Pc-2*K*Es+0.5*lpi*l-Et-kap*L;
for(int i=0;i<npr&&pr[i]<=x;i++)if(q%pr[i]==0){double lp=log(pr[i]);double Ap=(l-lp/2)*(l-lp/2)/2+2*K*lp/(pr[i]-1);B-=Ap+(Ap-kap*lp>0?Ap-kap*lp:0);}
if(B<=0){cnt++;sq+=q;if(q>mx)mx=q;}}
printf("exact per-q failing: %llu sumq %.4g max %llu (2^%.3f)\n",cnt,sq,mx,log2((double)mx));}
