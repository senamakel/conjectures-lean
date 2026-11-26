// prototype of the Lean kernel-enumeration block checker (exact node semantics, no duplicates)
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef unsigned long long u64;
#define NPR 400
static int pr[NPR], npr, nx; static double W[NPR]; static u64 Wn[NPR], RH[NPR];
static double ces[4000]; static u64 A,B,Bn; static u64 TCUT=16;
static u64 nnode=0, ndirect=0, nfail=0, nops=0, nnoncanon=0; static double sumq=0; static u64 maxq=0;
static int pre[400]; static int npre;
static int lam8(u64 n){ // floor(log2(n^8)) = floor(8 log2 n) approx via long double
  if(n<2) return 0; long double v=8*log2l((long double)n); int f=(int)floorl(v); return f; }
static FILE*out;
static void visit(int i, u64 P, u64 w){ // enumerate multiples of P in [A,B), node semantics
  u64 k0=(A+P-1)/P, k1=(B-1)/P;
  for(u64 k=k0;k<=k1;k++){ u64 q=k*P; ndirect++;
    int nc=0; for(int t=0;t<npre;t++){ nops++; if(q%pr[pre[t]]==0 && P%pr[pre[t]]!=0){nc=1;break;} }
    if(nc){nnoncanon++;continue;}
    u64 s=w; for(int j=i;j<nx;j++){ nops++; if(q%pr[j]==0) s+=Wn[j]; }
    if(s>=Bn){ nfail++; sumq+=q; if(q>maxq)maxq=q; if(out) fprintf(out,"%llu\n",q);} }
}
static void dfs(int i,u64 P,u64 w){
  nnode++;
  u64 R=(B-1)/P;
  if(w<Bn){
    if(i>=nx || (u64)pr[i]>R) return;
    if(w + RH[i]*(u64)lam8(R) < Bn) return;
  }
  u64 nm=(B-1)/P-(A-1)/P;
  if(w>=Bn || nm<=TCUT){ visit(i,P,w); return; }
  if(P%pr[i]!=0){ dfs(i+1,P*pr[i],w+Wn[i]); }
  pre[npre++]=i; dfs(i+1,P,w); npre--;
}
static double lam(int n){for(int i=0;i<npr&&pr[i]<=n;i++)if(n%pr[i]==0){int m=n;while(m%pr[i]==0)m/=pr[i];return m==1?log(pr[i]):0;}return 0;}
int main(int argc,char**argv){
  double lo2=atof(argv[1]), hi=atof(argv[2]); int wsh=atoi(argv[3]); TCUT=atoll(argv[4]); if(argc>5) out=fopen(argv[5],"w");
  double CC=1.657, SC=4294967296.0;
  for(int n=2;npr<NPR&&n<2000;n++){int ok=1;for(int d=2;d*d<=n;d++)if(n%d==0){ok=0;break;}if(ok)pr[npr++]=n;}
  for(int x=1;x<2000;x++){double s=0;for(int n=1;n<=x;n++)s+=lam(n)*(1.0/n)*(1-(double)n/x);ces[x]=s;}
  const double g=0.5772156649015329,lpi=log(M_PI);
  u64 a=(u64)pow(2,lo2),hh=(u64)hi; u64 nblk=0,nunif=0;
  while(a<hh){u64 b=a+((a>>wsh)>1?(a>>wsh):1); if(b>hh)b=hh;
    double La=log((double)a)-1e-9,Lb=log((double)b)+1e-9; int x=(int)floor(CC*La*La); if(x>1999)x=1999;
    double s=sqrt(x),l=log(x),K=(s+1+l/2)/(1+1.0/x-2/s),kap=K*(1-1.0/x)+l/2;
    double Es=-0.5*(1-1.0/x)*lpi-g/2*(1-1.0/x)+(l+2)/x,Et=M_PI*M_PI/6-g/2*l;
    double base=x-0.15*s-3*l-3+2*K*ces[x]-2*K*Es+0.5*lpi*l-Et; double Bq=base-kap*Lb;
    Bn=(u64)floor(Bq*SC);
    nx=0;while(nx<npr&&pr[nx]<=x)nx++;
    for(int i=0;i<nx;i++){double lp=log(pr[i]);double Ap=(l-lp/2)*(l-lp/2)/2+2*K*lp/(pr[i]-1);W[i]=Ap+(Ap-kap*lp>0?Ap-kap*lp:0);Wn[i]=(u64)ceil(W[i]*SC);}
    RH[nx]=0;for(int i=nx-1;i>=0;i--){u64 r=(Wn[i]+lam8(pr[i])-1)/lam8(pr[i]); RH[i]=r>RH[i+1]?r:RH[i+1];}
    A=a;B=b;npre=0; dfs(0,1,0); nblk++; a=b;}
  fprintf(stderr,"blocks %llu nodes %llu direct %llu noncanon %llu ops %llu fail %llu sumq %.4g maxq %llu\n",nblk,nnode,ndirect,nnoncanon,nops,nfail,sumq,maxq);
}
