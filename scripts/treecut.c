// Cut MTT Algorithm 1 (float model of Grosswald/Alg.lean) into chunks for scripts/gen_tree.py.
// Build: gcc -O2 -o treecut treecut.c -lm; run: ulimit -s unlimited; ./treecut 10000000000001 0 3e8 > tree_cut.txt
// C port of scripts/alg.py (MTT Algorithm 1 with the repo's constants), for sizing at lower LOW.
// usage: tree LOW [LIM]
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
static int PR[20000], NP;
static double LOW, LIM;
static double cand, nodes, leaves;
static int ok(double K, double y){ double x=y*y, g=1+2/y+3/(y*y*y), lp=2*log(x+3);
  return K*((2.0/3)*g*(lp+5.0/3)+(log(x)+2)/y) < y/2-1.0/20-3/y; }
static double ythresh(double K){ double lo=1, hi=1e30; for(int i=0;i<120;i++){double m=sqrt(lo*hi); if(ok(K,m)) hi=m; else lo=m;} return hi; }
static double Kval(int n,int s,double d){ return pow(2,n-s)*(2+(s-1)/d)-1; }
static int inl(int q,int*a,int na){for(int i=0;i<na;i++) if(a[i]==q) return 1; return 0;}

static char *buf; static size_t blen=0, bcap=0;
static void emit(const char*s){ size_t l=strlen(s); if(blen+l+1>bcap){bcap=(bcap+l+1)*2; buf=realloc(buf,bcap);} memcpy(buf+blen,s,l+1); blen+=l; }
static void fmtl(char*o,int*a,int na){ char t[32]; strcpy(o,"["); for(int i=na-1;i>=0;i--){ sprintf(t,"%d%s",a[i],i?", ":""); strcat(o,t);} strcat(o,"]"); }
static double CUT;
static double node(int n,int*X,int nx,int*Y,int ny){
  nodes++;
  size_t mark=blen;
  int L[64]; int nl=0; for(int i=0;i<NP&&nl<n;i++) if(!inl(PR[i],Y,ny)) L[nl++]=PR[i];
  double prodL=1; for(int i=0;i<n;i++) prodL*=L[i];
  double lower=fmax(prodL+1,LOW), up=-1;
  for(int s=0;s<n;s++){ double d=1; for(int j=n-s;j<n;j++) d-=1.0/L[j]; if(d<=0) continue;
    double y=ceil(ythresh(Kval(n,s,d))); double p=(y*y+2)*(y*y+2); if(up<0||p<up) up=p; }
  double prodX=1; for(int i=0;i<nx;i++) prodX*=X[i];
  double c;
  if(up<=lower) c=0;
  else { double en=floor((up-lower)/prodX);
    if(en>(n<=8?1e8:(n<=10?1e7:1e6))){ int q=0; for(int i=0;i<NP;i++) if(!inl(PR[i],X,nx)&&!inl(PR[i],Y,ny)){q=PR[i];break;}
      char t[64]; sprintf(t,"S %d\n",q); emit(t);
      X[nx]=q; c=node(n,X,nx+1,Y,ny); Y[ny]=q; c+=node(n,X,nx,Y,ny+1); emit("E\n");
    } else c=en+1; }
  if(c<=CUT){ blen=mark; buf[blen]=0; static char a[65536],b[65536],t[140000]; fmtl(a,X,nx); fmtl(b,Y,ny);
    sprintf(t,"C %d %.0f %s %s\n",n,c,a,b); emit(t); }
  return c;
}
int main(int argc,char**argv){
  LOW=atof(argv[1]); LIM=atof(argv[2]); CUT=atof(argv[3]);
  static char cc[200001]; for(int i=2;i<=200000;i++) if(!cc[i]){PR[NP++]=i; for(long j=(long)i*i;j<=200000;j+=i) cc[j]=1;}
  double tot=0;
  for(int n=1;n<=30;n++){ int X[20000],Y[20000]; X[0]=2; blen=0; emit(""); double c=node(n,X,1,Y,0); tot+=c; printf("N %d %.0f\n%s",n,c,buf); fflush(stdout); }
  fprintf(stderr,"total %.3e\n",tot);
}
