// Test WOWII open conjectures 40, 133, 189, 199 (formal-conjectures definitions) on graph6 input.
// Each conjecture checked literally against the fc definitions:
//  40: ceil((pc + b + 1)/2) <= f        (pc path cover number, b largest induced bipartite, f largest induced forest)
// 133: rad + l^{cC4} <= path            (l = average independence number of open neighbourhoods; cC4=1 iff no (not nec. induced) C4)
// 189: max_v distEven(v) <= 1 + sigma2  ==> Hamiltonian path   (sigma2 = second smallest degree)
// 199: tree - 2 (truncated) <= kappa    ==> Hamiltonian path
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MAXN 16
static int n; static uint32_t adj[MAXN];
static int ecnt[1<<MAXN]; static unsigned char conn[1<<MAXN];
static long long cnt=0, fail40=0, fail133=0, hyp189=0, fail189=0, hyp199=0, fail199=0;
static int minslack40=99; static double minslack133=99;

static int parse(char *s){
  int len=strlen(s); while(len&&(s[len-1]=='\n'||s[len-1]=='\r')) s[--len]=0;
  n=s[0]-63; memset(adj,0,sizeof adj);
  int k=0; int bitpos=0; unsigned char *p=(unsigned char*)s+1;
  for(int j=1;j<n;j++) for(int i=0;i<j;i++){
    int byte=p[bitpos/6]-63; int bit=(byte>>(5-bitpos%6))&1; bitpos++;
    if(bit){adj[i]|=1u<<j; adj[j]|=1u<<i;}
  }
  (void)k; return n;
}
static int isconn(uint32_t S){
  if(!S) return 0; uint32_t seen=S&(-S), fr=seen;
  while(fr){ uint32_t nf=0; for(uint32_t t=fr;t;t&=t-1){int v=__builtin_ctz(t); nf|=adj[v];} nf&=S&~seen; seen|=nf; fr=nf; }
  return seen==S;
}
static int bip(uint32_t S){ // induced bipartite?
  uint32_t rem=S;
  while(rem){ uint32_t c0=rem&(-rem), c1=0, fr=c0, all=c0;
    while(fr){ uint32_t nb=0; for(uint32_t t=fr;t;t&=t-1) nb|=adj[__builtin_ctz(t)]; nb&=S;
      // fr in side A (either c0 or c1); determine
      if(fr&c0){ if(nb&c0) return 0; uint32_t nw=nb&~all; c1|=nb; all|=nw; fr=nw; }
      else { if(nb&c1) return 0; uint32_t nw=nb&~all; c0|=nb; all|=nw; fr=nw; }
      if(c0&c1) return 0;
    }
    rem&=~all; }
  return 1;
}
static int comps(uint32_t S){ int c=0; uint32_t rem=S; while(rem){ uint32_t seen=rem&(-rem), fr=seen;
  while(fr){ uint32_t nf=0; for(uint32_t t=fr;t;t&=t-1) nf|=adj[__builtin_ctz(t)]; nf&=S&~seen; seen|=nf; fr=nf;} rem&=~seen; c++;} return c; }
static uint32_t ends[1<<MAXN];
static int hampath(void){ // ends[mask]: set of v that can end a path with vertex set mask
  int N=1<<n; for(int m=0;m<N;m++) ends[m]=0;
  for(int v=0;v<n;v++) ends[1u<<v]=1u<<v;
  for(int m=1;m<N;m++){ uint32_t e=ends[m]; if(!e) continue;
    uint32_t ext=0; for(uint32_t t=e;t;t&=t-1) ext|=adj[__builtin_ctz(t)]; ext&=~m;
    for(uint32_t t=ext;t;t&=t-1){int u=__builtin_ctz(t); if(adj[u]&e) ends[m|(1u<<u)]|=1u<<u;} }
  return ends[N-1]!=0;
}
static int pathcover(void){ // needs ends[] filled; min partition into path-sets
  int N=1<<n; static unsigned char best[1<<MAXN];
  best[0]=0;
  for(int m=1;m<N;m++){ int low=__builtin_ctz(m); uint32_t rest=m&~(1u<<low); int b=99;
    // submask containing low
    for(uint32_t s=rest;;s=(s-1)&rest){ uint32_t sub=s|(1u<<low); if(ends[sub]){int c=1+best[m&~sub]; if(c<b)b=c;} if(!s)break; }
    best[m]=b; }
  return best[N-1];
}
static int dist[MAXN][MAXN];
static void apsp(void){ for(int s=0;s<n;s++){ for(int t=0;t<n;t++) dist[s][t]=-1; dist[s][s]=0; uint32_t seen=1u<<s, fr=seen; int d=0;
  while(fr){ d++; uint32_t nf=0; for(uint32_t t=fr;t;t&=t-1) nf|=adj[__builtin_ctz(t)]; nf&=~seen; for(uint32_t t=nf;t;t&=t-1) dist[s][__builtin_ctz(t)]=d; seen|=nf; fr=nf; } } }
static int alpha(uint32_t S){ if(!S) return 0; int v=__builtin_ctz(S); uint32_t r=S&~(1u<<v);
  int a=alpha(r&~adj[v])+1; if(!(adj[v]&r)) return a; int b2=alpha(r); return a>b2?a:b2; }
int main(int argc,char**argv){
  char line[256];
  while(fgets(line,sizeof line,stdin)){
    parse(line); cnt++; int N=1<<n; uint32_t FULL=N-1;
    ecnt[0]=0; int f=0,bb=0,tree=0,pth=0,kappa=n-1;
    for(int m=1;m<N;m++){ int v=__builtin_ctz(m); uint32_t r=m&~(1u<<v); ecnt[m]=ecnt[r]+__builtin_popcount(adj[v]&r); }
    for(int m=1;m<N;m++){ int sz=__builtin_popcount(m);
      int c=comps(m); conn[m]=(c==1);
      if(ecnt[m]==sz-c){ if(sz>f) f=sz; if(c==1){ if(sz>tree) tree=sz;
          int ok=1; for(uint32_t t=m;t;t&=t-1) if(__builtin_popcount(adj[__builtin_ctz(t)]&m)>2){ok=0;break;}
          if(ok&&sz>pth) pth=sz; } }
      if(sz>bb && bip(m)) bb=sz;
    }
    // kappa: min |S| with G-S disconnected (fc: induce on complement not Connected; empty complement is not connected in Mathlib)
    for(int m=0;m<N;m++){ int sz=__builtin_popcount(m); if(sz>=kappa) continue; uint32_t c=FULL&~m; if(!conn[c]) kappa=sz; }
    if(n<=1) kappa=0;
    int hp=hampath();
    if(getenv("DBG")) printf("INV %d %d %d %d %d %d %d\n",f,bb,tree,pth,kappa,hp,hp?1:pathcover());
    // 40
    int pc=hp?1:pathcover();
    { int lhs=(pc+bb+1+1)/2; /* ceil((pc+bb+1)/2) */ int sl=f-lhs; if(sl<minslack40) minslack40=sl; if(sl<0){fail40++; printf("FAIL40 %s pc=%d b=%d f=%d\n",line,pc,bb,f);} }
    // 133
    apsp(); int rad=99; for(int s=0;s<n;s++){int e=0; for(int t=0;t<n;t++) if(dist[s][t]>e) e=dist[s][t]; if(e<rad) rad=e;}
    int hasC4=0; for(int a=0;a<n&&!hasC4;a++) for(int c=a+1;c<n;c++) if(__builtin_popcount(adj[a]&adj[c])>=2){hasC4=1;break;}
    double lhs133;
    if(hasC4) lhs133=rad+1.0; else { int s=0; for(int v=0;v<n;v++) s+=alpha(adj[v]); lhs133=rad+(double)s/n; }
    { double sl=pth-lhs133; if(sl<minslack133) minslack133=sl; if(sl<-1e-9){fail133++; printf("FAIL133 %s rad=%d path=%d C4=%d lhs=%.4f\n",line,rad,pth,hasC4,lhs133);} }
    // 189
    { int deg[MAXN]; for(int v=0;v<n;v++) deg[v]=__builtin_popcount(adj[v]);
      for(int i=1;i<n;i++){int x=deg[i],j=i-1; while(j>=0&&deg[j]>x){deg[j+1]=deg[j];j--;} deg[j+1]=x;}
      int sig=deg[1]; int mx=0; for(int s=0;s<n;s++){int c=0; for(int t=0;t<n;t++) if(dist[s][t]%2==0) c++; if(c>mx) mx=c;}
      if(mx<=1+sig){ hyp189++; if(!hp){fail189++; printf("FAIL189 %s maxeven=%d sigma=%d\n",line,mx,sig);} } }
    // 199
    { int lhs=tree>=2?tree-2:0; if(lhs<=kappa){ hyp199++; if(!hp){fail199++; printf("FAIL199 %s tree=%d kappa=%d\n",line,tree,kappa);} } }
  }
  fprintf(stderr,"graphs=%lld fail40=%lld minslack40=%d fail133=%lld minslack133=%.4f hyp189=%lld fail189=%lld hyp199=%lld fail199=%lld\n",
    cnt,fail40,minslack40,fail133,minslack133,hyp189,fail189,hyp199,fail199);
  return 0;
}
