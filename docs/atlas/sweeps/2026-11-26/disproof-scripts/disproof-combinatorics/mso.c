/* Jamison caterpillar question: among trees of order n (gentreeg -p parent arrays on stdin),
   find the maximum mean subtree order R/N and report whether every maximiser is a caterpillar. */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
typedef unsigned long long u64; typedef unsigned __int128 u128;
int main(){ char line[512]; u64 bR=0,bN=1; int cnt=0, allcat=1; long trees=0; char best[512]="";
  int par[64]; u64 f[64]; u128 g[64]; int deg[64];
  while(fgets(line,sizeof line,stdin)){ int n=0; char*p=line; while(*p){ while(*p==' ') p++; if(*p<'0'||*p>'9') break; par[++n]=strtol(p,&p,10); }
    if(!n) continue; trees++;
    for(int i=1;i<=n;i++){ f[i]=1; g[i]=0; deg[i]=0; }
    /* g[i] accumulates sum over children of g(c)/(1+f(c)) * f(i) later: use two passes */
    static u128 gs[64]; for(int i=1;i<=n;i++) gs[i]=0;
    for(int i=n;i>=1;i--){ /* children of i already final */
      /* f[i] is product over children (1+f(c)) accumulated; g[i] = f[i]*(1 + sum_c g(c)/(1+f(c))) */
      u128 G=f[i]; /* subtrees rooted at i: each contributes 1 for i */
      /* recompute contributions: need per-child data; done via gs list */
      G += gs[i]; g[i]=G;
      int q=par[i]; if(q){ deg[i]++; deg[q]++;
        /* adding child i to q: f[q] *= (1+f[i]); gs[q] = gs[q]*(1+f[i]) + g[i]*f_old[q] */
        u64 fo=f[q]; gs[q]=gs[q]*(u128)(1+f[i]) + g[i]*(u128)fo; f[q]=fo*(1+f[i]); }
    }
    u128 N=0,R=0; for(int i=1;i<=n;i++){ N+=f[i]; R+=g[i]; }
    u128 lhs=R*(u128)bN, rhs=(u128)bR*N;
    if(lhs>rhs || lhs==rhs){ int cat=1; /* remove leaves; remainder must be a path */
      int d2[64]; int m=0; for(int i=1;i<=n;i++) d2[i]=0;
      for(int i=2;i<=n;i++){ int a=i,b=par[i]; if(deg[a]>1 && deg[b]>1){ d2[a]++; d2[b]++; } }
      for(int i=1;i<=n;i++) if(deg[i]>1 && d2[i]>2) cat=0;
      if(lhs>rhs){ bR=(u64)R; bN=(u64)N; cnt=1; allcat=cat; strcpy(best,line); }
      else { cnt++; if(!cat) allcat=0; } }
  }
  printf("trees=%ld max mean=%llu/%llu=%.6f maximisers=%d all_caterpillar=%d example=%s",trees,bR,bN,(double)bR/bN,cnt,allcat,best); return 0; }
