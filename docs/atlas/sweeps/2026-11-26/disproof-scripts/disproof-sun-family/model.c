// model.c - local-obstruction census over classes n mod M.
// For a spec (mode 1/2 only) and a size X, take S_X = {s in list : s <= X}.
// For each class a mod M (M = product of the given prime powers), count
// U(a) = #{s in S_X : n - s is NOT locally blocked at any component}, where
// blocked at q^e means v_q(A m + B) is odd and < e for a bad prime q (odd q), or
// for q = 2 the odd part of A m + B is visibly in a forbidden class.
// Output: histogram of U over classes, and for kappa values, the expected number of
// n in [X, 2X) with no representation: X * mean_a exp(-kappa * U(a) / sqrt(ln X)).
// Also writes the worst classes (smallest U) to a file for the targeted search.
// usage: model spec X "q1^e1,q2^e2,..." worstfile nworst
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
typedef int64_t i64; typedef uint64_t u64;
#define MAXS 2048
#define WORDS (MAXS/64)
static int mode; static i64 QA,QB; static i64 S[MAXS]; static int ns;
static int bad(i64 q){ if(q==2) return 0; return mode==1 ? (q%4==3) : (q%8==5||q%8==7); }
// is residue N mod q^e (N = A m + B) visibly blocked?
static int blocked(i64 N, i64 q, int e, i64 qe){
  N%=qe; if(N<0) N+=qe; if(N==0) return 0;
  int v=0; while(N%q==0){ N/=q; v++; }
  if(q==2){ int need = (mode==2)?3:2; if(v+need>e) return 0; i64 u=N%(mode==2?8:4);
    if(mode==2) return (u==5||u==7); else return (QA%2==1) ? (u==3) : 0; }
  if(!bad(q)) return 0; return (v&1) && v<e; }
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); i64 t[8]; int dm[2],K;
  if(fscanf(f,"%ld %ld %ld %d %ld %ld %ld %d %d %ld %ld %d %d",&t[0],&t[1],&t[2],&dm[0],&t[3],&t[4],&t[5],&dm[1],&mode,&QA,&QB,&K,&ns)!=13) return 1;
  i64 *all=malloc(sizeof(i64)*ns); for(int i=0;i<ns;i++) if(fscanf(f,"%ld",&all[i])!=1) return 1; fclose(f);
  double X=atof(argv[2]); int n0=0; for(int i=0;i<ns;i++) if(all[i]<=X && n0<MAXS) S[n0++]=all[i]; ns=n0;
  // parse components
  i64 q[32],qe[32]; int e[32],nc=0; char*str=strdup(argv[3]); for(char*p=strtok(str,",");p;p=strtok(NULL,",")){ q[nc]=atol(p); char*c=strchr(p,'^'); e[nc]=c?atoi(c+1):1; qe[nc]=1; for(int j=0;j<e[nc];j++) qe[nc]*=q[nc]; nc++; }
  i64 M=1; for(int j=0;j<nc;j++) M*=qe[j];
  // tables: for component j and residue r mod qe[j]: bitmask over s of blocked
  u64 **tab=malloc(sizeof(u64*)*nc);
  for(int j=0;j<nc;j++){ tab[j]=calloc((size_t)qe[j]*WORDS,8);
    for(i64 r=0;r<qe[j];r++) for(int i=0;i<ns;i++){ i64 m=(r - S[i]%qe[j]); m%=qe[j]; if(m<0) m+=qe[j];
      i64 N=(QA*m+QB)%qe[j]; if(blocked(N,q[j],e[j],qe[j])) tab[j][r*WORDS+i/64]|=1ULL<<(i%64); } }
  // enumerate classes by mixed radix over components; class residue via CRT computed incrementally
  long long *H=calloc(ns+1,sizeof(long long)); int nw=(ns+63)/64;
  int idx[32]={0}; u64 acc[33][WORDS]; memset(acc,0,sizeof acc);
  // CRT coefficients
  i64 crt[32]; for(int j=0;j<nc;j++){ i64 Mj=M/qe[j]; i64 inv=0; for(i64 x=1;x<qe[j];x++) if((__int128)(Mj%qe[j])*x%qe[j]==1){inv=x;break;} if(qe[j]==1) inv=0; crt[j]=(i64)((__int128)Mj*inv%M); }
  int nworst=atoi(argv[5]); FILE*fw=fopen(argv[4],"w"); int Uthr_last=0; (void)Uthr_last;
  // keep classes with U <= threshold Uthr (chosen after a first pass): two passes
  for(int pass=0;pass<2;pass++){
    int Uthr=-1; long long cum=0; int changed=0;
    if(pass==1){ for(int u=0;u<=ns;u++){ cum+=H[u]; if(cum>=nworst){ Uthr=u; break; } } if(Uthr<0) Uthr=ns; fprintf(stderr,"Uthr=%d (cum %lld)\n",Uthr,cum); }
    memset(idx,0,sizeof idx);
    for(;;){
      // compute acc from level 0..nc-1 (recompute incrementally from changed level)
      for(int j=changed;j<nc;j++) for(int w=0;w<nw;w++) acc[j+1][w]=acc[j][w]|tab[j][(i64)idx[j]*WORDS+w];
      int blk=0; for(int w=0;w<nw;w++) blk+=__builtin_popcountll(acc[nc][w]); int U=ns-blk;
      if(pass==0) H[U]++; else if(U<=Uthr){ i64 a=0; for(int j=0;j<nc;j++) a=(i64)(((__int128)a+(__int128)crt[j]*idx[j])%M); fprintf(fw,"%ld %d\n",(long)a,U); }
      int j=nc-1; while(j>=0){ idx[j]++; if(idx[j]<qe[j]) break; idx[j]=0; j--; } if(j<0) break; changed=j;
    }
  }
  fclose(fw);
  printf("# spec %s X=%g M=%ld ns=%d\n",argv[1],X,(long)M,ns);
  double mean=0; for(int u=0;u<=ns;u++) mean+=u*(double)H[u]/M; printf("meanU %.2f\n",mean);
  printf("U-hist (lowest):"); int shown=0; for(int u=0;u<=ns && shown<25;u++) if(H[u]){ printf(" %d:%lld",u,H[u]); shown++; } printf("\n");
  if(argc>6){ FILE*fh=fopen(argv[6],"w"); fprintf(fh,"%ld %d\n",(long)M,ns); for(int u=0;u<=ns;u++) if(H[u]) fprintf(fh,"%d %lld\n",u,H[u]); fclose(fh); }
  double L=sqrt(log(X));
  for(double kap=0.2;kap<=3.01;kap+=0.2){ double E=0; for(int u=0;u<=ns;u++) E+=(double)H[u]/M*exp(-kap*u/L); printf("kappa %.1f  E[exc in [X,2X)] = %.4g\n",kap,E*X); }
  return 0; }
