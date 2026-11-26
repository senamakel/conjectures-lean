// hs.c - exhaustive scan with near-miss histogram for statements
//   n = s + F(c) + G(d),  s in a finite sorted list of sparse values,
//   F(c) = (fa c^2 + fb c)/fd,  G(d) = (ga d^2 + gb d)/gd, c,d in Z or in N (dom flag 1 = N).
// r(n) := #{distinct s in list, s <= n : n - s in Q},  Q = {F(c)+G(d)}.
// Stage 1: bitset of Q on a window, bit-sliced saturating counters over shifts s <= SW.
// Stage 2: for n with r_small < K, add large s using an exact membership test.
// Exact tests: mode 0 generic loop; mode 1: Q = {m : A m + B is a sum of two squares};
//              mode 2: Q = {m : A m + B is x^2 + 2y^2}.   (A,B in spec)
// usage: hs spec lo hi threads outprefix
// spec: "fa fb fd domF\nga gb gd domG\nmode A B\nK\nns\n s1 s2 ..."
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <omp.h>
typedef __int128 i128; typedef unsigned __int128 u128;
typedef uint64_t u64; typedef int64_t i64;
static i64 fa,fb,fd,ga,gb,gdd; static int domF,domG,mode,K; static i64 QA,QB;
static i64 *sv; static int ns;
#define BLK (1LL<<28)
#define SW  (1LL<<27)
static inline i64 F(i64 c){ return (i64)(((i128)fa*c*c+(i128)fb*c)/fd); }
static inline i64 G(i64 d){ return (i64)(((i128)ga*d*d+(i128)gb*d)/gdd); }
static int isG(i64 m){ if(m<0) return 0; i128 D=(i128)gb*gb+(i128)4*ga*gdd*m; long double r=sqrtl((long double)D); i64 s=(i64)r;
  for(i64 t=s-2;t<=s+2;t++){ if(t<0)continue; if((i128)t*t==D){ for(int sg=-1;sg<=1;sg+=2){ i128 num=-gb+sg*(i128)t; if(num%(2*ga)==0){ i64 d=(i64)(num/(2*ga)); if(domG && d<0) continue; if(G(d)==m) return 1; } } } } return 0; }
static int isQgen(i64 m){ if(m<0) return 0;
  for(int sg=0;sg<(domF?1:2);sg++) for(i64 c=(sg?-1:0);;c+=(sg?-1:1)){ i64 f=F(c); if(f>m){ if((sg==0&&c>3)||(sg==1&&c<-3)) break; else continue; } if(isG(m-f)) return 1; }
  return 0; }
// ---- factoring helpers
static inline u64 mulm(u64 a,u64 b,u64 m){ return (u64)((u128)a*b%m); }
static u64 powm(u64 a,u64 e,u64 m){ u64 r=1; a%=m; while(e){ if(e&1) r=mulm(r,a,m); a=mulm(a,a,m); e>>=1;} return r; }
static int isprime(u64 n){ if(n<2) return 0; static const u64 sp[]={2,3,5,7,11,13,17,19,23,29,31,37};
  for(int i=0;i<12;i++){ if(n%sp[i]==0) return n==sp[i]; }
  u64 d=n-1; int s=0; while(!(d&1)){d>>=1;s++;}
  for(int i=0;i<12;i++){ u64 x=powm(sp[i],d,n); if(x==1||x==n-1) continue; int ok=0; for(int r=1;r<s;r++){ x=mulm(x,x,n); if(x==n-1){ok=1;break;} } if(!ok) return 0; } return 1; }
static u64 gcdu(u64 a,u64 b){ while(b){u64 t=a%b;a=b;b=t;} return a; }
static u64 rho(u64 n){ if(n%2==0) return 2; for(u64 c=1;;c++){ u64 x=2,y=2,d=1; while(d==1){ x=(mulm(x,x,n)+c)%n; y=(mulm(y,y,n)+c)%n; y=(mulm(y,y,n)+c)%n; d=gcdu(x>y?x-y:y-x,n);} if(d!=n) return d; } }
static int NP;
static unsigned *pr;
static int badp(u64 p){ return mode==1 ? (p%4==3) : ((p%8==5)||(p%8==7)); }
// returns 1 if every bad prime has even exponent in n (n>=1)
static int goodrest(u64 n){ if(n==1) return 1; u64 r=(u64)sqrtl((long double)n); while(r*r>n) r--; while((r+1)*(r+1)<=n) r++;
  if(r*r==n) return 1; if(isprime(n)) return !badp(n);
  u64 d=rho(n); u64 e=n/d; // n has prime factors > trial bound; handle recursively by exponent parity
  // combine: count parity of each bad prime: factor fully
  u64 st[64]; int sp=0; u64 fs[64]; int nf=0; st[sp++]=d; st[sp++]=e;
  while(sp){ u64 x=st[--sp]; if(x==1) continue; if(isprime(x)){ fs[nf++]=x; continue; } u64 y=rho(x); st[sp++]=y; st[sp++]=x/y; }
  for(int i=0;i<nf;i++){ if(!badp(fs[i])) continue; int c=0; for(int j=0;j<nf;j++) if(fs[j]==fs[i]) c++; if(c&1) return 0; }
  return 1; }
static int isQfac(i64 m0){ if(m0<0) return 0; u64 n=(u64)((i128)QA*m0+QB); if(n==0) return 1;
  while(!(n&1)) n>>=1; // 2 is never bad (sum of two squares: 2 ok; x^2+2y^2: 2 ok)
  for(int i=1;i<NP;i++){ u64 p=pr[i]; if(p*p*p>n) break; if(n%p==0){ int e=0; while(n%p==0){n/=p;e++;} if((e&1)&&badp(p)) return 0; } }
  return goodrest(n); }
static inline int isQ(i64 m){ return mode==0 ? isQgen(m) : isQfac(m); }
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); if(!f){perror("spec");return 1;}
  if(fscanf(f,"%ld %ld %ld %d %ld %ld %ld %d %d %ld %ld %d %d",&fa,&fb,&fd,&domF,&ga,&gb,&gdd,&domG,&mode,&QA,&QB,&K,&ns)!=13){fprintf(stderr,"bad spec\n");return 1;}
  sv=malloc(sizeof(i64)*ns); for(int i=0;i<ns;i++) if(fscanf(f,"%ld",&sv[i])!=1){fprintf(stderr,"bad list\n");return 1;} fclose(f);
  i64 lo=(i64)atof(argv[2]), hi=(i64)atof(argv[3]); int th=atoi(argv[4]); char*out=argv[5];
  { int L=1<<21; char*s=calloc(L,1); pr=malloc(sizeof(unsigned)*200000); NP=0; for(int i=2;i<L;i++) if(!s[i]){ pr[NP++]=i; for(long j=(long)i*i;j<L;j+=i) s[j]=1; } free(s); }
  int nsmall=0; while(nsmall<ns && sv[nsmall]<=SW) nsmall++;
  i64 nblk=(hi-lo+BLK-1)/BLK; int NB=64; long long (*hist)[16]=calloc(NB,sizeof(*hist));
  char fn[512]; snprintf(fn,512,"%s.low",out); FILE*fo=fopen(fn,"a");
  omp_set_num_threads(th);
  #pragma omp parallel
  { u64 W=(BLK+SW)/64+4; u64*R=malloc(8*W); u64*P=malloc(8*(size_t)K*(BLK/64+2)); long long lh[64][16]; memset(lh,0,sizeof lh);
    #pragma omp for schedule(dynamic,1)
    for(i64 bi=0;bi<nblk;bi++){
      i64 L=lo+bi*BLK; i64 base=L-SW; i64 top=L+BLK; if(top>hi) top=hi; memset(R,0,8*W);
      for(int sg=0;sg<(domF?1:2);sg++) for(i64 c=(sg?-1:0);;c+=(sg?-1:1)){
        i64 fv=F(c); if(fv>=top){ if((sg==0&&c>3)||(sg==1&&c<-3)) break; else continue; }
        i64 lowv=base-fv; if(lowv<0) lowv=0; i64 hiv=top-fv;
        for(int dsg=0; dsg<(domG?1:2); dsg++){
          long double A=(long double)ga/gdd, Bq=(long double)(dsg?-gb:gb)/gdd;
          long double e0=(-Bq+sqrtl(Bq*Bq+4*A*(long double)lowv))/(2*A);
          i64 e=(i64)e0-3; if(e<(dsg?1:0)) e=(dsg?1:0);
          // make sure we did not start past the window for small e (vertex region): start at min when lowv small
          if(lowv<1000) e=(dsg?1:0);
          for(;;e++){ i64 d=dsg?-e:e; i64 g=G(d); if(g>=hiv){ if(e>6) break; else continue; } if(g>=lowv){ i64 j=fv+g-base; R[j>>6]|=1ULL<<(j&63);} }
        }
      }
      i64 nw=(top-L+63)/64; memset(P,0,8*(size_t)K*(BLK/64+2));
      for(int t=0;t<nsmall;t++){ i64 s=sv[t]; i64 off=SW-s; u64 wq=off>>6,bq=off&63;
        for(i64 w=0;w<nw;w++){ u64 v= bq? (R[w+wq]>>bq)|(R[w+wq+1]<<(64-bq)) : R[w+wq];
          for(int k=K-1;k>=1;k--) P[(size_t)k*(BLK/64+2)+w]|=P[(size_t)(k-1)*(BLK/64+2)+w]&v;
          P[w]|=v; } }
      u64*PK=P+(size_t)(K-1)*(BLK/64+2);
      for(i64 w=0;w<nw;w++) if(~PK[w]) for(int b=0;b<64;b++) if(!((PK[w]>>b)&1)){
        i64 n=L+w*64+b; if(n>=top) continue; int r=0; for(int k=0;k<K-1;k++) if((P[(size_t)k*(BLK/64+2)+w]>>b)&1) r=k+1;
        for(int t=nsmall;t<ns && r<K;t++){ i64 s=sv[t]; if(s>n) break; if(isQ(n-s)) r++; }
        int oc=63-__builtin_clzll((u64)n|1); if(oc>63) oc=63; if(r<16) lh[oc][r]++;
        if(r<=1){
          #pragma omp critical
          { fprintf(fo,"%ld %d\n",(long)n,r); fflush(fo); }
        }
      }
    }
    #pragma omp critical
    { for(int o=0;o<64;o++) for(int r=0;r<16;r++) hist[o][r]+=lh[o][r]; }
    free(R); free(P);
  }
  fclose(fo);
  snprintf(fn,512,"%s.hist",out); FILE*fh=fopen(fn,"a");
  fprintf(fh,"# range %ld %ld K=%d ns=%d nsmall=%d\n",(long)lo,(long)hi,K,ns,nsmall);
  for(int o=0;o<64;o++){ int any=0; for(int r=0;r<K;r++) if(hist[o][r]) any=1; if(!any) continue; fprintf(fh,"oct %d",o); for(int r=0;r<K;r++) fprintf(fh," %lld",hist[o][r]); fprintf(fh,"\n"); }
  fclose(fh); fprintf(stderr,"done %s [%ld,%ld)\n",out,(long)lo,(long)hi); return 0; }
