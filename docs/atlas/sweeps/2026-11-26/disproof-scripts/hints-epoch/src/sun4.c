// n = s + F(c) + G(d), s=(2^a q^b)^2, a,b>=0, c,d in Z, F(c)=(fa c^2+fb c)/fd, G(d)=(ga d^2+gb d)/gd
// usage: sun3 q fa fb fd ga gb gd lo hi   -> prints n in [lo,hi) with no representation
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
typedef __int128 i128;
static long p1,fnn,q,fa,fb,fd,ga,gb,gdn;
static inline int64_t F(int64_t c){ return (int64_t)(((i128)fa*c*c+(i128)fb*c)/fd); }
static inline int64_t G(int64_t d){ return (int64_t)(((i128)ga*d*d+(i128)gb*d)/gdn); }
// is m = G(d) for some integer d?  ga d^2 + gb d - gd*m = 0 -> d = (-gb ± sqrt(gb^2+4 ga gd m))/(2ga)
static int isG(int64_t m){ if(m<0) return 0; i128 D=(i128)gb*gb+(i128)4*ga*gdn*m; long double r=sqrtl((long double)D); int64_t s=(int64_t)r; 
  for(int64_t t=s-2;t<=s+2;t++){ if(t<0)continue; if((i128)t*t==D){ for(int sg=-1;sg<=1;sg+=2){ i128 num=-gb+sg*(i128)t; if(num%(2*ga)==0){ int64_t d=(int64_t)(num/(2*ga)); if(G(d)==m) return 1; } } } } return 0; }
static int isFG(int64_t m){ // exists c: m-F(c) in G
  for(int sg=0;sg<(fnn?1:2);sg++) for(int64_t c=(sg?-1:0);;c+=(sg?-1:1)){ int64_t f=F(c); if(f>m) { if((sg==0&&c>2)||(sg==1&&c<-2)) break; else continue; } if(isG(m-f)) return 1; }
  return 0; }
#define B (1LL<<28)
#define S (1LL<<26)
int main(int argc,char**argv){
  p1=atol(argv[1]); q=atol(argv[2]); fa=atol(argv[3]); fb=atol(argv[4]); fd=atol(argv[5]); fnn=atol(argv[6]); ga=atol(argv[7]); gb=atol(argv[8]); gdn=atol(argv[9]); argv+=2;
  int64_t lo=atoll(argv[8]), hi=atoll(argv[9]);
  int64_t sv[8192]; int ns=0;
  for(i128 x=1; x*x < ((i128)1<<62); x*=p1) for(i128 y=x; y*y < ((i128)1<<62); y*=q) sv[ns++]=(int64_t)(y*y);
  for(int i=1;i<ns;i++){int64_t v=sv[i];int j=i-1;while(j>=0&&sv[j]>v){sv[j+1]=sv[j];j--;}sv[j+1]=v;}
  uint64_t W=(B+S)/64+2; uint64_t*R=malloc(8*W),*O=malloc(8*(B/64+2)); long found=0;
  for(int64_t L=lo; L<hi; L+=B){
    int64_t base=L-S; int64_t top=L+B; memset(R,0,8*W);
    // enumerate c both signs
    for(int sg=0;sg<(fnn?1:2);sg++) for(int64_t c=(sg?-1:0);;c+=(sg?-1:1)){
      int64_t f=F(c); if(f>=top){ if((sg==0&&c>2)||(sg==1&&c<-2)) break; else continue; }
      int64_t lowv=base-f; if(lowv<0) lowv=0; int64_t hiv=top-f; // G(d) in [lowv,hiv)
      for(int dsg=0; dsg<2; dsg++){
        // d = dsg? -e : e ; e>=0 (dsg=1: e>=1). find e0 approx with G ~ lowv
        long double A=(long double)ga/gdn, Bq=(long double)(dsg?-gb:gb)/gdn;
        long double e0=( -Bq + sqrtl(Bq*Bq+4*A*(long double)lowv) )/(2*A);
        int64_t e=(int64_t)e0-3; if(e<(dsg?1:0)) e=(dsg?1:0);
        // walk back if needed (G monotone for e>= small)
        for(;;e++){ int64_t d=dsg?-e:e; int64_t g=G(d); if(g>=hiv){ if(e>5) break; else continue; } if(g>=lowv){ int64_t j=f+g-base; R[j>>6]|=1ULL<<(j&63);} }
      }
    }
    memset(O,0,8*(B/64+2));
    for(int t=0;t<ns;t++){ int64_t s=sv[t]; if(s>S) break; int64_t off=S-s; uint64_t wq=off>>6,bq=off&63;
      for(int64_t w=0;w<B/64;w++){ uint64_t v= bq? (R[w+wq]>>bq)|(R[w+wq+1]<<(64-bq)) : R[w+wq]; O[w]|=v; } }
    for(int64_t w=0;w<B/64;w++) if(~O[w]) for(int b=0;b<64;b++) if(!((O[w]>>b)&1)){
      int64_t n=L+w*64+b; if(n>=hi) continue; int ok=0;
      for(int t=0;t<ns;t++){ int64_t s=sv[t]; if(s>n) break; if(s<=S) continue; if(isFG(n-s)){ok=1;break;} }
      if(!ok){ printf("UNREP n=%ld\n",(long)n); fflush(stdout); found++; } }
  }
  fprintf(stderr,"q=%ld F=(%ld,%ld)/%ld G=(%ld,%ld)/%ld [%ld,%ld) unrep=%ld\n",q,fa,fb,fd,ga,gb,gdn,(long)lo,(long)hi,found); return 0; }
