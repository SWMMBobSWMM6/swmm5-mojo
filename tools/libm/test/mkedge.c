/* mkedge.c - edge-case test vectors for the ports of glibc's math routines, computed with the system libm.
   Same record format as mkvectors.c. Covers what the random vectors reach rarely: huge sin/cos/tan
   arguments (the __branred path), arguments near multiples of pi/2, pow with negative bases and integer
   exponents, pow and exp results near overflow and underflow (including subnormal results), log of
   subnormals and of values near 1, asin/acos near +-1, atan of huge and tiny arguments.
   Written by Claude (Anthropic). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
static uint64_t s = 0x9E3779B97F4A7C15ull;
static uint64_t xr(void){ s ^= s<<13; s ^= s>>7; s ^= s<<17; return s; }
static double asd(uint64_t u){ double d; memcpy(&d,&u,8); return d; }
static double uni(double a, double b){ return a + (b-a) * ((double)(xr()>>11) / 9007199254740992.0); }
static double lgu(int e0, int e1){ uint64_t r = xr(); return asd((r & 0x000fffffffffffffull) | ((uint64_t)(1023 + e0 + (int)((r>>52) % (uint64_t)(e1-e0))) << 52)); }
static double sg(double x){ return (xr() & 1) ? -x : x; }
static double nb(double x, int k){ uint64_t u; memcpy(&u,&x,8); u += k; return asd(u); }
typedef struct { const char *name; int nargs; double *a; long n, cap; } V;
static V vs[] = {{"exp",1},{"log",1},{"log10",1},{"pow",2},{"sin",1},{"cos",1},{"tan",1},{"asin",1},{"acos",1},{"atan",1}};
enum {NV = 10};
static void add(V *v, double x, double y) {
  if (v->n == v->cap) { v->cap = v->cap ? 2*v->cap : 1<<16; v->a = realloc(v->a, sizeof(double)*(v->nargs+1)*v->cap); }
  double *r = v->a + (v->nargs+1)*v->n++; r[0] = x; if (v->nargs > 1) r[1] = y;
}
static double call(int i, double *r) {
  switch (i) { case 0: return exp(r[0]); case 1: return log(r[0]); case 2: return log10(r[0]); case 3: return pow(r[0], r[1]);
    case 4: return sin(r[0]); case 5: return cos(r[0]); case 6: return tan(r[0]); case 7: return asin(r[0]); case 8: return acos(r[0]);
    default: return atan(r[0]); }
}
int main(int argc, char **argv) {
  long n = atol(argv[1]);
  for (long i = 0; i < n; i++) {
    double h = sg(lgu(20, 1024));                         /* huge: branred above 2^26.65 */
    double m = (double)(int64_t)uni(-1e6, 1e6) * M_PI_2;  /* near multiples of pi/2 */
    m = nb(m, (int)(xr() % 9) - 4);
    for (int k = 4; k <= 6; k++) { add(&vs[k], h, 0); add(&vs[k], m, 0); add(&vs[k], sg(lgu(-1074, -20)), 0); }
    { double x = -lgu(-40, 40); double y = (double)(int)uni(-40, 40); add(&vs[3], x, y);
      add(&vs[3], -uni(0.5, 2), (double)(int64_t)uni(-2000, 2000));            /* sign and over/underflow */
      add(&vs[3], uni(0.5, 2), uni(-1500, 1500));
      add(&vs[3], lgu(-1074, -1022), uni(-1, 1));                                /* subnormal base */
      add(&vs[3], nb(1.0, (int)(xr() % 2001) - 1000), sg(lgu(0, 60)));          /* base near 1 */
      add(&vs[3], -lgu(-10, 10), sg(lgu(53, 70)));                               /* huge even integer y */
      add(&vs[3], sg(lgu(-60, 60)), (double)(int)uni(-3, 4) + 0.5); }
    add(&vs[0], uni(700, 710), 0); add(&vs[0], uni(-746, -700), 0); add(&vs[0], sg(lgu(-1074, -30)), 0);
    add(&vs[1], lgu(-1074, -1022), 0); add(&vs[1], nb(1.0, (int)(xr() % 200001) - 100000), 0);
    add(&vs[2], lgu(-1074, -1022), 0); add(&vs[2], nb(1.0, (int)(xr() % 200001) - 100000), 0);
    add(&vs[2], pow(10.0, (double)(int)uni(-300, 300)), 0);
    for (int k = 7; k <= 8; k++) { add(&vs[k], sg(nb(1.0, -(int)(xr() % 100000))), 0); add(&vs[k], sg(lgu(-1074, -20)), 0); add(&vs[k], sg(uni(0.4, 0.6)), 0); }
    add(&vs[9], sg(lgu(20, 1024)), 0); add(&vs[9], sg(lgu(-1074, -20)), 0); add(&vs[9], sg(uni(0, 2)), 0);
  }
  FILE *o = fopen(argv[2], "wb");
  for (int i = 0; i < NV; i++) {
    V *v = &vs[i]; uint32_t m = v->n;
    fwrite(v->name, 1, strlen(v->name) + 1, o); fwrite(&m, 4, 1, o);
    for (long j = 0; j < v->n; j++) { double *r = v->a + (v->nargs+1)*j; double out[3]; memcpy(out, r, 8*v->nargs); out[v->nargs] = call(i, r); fwrite(out, 8, v->nargs+1, o); }
    fprintf(stderr, "%s %ld\n", v->name, v->n);
  }
  fclose(o);
  return 0;
}
