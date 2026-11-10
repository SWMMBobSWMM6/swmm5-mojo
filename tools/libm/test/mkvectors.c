/* mkvectors.c - test vectors for the TypeScript/Java ports of glibc's math routines, computed with the
   system libm (the reference EPA links against). Inputs: N random arguments per function over the ranges
   SWMM uses, plus every argument sampled by the census of the 480 gate models (tools/libm/census.c).
   Output records: name\0 n:u32, then n x (args..., result) as raw doubles.  Also fma vectors (checked
   against the hardware fma via glibc's fma()).  Written by Claude (Anthropic). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <dirent.h>
static uint64_t s = 0x2545F4914F6CDD1Dull;
static uint64_t xr(void){ s ^= s<<13; s ^= s>>7; s ^= s<<17; return s; }
static double asd(uint64_t u){ double d; memcpy(&d,&u,8); return d; }
static double uni(double a, double b){ return a + (b-a) * ((double)(xr()>>11) / 9007199254740992.0); }
static double lgu(int e0, int e1){ uint64_t r = xr(); return asd((r & 0x800fffffffffffffull) | ((uint64_t)(1023 + e0 + (int)((r>>52) % (uint64_t)(e1-e0))) << 52)); }
static double pick(int i, double a, double b, int e0, int e1, int sign) { double x = (i & 1) ? uni(a, b) : lgu(e0, e1); return sign && (xr() & 1) ? -x : x; }
typedef struct { const char *name; int nargs; double *a; long n, cap; } V;
static V vs[] = {{"exp",1},{"log",1},{"log10",1},{"pow",2},{"sin",1},{"cos",1},{"tan",1},{"asin",1},{"acos",1},{"atan",1},{"fma",3}};
enum {NV = 11};
static void add(V *v, double x, double y, double z) {
  if (v->n == v->cap) { v->cap = v->cap ? 2*v->cap : 1<<16; v->a = realloc(v->a, sizeof(double)*(v->nargs+1)*v->cap); }
  double *r = v->a + (v->nargs+1)*v->n++; r[0] = x; if (v->nargs > 1) r[1] = y; if (v->nargs > 2) r[2] = z;
}
static double call(int i, double *r) {
  switch (i) { case 0: return exp(r[0]); case 1: return log(r[0]); case 2: return log10(r[0]); case 3: return pow(r[0], r[1]);
    case 4: return sin(r[0]); case 5: return cos(r[0]); case 6: return tan(r[0]); case 7: return asin(r[0]); case 8: return acos(r[0]);
    case 9: return atan(r[0]); default: return fma(r[0], r[1], r[2]); }
}
int main(int argc, char **argv) {
  long n = atol(argv[1]); const char *cdir = argc > 3 ? argv[3] : NULL;
  for (long i = 0; i < n; i++) {
    add(&vs[0], (i % 3 == 0) ? uni(-745, 710) : pick(i, -20, 20, -60, 10, 1), 0, 0);
    add(&vs[1], pick(i, 0.5, 2.0, -1022, 1023, 0), 0, 0);
    add(&vs[2], pick(i, 0.5, 2.0, -1022, 1023, 0), 0, 0);
    { double x = (i % 3 == 0) ? uni(0, 100) : (i % 3 == 1) ? lgu(-30, 30) : uni(0.5, 2); double y = (i & 1) ? uni(-5, 5) : (double)(int)uni(-10, 10);
      if (i % 5 == 0) y = 5.0/3.0; if (i % 7 == 0) y = 0.5; if (i % 11 == 0) y = 1.5; if (i % 13 == 0) y = 2.0/3.0; add(&vs[3], x, y, 0); }
    add(&vs[4], (i % 3 == 2) ? uni(-1e6, 1e6) : pick(i, -10, 10, -40, 8, 1), 0, 0);
    add(&vs[5], (i % 3 == 2) ? uni(-1e6, 1e6) : pick(i, -10, 10, -40, 8, 1), 0, 0);
    add(&vs[6], (i % 3 == 2) ? uni(-1e6, 1e6) : pick(i, -10, 10, -40, 8, 1), 0, 0);
    add(&vs[7], pick(i, -1, 1, -40, 0, 1), 0, 0);
    add(&vs[8], pick(i, -1, 1, -40, 0, 1), 0, 0);
    add(&vs[9], pick(i, -50, 50, -40, 60, 1), 0, 0);
    { double a = pick(i, -10, 10, -60, 60, 1), b = pick(i+1, -10, 10, -60, 60, 1), c = (i % 4 == 0) ? -a*b : pick(i, -10, 10, -60, 60, 1);
      if (i % 4 == 1) c = -a*b + ldexp(1.0, ilogb(a*b) - 53 - (int)(xr() % 3));
      if (i % 97 == 0) { a = lgu(-1070, 1020); b = lgu(-1070, 1020); c = lgu(-1074, 1023); }
      add(&vs[10], a, b, c); }
  }
  /* special values */
  double sp[] = {0.0, -0.0, 1.0, -1.0, INFINITY, -INFINITY, NAN, 0.5, 2.0, 1e-310, -1e-310, 709.78, -745.2, 1e308, 3.0, 0.1};
  for (int i = 0; i < 16; i++) for (int j = 0; j < 16; j++) { add(&vs[3], sp[i], sp[j], 0); add(&vs[10], sp[i], sp[j], sp[(i+j)%16]); }
  for (int i = 0; i < 16; i++) for (int k = 0; k < 10; k++) add(&vs[k], sp[i], sp[(i*7)%16], 0);
  /* census samples */
  if (cdir) {
    DIR *d = opendir(cdir); struct dirent *e;
    while ((e = readdir(d))) {
      if (e->d_name[0] == '.') continue;
      char p[4096]; snprintf(p, sizeof p, "%s/%s", cdir, e->d_name);
      FILE *f = fopen(p, "rb"); if (!f) continue;
      for (;;) {
        char name[16]; int c, k = 0;
        while ((c = fgetc(f)) > 0 && k < 15) name[k++] = c; name[k] = 0;
        if (c < 0) break;
        uint64_t count; uint32_t m; if (fread(&count, 8, 1, f) != 1 || fread(&m, 4, 1, f) != 1) break;
        int na = strcmp(name, "pow") == 0 ? 2 : 1;
        for (uint32_t j = 0; j < m; j++) {
          double r[2]; if (fread(r, 8, na, f) != (size_t)na) break;
          for (int q = 0; q < 10; q++) if (strcmp(vs[q].name, name) == 0) add(&vs[q], r[0], na > 1 ? r[1] : 0, 0);
        }
      }
      fclose(f);
    }
    closedir(d);
  }
  FILE *o = fopen(argv[2], "wb");
  for (int i = 0; i < NV; i++) {
    V *v = &vs[i]; uint32_t m = v->n;
    fwrite(v->name, 1, strlen(v->name) + 1, o); fwrite(&m, 4, 1, o);
    for (long j = 0; j < v->n; j++) { double *r = v->a + (v->nargs+1)*j; double out[4]; memcpy(out, r, 8*v->nargs); out[v->nargs] = call(i, r); fwrite(out, 8, v->nargs+1, o); }
    fprintf(stderr, "%s %ld\n", v->name, v->n);
  }
  fclose(o);
}
