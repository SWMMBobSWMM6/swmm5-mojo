/* mkexact.c - test vectors, computed by C on this machine, for what the Mojo port does with doubles outside the
   transcendental functions: the math.h functions EPA calls that are exact in every library (sqrt, floor, ceil,
   fabs), and the C operations the runtime has to reproduce by hand (negation, the (float) cast, the (int) and
   (long) casts, x86's cvttsd2si), in the record format of tools/libm/test/mkvectors.c (name\0, n:u32, then
   n x (arg, result) as raw doubles; for d2i and d2l the result slot holds the integer's 64 bits).
   The special cases (signed zeros, NaN signs and payloads, infinities, huge arguments) are what this checks.
   gcc -O2 -fno-builtin -o mkexact mkexact.c -lm && ./mkexact N out.bin
   (Copied from lua/test/mkexact.c, itself adapted from php/test/mkexact.c.) Written by Claude (Anthropic) for Robert Dickinson; see ../README.md. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
static uint64_t s = 0x2545F4914F6CDD1Dull;
static uint64_t xr(void){ s ^= s<<13; s ^= s>>7; s ^= s<<17; return s; }
static double asd(uint64_t u){ double d; memcpy(&d,&u,8); return d; }
static double uni(double a, double b){ return a + (b-a) * ((double)(xr()>>11) / 9007199254740992.0); }
static double lgu(int e0, int e1){ uint64_t r = xr(); return asd((r & 0x800fffffffffffffull) | ((uint64_t)(1023 + e0 + (int)((r>>52) % (uint64_t)(e1-e0))) << 52)); }
static double anyd(void){ return asd(xr()); }
/* volatile keeps gcc from folding or reordering the operations under test */
static double neg(double x) { volatile double v = x; return -v; }
static double f32(double x) { volatile double v = x; volatile float f = (float)v; return (double)f; }
static double d2i(double x) { volatile double v = x; int64_t r = (int)v; double d; memcpy(&d, &r, 8); return d; }
static double d2l(double x) { volatile double v = x; int64_t r = (long)v; double d; memcpy(&d, &r, 8); return d; }
static double (*fn[8])(double) = {sqrt, floor, ceil, fabs, neg, f32, d2i, d2l};
static const char *names[8] = {"sqrt", "floor", "ceil", "fabs", "neg", "f32", "d2i", "d2l"};
int main(int argc, char **argv) {
  long n = atol(argv[1]);
  double sp[] = {0.0, -0.0, 1.0, -1.0, INFINITY, -INFINITY, NAN, -NAN, 0.5, -0.5, 0.49999999999999994, -0.49999999999999994,
    1e-310, -1e-310, 4503599627370495.5, -4503599627370495.5, 4503599627370496.0, 9007199254740993.0, 1e300, -1e300,
    asd(0x7ff0000000000123ull), asd(0xfff8000000000456ull), 2.5, -2.5, 1.5, -1.5, 0.9999999999999999, -0.9999999999999999,
    2147483647.0, 2147483647.9, 2147483648.0, -2147483648.0, -2147483648.9, -2147483649.0, 9.2233720368547758e18,
    -9.2233720368547758e18, 3.4028234663852886e38, 3.4028235677973366e38, 3.4028235677973362e38, 1.401298464324817e-45,
    7.006492321624085e-46, 7.006492321624087e-46, 1.1754942106924411e-38, 4.9e-324, 8.64e9};
  int nsp = sizeof sp / sizeof *sp;
  FILE *o = fopen(argv[2], "wb");
  for (int f = 0; f < 8; f++) {
    uint32_t m = (uint32_t)(n + nsp);
    fwrite(names[f], 1, strlen(names[f]) + 1, o); fwrite(&m, 4, 1, o);
    for (int i = 0; i < nsp; i++) { double r[2] = {sp[i], fn[f](sp[i])}; fwrite(r, 8, 2, o); }
    for (long i = 0; i < n; i++) {
      double x;
      switch (i % 6) {
      case 0: x = anyd(); break;                         /* any bit pattern: NaN payloads, subnormals, huge */
      case 1: x = uni(-1000, 1000); break;
      case 2: x = lgu(-60, 60); break;                  /* signed, wide range */
      case 3: x = (double)(int64_t)uni(-1e6, 1e6) + ((xr() & 1) ? 0.0 : 0.5); break;   /* integers and halves */
      case 4: x = lgu(-160, 140); break;                /* around the float range and its edges */
      default: x = uni(-2, 2) * ldexp(1.0, (int)(xr() % 70)); break;
      }
      double r[2] = {x, fn[f](x)};
      fwrite(r, 8, 2, o);
    }
  }
  fclose(o);
  return 0;
}
