/* mkstrtof.c - reference cases for sscanf's %f into a C float (strtof's single rounding, which converting the
   double strtod gives to float can miss): N decimal and hexadecimal texts, each with glibc's sscanf("%f") result
   as the float's bits, as lines  TEXT \t BITS. Most texts are chosen next to the midpoint between two floats,
   where rounding twice can go wrong. gcc -O2 -o mkstrtof mkstrtof.c && ./mkstrtof N
   Written by Claude (Anthropic) for Robert Dickinson; see ../README.md. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static uint64_t s = 0x9E3779B97F4A7C15ull;
static uint64_t xr(void) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; return s; }
int main(int argc, char **argv) {
  long n = atol(argv[1]);
  for (long i = 0; i < n; i++) {
    char t[80]; uint64_t r = xr();
    if (i % 4 == 3) {
      snprintf(t, sizeof t, "%.*g", 1 + (int)(r % 12), (double)(int64_t)(xr() % 2000000) / 997.0);
    } else {
      /* a float32 midpoint, nudged by a tiny relative amount or not at all, printed with 17 to 30 digits */
      uint32_t u = (uint32_t)(r % 0x7f000000u); float a, b; memcpy(&a, &u, 4); u++; memcpy(&b, &u, 4);
      double m = ((double)a + (double)b) / 2.0;
      int nudge = (int)((r >> 40) % 3) - 1;
      double x = m + nudge * m * 1e-17;
      snprintf(t, sizeof t, i % 4 == 2 ? "%.30e" : "%.17g", x);
    }
    float f = -77.0f; sscanf(t, "%f", &f);
    uint32_t b; memcpy(&b, &f, 4);
    printf("%s\t%08x\n", t, b);
  }
  return 0;
}
