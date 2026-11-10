/* powtime.c - nanoseconds per call of the system glibc's pow (and sin, cos) on SWMM-like arguments, for
   comparison with go/internal/powtime. Same generator, same argument sets.  gcc -O2 powtime.c -lm
   Written by Claude (Anthropic); see AI-USE.md. */
#include <stdio.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#define N 2000000
static double X[N], Y[N];
static uint64_t s = 88172645463325252ULL;
static double u(void) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; return (s >> 11) * 0x1.0p-53; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
int main(void) {
    for (int i = 0; i < N; i++) { X[i] = 0.001 + 100.0 * u(); Y[i] = (i % 3 == 0) ? 0.6666666666666666 : (i % 3 == 1) ? 1.6666666666666667 : -4.0 + 8.0 * u(); }
    volatile double acc = 0;
    for (int r = 0; r < 3; r++) {
        double t0 = now(); double a = 0; for (int i = 0; i < N; i++) a += pow(X[i], Y[i]); double t1 = now(); acc += a;
        double b = 0; for (int i = 0; i < N; i++) b += sin(X[i]); double t2 = now(); acc += b;
        double c = 0; for (int i = 0; i < N; i++) c += cos(X[i]); double t3 = now(); acc += c;
        if (r == 2) printf("glibc (C)        pow %5.1f ns   sin %5.1f ns   cos %5.1f ns\n", 1e9 * (t1 - t0) / N, 1e9 * (t2 - t1) / N, 1e9 * (t3 - t2) / N);
    }
    return acc == 0.12345;
}
