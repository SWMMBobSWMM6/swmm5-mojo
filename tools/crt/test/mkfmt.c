/* mkfmt.c - reference cases for the Go port's printf/strtod/sscanf, from the system glibc.
   Writes lines  KIND \t FORMAT \t ARG \t RESULT  (ARG and RESULT hex-encoded) to stdout.
   KIND: f (double arg), i (int), l (long), s (string), d (strtod: ARG text, RESULT bits and end offset),
   n (sscanf "%lf %d %s" style: ARG text).  gcc -O2 -o mkfmt mkfmt.c && ./mkfmt > fmt.txt
   Written by Claude (Anthropic); see AI-USE.md. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

static uint64_t s = 88172645463325252ULL;
static uint64_t rnd(void) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; return s; }
static double bits(uint64_t b) { double d; memcpy(&d, &b, 8); return d; }
static uint64_t dbits(double d) { uint64_t b; memcpy(&b, &d, 8); return b; }
static void hex(const char* p, int n) { for (int i = 0; i < n; i++) printf("%02x", (unsigned char)p[i]); }

static const char* FF[] = {"%f", "%.0f", "%.1f", "%.2f", "%.3f", "%.6f", "%4.2f", "%5.1f", "%6.1f", "%6.2f", "%6.3f",
    "%7.2f", "%8.2f", "%8.3f", "%8.4f", "%9.2f", "%9.3f", "%10.1f", "%10.2f", "%10.3f", "%10.4f", "%12.2f", "%12.3f",
    "%14.3f", "%-10f", "%lf", "%8lf", "%12.3g", "%14.3e", "%g", "%e", "%E", "%G", "%.0e", "%.10g", "%.17g", "%#g", "%#.0f",
    "%#.3g", "%+8.3f", "% 8.3f", "%010.3f", "%-12.4e", "%+.2e", "%.1g", "%.0g", "%5g", "%-9.3g", "%020.10f", "%.15f",
    "%*.*f", "%.12e", "%#.0e", "%010g", NULL};
static const char* IF[] = {"%d", "%2d", "%3d", "%4d", "%5d", "%6d", "%10d", "%02d", "%04d", "%-4d", "%i", "%u", "%x",
    "%X", "%o", "%+d", "% d", "%.3d", "%.0d", "%-8.3d", "%c", NULL};
static const char* LF[] = {"%ld", "%6ld", "%7ld", "%-5ld", "%-2ld", "%lu", "%lx", NULL};
static const char* SF[] = {"%s", "%3s", "%-20s", "%-16s", "%8s", "%14s", "%.3s", "%-s", "%10.2s", NULL};

static void fcase(const char* f, double x) {
    char out[512];
    int n = strcmp(f, "%*.*f") == 0 ? snprintf(out, sizeof out, f, 9, 3, x) : snprintf(out, sizeof out, f, x);
    printf("f\t%s\t%016llx\t", f, (unsigned long long)dbits(x)); hex(out, n); printf("\n");
}

int main(void) {
    double special[] = {0.0, -0.0, NAN, -NAN, INFINITY, -INFINITY, 1.0, -1.0, 0.5, 1.5, 2.5, -2.5, 0.125, 0.375,
        1e-300, 4.9e-324, 2.2250738585072014e-308, 1.7976931348623157e308, 1e20, 123456789.0, 0.1, 0.2, 0.3, 1e-5, 9.9999999e-5,
        0.00049999, 0.0005, 0.00050001, 999999.5, 9.9995, 99.995, 0.045, 0.055, 1e15, 1e16, 1e17, 123.456, -0.0049, 5e-7};
    for (const char** f = FF; *f; f++) {
        for (size_t i = 0; i < sizeof special / sizeof *special; i++) fcase(*f, special[i]);
        for (int k = 0; k < 20000; k++) {
            uint64_t r = rnd();
            double x;
            switch (k % 5) {
            case 0: x = bits(r); if (!(fabs(x) < 1e22)) x = fmod(x, 1e6); break;              /* any pattern */
            case 1: x = (double)(int64_t)(r % 2000001 - 1000000) / 1000.0; break;           /* SWMM-like 3-decimal */
            case 2: x = ldexp((double)(r % 100001), -(int)(r >> 50) % 20); break;            /* binary ties */
            case 3: x = (double)(int64_t)(r % 20001 - 10000) / 100.0 + ((r >> 40) & 1 ? 0.005 : 0.0); break;
            default: x = ldexp(bits((r & 0x000FFFFFFFFFFFFFULL) | 0x3FF0000000000000ULL), (int)((r >> 52) % 80) - 40);
            }
            if (isnan(x)) x = 1.0;
            fcase(*f, x);
        }
    }
    for (const char** f = IF; *f; f++)
        for (int k = 0; k < 4000; k++) {
            int v = k < 50 ? k - 25 : (int)(rnd() >> (32 + k % 31));
            if (k % 7 == 0) v = -v;
            if (strcmp(*f, "%c") == 0) v = 32 + (v & 63);
            char out[128]; int n = snprintf(out, sizeof out, *f, v);
            printf("i\t%s\t%08x\t", *f, (unsigned)v); hex(out, n); printf("\n");
        }
    for (const char** f = LF; *f; f++)
        for (int k = 0; k < 4000; k++) {
            long v = k < 50 ? k - 25 : (long)(rnd() >> (k % 63));
            if (k % 7 == 0) v = -v;
            char out[128]; int n = snprintf(out, sizeof out, *f, v);
            printf("l\t%s\t%016lx\t", *f, (unsigned long)v); hex(out, n); printf("\n");
        }
    const char* strs[] = {"", "a", "ab", "abc", "abcd", "Hello world", "SWMM_5.2.4", "x y z", "0123456789012345678901234"};
    for (const char** f = SF; *f; f++)
        for (size_t i = 0; i < sizeof strs / sizeof *strs; i++) {
            char out[128]; int n = snprintf(out, sizeof out, *f, strs[i]);
            printf("s\t%s\t", *f); hex(strs[i], strlen(strs[i])); printf("\t"); hex(out, n); printf("\n");
        }
    /* strtod on number-like text */
    const char* texts[] = {"0", "1", "-1", "+1", "1.5", ".5", "5.", "-.5e3", "1e10", "1E-10", "1e", "1e+", "1.e5", "  3.25",
        "inf", "-INF", "Infinity", "nan", "NaN(123)", "-nan", "abc", "", "0x1p3", "1e400", "1e-400", "2.2250738585072011e-308",
        "4.9e-324", "123456789012345678901234567890", "0.1000000000000000055511151231257827", "1.2.3", "--1", "12abc",
        "9007199254740993", "1e-5", "0.000001", "  -0", "1,5", "7d", "0x", "0x.8", "0X1.8P+1", "-0x10", "0x1p", "0x1p+",
        "0x1.fffffffffffff8p0", "0x1p-1075", "0x1p2000", "nan()", "nan(0x7b)", "-nan(12)", "nan(1x)", "nan(", NULL};
    for (const char** t = texts; *t; t++) {
        char* e; double v = strtod(*t, &e);
        printf("d\t-\t"); hex(*t, strlen(*t)); printf("\t%016llx:%d\n", (unsigned long long)dbits(v), (int)(e - *t));
    }
    for (int k = 0; k < 200000; k++) {
        char t[64]; uint64_t r = rnd();
        switch (k % 4) {
        case 0: snprintf(t, sizeof t, "%.*g", 1 + (int)(r % 17), bits(rnd())); break;
        case 1: snprintf(t, sizeof t, "%lld.%0*llde%d", (long long)(r % 100000), 1 + (int)((r >> 20) % 12), (long long)((r >> 30) % 1000000), (int)((r >> 50) % 60) - 30); break;
        case 2: snprintf(t, sizeof t, "%.3f", (double)(int64_t)(r % 2000001 - 1000000) / 7.0); break;
        default: snprintf(t, sizeof t, "%.20e", ldexp(1.0 + (double)(r % 1000) / 1000.0, (int)((r >> 40) % 2000) - 1000));
        }
        char* e; double v = strtod(t, &e);
        printf("d\t-\t"); hex(t, strlen(t)); printf("\t%016llx:%d\n", (unsigned long long)dbits(v), (int)(e - t));
    }
    /* sscanf patterns SWMM uses */
    const char* sc[] = {"12 3.5 abc", " 7 -2e3 x", "x 1 2", "", "  ", "5", "1.5 2", "-0 0 z", "2147483648 1 a",
        "99999999999999999999 1 a", "1e5 2 b", "nan 3 c", "3 inf d", NULL};
    for (const char** t = sc; *t; t++) {
        int i1 = -77; double d1 = -77.0; char b[32] = "?";
        int n = sscanf(*t, "%d %lf %s", &i1, &d1, b);
        printf("n\t%%d %%lf %%s\t"); hex(*t, strlen(*t)); printf("\t%d:%d:%016llx:", n, i1, (unsigned long long)dbits(d1)); hex(b, strlen(b)); printf("\n");
    }
    return 0;
}
