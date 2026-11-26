#include <assert.h>
#include <math.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef unsigned __int128 u128;

static inline uint64_t mulmod(uint64_t a, uint64_t b, uint64_t m) {
    return (uint64_t)((u128)a * b % m);
}

static uint64_t powmod(uint64_t a, uint64_t d, uint64_t n) {
    uint64_t r = 1;
    a %= n;
    while (d > 0) {
        if (d & 1) r = mulmod(r, a, n);
        a = mulmod(a, a, n);
        d >>= 1;
    }
    return r;
}

static bool is_prime64(uint64_t n) {
    if (n < 2) return false;
    static const uint64_t small[] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37};
    for (int i = 0; i < 12; i++) {
        if (n == small[i]) return true;
        if (n % small[i] == 0) return false;
    }
    uint64_t d = n - 1;
    int s = 0;
    while ((d & 1) == 0) { d >>= 1; s++; }
    static const uint64_t bases[] = {2, 325, 9375, 28178, 450775, 9780504, 1795265022};
    for (int i = 0; i < 7; i++) {
        uint64_t a = bases[i] % n;
        if (a == 0) continue;
        uint64_t x = powmod(a, d, n);
        if (x == 1 || x == n - 1) continue;
        bool comp = true;
        for (int r = 1; r < s; r++) {
            x = mulmod(x, x, n);
            if (x == n - 1) { comp = false; break; }
        }
        if (comp) return false;
    }
    return true;
}

int main(void) {
    const int N_MAX = 10000000;
    const int HALF_BOUND = N_MAX / 2 + 200000;
    const int PLIM = N_MAX + 300000;

    uint8_t *used = calloc((size_t)(2 * HALF_BOUND + 1), 1);
    uint8_t *sieve = malloc((size_t)(PLIM + 1));
    assert(used != NULL && sieve != NULL);

    memset(sieve, 1, (size_t)(PLIM + 1));
    sieve[0] = sieve[1] = 0;
    for (int i = 2; (long long)i * i <= PLIM; i++) {
        if (sieve[i]) {
            for (int j = i * i; j <= PLIM; j += i) sieve[j] = 0;
        }
    }

    static const int oeis_first_40[40] = {
        0, 2, -1, 1, -2, 3, -4, -6, -3, 4, 6, -5, -7, -9, 8, 5, 7, 9, -8, -10,
        -12, 11, 13, 10, 12, -11, -13, -15, 14, 16, 18, 15, -14, -16, -18, 19, 17, 20, -17, -19
    };

    struct { int n; double d; } hasler_records[14] = {
        {1, 1.5}, {7, 2.5}, {30, 3.0}, {117, 3.5}, {124, -4.0}, {326, -5.0}, {530, 6.0},
        {1137, 6.5}, {1142, -7.0}, {1342, 8.0}, {5363, 8.5}, {5370, -9.0}, {9567, 9.5}, {9568, 10.0}
    };
    int rec_idx = 0;

    used[HALF_BOUND + 0] = 1;
    int prev = 0;
    int u = 1;

    int violations = 0;
    int first_n = -1, first_a = 0;
    double first_lhs = 0.0, first_rhs = 0.0;

    double max_ratio = 0.0;
    int peak_ratio_n = 0, peak_ratio_a = 0;
    double peak_ratio_lhs = 0.0, peak_ratio_rhs = 0.0;

    double max_abs_d = 0.0;
    int peak_d_n = 0, peak_d_a = 0;

    for (int n = 1; n <= N_MAX; n++) {
        while (used[HALF_BOUND + u] && used[HALF_BOUND - u]) u++;
        int a = u;
        while (1) {
            assert(abs(a) <= HALF_BOUND);
            if (!used[HALF_BOUND + a]) {
                uint64_t diff = (uint64_t)llabs((long long)a - (long long)prev);
                bool prime_ok = (diff <= (uint64_t)PLIM) ? (sieve[diff] != 0) : is_prime64(diff);
                if (prime_ok) break;
            }
            if (a > 0) a = -a;
            else a = -a + 1;
        }
        used[HALF_BOUND + a] = 1;
        prev = a;

        if (n < 40) {
            assert(a == oeis_first_40[n]);
        }

        double signed_d = (double)llabs((long long)a) - (double)n / 2.0;
        if (rec_idx < 14 && n == hasler_records[rec_idx].n) {
            assert(fabs(signed_d - hasler_records[rec_idx].d) < 1e-12);
            rec_idx++;
        }

        double lhs = fabs(signed_d);
        double rhs = 2.0 * log((double)n + 2.0);
        double ratio = lhs / rhs;

        if (lhs > max_abs_d) {
            max_abs_d = lhs;
            peak_d_n = n;
            peak_d_a = a;
        }
        if (ratio > max_ratio) {
            max_ratio = ratio;
            peak_ratio_n = n;
            peak_ratio_a = a;
            peak_ratio_lhs = lhs;
            peak_ratio_rhs = rhs;
        }
        if (lhs >= rhs) {
            if (violations == 0) {
                first_n = n;
                first_a = a;
                first_lhs = lhs;
                first_rhs = rhs;
            }
            violations++;
        }
    }
    assert(rec_idx == 14);

    printf("OEIS A377090 first 40 terms and 14 Hasler records verified.\n");
    printf("Range tested: n = 1..%d\n", N_MAX);
    printf("First violation: n=%d, a(n)=%d, ||a(n)|-n/2|=%.4f >= 2*ln(n+2)=%.6f\n",
           first_n, first_a, first_lhs, first_rhs);
    printf("Total violations: %d\n", violations);
    printf("Peak ratio: %.6f at n=%d (a(n)=%d, ||a(n)|-n/2|=%.4f, 2*ln(n+2)=%.6f)\n",
           max_ratio, peak_ratio_n, peak_ratio_a, peak_ratio_lhs, peak_ratio_rhs);
    printf("Max |d(n)|: %.4f at n=%d (a(n)=%d)\n", max_abs_d, peak_d_n, peak_d_a);

    free(used);
    free(sieve);
    return 0;
}
