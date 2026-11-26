#include <algorithm>
#include <atomic>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <functional>
#include <iomanip>
#include <iostream>
#include <limits>
#include <mutex>
#include <random>
#include <sstream>
#include <string>
#include <thread>
#include <vector>

using ld = long double;

static inline ld comb_ld(int n, int k) {
    if (k < 0 || k > n) return 0.0L;
    if (k > n - k) k = n - k;
    ld r = 1.0L;
    for (int i = 1; i <= k; ++i) {
        r = r * (ld)(n - k + i) / (ld)i;
    }
    return r;
}

// Compute e[0..m] for a full vector y of length n
static inline void eval_esymm(const std::vector<ld>& y, int m, std::vector<ld>& e) {
    e.assign(m + 1, 0.0L);
    e[0] = 1.0L;
    for (ld v : y) {
        for (int j = m; j >= 1; --j) {
            e[j] += v * e[j - 1];
        }
    }
}

// Evaluate polynomial coefficients [t^0 .. t^m] of:
// F(t) = (1+t)^a * (1+u*t)^b * (1-v*t)^c
static inline void eval_three_block(int a, int b, int c, ld u, ld v, int m, std::vector<ld>& e) {
    e.assign(m + 1, 0.0L);
    e[0] = 1.0L;
    auto mul_pow = [&](ld coeff, int mult) {
        for (int rep = 0; rep < mult; ++rep) {
            for (int j = m; j >= 1; --j) {
                e[j] += coeff * e[j - 1];
            }
        }
    };
    mul_pow(1.0L, a);
    mul_pow(u, b);
    mul_pow(-v, c);
}

// Evaluate continuous Poisson limit F(t) = (1+t)^a * exp(lambda * t) * (1-v*t)^c
static inline void eval_poisson_block(int a, int c, ld lam, ld v, int m, std::vector<ld>& e) {
    e.assign(m + 1, 0.0L);
    // Start with exp(lambda * t) truncated to degree m
    ld term = 1.0L;
    e[0] = 1.0L;
    for (int j = 1; j <= m; ++j) {
        term = term * lam / (ld)j;
        e[j] = term;
    }
    auto mul_pow = [&](ld coeff, int mult) {
        for (int rep = 0; rep < mult; ++rep) {
            for (int j = m; j >= 1; --j) {
                e[j] += coeff * e[j - 1];
            }
        }
    };
    mul_pow(1.0L, a);
    mul_pow(-v, c);
}

// Evaluate 4-block: (1+t)^a * (1+u1*t)^b1 * (1+u2*t)^b2 * (1-v*t)^c
static inline void eval_four_block_u(int a, int b1, int b2, int c, ld u1, ld u2, ld v, int m, std::vector<ld>& e) {
    e.assign(m + 1, 0.0L);
    e[0] = 1.0L;
    auto mul_pow = [&](ld coeff, int mult) {
        for (int rep = 0; rep < mult; ++rep) {
            for (int j = m; j >= 1; --j) {
                e[j] += coeff * e[j - 1];
            }
        }
    };
    mul_pow(1.0L, a);
    mul_pow(u1, b1);
    mul_pow(u2, b2);
    mul_pow(-v, c);
}

// Evaluate 4-block with two negative blocks: (1+t)^a * (1+u*t)^b * (1-v1*t)^c1 * (1-v2*t)^c2
static inline void eval_four_block_v(int a, int b, int c1, int c2, ld u, ld v1, ld v2, int m, std::vector<ld>& e) {
    e.assign(m + 1, 0.0L);
    e[0] = 1.0L;
    auto mul_pow = [&](ld coeff, int mult) {
        for (int rep = 0; rep < mult; ++rep) {
            for (int j = m; j >= 1; --j) {
                e[j] += coeff * e[j - 1];
            }
        }
    };
    mul_pow(1.0L, a);
    mul_pow(u, b);
    mul_pow(-v1, c1);
    mul_pow(-v2, c2);
}

struct HitRecord {
    int m = 0;
    int k = 0;
    ld min_gap = 1e30L;
    ld min_ratio = 1e30L;
    ld min_ej = 0.0L;
    std::string desc;
    std::vector<ld> sample_y;
};

static void record_if_best(HitRecord& best, int m, const std::vector<ld>& e, const std::string& desc, const std::vector<ld>& sample_y = {}) {
    int d = m - 1;
    ld min_ej = 1e30L;
    for (int j = 1; j <= m; ++j) {
        if (e[j] < min_ej) min_ej = e[j];
    }
    if (min_ej < -1e-13L) return;

    for (int k = 2; k <= d; ++k) {
        ld target = comb_ld(d, k);
        ld gap = e[k] - target;
        ld ratio = e[k] / target;
        if (ratio < best.min_ratio || (ratio == best.min_ratio && gap < best.min_gap)) {
            best.m = m;
            best.k = k;
            best.min_gap = gap;
            best.min_ratio = ratio;
            best.min_ej = min_ej;
            best.desc = desc;
            best.sample_y = sample_y;
        }
    }
}

static void check_point_and_update(
    HitRecord& best,
    HitRecord& counterexample,
    int m,
    const std::vector<ld>& e,
    const std::string& desc,
    const std::vector<ld>& sample_y = {}
) {
    int d = m - 1;
    ld min_ej = 1e30L;
    for (int j = 1; j <= m; ++j) {
        if (e[j] < min_ej) min_ej = e[j];
    }
    if (min_ej < -1e-13L) return;

    record_if_best(best, m, e, desc, sample_y);
    for (int k = 2; k <= d; ++k) {
        ld target = comb_ld(d, k);
        ld gap = e[k] - target;
        if (gap < -1e-9L) {
            ld ratio = e[k] / target;
            if (gap < counterexample.min_gap) {
                counterexample.m = m;
                counterexample.k = k;
                counterexample.min_gap = gap;
                counterexample.min_ratio = ratio;
                counterexample.min_ej = min_ej;
                counterexample.desc = desc;
                counterexample.sample_y = sample_y;
            }
        }
    }
}

// Given univariate evaluator f(v) -> e[0..m], search all roots of e[m](v) = 0 on [v_lo, v_hi]
template <typename EvalFn>
static void sweep_roots_and_grid(
    int m,
    ld v_lo,
    ld v_hi,
    int grid_n,
    EvalFn&& eval_fn,
    const std::string& base_desc,
    HitRecord& best,
    HitRecord& counterexample,
    std::function<std::vector<ld>(ld)> make_vec = nullptr
) {
    if (v_hi < v_lo) return;
    std::vector<ld> e(m + 1), e_prev(m + 1);
    ld prev_v = v_lo;
    eval_fn(prev_v, e_prev);
    if (v_lo >= 0.0L) {
        std::vector<ld> sy = make_vec ? make_vec(prev_v) : std::vector<ld>{};
        check_point_and_update(best, counterexample, m, e_prev, base_desc + " v=" + std::to_string((double)prev_v), sy);
    }

    for (int gi = 1; gi <= grid_n; ++gi) {
        ld v = v_lo + (v_hi - v_lo) * (ld)gi / (ld)grid_n;
        eval_fn(v, e);

        // Also check grid point itself if feasible (handles interior minima or flat boundary)
        bool feas = true;
        for (int j = 1; j <= m; ++j) {
            if (e[j] < -1e-13L) { feas = false; break; }
        }
        if (feas) {
            std::vector<ld> sy = make_vec ? make_vec(v) : std::vector<ld>{};
            check_point_and_update(best, counterexample, m, e, base_desc + " v=" + std::to_string((double)v), sy);
        }

        // Check sign change in e[m] (or any e[j] crossing 0)
        for (int j_root : {m, m - 1}) {
            if (j_root < 2) continue;
            ld f0 = e_prev[j_root];
            ld f1 = e[j_root];
            if ((f0 <= 0.0L && f1 >= 0.0L) || (f0 >= 0.0L && f1 <= 0.0L)) {
                if (fabsl(f0) + fabsl(f1) > 0.0L) {
                    ld a = prev_v, b = v, fa = f0, fb = f1;
                    std::vector<ld> emid(m + 1);
                    for (int it = 0; it < 65; ++it) {
                        ld mid = 0.5L * (a + b);
                        eval_fn(mid, emid);
                        ld fm = emid[j_root];
                        if (fabsl(fm) < 1e-17L) { a = b = mid; break; }
                        if ((fa <= 0.0L && fm <= 0.0L) || (fa >= 0.0L && fm >= 0.0L)) {
                            a = mid; fa = fm;
                        } else {
                            b = mid; fb = fm;
                        }
                    }
                    ld v_star = 0.5L * (a + b);
                    // Nudge slightly inside feasibility if needed by testing v_star and neighbors
                    for (ld dv : {0.0L, -1e-13L, 1e-13L, -1e-11L, 1e-11L}) {
                        ld vt = v_star + dv;
                        if (vt < v_lo || vt > v_hi) continue;
                        eval_fn(vt, emid);
                        std::ostringstream oss;
                        oss << base_desc << " root_j=" << j_root << " v=" << std::setprecision(15) << (double)vt;
                        std::vector<ld> sy = make_vec ? make_vec(vt) : std::vector<ld>{};
                        check_point_and_update(best, counterexample, m, emid, oss.str(), sy);
                    }
                }
            }
        }
        prev_v = v;
        e_prev.swap(e);
    }
}

static void run_blocks_mode(int m_min, int m_max) {
    auto t0 = std::chrono::steady_clock::now();
    std::cout << "=== MO #476077 Structured Block & Poisson Limit Sweep (m = " << m_min << ".." << m_max << ") ===\n";

    unsigned nthreads = std::max(1u, std::thread::hardware_concurrency());
    for (int m = m_min; m <= m_max; ++m) {
        int d = m - 1;
        HitRecord best_3b, ce_3b;
        HitRecord best_poi, ce_poi;
        HitRecord best_4b, ce_4b;

        // Task 1: 3-block (1^a, u^b, (-v)^c)
        struct Job3 { int a, b, c; };
        std::vector<Job3> jobs3;
        std::vector<int> b_vals;
        for (int b = 1; b <= 2 * m; ++b) b_vals.push_back(b);
        b_vals.push_back(3 * m);
        b_vals.push_back(5 * m);
        b_vals.push_back(10 * m);
        for (int c = 1; c <= 6; ++c) {
            for (int a = 0; a <= m + c; ++a) {
                for (int b : b_vals) {
                    if (a + b + c < m) continue;
                    if (b + a - d < 0) continue;
                    jobs3.push_back({a, b, c});
                }
            }
        }

        std::atomic<size_t> idx3{0};
        std::mutex mtx;
        std::vector<std::thread> threads;
        for (unsigned tid = 0; tid < nthreads; ++tid) {
            threads.emplace_back([&]() {
                HitRecord lbest, lce;
                std::vector<ld> e(m + 1);
                while (true) {
                    size_t i = idx3.fetch_add(1);
                    if (i >= jobs3.size()) break;
                    auto [a, b, c] = jobs3[i];
                    ld v_max = (ld)(b + a - d) / (ld)c;
                    if (v_max <= 0.0L) continue;
                    // For a > d, u <= 1 gives v <= v_max; u can even be negative for v >= 0.
                    // Bound v_hi reasonably if a+b+c is huge, though u <= 1 already bounds v_max!
                    auto eval_fn = [&](ld v, std::vector<ld>& out) {
                        ld u = ((ld)(d - a) + (ld)c * v) / (ld)b;
                        eval_three_block(a, b, c, u, v, m, out);
                    };
                    auto make_vec = [&](ld v) {
                        ld u = ((ld)(d - a) + (ld)c * v) / (ld)b;
                        std::vector<ld> y;
                        for (int q = 0; q < a; ++q) y.push_back(1.0L);
                        for (int q = 0; q < b; ++q) y.push_back(u);
                        for (int q = 0; q < c; ++q) y.push_back(-v);
                        return y;
                    };
                    std::ostringstream oss;
                    oss << "3blk(a=" << a << ",b=" << b << ",c=" << c << ")";
                    sweep_roots_and_grid(m, 0.0L, v_max, 80, eval_fn, oss.str(), lbest, lce, make_vec);
                }
                std::lock_guard<std::mutex> lk(mtx);
                if (lbest.min_ratio < best_3b.min_ratio) best_3b = lbest;
                if (lce.min_gap < ce_3b.min_gap) ce_3b = lce;
            });
        }
        for (auto& th : threads) th.join();

        // Task 2: Continuous Poisson limit (1+t)^a * exp(lambda*t) * (1-v*t)^c, lambda = d - a + c*v
        for (int c = 1; c <= 8; ++c) {
            for (int a = 0; a <= m + c; ++a) {
                ld v_hi = (ld)(d + 4);
                auto eval_fn = [&](ld v, std::vector<ld>& out) {
                    ld lam = (ld)(d - a) + (ld)c * v;
                    eval_poisson_block(a, c, lam, v, m, out);
                };
                std::ostringstream oss;
                oss << "poisson(a=" << a << ",c=" << c << ")";
                sweep_roots_and_grid(m, 0.0L, v_hi, 200, eval_fn, oss.str(), best_poi, ce_poi);
            }
        }

        // Task 3: 4-block for m <= 14
        if (m <= 14) {
            struct Job4 { int kind, a, p1, p2, p3; };
            std::vector<Job4> jobs4;
            for (int a = 0; a <= d; ++a) {
                for (int c = 1; c <= 3; ++c) {
                    for (int b1 = 1; b1 <= m; ++b1) {
                        for (int b2 = 1; b2 <= m; ++b2) {
                            if (a + b1 + b2 + c < m) continue;
                            jobs4.push_back({0, a, b1, b2, c});
                        }
                    }
                }
                for (int b = 1; b <= m + 2; ++b) {
                    for (int c1 = 1; c1 <= 2; ++c1) {
                        for (int c2 = 1; c2 <= 2; ++c2) {
                            if (a + b + c1 + c2 < m) continue;
                            if (b + a - d < 0) continue;
                            jobs4.push_back({1, a, b, c1, c2});
                        }
                    }
                }
            }
            std::atomic<size_t> idx4{0};
            std::vector<std::thread> th4;
            for (unsigned tid = 0; tid < nthreads; ++tid) {
                th4.emplace_back([&]() {
                    HitRecord lbest, lce;
                    while (true) {
                        size_t i = idx4.fetch_add(1);
                        if (i >= jobs4.size()) break;
                        auto jb = jobs4[i];
                        if (jb.kind == 0) {
                            int a = jb.a, b1 = jb.p1, b2 = jb.p2, c = jb.p3;
                            for (int ui = -10; ui <= 19; ++ui) {
                                ld u1 = (ld)ui / 20.0L; // -0.5 to 0.95
                                ld v_max = (ld)(b2 + a + b1 * u1 - d) / (ld)c;
                                if (v_max <= 0.0L) continue;
                                auto eval_fn = [&](ld v, std::vector<ld>& out) {
                                    ld u2 = ((ld)(d - a) - (ld)b1 * u1 + (ld)c * v) / (ld)b2;
                                    eval_four_block_u(a, b1, b2, c, u1, u2, v, m, out);
                                };
                                auto make_vec = [&](ld v) {
                                    ld u2 = ((ld)(d - a) - (ld)b1 * u1 + (ld)c * v) / (ld)b2;
                                    std::vector<ld> y;
                                    for (int q = 0; q < a; ++q) y.push_back(1.0L);
                                    for (int q = 0; q < b1; ++q) y.push_back(u1);
                                    for (int q = 0; q < b2; ++q) y.push_back(u2);
                                    for (int q = 0; q < c; ++q) y.push_back(-v);
                                    return y;
                                };
                                std::ostringstream oss;
                                oss << "4blkU(a=" << a << ",b1=" << b1 << ",b2=" << b2 << ",c=" << c << ",u1=" << (double)u1 << ")";
                                sweep_roots_and_grid(m, 0.0L, v_max, 25, eval_fn, oss.str(), lbest, lce, make_vec);
                            }
                        } else {
                            int a = jb.a, b = jb.p1, c1 = jb.p2, c2 = jb.p3;
                            ld v1_cap = (ld)(b + a - d) / (ld)c1;
                            for (int vi = 1; vi <= 20; ++vi) {
                                ld v1 = v1_cap * (ld)vi / 22.0L;
                                ld v2_max = ((ld)(b + a - d) - (ld)c1 * v1) / (ld)c2;
                                if (v2_max <= 0.0L) continue;
                                auto eval_fn = [&](ld v2, std::vector<ld>& out) {
                                    ld u = ((ld)(d - a) + (ld)c1 * v1 + (ld)c2 * v2) / (ld)b;
                                    eval_four_block_v(a, b, c1, c2, u, v1, v2, m, out);
                                };
                                auto make_vec = [&](ld v2) {
                                    ld u = ((ld)(d - a) + (ld)c1 * v1 + (ld)c2 * v2) / (ld)b;
                                    std::vector<ld> y;
                                    for (int q = 0; q < a; ++q) y.push_back(1.0L);
                                    for (int q = 0; q < b; ++q) y.push_back(u);
                                    for (int q = 0; q < c1; ++q) y.push_back(-v1);
                                    for (int q = 0; q < c2; ++q) y.push_back(-v2);
                                    return y;
                                };
                                std::ostringstream oss;
                                oss << "4blkV(a=" << a << ",b=" << b << ",c1=" << c1 << ",c2=" << c2 << ",v1=" << (double)v1 << ")";
                                sweep_roots_and_grid(m, 0.0L, v2_max, 25, eval_fn, oss.str(), lbest, lce, make_vec);
                            }
                        }
                    }
                    std::lock_guard<std::mutex> lk(mtx);
                    if (lbest.min_ratio < best_4b.min_ratio) best_4b = lbest;
                    if (lce.min_gap < ce_4b.min_gap) ce_4b = lce;
                });
            }
            for (auto& th : th4) th.join();
        }

        std::cout << "m=" << m << " (d=" << d << "):"
                  << " 3blk min_ratio=" << std::setprecision(10) << (double)best_3b.min_ratio
                  << " (k=" << best_3b.k << ", gap=" << (double)best_3b.min_gap << ", " << best_3b.desc << ")";
        std::cout << " | poisson min_ratio=" << (double)best_poi.min_ratio
                  << " (k=" << best_poi.k << ", gap=" << (double)best_poi.min_gap << ", " << best_poi.desc << ")";
        if (m <= 14) {
            std::cout << " | 4blk min_ratio=" << (double)best_4b.min_ratio
                      << " (k=" << best_4b.k << ", gap=" << (double)best_4b.min_gap << ", " << best_4b.desc << ")";
        }
        std::cout << "\n";

        auto print_ce = [&](const char* tag, const HitRecord& ce) {
            if (ce.m > 0) {
                std::cout << "  [CANDIDATE COUNTEREXAMPLE " << tag << "] m=" << ce.m << " k=" << ce.k
                          << " gap=" << std::setprecision(15) << (double)ce.min_gap
                          << " ratio=" << (double)ce.min_ratio
                          << " min_ej=" << (double)ce.min_ej
                          << " desc=" << ce.desc << "\n";
                if (!ce.sample_y.empty()) {
                    std::cout << "    y = [";
                    for (size_t i = 0; i < ce.sample_y.size(); ++i) {
                        if (i) std::cout << ", ";
                        std::cout << std::setprecision(15) << (double)ce.sample_y[i];
                    }
                    std::cout << "]\n";
                }
            }
        };
        print_ce("3BLK", ce_3b);
        print_ce("POISSON", ce_poi);
        print_ce("4BLK", ce_4b);
    }
    auto t1 = std::chrono::steady_clock::now();
    std::cout << "Blocks mode elapsed: " << std::chrono::duration<double>(t1 - t0).count() << "s\n";
}

// Project a vector y (with y_i <= 1, sum(y_i) == d) onto strict feasibility via convex combo
// with interior point y_bar = (d/n, ..., d/n), where all e_j(y_bar) > 0 strictly.
static ld project_strict_feasible(const std::vector<ld>& y, int m, std::vector<ld>& y_out) {
    int n = (int)y.size();
    int d = m - 1;
    ld ubar = (ld)d / (ld)n;
    std::vector<ld> e(m + 1);
    eval_esymm(y, m, e);
    bool ok = true;
    for (int j = 1; j <= m; ++j) {
        if (e[j] < 0.0L) { ok = false; break; }
    }
    if (ok) {
        y_out = y;
        return 1.0L;
    }
    ld lo = 0.0L, hi = 1.0L;
    std::vector<ld> yt(n);
    for (int it = 0; it < 60; ++it) {
        ld mid = 0.5L * (lo + hi);
        for (int i = 0; i < n; ++i) yt[i] = mid * y[i] + (1.0L - mid) * ubar;
        eval_esymm(yt, m, e);
        bool feas = true;
        for (int j = 1; j <= m; ++j) {
            if (e[j] < 1e-14L) { feas = false; break; }
        }
        if (feas) lo = mid;
        else hi = mid;
    }
    y_out.resize(n);
    for (int i = 0; i < n; ++i) y_out[i] = lo * y[i] + (1.0L - lo) * ubar;
    return lo;
}

static void run_opt_mode(int m_min, int m_max) {
    auto t0 = std::chrono::steady_clock::now();
    unsigned nthreads = std::max(1u, std::thread::hardware_concurrency());
    std::cout << "=== MO #476077 Multi-Start Constrained Optimization (m = " << m_min << ".." << m_max
              << ", threads=" << nthreads << ") ===\n";

    struct OptTask { int m, n, k; };
    std::vector<OptTask> tasks;
    for (int m = m_min; m <= m_max; ++m) {
        int d = m - 1;
        std::vector<int> ns = {m + 1, m + 2, m + 3, m + 4, m + 6};
        std::vector<int> ks = {2, d};
        if (m / 2 >= 2 && m / 2 <= d && m / 2 != 2 && m / 2 != d) ks.push_back(m / 2);
        if (d - 1 >= 3 && d - 1 != m / 2) ks.push_back(d - 1);
        for (int n : ns) {
            for (int k : ks) {
                tasks.push_back({m, n, k});
            }
        }
    }

    std::atomic<size_t> tidx{0};
    std::vector<HitRecord> results(tasks.size());
    std::vector<HitRecord> ce_results(tasks.size());

    auto worker = [&](unsigned tid) {
        std::mt19937_64 rng(0x9e3779b97f4a7c15ULL ^ (tid + 1) * 1337ULL);
        std::uniform_real_distribution<double> U01(0.0, 1.0);
        std::vector<ld> e(m_max + 2);
        std::vector<ld> e_ij(m_max + 2);

        while (true) {
            size_t ti = tidx.fetch_add(1);
            if (ti >= tasks.size()) break;
            int m = tasks[ti].m, n = tasks[ti].n, k = tasks[ti].k;
            int d = m - 1;
            ld target = comb_ld(d, k);
            HitRecord local_best;
            local_best.m = m; local_best.k = k;
            HitRecord local_ce;

            const int restarts = 180;
            for (int r = 0; r < restarts; ++r) {
                std::vector<ld> y(n, 0.0L);
                int mode = r % 4;
                if (mode == 0) {
                    // Seed near 3-block with 1 or 2 negative coordinates and (a) ones
                    int a = rng() % std::max(1, d);
                    int c = 1 + (rng() % std::min(3, n - d));
                    int b = n - a - c;
                    if (b < 1) { b = n - a; c = 0; }
                    ld v = (c > 0) ? (0.05L + 0.8L * (ld)U01(rng)) : 0.0L;
                    ld u = ((ld)(d - a) + (ld)c * v) / (ld)b;
                    if (u > 1.0L) {
                        u = 0.99L;
                        v = (c > 0) ? (((ld)a + (ld)b * u - (ld)d) / (ld)c) : 0.0L;
                    }
                    int pos = 0;
                    for (int i = 0; i < a; ++i) y[pos++] = 1.0L;
                    for (int i = 0; i < b; ++i) y[pos++] = u + 0.02L * ((ld)U01(rng) - 0.5L);
                    for (int i = 0; i < c; ++i) y[pos++] = -v + 0.02L * ((ld)U01(rng) - 0.5L);
                } else if (mode == 1) {
                    // Random vector in [-0.6, 1.0] shifted/scaled to sum d
                    for (int i = 0; i < n; ++i) y[i] = -0.5L + 1.5L * (ld)U01(rng);
                } else if (mode == 2) {
                    // Near-equality y* = (1^d, 0^{n-d}) plus negative kick
                    for (int i = 0; i < d; ++i) y[i] = 1.0L - 0.2L * (ld)U01(rng);
                    for (int i = d; i < n; ++i) y[i] = -0.3L * (ld)U01(rng);
                } else {
                    // Concentrated negatives + spread positives
                    int c = 1 + (rng() % std::min(4, n - 1));
                    for (int i = 0; i < n - c; ++i) y[i] = 0.3L + 0.7L * (ld)U01(rng);
                    for (int i = n - c; i < n; ++i) y[i] = -0.1L - 0.8L * (ld)U01(rng);
                }

                // Enforce y_i <= 1 and sum(y) == d cleanly
                for (int i = 0; i < n; ++i) {
                    if (y[i] > 1.0L) y[i] = 1.0L;
                }
                for (int pass = 0; pass < 30; ++pass) {
                    ld s = 0.0L;
                    for (ld v : y) s += v;
                    ld diff = (ld)d - s;
                    if (fabsl(diff) < 1e-15L) break;
                    if (diff < 0.0L) {
                        ld per = diff / (ld)n;
                        for (int i = 0; i < n; ++i) y[i] += per;
                    } else {
                        int cnt_free = 0;
                        ld headroom = 0.0L;
                        for (int i = 0; i < n; ++i) {
                            if (y[i] < 1.0L - 1e-15L) {
                                cnt_free++;
                                headroom += (1.0L - y[i]);
                            }
                        }
                        if (cnt_free == 0) break;
                        ld scale = (headroom > 0.0L) ? std::min(1.0L, diff / headroom) : 0.0L;
                        for (int i = 0; i < n; ++i) {
                            if (y[i] < 1.0L - 1e-15L) {
                                y[i] = std::min(1.0L, y[i] + scale * (1.0L - y[i]));
                            }
                        }
                    }
                }

                auto eval_loss = [&](const std::vector<ld>& ev, ld rho) -> ld {
                    ld pen = 0.0L;
                    for (int j = 2; j <= m; ++j) {
                        if (ev[j] < 0.0L) {
                            pen += rho * ev[j] * ev[j] + std::sqrt(rho) * (-ev[j]);
                        }
                    }
                    return ev[k] + pen;
                };

                const ld rhos[4] = {100.0L, 10000.0L, 1e7L, 1e10L};
                for (int stage = 0; stage < 4; ++stage) {
                    ld rho = rhos[stage];
                    ld step = (stage == 0) ? 0.25L : (stage == 1 ? 0.08L : (stage == 2 ? 0.02L : 0.004L));
                    int max_iters = (stage < 2) ? 40 : 60;
                    for (int it = 0; it < max_iters; ++it) {
                        int i = (int)(rng() % n);
                        int j = (int)(rng() % n);
                        if (i == j) continue;
                        ld d_lo = y[j] - 1.0L;
                        ld d_hi = 1.0L - y[i];
                        if (d_hi < d_lo + 1e-15L) continue;

                        // Compute e_ij excluding i, j in O(m)
                        eval_esymm(y, m, e);
                        ld cur_loss = eval_loss(e, rho);
                        ld yi = y[i], yj = y[j];
                        // Remove yi, then yj via synthetic division
                        e_ij = e;
                        for (int r2 = 1; r2 <= m; ++r2) e_ij[r2] -= yi * e_ij[r2 - 1];
                        for (int r2 = 1; r2 <= m; ++r2) e_ij[r2] -= yj * e_ij[r2 - 1];

                        ld s1 = yi + yj;
                        ld p0 = yi * yj;
                        ld best_delta = 0.0L;
                        ld best_loss = cur_loss;
                        std::vector<ld> ev_try(m + 1);

                        // Sample candidate deltas around 0 + golden/bisection refinement + boundaries
                        ld cands[9] = {
                            d_lo, d_hi,
                            std::clamp(-step, d_lo, d_hi),
                            std::clamp(step, d_lo, d_hi),
                            std::clamp(-0.25L * step, d_lo, d_hi),
                            std::clamp(0.25L * step, d_lo, d_hi),
                            std::clamp(-2.0L * step, d_lo, d_hi),
                            std::clamp(2.0L * step, d_lo, d_hi),
                            0.5L * (yj - yi) // midpoint (equalize yi, yj)
                        };
                        for (ld del : cands) {
                            if (del < d_lo || del > d_hi) continue;
                            ld p = (yi + del) * (yj - del);
                            ev_try[0] = 1.0L;
                            ev_try[1] = e[1];
                            for (int r2 = 2; r2 <= m; ++r2) {
                                ev_try[r2] = e_ij[r2] + s1 * e_ij[r2 - 1] + p * e_ij[r2 - 2];
                            }
                            ld L = eval_loss(ev_try, rho);
                            if (L < best_loss) {
                                best_loss = L;
                                best_delta = del;
                            }
                        }
                        if (best_delta != 0.0L) {
                            y[i] += best_delta;
                            y[j] -= best_delta;
                        }
                    }
                }

                // Project onto strict feasibility and evaluate
                std::vector<ld> yf;
                project_strict_feasible(y, m, yf);
                eval_esymm(yf, m, e);
                bool has_neg = false;
                for (ld v : yf) if (v < -1e-6L) has_neg = true;
                std::ostringstream oss;
                oss << "opt(m=" << m << ",n=" << n << ",k=" << k << ",neg=" << has_neg << ")";
                check_point_and_update(local_best, local_ce, m, e, oss.str(), yf);
            }
            results[ti] = local_best;
            ce_results[ti] = local_ce;
        }
    };

    std::vector<std::thread> pool;
    for (unsigned tid = 0; tid < nthreads; ++tid) pool.emplace_back(worker, tid);
    for (auto& th : pool) th.join();

    for (size_t ti = 0; ti < tasks.size(); ++ti) {
        const auto& t = tasks[ti];
        const auto& r = results[ti];
        const auto& ce = ce_results[ti];
        std::cout << "m=" << t.m << " n=" << t.n << " k=" << t.k
                  << " | min_ratio=" << std::setprecision(10) << (double)r.min_ratio
                  << " gap=" << (double)r.min_gap
                  << " min_ej=" << (double)r.min_ej;
        if (ce.m > 0) {
            std::cout << " [COUNTEREXAMPLE!! gap=" << (double)ce.min_gap << "]\n    y=[";
            for (size_t i = 0; i < ce.sample_y.size(); ++i) {
                if (i) std::cout << ", ";
                std::cout << std::setprecision(15) << (double)ce.sample_y[i];
            }
            std::cout << "]";
        }
        std::cout << "\n";
    }
    auto t1 = std::chrono::steady_clock::now();
    std::cout << "Opt mode elapsed: " << std::chrono::duration<double>(t1 - t0).count() << "s\n";
}

int main(int argc, char** argv) {
    if (argc < 2) {
        std::cerr << "Usage: " << argv[0] << " --blocks <m_min> <m_max> | --opt <m_min> <m_max>\n";
        return 1;
    }
    std::string mode = argv[1];
    int m_min = (argc >= 3) ? std::atoi(argv[2]) : 6;
    int m_max = (argc >= 4) ? std::atoi(argv[3]) : m_min;
    if (mode == "--blocks") {
        run_blocks_mode(m_min, m_max);
    } else if (mode == "--opt") {
        run_opt_mode(m_min, m_max);
    } else {
        std::cerr << "Unknown mode: " << mode << "\n";
        return 1;
    }
    return 0;
}
