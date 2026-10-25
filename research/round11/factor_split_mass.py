"""Round 11, step 2: how much of the Moebius mass can 'pointwise (bootstrap) x mean value' splits handle?

Model: for n ~ D = U^t, the log-sizes of the prime factors (in units of log U) are t * PD(1)
(Poisson-Dirichlet), i.e. the Dickman/Billingsley law of a random integer.
A piece with prime factors of sizes alpha_i can be grouped into
  S (pointwise, bootstrap bound |block|^2 <= B^{delta*} * diag)   cost delta* * sum_S alpha
  T (mean value: large sieve if length <= U, amplification if longer)  cost (5/6) max(0, sum_T alpha - 1)
Costs are exponents of U relative to the diagonal U*||mu||^2. Amplification alone costs (5/6)(t-1).
A configuration GAINS if min_S cost <= (5/6)(t-1) - need, need = 2.6e-4.
Since small primes give arbitrary granularity, we treat primes with alpha < eps as a continuous
'dust' mass that can be split freely between S and T.
"""
import numpy as np

rng = np.random.default_rng(11)


def pd_sample(t, eps=1e-3):
    """Stick-breaking for PD(1): sizes of prime factors > eps (in units of log U) plus dust."""
    rem = 1.0
    parts = []
    while rem * t > eps:
        x = rng.random() * rem
        parts.append(x * t)
        rem -= x
    dust = rem * t
    return sorted(parts, reverse=True), dust


def best_cost(parts, dust, t, dstar):
    """min over subsets S of big parts (<= 12 big parts enumerated) with optimal dust split."""
    big = [a for a in parts if a > 0.01]
    small = sum(a for a in parts if a <= 0.01) + dust
    k = len(big)
    best = 10.0
    amp = 5.0 / 6.0
    for mask in range(1 << k):
        sS = sum(big[i] for i in range(k) if mask >> i & 1)
        sT = t - small - sS
        # put x of the small mass into S, small-x into T, choose x in [0, small] optimally
        # cost(x) = dstar*(sS+x) + amp*max(0, sT+small-x-1); piecewise linear, check endpoints/kink
        cands = [0.0, small]
        kink = sT + small - 1.0
        if 0 < kink < small:
            cands.append(kink)
        for x in cands:
            c = dstar * (sS + x) + amp * max(0.0, sT + small - x - 1.0)
            best = min(best, c)
    return best


def run(t=1.155, dstar=0.749, need=2.6e-4, N=200000):
    base = 5.0 / 6.0 * (t - 1)
    gains = np.empty(N)
    has_long = np.empty(N, dtype=bool)
    for j in range(N):
        parts, dust = pd_sample(t)
        c = best_cost(parts, dust, t, dstar)
        gains[j] = base - c
        has_long[j] = parts[0] >= 1.0 if parts else False
    bad = gains < need
    print(f"t={t} delta*={dstar} amplification cost={base:.5f} need={need}")
    print(f"  fraction of mass with gain >= need : {1 - bad.mean():.4f}")
    print(f"  bad mass                         : {bad.mean():.4f}")
    print(f"    of which largest prime >= U     : {(bad & has_long).mean():.4f}")
    print(f"    of which all primes < U         : {(bad & ~has_long).mean():.4f}")
    print(f"  median gain on good part          : {np.median(gains[~bad]):.5f}")
    print(f"  max possible gain (x = t-1)       : {(t - 1) * (5 / 6 - dstar):.5f}")
    return gains, bad


if __name__ == "__main__":
    for dstar in (0.749, 0.70, 0.60):
        run(dstar=dstar, N=60000)
    run(t=1.30, dstar=0.749, N=60000)
