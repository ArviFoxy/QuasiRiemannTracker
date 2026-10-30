"""Exponent bookkeeping for research/rip/eighth/STRATEGIES.md (plain eighth moment of the thin sextic family).

Target: sum_z |A(z)|^4 << Z^{1+2 eta + eps} N^2,  A = X1 X2,  X_i plain of length N_i = Z^{m_i},  N = Z^mu.
Balanced case m1 = m2 = m = mu/2 <= 1/2 throughout.  All quantities are exponents of Z.

Inputs (names as in STRATEGIES.md):
  H1  zero-free half-plane Re s > (1+kappa)/2, kappa = 2*theta - 1 (theta = 0.87341 -> kappa = 0.74682)
  H2  family zero count: #{z : L(s,chi_z) has a zero with Re >= (1+nu)/2, |Im| <= Z^eps} << Z^{rho(nu)}
      rho(nu) = (15 - 16 nu)/(15 - 6 nu)   (round9 lattice game = Xu-Sang (31-32 sigma)/(21-12 sigma))
  H3  plain fourth moment sum_z |A|^2 << Z^{1+eps} N   (mu <= 1)
  dF  de Faveri: Theta_6(A,B) << A + B + A^{5/6} B^{1/3} + A^{1/3} B^{5/6}  (sharp: Xu-Sang 2610.17675)
  Bu  Burgess (r = 2,3,...) for the short sums: |X|^2/M <= M^{1-2/r} Z^{(r+1)/(2 r^2)}
usage: python3 -I strat_exponents.py
"""
import math

THETA = 0.87341198
KAPPA = 2 * THETA - 1          # 0.74682


def rho_xs(nu):                # H2, unmarked count (Xu-Sang / round 9)
    return (15 - 16 * nu) / (15 - 6 * nu)


def rho_dh(nu):                # density hypothesis N(sigma) << Z^{2(1-sigma)}
    return 1 - nu


def grid(a, b, n=4000):
    return [a + (b - a) * i / n for i in range(n + 1)]


# ---------------------------------------------------------------- general-vector and pointwise routes
def eta_defaveri(mu):
    """sum|A|^4 <= Theta_6(Z, N^2) * ||c||^2 with ||c||^2 ~ N^2."""
    B = 2 * mu
    th = max(1, B, 5 / 6 + B / 3, 1 / 3 + 5 * B / 6)
    return (th - 1) / 2


def eta_holder_zerofree(mu, kappa=KAPPA):
    """sum|A|^4 <= max|A|^2 * sum|A|^2, |X|^2 <= M^{1+kappa} (Littlewood in Re s > (1+kappa)/2)."""
    return kappa * mu / 2


def eta_holder_burgess(mu):
    """Same with Burgess for the pointwise bound (best r), or the trivial bound |X|^2 <= M^2."""
    m = mu / 2
    best = m                                   # trivial: |X|^2/M <= M
    for r in range(2, 40):
        if m > (r + 1) / (4 * r) + 1e-12:      # Burgess nontrivial range M > q^{(r+1)/(4r)}
            best = min(best, (1 - 2 / r) * m + (r + 1) / (2 * r * r))
    return best                                # 2*eta = 2*best*... : |A|^2/N = (|X|^2/M)^2 -> 2 eta = 2*best
                                               # (returned value is eta)


# ---------------------------------------------------------------- S1: stratification by the rightmost zero
def two_eta_S1(mu, rho=rho_xs, kappa=KAPPA, use_H3=True):
    """2 eta = sup_{0<=d<=kappa} min(mu d [H3 + Littlewood], rho(d) - 1 + 2 mu d [count x max])."""
    best = -1e9
    for d in grid(0, kappa):
        t2 = rho(d) - 1 + 2 * mu * d
        v = min(mu * d, t2) if use_H3 else t2
        best = max(best, v)
    return max(best, 0.0)


def two_eta_lemmaD(mu, rho=rho_xs, kappa=KAPPA):
    """With the (missing) Lemma D: sum over the class of |A|^2 <= Z^{rho(d)} N (diagonal share)."""
    best = -1e9
    for d in grid(0, kappa):
        best = max(best, min(mu * d, rho(d) - 1 + mu * d))
    return max(best, 0.0)


# ---------------------------------------------------------------- lattice adversary (round 9) at spacing s
def lattice_count(nu, s):
    """Count of the two-term adversary L ~ 1 + b U^{-s(w-a)} with zero at a = (1+nu)/2 and saturated
    lengths s*N: plain block at s (P line), Moebius blocks at ks (I line for ks <= 1, long line after)."""
    c = 1 - 2 * nu * s                                   # P: saturated plain block of length s <= 1/2
    k_lo = math.floor(1 / s + 1e-12)
    if k_lo >= 1:
        c = min(c, 1 - nu * k_lo * s)                    # I: Moebius block of length k s <= 1
    k_hi = math.ceil(1 / s - 1e-12)
    y = k_hi * s
    if y >= 1:
        c = min(c, (1 + 5 * y) / 6 - nu * y)             # L: amplified long moment at length y >= 1
    return c


def two_eta_adversary(mu, kappa=KAPPA):
    """Lower bound for length-only proofs: adversary rows with zero at (1+nu)/2 and |X_m|^2 = M^{1+nu}
    (spacing s = m), count Z^{c}; excess c - 1 + 2 nu mu.  Requires 1/3 <= m <= 1/2 (2s <= 1 <= 3s)."""
    m = mu / 2
    best = 0.0
    for nu in grid(0, kappa, 2000):
        c = lattice_count(nu, m)
        c = min(c, rho_xs(nu))                           # every adversary obeys the proved count
        if c < 0:
            continue
        best = max(best, c - 1 + 2 * nu * mu)
    return best


def two_eta_adversary_2freq(mu, kappa=KAPPA, s0=None):
    """d = 2 model: saturated plain at m and lattice spacing s0(kappa) = 5/(15 - 6 kappa) for the Moebius
    blocks; count = min over all witnesses (lengths i*m + j*s0); excess at nu = kappa."""
    m = mu / 2
    nu = kappa
    s0 = s0 or 5 / (15 - 6 * nu)
    c = rho_xs(nu)
    c = min(c, 1 - 2 * nu * m)                           # plain at m
    for i in range(0, 4):
        for j in range(0, 4):
            y = i * m + j * s0
            if y <= 0 or y > 1.5 + 1e-9:
                continue
            if y <= 1:
                c = min(c, 1 - nu * y)
            else:
                c = min(c, (1 + 5 * y) / 6 - nu * y)
    return c - 1 + 2 * nu * mu, c


# ---------------------------------------------------------------- pointwise barrier (Prop. 0)
def pointwise_barrier(mu, kappa=KAPPA):
    """eta < kappa*mu - 1/2 forces max|A|^2/N < Z^{kappa mu}: a pointwise gain beyond H1."""
    return max(0.0, kappa * mu - 0.5)


def pointwise_barrier_unconditional(mu):
    """eta < 2*best_pointwise - 1/2, best_pointwise = Burgess/trivial exponent of |X|^2/M."""
    return max(0.0, 2 * eta_holder_burgess(mu) - 0.5)


# ---------------------------------------------------------------- side routes for the twisted moment F
def loss_S1_holder(mu, s, rho=rho_xs, kappa=KAPPA):
    """Hoelder decoupling F <= (sum|A|^{2p'})^{1/p'} (sum|Q|^{2p})^{1/p}, p = 1/(2s), with S1 classes."""
    best = 0.0
    for d in grid(0, kappa, 2000):
        best = max(best, min(2 * s * mu * d, (1 - 2 * s) * (rho(d) - 1) + mu * d))
    return best


def loss_S1_direct(mu, s, rho=rho_xs, kappa=KAPPA):
    """Stratify F itself: on class d, |Q|^2 <= ||a||^2 Z^{s d} (explicit formula), |A|^2 <= N^{1+d}."""
    best = 0.0
    for d in grid(0, kappa, 2000):
        best = max(best, min(s * d, rho(d) - 1 + (mu + s) * d))
    return best


def main():
    print(f"theta = {THETA}, kappa = {KAPPA:.5f}")
    mus = [0.25, 1 / 3, 0.4, 0.5, 0.6, 2 / 3, 0.7, 0.75, 0.8, 0.87, 0.93, 1.0]
    print("\nTable 1. eta(mu) by route (eta = excess/2; target eta = 0)")
    hdr = ("mu", "deFav", "Burg+H3", "ZF+H3", "S1(XS)", "S1(DH)", "S1 no H1", "LemD", "adv(lat)", "pw-bar", "pw-bar unc")
    print("  ".join(f"{h:>8}" for h in hdr))
    for mu in mus:
        row = [mu, eta_defaveri(mu), eta_holder_burgess(mu), eta_holder_zerofree(mu),
               two_eta_S1(mu) / 2, two_eta_S1(mu, rho=rho_dh) / 2,
               two_eta_S1(mu, kappa=15 / 16) / 2, two_eta_lemmaD(mu) / 2,
               (two_eta_adversary(mu) / 2 if mu >= 2 / 3 - 1e-9 else float('nan')),
               pointwise_barrier(mu), pointwise_barrier_unconditional(mu)]
        print("  ".join(f"{x:8.4f}" for x in row))

    print("\nTable 1b. Lattice adversary with spacing m = mu/2 for all mu (eta), with the XS count cap and with a")
    print("density-hypothesis cap 1 - nu (the excess for mu > 1/2 survives even DH)")
    for mu in (0.4, 0.5, 0.52, 0.55, 0.6, 2 / 3, 0.75, 0.87, 0.93, 1.0):
        m = mu / 2
        best_xs = best_dh = 0.0
        for nu in grid(0, KAPPA, 2000):
            c = lattice_count(nu, m)
            if c >= 0:
                best_xs = max(best_xs, min(c, rho_xs(nu)) - 1 + 2 * nu * mu)
                best_dh = max(best_dh, min(c, rho_dh(nu)) - 1 + 2 * nu * mu)
        print(f"  mu={mu:.3f}: adversary eta = {best_xs/2:.4f} (XS cap), {best_dh/2:.4f} (DH cap);  "
              f"S1 eta = {two_eta_S1(mu)/2:.4f}")

    mu = 0.93
    e2, c2 = two_eta_adversary_2freq(mu)
    print(f"\nAdversary detail at mu = {mu}: lattice spacing m = {mu/2}: count at nu = kappa: "
          f"{min(lattice_count(KAPPA, mu/2), rho_xs(KAPPA)):.4f}, 2eta = {two_eta_adversary(mu):.4f}; "
          f"two-frequency model count {c2:.4f}, 2eta = {e2:.4f};  S1: 2eta = {two_eta_S1(mu):.4f}")

    # consistency of the adversary with the other inputs at mu = 0.93, nu = kappa
    m, nu, c = mu / 2, KAPPA, min(lattice_count(KAPPA, mu / 2), rho_xs(KAPPA))
    print("Adversary vs. inputs (exponents; adversary must not exceed the bound):")
    print(f"  H3   4th moment, length m:     {c + 2*m*(1+nu):.4f} <= {1 + 2*m:.4f}")
    for k in (2, 3, 4):
        B = k * m
        th = max(1, B, 5 / 6 + B / 3, 1 / 3 + 5 * B / 6)
        print(f"  dF   {2*k}-th moment:            {c + k*m*(1+nu):.4f} <= {th + k*m:.4f}")
    print(f"  Bu   pointwise |X|^2/M:         {nu*m:.4f} <= {eta_holder_burgess(mu):.4f}")
    print(f"  H2   count:                     {c:.4f} <= {rho_xs(nu):.4f}")

    # what is needed for eta <= 1/4 at mu = 0.93
    print("\nRequirements for eta <= 1/4 at mu = 0.93 through S1:")
    print("  count needed: rho(nu) <= 1.5 - 1.86 nu on [0.5376, kappa]; XS gives:")
    for nu in (0.55, 0.6, 0.65, 0.7, KAPPA):
        print(f"    nu = {nu:.3f}: need <= {1.5 - 1.86*nu:.4f}, have {rho_xs(nu):.4f}")
    print(f"  sixth moment route: 2eta = eps6 + kappa*m -> eps6 <= {0.5 - KAPPA*0.465:.4f} for eta = 1/4; "
          f"eps6 < {two_eta_S1(0.93) - KAPPA*0.465:.4f} to beat S1")
    y = 3 * 0.465
    need = 0.112 + KAPPA * y
    lam = (need - y) / (1 - y)
    print(f"  long-moment route (adversary count at nu = kappa set by the long line at y = {y:.3f}): "
          f"exponent {(1+5*y)/6:.4f} -> {need:.4f}, i.e. lambda = {lam:.3f} in U + D^(1-lambda) U^lambda")

    print("\nTable 2. Side remark: loss of the twisted moment F on the D1 window")
    print("  (Cauchy-Schwarz pool: s; H1-pointwise pool: kappa s; Hoelder through max|A|^2: 2 s kappa mu)")
    print(f"{'mu':>6} {'s':>6} {'kappa s':>8} {'2s kappa mu':>12} {'S1-Hoelder':>11} {'S1-direct':>10}")
    for mu in (0.76, 0.865):
        for s in (0.02, 0.05, 0.1, 0.14):
            print(f"{mu:6.3f} {s:6.3f} {KAPPA*s:8.4f} {2*s*KAPPA*mu:12.4f} {loss_S1_holder(mu, s):11.4f} "
                  f"{loss_S1_direct(mu, s):10.4f}")
    print("  S1-direct is diagonal exactly when mu + s <= 2/3 (outside the window).")

    print("\nTable 3. Zero count that S1 needs (R(nu) <= 1 + 2 eta - 2 mu nu for nu in (2 eta/mu, kappa])")
    for mu, eta in ((0.5, 0.0), (0.93, 0.0), (0.93, 0.25), (0.93, 0.3), (0.75, 0.0), (0.75, 0.1)):
        lo = 2 * eta / mu
        pts = [lo + (KAPPA - lo) * t for t in (0.0, 0.5, 1.0)] if lo < KAPPA else []
        s = ", ".join(f"nu={nu:.3f}: need {1 + 2*eta - 2*mu*nu:+.3f} (XS {rho_xs(nu):.3f})" for nu in pts)
        print(f"  mu={mu:.2f} eta={eta:.2f}: {s}")
    print(f"  amplification: beating max|A|^2 <= N^(1+kappa) needs an amplifier of length > 1 - kappa*mu "
          f"= {1 - KAPPA*0.93:.3f} at mu = 0.93; the ideal face allows 1 - mu = {1 - 0.93:.2f}")


if __name__ == '__main__':
    main()
