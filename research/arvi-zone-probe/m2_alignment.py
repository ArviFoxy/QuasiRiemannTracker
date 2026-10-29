"""Mechanism 2: large-sieve sharpness / duality / phase alignment with one row or many rows.

(i)   Functional-equation threshold: |A(z)|^2/X as a function of the dual length  delta = 3 N(f) / (4 pi^2 X),  N(f) = TRUE conductor norm of the row character
      (toy.cond_norm: the part away from 2, lambda times the 2- and lambda-parts, which reach N(72) = 5184):
      alive (~ 0.1-0.4) for delta >~ 1, dead (-> 0) for delta << 1.  This is what makes every plain length  m_j > M  harmless, and caps the effective plain length at min(X, q/X).
(ii)  One row: how large can the adversary make a SINGLE kept row by choosing the admissible smooth data (t, v, profile shapes, X-scales)?
(iii) Many rows: sum of the largest K^u row energies (Phi can select any set of norm values) compared with the allowed K.

   python3 m2_alignment.py     (writes logs/m2_alignment.log)
"""
import math
import os
import time

import numpy as np

import sweep
import toy

HERE = os.path.dirname(os.path.abspath(__file__))
LOG = open(os.path.join(HERE, "logs", "m2_alignment.log"), "w")


def out(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    LOG.write(s + "\n")
    LOG.flush()


def threshold_scan(Z, rng, R=2400):
    """|A|^2/X against the dual length  delta = |d_K| N(f) / (4 pi^2 X) = 3 N(f) / (4 pi^2 X),  N(f) = TRUE conductor norm of the row character."""
    B = 2 * Z
    xs, ys = toy.sample_rows(B, R, rng)
    keep = np.array([not toy.is_removed(int(a), int(b)) for a, b in zip(xs, ys)])
    q6 = np.array([toy.q6_norm(int(a), int(b)) for a, b in zip(xs, ys)])
    Nf = np.array([toy.cond_norm(int(a), int(b)) for a, b in zip(xs, ys)])
    C23 = Nf / q6
    out(f"== (i) functional-equation threshold, Z = {Z:.0e}: |A(z)|^2/X for A = sum_I (z/I)_6 W(N I / X), against delta = 3 N(f) / (4 pi^2 X) ==")
    out(f"   rows sampled with N(z) <= 2K: {R}; kept: {int(keep.sum())}.  N(f) = q6 * 4^f2 * 3^flam (toy.cond_norm, local class field theory, checked against discriminants in selftest.py).")
    qs = np.quantile(C23[keep], [0.0, 0.25, 0.5, 0.75, 1.0])
    out(f"   2,lambda-part of the conductor N(f)/q6 over kept rows: min {qs[0]:.0f}, quartiles {qs[1]:.0f} / {qs[2]:.0f} / {qs[3]:.0f}, max {qs[4]:.0f}  (N(72) = {4**3 * 3**4})")
    cs = [0.003, 0.01, 0.03, 0.1, 0.3, 1, 3, 10, 30, 100]
    Xs = [c * Z for c in cs]
    Nmax = int(2.25 * max(Xs)) + 10
    PI = toy.build_prime_ideals(Nmax)
    IL = toy.build_ideals(PI, Nmax)
    chunk = int(max(100, min(R, 2.0e8 / IL.n)))
    profiles = [("Schwartz-type flat-top (the kind the Lean statement uses)", toy.make_profile(0.25, 2.25, 0.25)),
                ("polynomial bump (4(y-1/4)(9/4-y)/4)^6, only C^5 -- display only", toy.make_poly_profile(0.25, 2.25, 6))]
    edges = [0.0, 0.001, 0.003, 0.01, 0.03, 0.1, 0.3, 1.0, 3.0, 10.0, 30.0, 1e30]
    for pname, W in profiles:
        cols = []
        for s0 in range(0, R, chunk):
            sl = slice(s0, min(R, s0 + chunk))
            ctx = toy.build_context(Z, Nmax, xs[sl], ys[sl], K=Z, PI=PI, IL=IL, keep=keep[sl])
            cols.append(np.array([np.abs(toy.plain_sum(ctx, X, W)) ** 2 / X for X in Xs]))
        P = np.concatenate(cols, axis=1)  # (len(Xs), R)
        delta = 3.0 * Nf[None, :] / (4 * math.pi ** 2 * np.array(Xs)[:, None])
        out(f"   profile: {pname}")
        out(f"   {'delta in':>16s} | {'all kept rows':>22s} | {'2,lambda-part = 1':>22s} | {'2,lambda-part >= 500':>22s}   (mean |A|^2/X, pairs (row, X))")
        for lo, hi in zip(edges[:-1], edges[1:]):
            cells = []
            for sub in (np.ones(R, bool), C23 == 1, C23 >= 500):
                m = keep[None, :] & sub[None, :] & (delta > lo) & (delta <= hi)
                cells.append(f"{P[m].mean():10.3e} ({int(m.sum()):6d})" if m.sum() > 5 else f"{'-':>10s} ({int(m.sum()):6d})")
            hi_s = f"{hi:.3g}" if hi < 1e29 else "inf"
            out(f"   {lo:7.3g} .. {hi_s:>6s} | {cells[0]:>22s} | {cells[1]:>22s} | {cells[2]:>22s}")
        # the same data binned by q6 alone, as in the first version of this script (ignores the 2,lambda-part)
        rat = np.array(Xs)[:, None] / q6[None, :]
        m = keep[None, :] & (rat >= 30)
        out(f"   (binned by X/q6 >= 30 alone, i.e. ignoring the 2,lambda-part: mean {P[m].mean():.3f} over {int(m.sum())} pairs -- NOT dead, because N(f)/q6 reaches {qs[4]:.0f})")
    out("   => alive (|A|^2/X ~ 0.1-0.4, the diagonal size) for delta >~ 1; collapsing for delta <~ 0.3, whatever the 2,lambda-part: rigorous consequence of the functional equation (dual length < 1).")
    out("")


def lattice_rows(B):
    """all z = x + y w with 0 < N(z) <= B"""
    xmax = int(2 * math.sqrt(B / 3.0)) + 2
    X, Y = [], []
    for x in range(-xmax, xmax + 1):
        for y in range(-xmax, xmax + 1):
            if 0 < x * x - x * y + y * y <= B:
                X.append(x)
                Y.append(y)
    return np.array(X, dtype=np.int64), np.array(Y, dtype=np.int64)


def threshold_typical(Z, cs=(1, 10, 100, 300, 1e3, 3e3, 1e4, 3e4)):
    """all kept rows with N(z) <= 2K at a small Z, Phi-weighted: how large must X/K be before the typical row is dead?"""
    B = 2 * Z
    xs, ys = lattice_rows(B)
    keep = np.array([not toy.is_removed(int(a), int(b)) for a, b in zip(xs, ys)])
    Nf = np.array([toy.cond_norm(int(a), int(b)) for a, b in zip(xs, ys)])
    Xs = [c * Z for c in cs]
    Nmax = int(2.25 * max(Xs)) + 10
    PI = toy.build_prime_ideals(Nmax)
    IL = toy.build_ideals(PI, Nmax)
    chunk = int(max(20, min(len(xs), 2.0e8 / IL.n)))
    W = toy.make_profile(0.25, 2.25, 0.25)
    cols, phis = [], []
    for s0 in range(0, len(xs), chunk):
        sl = slice(s0, min(len(xs), s0 + chunk))
        ctx = toy.build_context(Z, Nmax, xs[sl], ys[sl], K=Z, PI=PI, IL=IL, keep=keep[sl])
        cols.append(np.array([np.abs(toy.plain_sum(ctx, X, W)) ** 2 / X for X in Xs]))
        phis.append(ctx.phi)
    P = np.concatenate(cols, axis=1)
    w = np.concatenate(phis) * keep
    out(f"== (i-b) typical rows: ALL {len(xs)} lattice rows with N(z) <= 2K, K = Z = {Z:.0e}; {int(keep.sum())} kept; Phi-weighted mean of |A|^2/X, single plain polynomial, Schwartz-type profile ==")
    out(f"   median of the true conductor norm N(f) over kept rows: {float(np.median(Nf[keep])):.3g} = {float(np.median(Nf[keep])) / Z:.0f} K   (K = {Z:.0e})")
    out(f"   {'X/K':>8s} {'X':>10s} | {'mean |A|^2/X':>13s} | {'delta at median N(f)':>20s}")
    medNf = float(np.median(Nf[keep]))
    for i, (c, X) in enumerate(zip(cs, Xs)):
        m = float(np.sum(w * P[i]) / np.sum(w))
        out(f"   {c:8.3g} {X:10.3g} | {m:13.4e} | {3.0 * medNf / (4 * math.pi ** 2 * X):20.3g}")
    out("   => the typical kept row is alive up to X ~ N(f) (here ~ 10^2 K, because the 2,lambda-part multiplies q6 by a median factor ~ 4e2) and collapses beyond it;")
    out("      at accessible Z the constant N(f)/K postpones the dead regime to m_j - 1 >~ log(N(f)/K * 30)/log Z; asymptotically Z^delta beats every constant.")
    out("")


def one_row_search(Z, cfg, rng, nrows=400, nparam=150):
    out(f"== (ii) one row: best admissible data per row;  Z = {Z:.0e}, base config {sweep.config_name(cfg)} ==")
    B = 2 * Z
    xs, ys = toy.sample_rows(B, nrows, rng)
    Nmax = sweep.nmax_for(Z, [toy.Data(cfg.m1 + 0.0, cfg.m2 + 0.0, cfg.slots, x_scale=(1.5, 1.5))])
    PI = toy.build_prime_ideals(Nmax)
    IL = toy.build_ideals(PI, Nmax)
    ctx = toy.build_context(Z, Nmax, xs, ys, K=Z, PI=PI, IL=IL)
    T = (Z ** cfg.m1) * (Z ** cfg.m2) * (np.prod([Z ** w for w in cfg.slots]) if cfg.slots else 1.0)
    best = np.zeros(nrows)
    allv = []
    for _ in range(nparam):
        d = toy.Data(m1=cfg.m1, m2=cfg.m2, slots=cfg.slots,
                     t=float(rng.uniform(-200, 200)) if rng.random() < 0.7 else 0.0,
                     v=tuple(float(rng.uniform(-200, 200)) for _ in cfg.slots),
                     flat_plain=float(rng.uniform(0.05, 0.5)), flat_slot=float(rng.uniform(0.05, 0.5)),
                     x_scale=(float(rng.uniform(0.7, 1.5)), float(rng.uniform(0.7, 1.5))))
        e = toy.row_energies(ctx, d)
        allv.append(e)
        best = np.maximum(best, e)
    allv = np.array(allv)
    keep = ctx.keep
    out(f"   trivial size T = {T:.3e}, allowed per-row size K = {Z:.3e}")
    out(f"   mean over rows and params:          {allv[:, keep].mean():10.3f}")
    out(f"   median over rows of best-over-params: {np.median(best[keep]):10.3f}")
    out(f"   max over rows of best-over-params:    {best[keep].max():10.3f}   (= {best[keep].max()/Z:.2e} K, = {best[keep].max()/T:.2e} T)")
    out("")
    return best[keep], ctx.phi[keep]


def many_rows(Z, cfg, rng, R=6000):
    out(f"== (iii) many rows: sum of the K^u largest row energies (Phi may select any set of norm values), Z = {Z:.0e}, {sweep.config_name(cfg)} ==")
    B = 2 * Z
    xs, ys = toy.sample_rows(B, R, rng)
    Nmax = sweep.nmax_for(Z, [cfg])
    ctx = toy.build_context(Z, Nmax, xs, ys, K=Z)
    e = toy.row_energies(ctx, cfg)
    e = np.sort(e[ctx.keep & (ctx.phi > 0)])[::-1]
    Keff = toy.lattice_rows_count(B) * (len(e) / R)
    out(f"   {'u':>5s} {'#rows K^u':>11s} {'sum of top K^u energies (est.)':>32s} {'/ K':>9s}")
    for u in (0.0, 0.1, 0.2, 0.4, 0.6, 0.8, 0.9, 1.0):
        n = Z ** u
        f = n / Keff
        if f * len(e) < 1:
            val = float(e[0]) * n
        else:
            k = max(1, int(round(f * len(e))))
            val = float(np.mean(e[:k])) * n
        out(f"   {u:5.2f} {n:11.1f} {val:32.2f} {val / Z:9.3f}")
    out("")


KNOBS = """== (iv) the adversary's knobs in RegionAffineAt / UnitRegionSource and whether they can align phases with a kept row ==
 knob                          quantifier position                    effect on the coefficient vector a_n (n = I1 I2 P1..Pk)            alignment with kept rows?
 t, height, v_i                inside, real, polynomially penalised   multiplies a_n by N(n)^{it} and (N(P)/D)^{i v}: smooth in N(.)       no  (the rows are finite-order characters; a smooth phase cannot imitate them)
 theta_i                       inside, finite group Char(M,H)         trivial on the pool (identity class)                                  no  (inert)
 w_i <= mesh, sigma_i = 33/50  inside / fixed                         lengths of slots; sigma only a smooth weight (N/D)^(-sigma)           no
 profiles p (2 Schwartz fns)   inside, control^2 allowed              smooth weight in N(I)/X on all ideals                                 no
 X1, X2 > 0                    inside                                 lengths; with X > q the sum is negligible (dual length q/X < 1)       no (helps the prover)
 Phi (Re >= 0, sup-norm only)  inside                                 selects rows by NORM value N(z); weights in [0,1] arbitrary            selects rows, creates no correlation: E is monotone in Phi
 eta, eta0, Q, rayModulus, H   OUTSIDE the exists-C (fixed, Z-free)   fixed finite-conductor twists                                         only with rows whose primitive character has conductor | Q0 = internalQ  -> exactly the rows initialKeep removes
 alpha (number of slots)       OUTSIDE                                bounded number of slots k                                              no
 => the only rows that a fixed finite-conductor datum can align with are the FixedInducingRow ones, and they are excluded from the sum.
"""


def main():
    t0 = time.time()
    out(f"# m2_alignment  {time.strftime('%Y-%m-%d %H:%M:%S')}")
    rng = np.random.default_rng(21)
    threshold_scan(3e3, rng, R=2400)
    threshold_typical(100.0)
    one_row_search(1e5, toy.Data(0.5, 0.5), rng)
    one_row_search(1e5, toy.Data(0.75, 0.75), rng)
    one_row_search(1e5, toy.Data(0.4, 0.4, slots=(0.3,)), rng)
    many_rows(1e5, toy.Data(0.75, 0.75), rng)
    many_rows(1e5, toy.Data(0.4, 0.4, slots=(0.3,)), rng)
    out(KNOBS)
    out(f"# time {time.time()-t0:.0f}s")


if __name__ == "__main__":
    main()
