"""Mechanism 4b: adversarial search.  For fixed (Z, m1, m2, slots) maximise the mean row energy of the toy over the admissible smooth data
(t, v_i, profile flatness, X-scales; each O(1), i.e. not growing with Z, because growth of t, v would be paid for by (1+|t|+height)^degree
and large derivative norms by (control S)^2), and look at how the OPTIMUM grows with Z.

   python3 m4_adversary.py     (writes logs/m4_adversary.log)
"""
import math
import os
import time

import numpy as np

import sweep
import toy

HERE = os.path.dirname(os.path.abspath(__file__))
LOG = open(os.path.join(HERE, "logs", "m4_adversary.log"), "w")


def out(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    LOG.write(s + "\n")
    LOG.flush()


def rand_data(base: toy.Data, rng, allow_t=True):
    return toy.Data(
        m1=base.m1, m2=base.m2, slots=base.slots,
        t=float(rng.uniform(-300, 300)) if (allow_t and rng.random() < 0.7) else 0.0,
        v=tuple(float(rng.uniform(-300, 300)) if rng.random() < 0.7 else 0.0 for _ in base.slots),
        flat_plain=float(rng.uniform(0.1, 0.5)), flat_slot=float(rng.uniform(0.1, 0.5)),
        x_scale=(float(rng.uniform(0.7, 1.5)), float(rng.uniform(0.7, 1.5))), sigma=base.sigma)


def optimise(ctx, base, rng, n=120):
    best = None
    vals = []
    for i in range(n):
        d = base if i == 0 else rand_data(base, rng)
        e = toy.row_energies(ctx, d)
        w = ctx.phi * ctx.keep
        v = float(np.sum(w * e) / np.sum(w))
        vals.append(v)
        if best is None or v > best[0]:
            best = (v, d)
    return best, vals


def main():
    t0 = time.time()
    out(f"# m4_adversary  {time.strftime('%Y-%m-%d %H:%M:%S')}")
    out("mean_row at the baseline datum, the maximum over 120 random admissible data, and the median over the 120; one fixed row sample per Z.")
    configs = [toy.Data(0.5, 0.5), toy.Data(0.75, 0.75), toy.Data(0.75, 0.0), toy.Data(0.4, 0.4, slots=(0.3,)),
               toy.Data(0.25, 0.25, slots=(0.3,)), toy.Data(0.0, 0.0, slots=(0.3,)), toy.Data(0.4, 0.4, slots=(0.15, 0.15))]
    Zs = [1e4, 1e5, 1e6, 1e7]
    rng = np.random.default_rng(99)
    table = {}
    for Z in Zs:
        B = 2 * Z
        xs, ys = toy.sample_rows(B, 2500, rng)
        Nmax = max(sweep.nmax_for(Z, [toy.Data(c.m1, c.m2, c.slots, x_scale=(1.5, 1.5)) for c in configs]), 100)
        if Nmax > 1.2e6:
            continue
        PI = toy.build_prime_ideals(Nmax)
        IL = toy.build_ideals(PI, Nmax)
        ctx = toy.build_context(Z, Nmax, xs, ys, K=Z, PI=PI, IL=IL, keep=np.ones(len(xs), bool))
        for base in configs:
            (bv, bd), vals = optimise(ctx, base, rng)
            table.setdefault(sweep.config_name(base), []).append((Z, vals[0], bv, float(np.median(vals)), bd))
            out(f"Z={Z:8.0e} {sweep.config_name(base):32s} baseline={vals[0]:8.4f}  max={bv:8.4f}  median={np.median(vals):8.4f}  max/base={bv/vals[0]:5.2f}"
                f"   best datum: t={bd.t:+.0f} v={tuple(round(x) for x in bd.v)} flat=({bd.flat_plain:.2f},{bd.flat_slot:.2f}) xs=({bd.x_scale[0]:.2f},{bd.x_scale[1]:.2f})")
    out("")
    out("growth exponent in Z of the OPTIMISED energy (max over data) and of the baseline:")
    for cname, rows in table.items():
        if len(rows) < 3:
            continue
        Zs_ = np.array([r[0] for r in rows])
        kb = np.polyfit(np.log(Zs_), np.log([r[2] for r in rows]), 1)[0]
        k0 = np.polyfit(np.log(Zs_), np.log([r[1] for r in rows]), 1)[0]
        out(f"  {cname:34s} kappa(max over data) = {kb:+.3f}   kappa(baseline) = {k0:+.3f}")
    out(f"# time {time.time()-t0:.0f}s")


if __name__ == "__main__":
    main()
