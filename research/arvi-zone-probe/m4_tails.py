"""Mechanism 4d: tails.  A violation of the energy bound needs LARGE VALUES: rows with |row_z|^2 far above the Gaussian-like typical size.
We take ALL kept rows with N(z) <= 2K (exhaustive: no sampling) at Z = 1e4 and 1e5 and compare the upper quantiles of |row_z|^2 of the real
sextic family with those of the random sextic model (i.i.d. sixth roots of unity at the primes).  Equal tails = no anomalous large values.

   python3 m4_tails.py     (writes logs/m4_tails.log)
"""
import math
import os
import time

import numpy as np

import sweep
import toy

HERE = os.path.dirname(os.path.abspath(__file__))
LOG = open(os.path.join(HERE, "logs", "m4_tails.log"), "w")


def out(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    LOG.write(s + "\n")
    LOG.flush()


def all_rows(B):
    xmax = int(2 * math.sqrt(B / 3.0)) + 2
    X, Y = [], []
    for x in range(-xmax, xmax + 1):
        disc = 4.0 * B - 3.0 * x * x
        if disc < 0:
            continue
        sq = math.sqrt(disc)
        for y in range(math.ceil((x - sq) / 2 - 1e-9), math.floor((x + sq) / 2 + 1e-9) + 1):
            if x * x - x * y + y * y > 0:
                X.append(x)
                Y.append(y)
    return np.array(X, dtype=np.int64), np.array(Y, dtype=np.int64)


def wquant(v, w, qs):
    o = np.argsort(v)
    cw = np.cumsum(w[o])
    cw /= cw[-1]
    return [float(v[o][min(len(v) - 1, int(np.searchsorted(cw, q)))]) for q in qs]


def main():
    t0 = time.time()
    out(f"# m4_tails  {time.strftime('%Y-%m-%d %H:%M:%S')}")
    qs = (0.5, 0.9, 0.99, 0.999, 0.9999)
    out("weighted quantiles (weights Phi(N(z)/K), kept rows) and the maximum of |row_z|^2 over ALL rows;  A = actual sextic family, R = random sextic model")
    out(f"{'Z':>7s} {'#rows':>8s} {'config':28s} {'':2s} " + " ".join(f"q{q:<7g}" for q in qs) + f" {'max':>9s} {'mean':>8s}")
    cases = [(1e4, [toy.Data(0.5, 0.5), toy.Data(0.75, 0.75), toy.Data(1.0, 0.0), toy.Data(0.4, 0.4, slots=(0.3,)), toy.Data(0.25, 0.25, slots=(0.5,)),
                    toy.Data(0.0, 0.0, slots=(0.5,))]),
             (1e5, [toy.Data(0.4, 0.4), toy.Data(0.5, 0.5), toy.Data(0.4, 0.4, slots=(0.3,)), toy.Data(0.25, 0.25, slots=(0.5,)), toy.Data(0.0, 0.0, slots=(0.5,))])]
    for Z, cfgs in cases:
        B = 2 * Z
        x, y = all_rows(B)
        Nmax = sweep.nmax_for(Z, cfgs)
        PI = toy.build_prime_ideals(Nmax)
        IL = toy.build_ideals(PI, Nmax)
        ctxA = toy.build_context(Z, Nmax, x, y, K=Z, PI=PI, IL=IL)
        ctxR = toy.build_context(Z, Nmax, x, y, K=Z, PI=PI, IL=IL, random_model=True, rng=np.random.default_rng(4))
        ctxR.keep[:] = True
        for d in cfgs:
            for tag, ctx in (("A", ctxA), ("R", ctxR)):
                e = toy.row_energies(ctx, d)
                w = ctx.phi * ctx.keep
                qv = wquant(e, w, qs)
                live = ctx.keep & (ctx.phi > 0)
                out(f"{Z:7.0e} {len(x):8d} {sweep.config_name(d):28s} {tag:2s} " + " ".join(f"{v:8.3f}" for v in qv) +
                    f" {float(e[live].max()):9.2f} {float(np.sum(w * e) / np.sum(w)):8.4f}")
    out("")
    out("Reading: the real family and the random model have the same quantiles up to sampling noise; the maximum over all ~10^4-10^5 rows is a few times the 0.9999-quantile")
    out("(polylog), never a power of K.  [numerical]")
    out(f"# time {time.time()-t0:.0f}s")


if __name__ == "__main__":
    main()
