"""Mechanism 4 (numerics): growth exponent of the toy energy in Z at representative grid points.

   python3 m4_scaling.py S1 S2 S4 S5      (any subset; results -> logs/m4_<name>.{log,json})

What is measured:   mean_row(Z) = weighted mean over kept rows of |row_z|^2 ,  so that  E = K_eff * mean_row , K = Z (M = 1).
The Lean bound  E <= C * diagonalControl(Phi) * control^2 * (1+|t|+height)^degree * Z^{1+eps}  is equivalent to  mean_row <= C' Z^eps.
A power-law violation would show up as kappa > 0 in  mean_row ~ Z^kappa.
"""
import json
import os
import sys
import time

import numpy as np

import sweep
import toy

HERE = os.path.dirname(os.path.abspath(__file__))
LOGDIR = os.path.join(HERE, "logs")

ZS_BIG = [1e3, 3e3, 1e4, 3e4, 1e5, 3e5, 1e6, 3e6]
ZS_HIGH = [1e4, 1e5, 1e6, 1e7, 1e8, 1e9, 1e10, 1e11, 1e12]


def feasible(d: toy.Data, Z: float, cap=9e5) -> bool:
    return sweep.nmax_for(Z, [d]) <= cap


def run(name, Zs, configs, **kw):
    path = os.path.join(LOGDIR, f"m4_{name}.log")
    f = open(path, "w")

    def out(s=""):
        print(s, flush=True)
        f.write(s + "\n")
        f.flush()

    out(f"# experiment {name}   ({time.strftime('%Y-%m-%d %H:%M:%S')})")
    out(f"# kw = { {k: v for k, v in kw.items()} }")
    t0 = time.time()
    S = sweep.sweep(f"m4_{name}", Zs, configs, logdir=LOGDIR, Z_filter=feasible, **kw)
    out(f"# time {time.time()-t0:.0f}s")
    sweep.print_summary(S, out)
    out("")
    out("# per-Z detail: config | Z | rows | mean_row +- se | E/K | max_row | q99 | kept_fraction")
    for cname, s in S.items():
        for r in s["rows"]:
            out(f"{cname:44s} Z={r['Z']:9.3g} R={r['R']:6d} mean_row={r['mean_row']:9.4f}+-{r['se_mean_row']:.4f} "
                f"E/K={r['E_over_K']:8.4f} max_row={r['max_row']:9.2f} q99={r['q99_row']:8.3f} kept={r['kept_fraction']:.4f} min_pool={min(r.get('min_pool', 0), 999999)}")
    f.close()
    return S


def D(m1, m2, slots=(), **kw):
    return toy.Data(m1=m1, m2=m2, slots=tuple(slots), **kw)


def experiments():
    S1 = [D(0.4, 0.4), D(0.5, 0.5), D(0.6, 0.6), D(0.75, 0.75), D(0.9, 0.9), D(0.75, 0.25), D(0.5, 0.0), D(0.75, 0.0),
          D(1.0, 0.0), D(1.0, 0.5), D(1.1, 0.0), D(1.2, 0.3), D(1.0, 1.0)]
    S2 = [D(0.4, 0.4, (0.3,)), D(0.4, 0.4, (0.15, 0.15)), D(0.4, 0.4, (0.1, 0.1, 0.1)), D(0.5, 0.5, (0.3,)),
          D(0.75, 0.0, (0.3,)), D(0.25, 0.25, (0.3,)), D(0.0, 0.0, (0.3,)), D(0.75, 0.75, (0.3,)),
          # beyond the probed window (stress tests of the classical barrier a+s=1)
          D(0.0, 0.0, (0.5,)), D(0.0, 0.0, (0.8,)), D(0.0, 0.0, (1.0,)), D(0.5, 0.0, (0.6,)), D(0.5, 0.5, (0.5,)),
          D(0.4, 0.4, (0.5, 0.5))]
    # high-Z set: only configurations whose ideal tables stay small (a <= ~1.0 for Z up to 1e10)
    S3 = []
    for a_split in [(0.0, 0.0), (0.15, 0.15), (0.25, 0.25), (0.4, 0.4), (0.5, 0.5), (0.5, 0.0), (0.4, 0.0), (0.75, 0.0)]:
        for slots in [(), (0.1,), (0.2,), (0.3,), (0.15, 0.15), (0.1, 0.1, 0.1)]:
            if a_split == (0.0, 0.0) and not slots:
                continue
            S3.append(D(a_split[0], a_split[1], slots))
    # beyond the window (classical barrier a + s = 1 would be crossed)
    S3 += [D(0.0, 0.0, (0.5,)), D(0.25, 0.25, (0.5,)), D(0.5, 0.5, (0.3,)), D(0.5, 0.5, (0.4,)), D(0.4, 0.4, (0.5,)), D(0.0, 0.0, (0.7,)), D(0.25, 0.25, (0.8,)), D(0.15, 0.15, (0.4, 0.4))]
    return {"S1": S1, "S2": S2, "S3": S3}


if __name__ == "__main__":
    which = sys.argv[1:] or ["S1"]
    ex = experiments()
    for w in which:
        if w == "S1":
            run("S1_plain_only", ZS_BIG, ex["S1"], R_total=4000, seed=1)
        elif w == "S2":
            run("S2_with_slots", ZS_BIG, ex["S2"], R_total=4000, seed=2)
        elif w == "S3":
            run("S3_high_Z", ZS_HIGH, ex["S3"], R_total=4000, seed=6)
        elif w == "S4":  # random sextic model, same configs
            run("S4_random_model", ZS_BIG, ex["S1"] + ex["S2"], R_total=4000, seed=3, random_model=True)
        elif w == "S4b":
            run("S4b_random_model_high_Z", ZS_HIGH, ex["S3"], R_total=4000, seed=7, random_model=True)
        elif w == "S5":  # eta = (c0/.)_6 with c0 = 3 + w (prime of norm 7)
            run("S5_eta_twist", ZS_BIG, [D(0.5, 0.5), D(0.75, 0.75), D(0.4, 0.4, (0.3,)), D(0.75, 0.0)], R_total=4000, seed=4,
                c0=(3, 1))
        else:
            print("unknown experiment", w)
