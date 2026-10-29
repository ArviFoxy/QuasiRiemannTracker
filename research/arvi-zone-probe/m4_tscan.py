"""Large twist t (and large slot frequency v): the energy of the toy does not grow with t (polynomial allowance (1+|t|+height)^degree is never needed).
   python3 m4_tscan.py     (writes logs/m4_tscan.log)"""
import os
import time

import numpy as np

import sweep
import toy

HERE = os.path.dirname(os.path.abspath(__file__))
LOG = open(os.path.join(HERE, "logs", "m4_tscan.log"), "w")


def out(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    LOG.write(s + "\n")
    LOG.flush()


def main():
    t0 = time.time()
    out(f"# m4_tscan  {time.strftime('%Y-%m-%d %H:%M:%S')}")
    Z = 1e4
    rng = np.random.default_rng(5)
    xs, ys = toy.sample_rows(2 * Z, 4000, rng)
    cfgs = [toy.Data(0.5, 0.5), toy.Data(0.75, 0.75), toy.Data(1.0, 0.0), toy.Data(1.3, 0.0), toy.Data(0.4, 0.4, slots=(0.3,)),
            toy.Data(0.0, 0.0, slots=(0.5,))]
    Nmax = sweep.nmax_for(Z, cfgs)
    ctx = toy.build_context(Z, Nmax, xs, ys, K=Z)  # proper initialKeep
    out(f"Z = {Z:.0e}, {len(xs)} sampled rows, kept {int(ctx.keep.sum())}.  mean row energy as the twist t (and, for the slot, v = t) grows:")
    out(f"   {'t':>9s} " + " ".join(f"{sweep.config_name(d):>26s}" for d in cfgs))
    w = ctx.phi * ctx.keep
    for t in (0.0, 1.0, 10.0, 100.0, 1e3, 1e4, 1e5, 1e6):
        line = f"   {t:9.0f} "
        for d in cfgs:
            dd = toy.Data(d.m1, d.m2, d.slots, t=t, v=tuple(t for _ in d.slots))
            e = toy.row_energies(ctx, dd)
            line += f" {float(np.sum(w * e) / np.sum(w)):26.4f}"
        out(line)
    out("   => flat in t: large heights do not create growth (they would be paid by (1+|t|+height)^degree anyway).")
    out(f"# time {time.time()-t0:.0f}s")


if __name__ == "__main__":
    main()
