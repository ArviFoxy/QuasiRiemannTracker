"""Mechanism 4c: do the plain polynomials and the slot polynomials decouple?
rho = mean(prod of the factors |A1|^2/X1, |A2|^2/X2, |S_i|^2/D_i) / prod(mean of each factor)   (weighted over kept rows).
rho ~ 1 means the energy factorises:  E/K = (plain factor) x (slot factors),  each of which is O(1) (plain: ~0.3-0.4, flat in Z; slot: ~ 1/ln D).

   python3 m4_decoupling.py     (writes logs/m4_decoupling.log)
"""
import os
import time

import numpy as np

import sweep
import toy

HERE = os.path.dirname(os.path.abspath(__file__))
LOG = open(os.path.join(HERE, "logs", "m4_decoupling.log"), "w")


def out(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    LOG.write(s + "\n")
    LOG.flush()


def main():
    t0 = time.time()
    out(f"# m4_decoupling  {time.strftime('%Y-%m-%d %H:%M:%S')}")
    out("A-part = |A1|^2 |A2|^2 / (X1 X2),  S-part = prod_i |S_i|^2 / D_i,  rho_cross = E[A-part S-part] / (E[A-part] E[S-part])   (weighted over kept rows).")
    out("rho_cross ~ 1: the plain and slot polynomials are uncorrelated, so E/K = (plain factor) x (slot factor), each O(1) and not growing.")
    out("(A1, A2 are two views of the same L-function: E[A-part] ~ 2 E|A1|^2 E|A2|^2 ;  slots with equal w_i are the same polynomial: E[S-part] = k! (E|S|^2)^k - both are inside the factors, not in rho_cross.)")
    out(f"{'config':36s} {'Z':>7s} {'E[A-part]':>10s} {'E[S-part]':>10s} {'E[joint]':>10s} {'rho_cross':>9s}")
    rng = np.random.default_rng(8)
    configs = [toy.Data(0.5, 0.5, slots=(0.3,)), toy.Data(0.75, 0.75, slots=(0.3,)), toy.Data(1.0, 0.0, slots=(0.3,)),
               toy.Data(0.5, 0.5, slots=(0.5,)), toy.Data(0.5, 0.5, slots=(0.8,)), toy.Data(0.75, 0.75, slots=(0.5,)),
               toy.Data(1.0, 1.0, slots=(0.5,)), toy.Data(0.5, 0.5, slots=(1.0,)), toy.Data(0.4, 0.4, slots=(0.5, 0.7)),
               toy.Data(0.5, 0.5, slots=(0.3, 0.4, 0.5))]
    for Z in (1e4, 1e5, 3e5):
        feas = [d for d in configs if sweep.nmax_for(Z, [d]) <= 7e5]
        if not feas:
            continue
        Nmax = sweep.nmax_for(Z, feas)
        PI = toy.build_prime_ideals(Nmax)
        IL = toy.build_ideals(PI, Nmax)
        R = int(min(6000, 2.5e8 / IL.n))
        xs, ys = toy.sample_rows(2 * Z, R, rng)
        ctx = toy.build_context(Z, Nmax, xs, ys, K=Z, PI=PI, IL=IL)
        w = ctx.phi * ctx.keep
        for d in feas:
            e, parts = toy.row_energies(ctx, d, return_parts=True)
            apart = parts["A1"] * parts["A2"]
            spart = np.ones_like(apart)
            for k, v in parts.items():
                if k.startswith("S"):
                    spart = spart * v
            m = lambda v: float(np.sum(w * v) / np.sum(w))
            ea, es, ej = m(apart), m(spart), m(e)
            out(f"{sweep.config_name(d):36s} {Z:7.0e} {ea:10.4f} {es:10.4f} {ej:10.4f} {ej / (ea * es):9.2f}")
    out(f"# time {time.time()-t0:.0f}s")


if __name__ == "__main__":
    main()
