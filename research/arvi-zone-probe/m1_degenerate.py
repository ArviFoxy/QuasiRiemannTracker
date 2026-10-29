"""Mechanism 1: degenerate rows (principal / perfect powers / units / low conductor).

Questions answered numerically here
  (a) how many rows have a given sextic-conductor exponent u  (N(rad_6 z) = K^u),  and how many are removed by initialKeep;
  (b) for each class of degenerate row: is it removed by the mask?  if kept, is its row energy of the trivial size T?
  (c) positive control: if the mask were absent, the exactly-principal rows z = w^6 would give  E_pr ~ K^{1/6} T  -> numerically measured exponent.

   python3 m1_degenerate.py     (writes logs/m1_degenerate.log)
"""
import math
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor

import numpy as np

import sweep
import toy

HERE = os.path.dirname(os.path.abspath(__file__))
LOG = open(os.path.join(HERE, "logs", "m1_degenerate.log"), "w")


def out(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    LOG.write(s + "\n")
    LOG.flush()


# ---------------------------------------------------------------------------------------------
# (a) conductor statistics of the family
# ---------------------------------------------------------------------------------------------

def _row_stats(args):
    xs, ys = args
    res = np.empty(len(xs), dtype=np.float64)
    for i, (x, y) in enumerate(zip(xs.tolist(), ys.tolist())):
        vals = toy.prime_valuations(x, y)
        q6 = 1.0
        for (p, tag), v in vals.items():
            if v % 6:
                q6 *= p if tag in (0, 1) else float(p * p)
        res[i] = q6
    return res


def all_rows(B):
    xmax = int(2 * math.sqrt(B / 3.0)) + 2
    X, Y = [], []
    for x in range(-xmax, xmax + 1):
        disc = 4.0 * B - 3.0 * x * x
        if disc < 0:
            continue
        sq = math.sqrt(disc)
        lo = math.ceil((x - sq) / 2.0 - 1e-9)
        hi = math.floor((x + sq) / 2.0 + 1e-9)
        for y in range(lo, hi + 1):
            if x * x - x * y + y * y > 0:
                X.append(x)
                Y.append(y)
    return np.array(X, dtype=np.int64), np.array(Y, dtype=np.int64)


def conductor_statistics(Ks):
    out("== (a) conductor statistics of the row family (eta trivial, Q0 = (72)) ==")
    out("   q6(z) = prod of N(P) over primes P not above 2,3 with v_P(z) != 0 mod 6  ( ~ conductor norm of (z/.)_6 away from 2, lambda )")
    out("   rows with q6 = 1 are exactly the rows REMOVED by initialKeep (their primitive character has conductor | 72).")
    out(f"{'K':>9s} {'rows':>9s} {'removed':>8s} {'removed/K^(1/6)':>16s} " + " ".join(f"#(u<={u:.1f})/K^((5u+1)/6)".rjust(21) for u in (0.2, 0.4, 0.6, 0.8)))
    data = {}
    for K in Ks:
        x, y = all_rows(K)
        n = len(x)
        parts = np.array_split(np.arange(n), 8)
        with ProcessPoolExecutor(max_workers=4) as ex:
            res = list(ex.map(_row_stats, [(x[p], y[p]) for p in parts]))
        q6 = np.concatenate(res)
        removed = int((q6 == 1).sum())
        row = f"{K:9.0f} {n:9d} {removed:8d} {removed/K**(1/6):16.3f} "
        for u in (0.2, 0.4, 0.6, 0.8):
            cnt = int((q6 <= K ** u).sum())
            row += f"{cnt / K ** ((5 * u + 1) / 6):21.3f} "
        out(row)
        data[K] = (removed, n)
    ks = sorted(data)
    if len(ks) >= 2:
        sl = np.polyfit(np.log(ks), np.log([data[k][0] for k in ks]), 1)[0]
        out(f"   fitted exponent of #removed rows in K: {sl:.3f}   (prediction 1/6 = 0.167; log-factors from the 2^a lambda^b parts)")
    out("")


# ---------------------------------------------------------------------------------------------
# (b) per-class row energies, in units of the trivial size T
# ---------------------------------------------------------------------------------------------

def cube6(w):
    w2 = toy.mul_eis(w, w)
    w3 = toy.mul_eis(w2, w)
    return toy.mul_eis(w3, w3)


def prime_element(norm_target, which=0):
    """a + b w of norm norm_target (a prime), `which`-th representative"""
    cands = []
    lim = int(2 * math.sqrt(norm_target / 3.0)) + 2
    for a in range(-lim, lim + 1):
        for b in range(-lim, lim + 1):
            if toy.norm_eis(a, b) == norm_target:
                cands.append((a, b))
    return cands[which % len(cands)]


def make_class_rows(cls, K, n, rng):
    """Return list of (x,y) rows with N(z) <= 2K belonging to the class."""
    rows = []
    wmax = max(1, int((2 * K) ** (1 / 12)))  # |w|^12 <= 2K  ->  N(w)=|w|^2 <= (2K)^(1/6)
    pi7 = prime_element(7, 0)
    pi13 = prime_element(13, 0)
    pi19 = prime_element(19, 0)
    pi31 = prime_element(31, 1)
    tries = 0
    while len(rows) < n and tries < 200000:
        tries += 1
        w = (int(rng.integers(-wmax - 1, wmax + 2)), int(rng.integers(-wmax - 1, wmax + 2)))
        if w == (0, 0):
            continue
        if cls == "principal (z=w^6)":
            z = cube6(w)
        elif cls == "2^a lambda^b u w^6, (a,b,u)!=0 [removed, bounded cond | 72]":
            a, b, uu = int(rng.integers(0, 3)), int(rng.integers(0, 3)), int(rng.integers(0, 3))
            if (a, b, uu) == (0, 0, 0):
                continue
            z = cube6(w)
            for _ in range(a):
                z = toy.mul_eis(z, (2, 0))
            for _ in range(b):
                z = toy.mul_eis(z, (1, -1))
            for _ in range(uu):
                z = toy.mul_eis(z, (0, 1))  # multiply by w (the unit omega)
        elif cls == "pi7 w^6 [kept, conductor 7]":
            z = toy.mul_eis(pi7, cube6(w))
        elif cls == "pi7 pi13 w^6 [kept, conductor 91]":
            z = toy.mul_eis(toy.mul_eis(pi7, pi13), cube6(w))
        elif cls == "pi7 pi13 pi19 pi31 w^6 [kept, conductor ~1.6e5 / alive?]":
            z = toy.mul_eis(toy.mul_eis(toy.mul_eis(pi7, pi13), toy.mul_eis(pi19, pi31)), cube6(w))
        elif cls == "cube w^3 [kept, quadratic char, cond N(w)]":
            w2 = toy.mul_eis(w, w)
            z = toy.mul_eis(w2, w)
        elif cls == "square w^2 [kept, cubic char, cond N(w)]":
            z = toy.mul_eis(w, w)
        elif cls == "generic":
            z = (int(rng.integers(-int((2 * K) ** 0.5), int((2 * K) ** 0.5))), int(rng.integers(-int((2 * K) ** 0.5), int((2 * K) ** 0.5))))
        else:
            raise ValueError(cls)
        if 0 < toy.norm_eis(*z) <= 2 * K:
            rows.append(z)
    return rows


CLASSES = [
    "principal (z=w^6)",
    "2^a lambda^b u w^6, (a,b,u)!=0 [removed, bounded cond | 72]",
    "pi7 w^6 [kept, conductor 7]",
    "pi7 pi13 w^6 [kept, conductor 91]",
    "pi7 pi13 pi19 pi31 w^6 [kept, conductor ~1.6e5 / alive?]",
    "cube w^3 [kept, quadratic char, cond N(w)]",
    "square w^2 [kept, cubic char, cond N(w)]",
    "generic",
]


def class_energies(Z, configs, nrows=60, seed=5):
    rng = np.random.default_rng(seed)
    K = Z
    Nmax = sweep.nmax_for(Z, configs)
    PI = toy.build_prime_ideals(Nmax)
    IL = toy.build_ideals(PI, Nmax)
    out(f"   Z = {Z:.0e}, K = Z, ~{nrows} rows per class.  tau = |row|^2 / T with T = X1 X2 prod D_i the TRIVIAL size; a row with a pole has tau ~ 0.04 / (log D)^(2k), a generic row tau ~ 1/T.")
    out("   entries: median / max of tau over the KEPT rows of the class and over the REMOVED rows of the class  (n = number of rows)")
    for d in configs:
        out(f"   --- datum {sweep.config_name(d)}   (T = {(Z ** d.m1) * (Z ** d.m2) * float(np.prod([Z ** w for w in d.slots])):.2e})")
        out(f"   {'class':64s} {'kept: n':>7s} {'median':>10s} {'max':>10s} | {'removed: n':>10s} {'median':>10s} {'max':>10s}")
        for cls in CLASSES:
            rows = make_class_rows(cls, K, nrows, rng)
            if not rows:
                out(f"   {cls:64s}  (no rows generated)")
                continue
            xs = np.array([r[0] for r in rows], dtype=np.int64)
            ys = np.array([r[1] for r in rows], dtype=np.int64)
            ctx = toy.build_context(Z, Nmax, xs, ys, K=Z, PI=PI, IL=IL)
            e = toy.row_energies(ctx, d)
            T = (Z ** d.m1) * (Z ** d.m2) * float(np.prod([Z ** w for w in d.slots]))
            tau = e / T
            kp, rm = ctx.keep, ~ctx.keep
            def st(m):
                return (int(m.sum()), float(np.median(tau[m])) if m.any() else float("nan"), float(np.max(tau[m])) if m.any() else float("nan"))
            a, b = st(kp), st(rm)
            out(f"   {cls:64s} {a[0]:7d} {a[1]:10.2e} {a[2]:10.2e} | {b[0]:10d} {b[1]:10.2e} {b[2]:10.2e}")
    out("")


# ---------------------------------------------------------------------------------------------
# (c) positive control: if the mask were absent
# ---------------------------------------------------------------------------------------------

def removed_rows(K, bound_factor=2):
    """all rows with N(z) <= 2K and q6(z) = 1  (the rows removed by initialKeep for eta = trivial)."""
    B = bound_factor * K
    rows = set()
    wmax = int(B ** (1 / 12)) + 2
    for a in range(0, 12):
        for b in range(0, 12):
            base = (1, 0)
            for _ in range(a):
                base = toy.mul_eis(base, (2, 0))
            for _ in range(b):
                base = toy.mul_eis(base, (1, -1))
            if toy.norm_eis(*base) > B:
                continue
            for u in range(6):
                bu = base
                for _ in range(u):
                    bu = toy.mul_eis(bu, (0, 1))
                for wx in range(-wmax, wmax + 1):
                    for wy in range(-wmax, wmax + 1):
                        if (wx, wy) == (0, 0):
                            continue
                        z = toy.mul_eis(bu, cube6((wx, wy)))
                        if 0 < toy.norm_eis(*z) <= B:
                            rows.add(z)
    return sorted(rows)


def positive_control(Zs, configs):
    out("== (c) positive control: energy carried by the exactly-principal rows (z = w^6), i.e. what the mask removes ==")
    out("   E_pr = sum_{z=w^6, N(z)<=2K} Phi(N(z)/K) |row_z|^2 ;  prediction  E_pr ~ K^{1/6} T  =>  E_pr/K ~ Z^{1/6 + a + s - 1}")
    npr = []
    for Z in Zs:
        rr = [r for r in removed_rows(Z) if toy.norm_eis(*r) <= 2 * Z and _is_w6(r)]
        npr.append(len(rr))
    out("   number of exactly-principal rows z=w^6 with N(z) <= 2K:  " + "  ".join(f"Z={Z:.0e}: {n}" for Z, n in zip(Zs, npr)))
    out(f"   {'config':32s}" + "".join(f"  Z={Z:7.0e}" for Z in Zs) + "   fitted exponent of E_pr/K   predicted 1/6+a+s-1")
    for d in configs:
        vals = []
        for Z in Zs:
            Nmax = sweep.nmax_for(Z, [d])
            rows = [r for r in removed_rows(Z) if toy.norm_eis(*r) <= 2 * Z]
            # restrict to exactly principal rows w^6 (eta trivial): characters (z/.)_6 trivial away from w
            rows = [r for r in rows if _is_w6(r)]
            xs = np.array([r[0] for r in rows], dtype=np.int64)
            ys = np.array([r[1] for r in rows], dtype=np.int64)
            ctx = toy.build_context(Z, Nmax, xs, ys, K=Z, keep=np.ones(len(xs), bool))
            e = toy.row_energies(ctx, d)
            vals.append(float(np.sum(ctx.phi * e)) / Z)
        Zs_ = np.array(Zs, float)
        sl = np.polyfit(np.log(Zs_), np.log(vals), 1)[0] if all(v > 0 for v in vals) else float("nan")
        a = d.m1 + d.m2
        s = sum(d.slots)
        out(f"   {sweep.config_name(d):32s}" + "".join(f"  {v:9.3e}" for v in vals) + f"   {sl:+8.3f}                     {1/6 + a + s - 1:+8.3f}")
    out("")


_PI400 = toy.build_prime_ideals(400)


def _is_w6(r):
    """True iff the row character (z/.)_6 is trivial off the support of z (principal): tested on all primes of norm <= 400."""
    x, y = r
    E = toy.prime_symbols(_PI400, np.array([x]), np.array([y]))[:, 0]
    return bool(np.all((E == 0) | (E == 6)))


def main():
    t0 = time.time()
    out(f"# m1_degenerate  {time.strftime('%Y-%m-%d %H:%M:%S')}")
    conductor_statistics([2e3, 8e3, 3e4, 1e5, 3e5])
    out("== (b) per-class row energies in units of the trivial size T ==")
    class_energies(1e5, [toy.Data(0.5, 0.5), toy.Data(0.75, 0.75), toy.Data(0.5, 0.5, slots=(0.3,))], nrows=80)
    class_energies(1e6, [toy.Data(0.5, 0.5), toy.Data(0.75, 0.75)], nrows=60)
    positive_control([1e4, 3e4, 1e5, 3e5, 1e6, 3e6],
                     [toy.Data(0.4, 0.4), toy.Data(0.5, 0.5), toy.Data(0.6, 0.6), toy.Data(0.7, 0.7), toy.Data(0.75, 0.75),
                      toy.Data(0.5, 0.5, slots=(0.3,)), toy.Data(0.75, 0.75, slots=(0.3,))])
    out(f"# time {time.time()-t0:.0f}s")


if __name__ == "__main__":
    main()
