"""Generic Monte-Carlo / exhaustive evaluator of the toy energy over a list of Z values and data configurations.

mean_row(Z)  = weighted mean of |row_z|^2 over kept rows  (the quantity whose growth in Z is  Z^kappa  ->  E ~ K^{1+kappa})
E(Z)         = K_eff * mean_row   with K_eff = sum_z kept Re Phi(N(z)/K)
The Lean bound says  E <= C diagonalControl(Phi) control^2 (1+|t|+height)^degree Z^{M+eps}  with M = 1 (K = Z),
i.e. it is the statement  mean_row <= C' Z^eps.
"""
from __future__ import annotations

import json
import math
import os
import time
from concurrent.futures import ProcessPoolExecutor

import numpy as np

import toy


def config_name(d: toy.Data) -> str:
    s = f"m=({d.m1:g},{d.m2:g})"
    if d.slots:
        s += " w=(" + ",".join(f"{w:g}" for w in d.slots) + ")"
    if d.t:
        s += f" t={d.t:g}"
    if any(d.v):
        s += " v=(" + ",".join(f"{v:g}" for v in d.v) + ")"
    if d.flat_plain != 0.25 or d.flat_slot != 0.25:
        s += f" flat=({d.flat_plain:g},{d.flat_slot:g})"
    if d.x_scale != (1.0, 1.0):
        s += f" xs=({d.x_scale[0]:g},{d.x_scale[1]:g})"
    return s


def nmax_for(Z: float, configs) -> int:
    best = 10
    for d in configs:
        best = max(best, 2.25 * d.x_scale[0] * Z ** d.m1, 2.25 * d.x_scale[1] * Z ** d.m2)
        for w in d.slots:
            best = max(best, 2.0 * Z ** w)
    return int(best) + 10


def _worker(args):
    (Z, K, rows_x, rows_y, configs, c0, random_model, seed, Nmax, PI, IL, assume_kept) = args
    keep = np.ones(len(rows_x), dtype=bool) if assume_kept else None
    ctx = toy.build_context(Z, Nmax, rows_x, rows_y, K=K, c0=c0, random_model=random_model,
                            rng=np.random.default_rng(seed), PI=PI, IL=IL, keep=keep)
    if random_model:
        ctx.keep[:] = True
    out = []
    for d in configs:
        e = toy.row_energies(ctx, d)
        out.append((e, ctx.phi.copy(), ctx.keep.copy()))
    return out


_PI_IL_CACHE = {}


def run_Z(Z: float, configs, R_total: int, c0=(1, 0), random_model=False, seed=0, max_cells=2.5e8,
          workers=4, M=1.0, verbose=True):
    """Return list of dict (one per config)."""
    K = Z ** M
    B = 2.0 * K  # Phi supported in x <= 2
    Npts = toy.lattice_rows_count(B)
    Nmax = nmax_for(Z, configs)
    key = Nmax
    if key not in _PI_IL_CACHE:
        PI = toy.build_prime_ideals(Nmax)
        IL = toy.build_ideals(PI, Nmax)
        _PI_IL_CACHE.clear()
        _PI_IL_CACHE[key] = (PI, IL)
    PI, IL = _PI_IL_CACHE[key]
    chunk = int(max(200, min(6000, max_cells / max(1, IL.n))))
    exhaustive = Npts <= R_total
    rng = np.random.default_rng(seed + int(Z) % 1000003)
    if exhaustive:
        # enumerate all lattice points 0 < N(z) <= B
        xmax = int(2 * math.sqrt(B / 3.0)) + 2
        xs, ys = [], []
        for x in range(-xmax, xmax + 1):
            disc = 4.0 * B - 3.0 * x * x
            if disc < 0:
                continue
            sq = math.sqrt(disc)
            lo = math.ceil((x - sq) / 2.0 - 1e-9)
            hi = math.floor((x + sq) / 2.0 + 1e-9)
            for y in range(lo, hi + 1):
                if x * x - x * y + y * y > 0:
                    xs.append(x)
                    ys.append(y)
        rx = np.array(xs, dtype=np.int64)
        ry = np.array(ys, dtype=np.int64)
        R_used = len(rx)
    else:
        rx, ry = toy.sample_rows(B, R_total, rng)
        R_used = R_total
    chunks = [(rx[i : i + chunk], ry[i : i + chunk]) for i in range(0, R_used, chunk)]
    t0 = time.time()
    assume_kept = bool(Z > 3e7)  # removed rows have density ~ K^(-5/6): a uniform sample never contains one
    jobs = [(Z, K, cx, cy, configs, c0, random_model, seed + 17 * j, Nmax, PI, IL, assume_kept) for j, (cx, cy) in enumerate(chunks)]
    if workers > 1 and len(jobs) > 1:
        with ProcessPoolExecutor(max_workers=workers) as ex:
            res = list(ex.map(_worker, jobs))
    else:
        res = [_worker(j) for j in jobs]
    results = []
    for ci, d in enumerate(configs):
        e = np.concatenate([r[ci][0] for r in res])
        phi = np.concatenate([r[ci][1] for r in res])
        keep = np.concatenate([r[ci][2] for r in res])
        w = phi * keep
        den = float(w.sum())
        num = float((w * e).sum())
        wmean = num / den if den > 0 else 0.0
        if exhaustive:
            se = 0.0
            Keff = den
        else:
            se = math.sqrt(float(np.sum((w * (e - wmean)) ** 2))) / den if den > 0 else float("nan")
            Keff = Npts * den / len(e)
        live = keep & (phi > 0)
        pools = []
        for w in d.slots:
            Dd = Z ** w
            pools.append(int(np.sum((PI.norm >= Dd) & (PI.norm <= 2 * Dd))))
        results.append({
            "min_pool": (min(pools) if pools else 10 ** 9),
            "config": config_name(d), "Z": Z, "K": K, "R": int(len(e)), "exhaustive": bool(exhaustive),
            "mean_row": wmean, "se_mean_row": se, "Keff": Keff, "E": Keff * wmean,
            "E_over_K": Keff * wmean / K, "max_row": float(e[live].max()) if live.any() else 0.0,
            "kept_fraction": float(keep.mean()),
            "q99_row": float(np.quantile(e[live], 0.99)) if live.any() else 0.0,
        })
    if verbose:
        print(f"  Z={Z:.3g} rows={R_used} (exhaustive={exhaustive}) ideals={IL.n} chunk={chunk} time={time.time()-t0:.1f}s", flush=True)
    return results


def fit_power(Zs, ys, ses, floor_rel=0.005):
    """weighted LS of ln y on ln Z:  y ~ c Z^kappa ;  returns kappa, se(kappa), chi2/dof."""
    Zs = np.asarray(Zs, float)
    ys = np.asarray(ys, float)
    ses = np.asarray(ses, float)
    ok = ys > 0
    if ok.sum() < 3:
        return (float("nan"),) * 3
    x = np.log(Zs[ok])
    yl = np.log(ys[ok])
    sig = np.maximum(ses[ok] / ys[ok], floor_rel)
    wts = 1.0 / sig ** 2
    A = np.vstack([np.ones_like(x), x]).T
    W = np.diag(wts)
    cov = np.linalg.inv(A.T @ W @ A)
    beta = cov @ A.T @ W @ yl
    resid = yl - A @ beta
    chi2 = float(np.sum(wts * resid ** 2))
    dof = max(1, len(x) - 2)
    # inflate errors if chi2/dof > 1
    infl = max(1.0, math.sqrt(chi2 / dof))
    return float(beta[1]), float(math.sqrt(cov[1, 1]) * infl), chi2 / dof


def fit_polylog(Zs, ys, ses, floor_rel=0.005):
    """y ~ c (ln Z)^beta."""
    Zs = np.asarray(Zs, float)
    ys = np.asarray(ys, float)
    ses = np.asarray(ses, float)
    ok = ys > 0
    if ok.sum() < 3:
        return (float("nan"),) * 3
    x = np.log(np.log(Zs[ok]))
    yl = np.log(ys[ok])
    sig = np.maximum(ses[ok] / ys[ok], floor_rel)
    wts = 1.0 / sig ** 2
    A = np.vstack([np.ones_like(x), x]).T
    W = np.diag(wts)
    cov = np.linalg.inv(A.T @ W @ A)
    beta = cov @ A.T @ W @ yl
    resid = yl - A @ beta
    chi2 = float(np.sum(wts * resid ** 2))
    dof = max(1, len(x) - 2)
    infl = max(1.0, math.sqrt(chi2 / dof))
    return float(beta[1]), float(math.sqrt(cov[1, 1]) * infl), chi2 / dof


def sweep(name: str, Zs, configs, R_total=6000, c0=(1, 0), random_model=False, seed=0, workers=4, logdir=None,
          Z_filter=None):
    """Evaluate all configs at each Z.  Z_filter(config, Z) -> bool can skip infeasible (config, Z) pairs."""
    seen = set()
    uniq = []
    for d in configs:  # drop duplicate configurations
        if config_name(d) not in seen:
            seen.add(config_name(d))
            uniq.append(d)
    configs = uniq
    table = {config_name(d): [] for d in configs}
    for Z in Zs:
        cfgs = [d for d in configs if Z_filter is None or Z_filter(d, Z)]
        if not cfgs:
            continue
        res = run_Z(Z, cfgs, R_total, c0=c0, random_model=random_model, seed=seed, workers=workers)
        for r in res:
            table[r["config"]].append(r)
    summary = {}
    for cname, rows in table.items():
        fit_rows = [r for r in rows if r.get("min_pool", 10 ** 9) >= 6]
        if len(fit_rows) < 3:
            summary[cname] = {"rows": rows, "fit_rows": len(fit_rows)}
            continue
        Zs_ = [r["Z"] for r in fit_rows]
        ys = [r["mean_row"] for r in fit_rows]
        ses = [r["se_mean_row"] for r in fit_rows]
        kappa, kse, chi = fit_power(Zs_, ys, ses)
        beta, bse, chib = fit_polylog(Zs_, ys, ses)
        summary[cname] = {"rows": rows, "fit_rows": len(fit_rows), "fit_Zmin": Zs_[0], "fit_Zmax": Zs_[-1],
                          "kappa": kappa, "kappa_se": kse, "kappa_chi2dof": chi,
                          "polylog_beta": beta, "polylog_beta_se": bse, "polylog_chi2dof": chib}
    if logdir:
        with open(os.path.join(logdir, f"{name}.json"), "w") as f:
            json.dump(summary, f, indent=1)
    return summary


def print_summary(summary, out=print):
    out(f"{'config':44s} {'fit Z range':>16s} {'mean_row(first)':>15s} {'mean_row(last)':>14s} {'kappa':>14s} {'chi2/dof':>8s} {'polylog beta':>14s}")
    for cname, s in summary.items():
        rows = [r for r in s["rows"] if r.get("min_pool", 10 ** 9) >= 6]
        if not rows:
            continue
        zr = f"{rows[0]['Z']:.0e}-{rows[-1]['Z']:.0e}"
        if "kappa" in s:
            out(f"{cname:44s} {zr:>16s} {rows[0]['mean_row']:15.4f} {rows[-1]['mean_row']:14.4f} "
                f"{s['kappa']:+7.3f}+-{s['kappa_se']:.3f} {s['kappa_chi2dof']:8.2f} {s['polylog_beta']:+7.2f}+-{s['polylog_beta_se']:.2f}")
        else:
            out(f"{cname:44s} {zr:>16s} {rows[0]['mean_row']:15.4f} {rows[-1]['mean_row']:14.4f}   (fewer than 3 usable Z values)")
