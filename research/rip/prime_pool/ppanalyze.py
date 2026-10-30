"""ppanalyze.py -- tables, growth exponents, breaks and Lambda estimates from results/*.json.

    python3 -I ppanalyze.py            (writes results/results_tables.md, prints the summary)

Definitions used throughout (see README.md):
  F/D      = F / (R sum_m |c_m|^2)                         (the task's ratio, includes the zero-forced rows)
  F/Dcop   = F / (R sum_m |c_m|^2 rho_m)                    (diagonal corrected for rows sharing a prime ideal with m: the exact
                                                             expectation of F for independent sextic characters) -- the ratio that
                                                             should be 1.00 if nothing arithmetic happens.
  e(m,s)   = d ln(F/Dcop)/d ln B    (growth exponent at fixed exponents (m,s); weighted LS over B >= 5e4)
  face model: ln(F/Dcop)/ln B = kappa max(0, 2m + Lambda s - 1).
"""
import os, sys, json, glob, math
import numpy as np
from scipy.optimize import least_squares

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, 'results')
OUT = []
def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s); OUT.append(s)


def load_grids():
    G = {}
    for f in sorted(glob.glob(os.path.join(RES, 'grid_*.json'))):
        d = json.load(open(f)); G[d['B']] = d
    return G


def table_entries(d, kind):
    out = {}
    for e in d['entries']:
        if e['kind'] == kind and e['s'] is not None:
            out[(round(e['m'], 4), round(e['s'], 4))] = e
    return out


def base_entries(d, kind):
    return {round(e['m'], 4): e for e in d['entries'] if e['kind'] == kind and e['s'] is None}


def rand_idx(d):
    return [i for i, v in enumerate(d['varnames']) if v.startswith('rand')]


def vals(e, d):
    """dict name -> (F/Dcop, F/D, se_rel)."""
    vn = d['varnames']
    F = np.array(e['F']); D = np.array(e['D']); Dc = np.array(e['Dcop']); SE = np.array(e['SE'])
    out = {v: (F[i] / Dc[i], F[i] / D[i], SE[i] / F[i]) for i, v in enumerate(vn)}
    ri = rand_idx(d)
    out['rand'] = (float(np.mean(F[ri] / Dc[ri])), float(np.mean(F[ri] / D[ri])), float(np.std(F[ri] / Dc[ri])))   # mean, mean raw, sd across seeds
    out['ctrl'] = (e['Fc'] / e['Dccop'], e['Fc'] / e['Dc'], e['SEc'] / e['Fc'])
    return out


# --------------------------------------------------------------------------------------------- tables
def table_task_grid(G, Bs, kind, minpool=5):
    P('')
    for B in Bs:
        if B not in G: continue
        d = G[B]; E = table_entries(d, kind); bs = base_entries(d, kind)
        P('#### B = %d, W = %s   (R = %d rows, log_B R = %.3f)' % (B, kind, d['R'], d['logB_R']))
        P('')
        P('| m | s | n pool | T=2m+s | F/D (a=1) | F/Dcop a=1 | F/Dcop rand (mean +- sd, 8 seeds) | t=5 | t=20 | gauss simple | gauss canon | control (plain X3) | row-SE of F (a=1) |')
        P('|---|---|---|---|---|---|---|---|---|---|---|---|---|')
        for m in sorted(bs):
            b = bs[m]
            P('| %.2f | (X alone) | - | %.2f | %.3f | %.3f | | | | | | | %.1f%% |' % (m, 2 * m, b['F0'] / b['D0'], b['F0'] / b['D0cop'], 100 * b['SE0'] / b['F0']))
            for (mm, s) in sorted(E):
                if mm != m: continue
                e = E[(mm, s)]
                if e['npool'] < minpool: continue
                v = vals(e, d)
                P('| %.2f | %.2f | %d | %.2f | %.3f | %.3f | %.3f +- %.3f | %.3f | %.3f | %.3f | %.3f | %.3f | %.1f%% |' % (
                    m, s, e['npool'], e['T'], v['ones'][1], v['ones'][0], v['rand'][0], v['rand'][2], v['t5'][0], v['t20'][0],
                    v['gauss_simple'][0], v['gauss_canon'][0], v['ctrl'][0], 100 * v['ones'][2]))
        P('')


def table_wide(G, Bs, kind, variants=('ones', 'rand', 'gauss_canon', 'ctrl'), minpool=5):
    P('')
    P('F/Dcop (row-SE in percent) for W = %s; columns are B. Only pools with >= %d prime ideals.' % (kind, minpool))
    P('')
    hdr = '| m | s | variant | ' + ' | '.join('%g' % B for B in Bs) + ' |'
    P(hdr); P('|' + '---|' * (3 + len(Bs)))
    keys = set()
    for B in Bs:
        if B in G: keys |= set(table_entries(G[B], kind))
    for (m, s) in sorted(keys):
        for var in variants:
            cells = []
            ok = False
            for B in Bs:
                e = table_entries(G[B], kind).get((m, s)) if B in G else None
                if e is None or e['npool'] < minpool: cells.append(''); continue
                v = vals(e, G[B]); ok = True
                if var == 'rand': cells.append('%.3f (%.1f, sd %.1f)' % (v['rand'][0], 100 * v['ones'][2], 100 * v['rand'][2]))
                else: cells.append('%.3f (%.1f)' % (v[var][0], 100 * v[var][2]))
            if ok: P('| %.2f | %.2f | %s | %s |' % (m, s, var, ' | '.join(cells)))
    P('')


# --------------------------------------------------------------------------------------------- growth exponents
def wls_slope(x, y, sy):
    """weighted LS slope of y on x with errors sy; error inflated by sqrt(chi2_red) if > 1."""
    w = 1 / np.maximum(sy, 1e-9) ** 2
    X = np.stack([np.ones_like(x), x], 1)
    A = X.T @ (X * w[:, None]); b = X.T @ (w * y)
    cov = np.linalg.inv(A); beta = cov @ b
    res = y - X @ beta
    dof = max(1, len(x) - 2)
    chi2 = float(np.sum(w * res ** 2)) / dof
    return beta[1], math.sqrt(cov[1, 1] * max(1.0, chi2)), chi2


def growth_exponents(G, kind='smooth', Bmin=50000, minpool=5, variants=('ones', 'rand', 't5', 't20', 'gauss_simple', 'gauss_canon', 'ctrl')):
    Bs = [B for B in sorted(G) if B >= Bmin]
    keys = set()
    for B in Bs: keys |= set(table_entries(G[B], kind))
    res = {}
    for (m, s) in sorted(keys):
        for var in variants:
            xs, ys, sy = [], [], []
            for B in Bs:
                e = table_entries(G[B], kind).get((m, s))
                if e is None or e['npool'] < minpool: continue
                v = vals(e, G[B])
                r, _, se = v[var]
                if var == 'rand':
                    se = max(v['ones'][2], v['rand'][2])      # seed-to-seed spread / row SE, whichever is larger
                xs.append(math.log(B)); ys.append(math.log(r)); sy.append(se)
            if len(xs) >= 3:
                res[(m, s, var)] = wls_slope(np.array(xs), np.array(ys), np.array(sy)) + (len(xs),)
    return res


def table_growth(res, variants):
    P('')
    P('| m | s | T | ' + ' | '.join('e (%s)' % v for v in variants) + ' | #B |')
    P('|' + '---|' * (4 + len(variants)))
    keys = sorted({(m, s) for (m, s, v) in res})
    for (m, s) in keys:
        cells = []
        nB = 0
        for v in variants:
            r = res.get((m, s, v))
            if r is None: cells.append('')
            else: cells.append('%+.4f +- %.4f' % (r[0], r[1])); nB = r[3]
        P('| %.2f | %.2f | %.2f | %s | %d |' % (m, s, 2 * m + s, ' | '.join(cells), nB))
    P('')


# --------------------------------------------------------------------------------------------- breaks, Lambda
def s_break(svals, rvals, tau):
    """first s where r crosses tau (log-linear interpolation in s); None if never."""
    s = np.asarray(svals); r = np.asarray(rvals)
    for i in range(len(s)):
        if r[i] >= tau:
            if i == 0: return float(s[0])
            t = (math.log(tau) - math.log(r[i - 1])) / (math.log(r[i]) - math.log(r[i - 1]))
            return float(s[i - 1] + t * (s[i] - s[i - 1]))
    return None


def fit_kappa_lambda(pts, B, bounds=((0.0, 0.2), (3.0, 5.0))):
    """pts: list of (m, s, ratio).  y = ln ratio / ln B ~ kappa max(0, 2m + Lambda s - 1)."""
    m = np.array([p[0] for p in pts]); s = np.array([p[1] for p in pts]); y = np.log([p[2] for p in pts]) / math.log(B)
    f = lambda th: th[0] * np.maximum(0, 2 * m + th[1] * s - 1) - y
    best = None
    for k0 in (0.3, 1.0):
        for l0 in (0.8, 1.5, 2.5):
            r = least_squares(f, [k0, l0], bounds=bounds)
            if best is None or r.cost < best.cost: best = r
    return best.x, best.cost


def load_adv():
    A = {}
    for f in sorted(glob.glob(os.path.join(RES, 'adv_*.json'))):
        d = json.load(open(f)); A[d['B']] = d
    return A


def adv_tables(A):
    P('')
    P('### Adversarial / extended-s probe (ppadv.py): sup over weights of F/Dcop')
    P('')
    P('sup_uni = best unimodular pool weights found (lower bound of the unimodular sup); sup_L2 = sup over ALL complex weights (generalised top eigenvalue;')
    P('upper bound for every weight class); MP = (1+sqrt(n/Reff))^2 with Reff the participation ratio of |X|^4 over the rows.')
    P('')
    for B in sorted(A):
        d = A[B]
        P('#### B = %d (R = %d)' % (B, d['R']))
        P('')
        P('| W | m | s | n pool | T | Reff/R | ones | rand (mean of seeds) | t=5 | t=20 | gauss simple | gauss canon | sup_uni | sup_L2 | MP guess |')
        P('|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|')
        for e in d['entries']:
            v = e['var']; rm = np.mean([x for k, x in v.items() if k.startswith('rand')])
            se = e.get('var_se', {})
            P('| %s | %.2f | %.2f | %d | %.2f | %.2f | %.3f | %.3f | %.3f | %.3f | %.3f | %.3f | %.3f | %.3f | %.3f |' % (
                e['kind'], e['m'], e['s'], e['n'], e['T'], e['Reff'] / d['R'], v['ones'], rm, v['t5'], v['t20'], v['gauss_simple'], v['gauss_canon'],
                e['sup_uni'], e['sup_l2'], e['mp_guess']))
        P('')


def adv_breaks(A, taus=(1.5, 2.0, 3.0), key='sup_uni'):
    """per B, per (kind, m): s where the sup first reaches tau, and Lambda_adv = (1-2m)/s_break."""
    out = {}
    for B in sorted(A):
        d = A[B]
        groups = {}
        for e in d['entries']:
            groups.setdefault((e['kind'], e['m']), []).append(e)
        for (k, m), es in groups.items():
            es.sort(key=lambda e: e['s'])
            ss = [e['s'] for e in es]; rr = [e[key] for e in es]
            for tau in taus:
                sb = s_break(ss, rr, tau)
                out[(B, k, m, tau)] = (sb, None if sb is None else (1 - 2 * m) / sb, ss[0], ss[-1])
    return out


def pava(y):
    """isotonic (non-decreasing) least-squares fit, equal weights."""
    vals, cnt = [], []
    for v in y:
        vals.append(float(v)); cnt.append(1)
        while len(vals) > 1 and vals[-2] > vals[-1]:
            c = cnt[-2] + cnt[-1]; v2 = (vals[-2] * cnt[-2] + vals[-1] * cnt[-1]) / c
            vals[-2:] = [v2]; cnt[-2:] = [c]
    out = []
    for v, c in zip(vals, cnt): out += [v] * c
    return np.array(out)


def load_qalone():
    """merge all qalone_*.json by B: dict B -> list of (s, n, P2B, {name: (ratio, se)})."""
    Q = {}
    for f in sorted(glob.glob(os.path.join(RES, 'qalone_*.json'))):
        d = json.load(open(f))
        for e in d['entries']:
            nm = e['names']
            rec = {k: (e['ratio'][i], e['se'][i]) for i, k in enumerate(nm)}
            rec['rand'] = (float(np.mean([e['ratio'][i] for i, k in enumerate(nm) if k.startswith('rand')])), float(np.std([e['ratio'][i] for i, k in enumerate(nm) if k.startswith('rand')])))
            Q.setdefault(d['B'], {})[round(e['s'], 4)] = (e['n'], e['P2B'], rec, d['R'])
    return Q


def qalone_tables(Q):
    P('')
    P('## 7. The pool alone (X = 1, m = 0): F/(R n) = sum_z |Q(z)|^2/(R sum|a_P|^2), ppqalone.py')
    P('')
    P('Null expectation 1 (up to the coprimality correction of a few per mille for P0 >~ 100).  gsimple/gcanon: a_P = conj g~(P) with additive character e(x/p) resp. e(-b x/p);')
    P('gsimple_c/gcanon_c: the non-conjugated Gauss sums; ang1/ang-1: angular characters (P/|P|)^{+-1}.  SE = row-sampling error (about the same for every column).')
    P('')
    P('| B | R | s | n | P0^2/B | ones | rand (mean of 4) | t=5 | t=20 | gsimple | gcanon | gsimple_c | gcanon_c | ang1 | ang-1 | SE |')
    P('|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|')
    for B in sorted(Q):
        for s in sorted(Q[B]):
            n, p2b, rec, R = Q[B][s]
            P('| %d | %d | %.3f | %d | %.2f | %.3f | %.3f | %.3f | %.3f | %.3f | %.3f | %.3f | %.3f | %.3f | %.3f | %.3f |' % (
                B, R, s, n, p2b, rec['ones'][0], rec['rand'][0], rec['t5'][0], rec['t20'][0], rec['gsimple'][0], rec['gcanon'][0],
                rec['gsimple_c'][0], rec['gcanon_c'][0], rec['ang1'][0], rec['ang-1'][0], rec['ones'][1]))
    P('')


def onset_analysis(Q, names=('gsimple', 'gcanon'), taus=(0.02, 0.04), nboot=300):
    """per B: s* where the isotonic fit of F/(R n) crosses 1+tau; Lambda_onset = 1/s* (m = 0)."""
    rng = np.random.default_rng(3)
    out = {}
    P('')
    P('### Onset of the Gauss-aligned excess for the pool alone: s*(tau) = first s with isotonic-fit F/(R n) >= 1 + tau;  Lambda_onset = 1/s*  (m = 0)')
    P('')
    P('Parametric bootstrap (300 draws of the row-SE noise) for the error of s*.  Only the s-range scanned (0.45-0.85) can show a crossing; ">" means no crossing.')
    P('')
    P('| B | log10(P0^2/B) at s* (tau=2%) | variant | s*(2%) | Lambda_onset(2%) | s*(4%) | Lambda_onset(4%) | plateau (mean of ratios with P0^2/B > 100) |')
    P('|---|---|---|---|---|---|---|---|')
    for B in sorted(Q):
        ss = sorted(Q[B])
        if len(ss) < 6: continue
        for nm in names:
            y = np.array([Q[B][s][2][nm][0] for s in ss]); se = np.array([Q[B][s][2][nm][1] for s in ss])
            p2b = np.array([Q[B][s][1] for s in ss])
            cells = []; xs = None
            for tau in taus:
                def cross(yy):
                    f = pava(yy)
                    for i in range(len(ss)):
                        if f[i] >= 1 + tau:
                            if i == 0: return ss[0]
                            t = (1 + tau - f[i - 1]) / (f[i] - f[i - 1])
                            return ss[i - 1] + t * (ss[i] - ss[i - 1])
                    return None
                s0 = cross(y)
                bs = [cross(y + rng.normal(0, se)) for _ in range(nboot)]
                okb = [b for b in bs if b is not None]
                if s0 is None:
                    cells += ['>%.2f' % ss[-1], '']
                else:
                    sd = float(np.std(okb)) if len(okb) > 5 else float('nan')
                    cells += ['%.3f +- %.3f' % (s0, sd), '%.2f +- %.2f' % (1 / s0, sd / s0 ** 2)]
                    if tau == taus[0]: xs = math.log10(B ** (2 * s0 - 1))
                    out[(B, nm, tau)] = (s0, sd)
            hi = [y[i] for i in range(len(ss)) if p2b[i] > 100]
            P('| %d | %s | %s | %s | %s | %s | %s | %s |' % (B, '' if xs is None else '%.2f' % xs, nm, cells[0], cells[1], cells[2], cells[3], '%.3f' % np.mean(hi) if hi else ''))
    P('')
    return out


def gauss_vs_m(A):
    P('')
    P('### Gauss-aligned excess with plain factors present: F/Dcop (gauss simple | gauss canon | rand mean) vs m, at the same s  (ppadv.py, W = smooth for m > 0)')
    P('')
    for B in sorted(A):
        if B < 30000: continue
        d = A[B]
        P('B = %d (R = %d)' % (B, d['R']))
        P('')
        ms_ = sorted({e['m'] for e in d['entries']})
        P('| s | n | ' + ' | '.join('m=%.2f' % m for m in ms_) + ' |')
        P('|---|---|' + '---|' * len(ms_))
        for s_ in sorted({e['s'] for e in d['entries']}):
            es = {e['m']: e for e in d['entries'] if e['s'] == s_}
            cells = []
            for m in ms_:
                e = es.get(m)
                if e is None: cells.append(''); continue
                v = e['var']; se = e['var_se']; rm = np.mean([x for k, x in v.items() if k.startswith('rand')])
                cells.append('%.3f (%.3f) / %.3f / %.3f' % (v['gauss_simple'], se['gauss_simple'], v['gauss_canon'], rm))
            n = next(iter(es.values()))['n']
            P('| %.2f | %d | %s |' % (s_, n, ' | '.join(cells)))
        P('')


def main():
    G = load_grids()
    A = load_adv()
    task_Bs = [3000, 6000, 12000, 20000]
    ext_Bs = [B for B in sorted(G) if B >= 50000]
    P('# Results tables (generated by ppanalyze.py)')
    P('')
    P('Grids found: B = ' + ', '.join(str(B) for B in sorted(G)))
    P('')
    P('## 1. Required grid, B in {3000, 6000, 12000, 20000}')
    P('')
    P('Rows: squarefree z, N(z) in [B,2B], (z,6)=1.  m1=m2=m.  Pool: split primary primes with P0 < N(P) <= 2 P0, P0 = B^s, a_P as named.')
    P('Only pools with >= 5 prime ideals are listed (both conjugate primes of a split rational prime count).  "X alone" rows: the plain fourth moment sum|X|^4 / diagonal.')
    for kind in ('smooth', 'plain'):
        P('')
        P('### W = %s' % kind)
        table_task_grid(G, task_Bs, kind)
    P('')
    P('## 2. Extended B (same definitions), W = smooth')
    table_wide(G, ext_Bs, 'smooth')
    P('')
    P('### W = plain (sharp cutoff)')
    table_wide(G, ext_Bs, 'plain', variants=('ones', 'rand', 'gauss_canon'))
    P('')
    P('## 3. Growth exponents e(m,s) = d ln(F/Dcop)/d ln B  (weighted LS over B >= 5e4, pools with >= 5 ideals; error inflated by sqrt(chi2_red) if > 1)')
    variants = ('ones', 'rand', 't5', 't20', 'gauss_simple', 'gauss_canon', 'ctrl')
    ge = growth_exponents(G, 'smooth', variants=variants)
    table_growth(ge, variants)
    # summary of exponents by T bin
    P('Summary: weighted mean of e over the points of each T-bin (points share rows, so the quoted error is the scatter-based one, not independent):')
    P('')
    P('| variant | T in [0.6,0.9) | T in [0.9,1.05) | T in [1.05,1.3) |')
    P('|---|---|---|---|')
    for v in variants:
        cells = []
        for lo, hi in ((0.6, 0.9), (0.9, 1.05), (1.05, 1.3)):
            es = [(r[0], r[1]) for (m, s, vv), r in ge.items() if vv == v and lo <= 2 * m + s < hi]
            if not es: cells.append(''); continue
            e = np.array([x[0] for x in es]); sg = np.array([x[1] for x in es])
            w = 1 / sg ** 2
            mean = float(np.sum(w * e) / np.sum(w)); sd = float(np.std(e)) if len(e) > 1 else 0.0
            cells.append('%+.4f (formal +- %.4f, spread %.4f, %d pts)' % (mean, 1 / math.sqrt(np.sum(w)), sd, len(e)))
        P('| %s | %s |' % (v, ' | '.join(cells)))
    P('')
    # face-model limits on Lambda from exponents
    P('### Face-model limits on Lambda from the exponents: e <= kappa max(0, 2m + Lambda s - 1)  =>  Lambda <= (1 - 2m + e_up/kappa)/s')
    P('')
    P('e_up = e + 2 sigma at the grid point (variant: pooled over ones/rand/t5/t20/gauss_canon; the largest e_up per (m,s)).  kappa = 1 and 1/3 (a Heath-Brown-type exponent).')
    P('')
    P('| m | best (smallest) bound over s: Lambda_max(kappa=1) | at s | Lambda_max(kappa=1/3) | at s |')
    P('|---|---|---|---|---|')
    for m in sorted({m for (m, s, v) in ge}):
        best = {1.0: (9e9, None), 1 / 3: (9e9, None)}
        for (mm, s, v), r in ge.items():
            if mm != m or v not in ('ones', 'rand', 't5', 't20', 'gauss_canon', 'gauss_simple'): continue
            pass
        # per (m,s): max e_up over variants
        sset = sorted({s for (mm, s, v) in ge if mm == m})
        for s in sset:
            eup = max(r[0] + 2 * r[1] for (mm, ss_, v), r in ge.items() if mm == m and ss_ == s and v in ('ones', 'rand', 't5', 't20', 'gauss_simple', 'gauss_canon'))
            eup = max(eup, 0.0)
            for kap in best:
                lam = (1 - 2 * m + eup / kap) / s
                if lam < best[kap][0]: best[kap] = (lam, s)
        P('| %.2f | %.2f | %.2f | %.2f | %.2f |' % (m, best[1.0][0], best[1.0][1], best[1 / 3][0], best[1 / 3][1]))
    P('')
    # signed kappa-Lambda fit of the grid data themselves
    P('### Fit of the grid data to ln(F/Dcop)/ln B = kappa max(0, 2m + Lambda s - 1)  (kappa of either sign)')
    P('')
    P('All points (m, s, B) with B >= 1e6 and pool >= 5 ideals (W = smooth); weights 1/sigma^2 with sigma = rowSE/ln B; 300 bootstrap resamples of the points.')
    P('A variant whose kappa is consistent with 0 carries no information on Lambda (Lambda is then unconstrained: listed as the best-fit value with its spread).')
    P('')
    P('| variant | kappa | Lambda | #points | kappa=0 chi2/dof | best chi2/dof |')
    P('|---|---|---|---|---|---|')
    rng = np.random.default_rng(7)
    def signed_fit(pts):
        m = np.array([p[0] for p in pts]); s_ = np.array([p[1] for p in pts]); y = np.array([p[2] for p in pts]); sg = np.array([p[3] for p in pts])
        f = lambda th: (th[0] * np.maximum(0, 2 * m + th[1] * s_ - 1) - y) / sg
        best = None
        for k0 in (-0.01, 0.01):
            for l0 in (0.8, 1.2, 2.0):
                r = least_squares(f, [k0, l0], bounds=([-1.0, 0.2], [1.0, 4.0]))
                if best is None or r.cost < best.cost: best = r
        return best.x, 2 * best.cost / max(1, len(pts) - 2), float(np.sum((y / sg) ** 2)) / max(1, len(pts))
    for var in ('ones', 'rand', 't5', 't20', 'gauss_simple', 'gauss_canon', 'ctrl'):
        pts = []
        for B in sorted(G):
            if B < 1000000: continue
            d = G[B]
            for (m, s_), e in table_entries(d, 'smooth').items():
                if e['npool'] < 5: continue
                v = vals(e, d); r, _, se = v[var]
                if var == 'rand': se = max(v['ones'][2], v['rand'][2])
                pts.append((m, s_, math.log(r) / math.log(B), max(se, 1e-4) / math.log(B)))
        if len(pts) < 8: continue
        th, c2, c20 = signed_fit(pts)
        bs = []
        for _ in range(300):
            idx = rng.integers(0, len(pts), len(pts))
            try: bs.append(signed_fit([pts[i] for i in idx])[0])
            except Exception: pass
        bs = np.array(bs)
        P('| %s | %+.4f +- %.4f | %.2f +- %.2f | %d | %.2f | %.2f |' % (var, th[0], bs[:, 0].std(), th[1], bs[:, 1].std(), len(pts), c20, c2))
    P('')
    # max deviations per B
    P('## 4. Largest deviation of F/Dcop from 1 on the required grid and extended B (pools >= 5 ideals, W = smooth)')
    P('')
    P('| B | R | log_B R | max T reached | max F/Dcop (a=1) | min F/Dcop (a=1) | max F/Dcop (gauss canon) | max F/Dcop (rand mean) | max ctrl | typical row-SE |')
    P('|---|---|---|---|---|---|---|---|---|---|')
    for B in sorted(G):
        d = G[B]; E = table_entries(d, 'smooth')
        rr = [(vals(e, d), e) for e in E.values() if e['npool'] >= 5]
        if not rr: continue
        P('| %d | %d | %.3f | %.2f | %.3f | %.3f | %.3f | %.3f | %.3f | %.1f%% |' % (
            B, d['R'], d['logB_R'], max(e['T'] for v, e in rr), max(v['ones'][0] for v, e in rr), min(v['ones'][0] for v, e in rr),
            max(v['gauss_canon'][0] for v, e in rr), max(v['rand'][0] for v, e in rr), max(v['ctrl'][0] for v, e in rr),
            100 * float(np.median([v['ones'][2] for v, e in rr]))))
    P('')
    # empirical Lambda from structured variants: no break -> upper bounds
    P('## 5. Empirical Lambda = (1 - 2m)/s_break for the structured weight variants')
    P('')
    P('s_break(tau) = first s at which F/Dcop >= tau.  For the structured variants no break occurs up to s = 0.45, so only the one-sided bound')
    P('Lambda_emp < (1 - 2m)/0.45 is available from the required window (listed below); B = 4e6 and 1e7 have row-SE <= 1%.')
    P('')
    P('| m | (1-2m)/0.45 | max F/Dcop over s (B=4e6; ones / rand / gauss canon / ctrl) | max F/Dcop over s (B=1e7; same) |')
    P('|---|---|---|---|')
    for m in (0.25, 0.3, 0.35, 0.4):
        cells = []
        for B in (4000000, 10000000):
            if B not in G: cells.append(''); continue
            d = G[B]; E = table_entries(d, 'smooth')
            vv = [vals(e, d) for (mm, s), e in E.items() if mm == m and e['npool'] >= 5]
            cells.append('%.3f / %.3f / %.3f / %.3f' % (max(v['ones'][0] for v in vv), max(v['rand'][0] for v in vv), max(v['gauss_canon'][0] for v in vv), max(v['ctrl'][0] for v in vv)))
        P('| %.2f | %.2f | %s |' % (m, (1 - 2 * m) / 0.45, ' | '.join(cells)))
    P('')
    if A:
        adv_tables(A)
        P('## 6. Breaks of the worst-case weights: s_break(tau) and Lambda_adv = (1-2m)/s_break')
        P('')
        for key in ('sup_uni', 'sup_l2'):
            P('### %s' % key)
            P('')
            P('| B | W | m | tau=1.5: s_break (Lambda) | tau=2: s_break (Lambda) | tau=3: s_break (Lambda) | s-range scanned |')
            P('|---|---|---|---|---|---|---|')
            br = adv_breaks(A, key=key)
            for B in sorted(A):
                for (k, m) in sorted({(kk, mm) for (BB, kk, mm, t) in br if BB == B}):
                    cells = []
                    for tau in (1.5, 2.0, 3.0):
                        sb, lam, s0, s1 = br[(B, k, m, tau)]
                        cells.append('>%.2f (Lambda <%.2f)' % (s1, (1 - 2 * m) / s1) if sb is None else '%.3f (%.2f)' % (sb, lam))
                    P('| %d | %s | %.2f | %s | %.2f-%.2f |' % (B, k, m, ' | '.join(cells), s0, s1))
            P('')
        P('### Alternative fit  ln(sup)/ln B = kappa max(0, 2m + Lambda s - 1)  per B (all (m,s) points of the adversarial scan; bootstrap over points, 200 resamples)')
        P('')
        P('| B | key | kappa | Lambda | cost (sum sq. resid of ln/lnB) |')
        P('|---|---|---|---|---|')
        rng = np.random.default_rng(1)
        for B in sorted(A):
            for key in ('sup_uni', 'sup_l2'):
                pts = [(e['m'], e['s'], max(e[key], 1.0)) for e in A[B]['entries']]
                if len(pts) < 6: continue
                th, cost = fit_kappa_lambda(pts, B)
                bs = []
                for _ in range(200):
                    idx = rng.integers(0, len(pts), len(pts))
                    try: bs.append(fit_kappa_lambda([pts[i] for i in idx], B)[0])
                    except Exception: pass
                bs = np.array(bs)
                P('| %d | %s | %.2f +- %.2f | %.2f +- %.2f | %.2e |' % (B, key, th[0], bs[:, 0].std(), th[1], bs[:, 1].std(), cost))
        P('')
    Q = load_qalone()
    if Q:
        qalone_tables(Q)
        onset_analysis(Q)
    if A:
        gauss_vs_m(A)
    with open(os.path.join(RES, 'results_tables.md'), 'w') as f:
        f.write('\n'.join(OUT) + '\n')


if __name__ == '__main__':
    main()
