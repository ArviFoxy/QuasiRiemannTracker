"""Exact-return price (T-A toolchain `ta/exact.py`: six branches, box ell < 0.18, Lemma-W windows) of a doubled chain,
with and without the RETURN-SIDE carrying cost of the doubled slots.

Carrying cost model [derivation in the report]: an energy to which chain face k is applied must contain the doubled
volume X_k consumed by steps 0..k (each step transfers its doubled units out of the object; the residual is handed to
the parent face).  In the return these slots have no zero-correlated amplitude (Q2(chi_u) = Q(chi_u^2) is not saturated
by a zero of L(s, eta psi_u-bar)), so they only use face budget:
    count face:     2m + Lam_C (z + lam X_C) <= B_C    ->  B_C' = B_C - lam Lam_C X_C
    physical face:  X1 + X2 + Lam_P (sum w + lam X_P) <= B_P  ->  B_P' = B_P - lam Lam_P X_P
lam = 1 (slot counted by prime size / volume, R2's r = 1) or 2 (counted by norm, R3's multiplicity reading).
X_k: capacity model  X_k = (k+1) UD;  share model  X_k = phi * sum_{j<=k} u_j(vmax_j)  (R2's accounting, sum u at vmax).
usage: python3 price.py chain.json MODE PAR LAM [physical_source.json]
"""
import sys, os, json
TA = '/home/user/QuasiRiemannTracker/research/newpowers/ta'
sys.path.insert(0, TA)
import exact  # noqa: E402

RECORD = 0.87387234


def load(fn):
    return [r for r in json.load(open(fn)) if not r.get('infeasible')]


def dvol(rows, mode, par):
    X, tot = [], 0.0
    for r in rows:
        if mode == 'cap':
            tot += par
        elif mode == 'share':
            vmax = 0.1 - r['s0']
            tot += par * r['A'] * vmax / (1 + r['D'] * vmax)
        X.append(tot)
    return X


def faces(rows, X, lam):
    return [(r['L'], r['B'] - lam * r['L'] * x, r['s0']) for r, x in zip(rows, X)]


def th(fc, fp, unit=10**8, guess=0.87387):
    r = exact.theta_exact(fc[1], fc[0], fp[1], fp[0], guess=guess, unit=unit, span=300 if unit == 10**8 else 400)
    return None if r is None else r[0]


def search(FC, FP, verbose=False):
    n = len(FC)
    cc = sorted(set(list(range(max(0, n - 16), n)) + list(range(max(0, n - 70), n, 4))))
    pc = [i for i, f in enumerate(FP) if 2.15 <= f[0] <= 2.40][::2]
    P0 = min(pc, key=lambda i: abs(FP[i][0] - 2.25))
    best = None
    for i in cc:
        t = th(FC[i], FP[P0])
        if t is not None and (best is None or t < best[0]):
            best = (t, i)
    iC = best[1]
    bestP = None
    for j in pc:
        t = th(FC[iC], FP[j])
        if t is not None and (bestP is None or t < bestP[0]):
            bestP = (t, j)
    iP = bestP[1]
    fin = None
    for a in range(iC - 3, iC + 4):
        for b in range(iP - 3, iP + 4):
            if 0 <= a < n and 0 <= b < len(FP) and abs(a - iC) + abs(b - iP) <= 3:
                t = th(FC[a], FP[b], unit=10**9, guess=bestP[0])
                if t is not None and (fin is None or t < fin[0]):
                    fin = (t, a, b)
    return fin


def main():
    fn, mode, par, lam = sys.argv[1], sys.argv[2], float(sys.argv[3]), float(sys.argv[4])
    rows = load(fn)
    X = dvol(rows, mode, par)
    FC = faces(rows, X, lam)
    if len(sys.argv) > 5:                       # physical face from another (cost-free) chain
        prow = load(sys.argv[5])
        FP = faces(prow, [0.0] * len(prow), 0.0)
        ptag = 'P=' + os.path.basename(sys.argv[5])
    else:
        FP = FC
        ptag = 'P=same'
    t, a, b = search(FC, FP)
    print('%s %s %g lam=%g %s: theta=%.9f (vs record %+.2e) | C step %d L=%.4f B=%.6f X_C=%.2e | P step %d L=%.4f B=%.6f X_P=%.2e | steps %d, end L=%.4f, X_end=%.2e'
          % (os.path.basename(fn), mode, par, lam, ptag, t, t - RECORD, a, FC[a][0], FC[a][1], X[a], b, FP[b][0], FP[b][1],
             (X[b] if FP is FC else 0.0), len(rows), rows[-1]['L'], X[-1]), flush=True)


if __name__ == '__main__':
    main()
