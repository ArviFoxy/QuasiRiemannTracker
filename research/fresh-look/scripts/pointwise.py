"""Pointwise best count over all restrictions (B' <= B, L' >= L, cap' <= cap) of the E5 source face, for
several guard regimes; theta* on the newTop edge (other edges have large slack)."""
import numpy as np, sys
from fast import branch, old_count
from ideal import E_newtop, theta_star
ETA = 1e-7
K = 4.5

def count_guarded(d, p, B, L, cap, capped, regime):
    b = branch(d, p, B, L, cap, capped)
    Zc = b['Zc']
    D, A, C0, U, J, N, T, RN, MN, DJ, dU, dJ = (b[k] for k in ('D', 'A', 'C0', 'U', 'J', 'N', 'T', 'RN', 'MN', 'DJ', 'dU', 'dJ'))
    tmax = 1.5 if regime['t15'] else 1.2499
    mMinus = regime['mMinus']
    if regime['nm'] == 'merged':
        nm = (1 - K * 0.03) / 2
    else:
        nm = min((B - L * regime['sig']) / 2, 0.4999)
    sM = (1 - 2 * nm) / K
    if capped:
        lowerM = mMinus + ETA
        upperM = (B - L * Zc) / 2 - ETA
        if regime['nm'] == 'merged': upperM = min(min(11 / 25 - ETA, nm - ETA), upperM)
    else:
        lowerM = max(mMinus + ETA, (B - L * (cap - ETA)) / 2 + ETA)
        upperM = 1.0
        if regime['nm'] == 'merged': upperM = min(min(11 / 25 - ETA, nm - ETA), (B - L * (0.03 + ETA)) / 2 - ETA)
    tail = 1 - 2 * nm * d - 2 * sM * d * p
    ok = (D > 0) & (J > 0) & (T > J) & (tmax * J > T) & (RN > 23 / 37 * DJ) & (DJ > RN) & (MN > lowerM * DJ) & (upperM * DJ > MN)
    ok &= (N > tail * J) & (U * dJ - dU * J > 0)
    if regime['nm'] == 'merged':
        ok &= (B - 2 * nm - L * (0.03 + ETA) - 2 * ETA > 0)
    else:
        ok &= ((B - 2 * nm) / L > 2e-7)
    if capped: ok &= (Zc > 0)
    return ok, N / J

REGIMES = {
    'merged': dict(t15=False, mMinus=0.377, nm='merged'),
    'tail': dict(t15=False, mMinus=0.377, nm='perface', sig=1e-4),
    'tail+t': dict(t15=True, mMinus=0.377, nm='perface', sig=1e-4),
    'tail+t+mLo0': dict(t15=True, mMinus=0.0, nm='perface', sig=1e-4),
    'mLo0 only': dict(t15=False, mMinus=0.0, nm='merged'),
}

def best_env(DD, PP, regime, src=(0.99999, 2.02, 0.13309), Bs=None, caps=None, Ls=None):
    B0, L0, c0 = src
    Bs = np.linspace(B0 - 0.10, B0, 101) if Bs is None else Bs
    caps = np.linspace(0.04, c0, 47) if caps is None else caps
    Ls = [L0, L0 + 0.03, L0 + 0.1, L0 + 0.3] if Ls is None else Ls
    best = np.full(DD.shape, np.inf)
    for L in Ls:
        for cap in caps:
            for capped in (False, True):
                for B in Bs:
                    ok, c = count_guarded(DD, PP, B, L, cap, capped, regime)
                    best = np.minimum(best, np.where(ok, c, np.inf))
    return best

if __name__ == '__main__':
    d = np.round(np.arange(0.25, 0.72, 0.001), 6)
    p = np.round(np.concatenate([np.arange(0.20, 0.49, 0.02), [0.49, 0.495, 0.499, 0.5]]), 6)
    DD, PP = np.meshgrid(d, p, indexing='ij')
    for name in sys.argv[1:] or list(REGIMES):
        env = best_env(DD, PP, REGIMES[name])
        th, k, oc = theta_star(DD, PP, env)
        who = 'old' if oc[k] <= env[k] else 'face'
        print('%-14s theta* = %.8f  bind d=%.3f p=%.3f via %s' % (name, th, d[k[0]], p[k[1]], who), flush=True)
