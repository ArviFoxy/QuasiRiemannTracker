"""The Lean-faithful relaxed guard set: global sMinus (naturalM = (1 - 4.5 sMinus)/2), plain floor mMinus,
11/25 replaced by 1/2 in upperM and guard 12, cutoff bound 12499/10000 kept. Window cover on all four edges."""
import numpy as np
from fast import branch
ETA = 1e-7
def count_lean(d, p, B, L, cap, capped, sMinus=1e-4, mMinus=0.0, tmax=1.2499, eleven=0.5):
    b = branch(d, p, B, L, cap, capped)
    nm = (1 - 4.5 * sMinus) / 2
    Zc = b['Zc']
    D, A, C0, U, J, N, T, RN, MN, DJ, dU, dJ = (b[k] for k in ('D', 'A', 'C0', 'U', 'J', 'N', 'T', 'RN', 'MN', 'DJ', 'dU', 'dJ'))
    if capped:
        lowerM = mMinus + ETA
        upperM = min(min(eleven - ETA, nm - ETA), (B - L * Zc) / 2 - ETA)
    else:
        lowerM = max(mMinus + ETA, (B - L * (cap - ETA)) / 2 + ETA)
        upperM = min(min(eleven - ETA, nm - ETA), (B - L * (sMinus + ETA)) / 2 - ETA)
    tail = 1 - 2 * nm * d - 2 * sMinus * d * p
    g = [D, A, C0, J, T - J, tmax * J - T, RN - 23 / 37 * DJ, DJ - RN, MN - lowerM * DJ, upperM * DJ - MN,
         N - tail * J, U * dJ - dU * J]
    ok = np.ones(np.shape(J), dtype=bool)
    for x in g: ok &= (x > 0)
    const = (eleven - nm - ETA > 0) and (B - 2 * nm - L * (sMinus + ETA) - 2 * ETA > 0) and ((Zc - sMinus - ETA > 0) if capped else True)
    return ok & const, N / J

if __name__ == '__main__':
    import cover
    from cover import windows_for, excess
    DG = np.round(np.arange(0.0, 0.7501, 0.0005), 6)
    PG = np.round(np.concatenate([np.arange(0.0, 0.48, 0.02), np.arange(0.48, 0.5, 0.0025), [0.5]]), 6)
    DD, PP = np.meshgrid(DG, PG, indexing='ij')
    full = (0.99999, 2.02, 0.13309)
    for mM in (0.0, 0.30, 0.35, 0.377):
        for br in ({'C': (*full, False), 'capC': (*full, True), 'capC2': (0.99999, 2.02, 0.12, True)},
                   {'C': (*full, False), 'capC': (0.99999, 2.02, 0.12, True), 'capC2': (0.99999, 2.02, 0.10, True)}):
            env = np.full(DD.shape, np.inf); nw = 0
            for name, (B, L, cap, capped) in br.items():
                ok, v = count_lean(DD, PP, B, L, cap, capped, mMinus=mM)
                for (ilo, ihi, jlo) in windows_for(DG, PG, ok, range(len(PG))):
                    env[ilo:ihi + 1, jlo:] = np.minimum(env[ilo:ihi + 1, jlo:], v[ilo:ihi + 1, jlo:]); nw += 1
            lo, hi = 0.868, 0.878
            for _ in range(40):
                mid = (lo + hi) / 2
                ex = excess(mid, DD, PP, env)
                if max(e.max() for e in ex.values()) > 0: lo = mid
                else: hi = mid
            ex = excess(hi, DD, PP, env)
            k = np.unravel_index(np.argmax(ex['newTop']), DD.shape)
            print('mMinus %.3f caps %s: theta* = %.8f (newTop bind d=%.4f p=%.4f; other edges max %.1e)' % (
                mM, [round(v[2], 4) for v in br.values()], hi, DG[k[0]], PG[k[1]], max(ex[e].max() for e in ('oldSmall', 'oldSwitch', 'newSwitch'))))
