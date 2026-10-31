"""Conditional theta gains: what each open input would buy, priced before committing to a long project.

theta* is the float model of the return's newTop row (`fresh-look/second/base_models/worth.py`, reproduces the bank
0.87338228 at (B, Lambda) = (0.99999, 2.0001), h = 0.8097). For each hypothetical input the native line is rerun
(continuum limit, as `selected-leaf/envelope_c.py`) to find the end face (Lambda_end, cap_end) and the gate that stops
it; then theta* is evaluated there, with h re-optimized inside the bank fork's box (h < 81/100 and the floor-margin
ceiling at margin 1/1000).  [numerical; the model sees only the newTop edge, so large moves are first-order]

Inputs:
  K      the deletion cut of the native step (K-wall): K = 1/2 + 1e-6 today (PR 93's selected norm at slope > 1/2);
         K < 1/2 needs the selected norm at its fixed point below slope 1/2 (open: balanced-corner fourth moment, plus
         input A for single-factor leaves).
  ref    'half': today's reference gate (principal gate Lambda > 2 + 4.5a);
         'pd'  : target 2, the prime-dilated short reference (journal 2026-10-31), short reference up to
                 b <= min((1+S)/2, 3/4 - S, (6+S)/11) at S = cap (no metaplectic input; Lean core done).
usage: python3 conditional_gains.py
"""
import sys, io, contextlib
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/fresh-look/second/base_models')
sys.dont_write_bytecode = True
with contextlib.redirect_stdout(io.StringIO()):
    import worth

PR99 = 0.8733819666133
BAR = PR99 - 5e-5
BANK = 0.87338228


def hceil(theta, margin=1 / 1000, hu=0.81):
    """largest h allowed by BoundsN.floor_margin in the bank fork (margin 1/1000, box h < 81/100)"""
    ell = 11 / 3 - 4 * theta
    def fm(h):
        x = 1 + ell - h; y = h - 2 * ell; dP = h + 1e-10
        sig = x / 2 + (y - x) / 12
        return sig - margin - (0.16 * x - 0.15 - 0.51 * y + 0.67 * dP - 0.15 * ell)
    f0, f1 = fm(0.0), fm(1.0)
    return min(-f0 / (f1 - f0), hu - 1e-6)


def theta_at(L, cap, B=0.99999, LONG=5 / 6, numCap=0.075, hfix=None):
    """(theta*, h): h fixed, or scanned over [0.800, 0.810) subject to the floor-margin ceiling"""
    if hfix is not None:
        return worth.theta_star(LONG, L=L, B=B, cap=cap, h=hfix, numCap=numCap)[0], hfix
    best = None
    for i in range(100):
        h = 0.800 + 0.0001 * i
        t = worth.theta_star(LONG, L=L, B=B, cap=cap, h=h, numCap=numCap)[0]
        if h > hceil(t):
            continue
        if best is None or t < best[0]:
            best = (t, h)
    return best


def gpd(S):
    return min((1 + S) / 2, 3 / 4 - S, (6 + S) / 11)


def native_line(K, ref='half', c6=6.0, B=0.99999, L0=3.72, c0=0.06, step=1e-4, Lstop=0.0):
    """end face of the native line (continuum limit): returns (Lambda_end, cap_end, reason)"""
    L, c = L0, c0
    while L > Lstop:
        Ln = L - step
        den = L * (1 + K) - c6 * K * B
        if den <= 0:
            return L, c, 'overshoot'
        a = K * step / den * (1 + 1e-9)
        if a > (Ln - 1) / (c6 - 2):
            return L, c, 'selected branch'
        cn = c / (1 - a + c6 * a * c) * (1 - 1e-12)
        S = cn
        if ref == 'pd':
            principal = (3 / 4 + gpd(S) / 2 - B) + (Ln - 2) * S - 4.5 * a * S > 0
        else:
            principal = Ln - 2 - 4.5 * a > 0
        ok = {'principal': principal, 'diagonal': Ln - 1 - 4 * a > 0, 'secondRef': 1.5 * Ln - 2.5 - 4.5 * a > 0,
              'refPos': 1 / 6 - (1 + 1.5 * a) * cn > 0, 'H': 1 - c6 * a * cn > 0, 'cap_lt': c < 1 / 6}
        bad = [k for k, v in ok.items() if not v]
        if bad:
            return L, c, ','.join(bad)
        L, c = Ln, cn
    return L, c, 'Lstop'


def row(label, L, cap, why=''):
    t, h = theta_at(L, cap)
    t0, _ = theta_at(L, cap, hfix=0.8097)
    print('%-44s Lambda_end %.4f cap %.4f (%s)  theta* %.8f [h %.4f]  (h=0.8097: %.8f)  vs PR99 %+.2e  vs bar %+.2e'
          % (label, L, cap, why, t, h, t0, t - PR99, t - BAR), flush=True)
    return t


if __name__ == '__main__':
    print('bank check:', '%.8f' % worth.theta_star(5 / 6, L=2.0001, B=0.99999, h=0.8097)[0], ' bar %.10f' % BAR)
    print('\n== A. End face of the native line under the two walls ==')
    for K, ref in ((0.500001, 'half'), (0.500001, 'pd'), (0.48, 'half')):
        L, c, why = native_line(K, ref)
        row('K=%.6f ref=%s' % (K, ref), L, c, why)
    for K in (0.495, 0.49, 0.4877, 0.4869, 0.48, 0.47, 0.46, 0.45, 0.44, 0.42, 0.40, 0.35, 0.30, 0.25, 0.2):
        L, c, why = native_line(K, 'pd')
        row('K-wall to K=%.4f + target 2' % K, L, c, why)
    print('\n== B. theta* along the face Lambda (cap from the bank cap line), independent of how the face is reached ==')
    for L in (2.0001, 1.99, 1.98, 1.97, 1.96, 1.95, 1.93, 1.90, 1.85, 1.80, 1.75, 1.70, 1.667):
        cap = 0.1 + 0.06 * (5143 / 2000 - L)
        row('face Lambda=%.4f (cap line)' % L, L, cap)
    print('\n== C. Single levers at the bank face ==')
    for dl in (0.001, 0.005, 0.0107, 0.02, 0.05):
        t = worth.theta_star(5 / 6 - dl, L=2.0001, B=0.99999, h=0.8097)[0]
        print('long slope 5/6 - %.4f: theta* %.8f  vs bar %+.2e' % (dl, t, t - BAR), flush=True)
