"""Q3: sensitivity of theta* (ODE limit, role split re-optimised) to the leaf's count exponent R.
R -> R - eps in the HIGH gate (cs += eps*Q) for all (nu,x) and, for the windowed version, only while L is in a window."""
import sys, os, json, time
import numpy as np
import ode, run_ode, split

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, 'results')


def theta_with(var, floor, boot, dfac, shift_R=0.0, tag='', **kw):
    out = run_ode.run_ode(var, boot, dfac, floors=(floor,), shift_R=shift_R, tag=tag, verbose=False, **kw)
    return out[0]


def sens(var, floor, boot=True, dfac=1.0, eps=2e-3):
    r0 = theta_with(var, floor, boot, dfac, 0.0)
    r1 = theta_with(var, floor, boot, dfac, eps, tag='_dR%g' % eps)
    return r0['theta'], r1['theta'], (r0['theta'] - r1['theta']) / eps, r0, r1


def window_sens(var, floor, windows, boot=True, dfac=1.0, eps=2e-3):
    r0 = theta_with(var, floor, boot, dfac, 0.0)
    out = []
    for (Lhi, Llo) in windows:
        f = (lambda L, a=Lhi, b=Llo, e=eps: e if (b <= L <= a) else 0.0)
        r1 = theta_with(var, floor, boot, dfac, f, tag='_win%.2f_%.2f' % (Lhi, Llo))
        out.append(((Lhi, Llo), r1['theta'], (r0['theta'] - r1['theta']) / eps))
    return r0['theta'], out


if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'whole':
        var = sys.argv[2]; floor = float(sys.argv[3])
        t0 = time.time()
        a, b, s, r0, r1 = sens(var, floor)
        print('%-4s floor %.2f all-on: theta0=%.9f theta(R-2e-3)=%.9f  dtheta/dR=%.4e  [C L=%.3f -> %.3f; P L=%.3f -> %.3f] %.0fs' % (
            var, floor, a, b, s, r0['C']['L'], r1['C']['L'], r0['P']['L'], r1['P']['L'], time.time() - t0), flush=True)
    elif mode == 'windows':
        var = sys.argv[2]; floor = float(sys.argv[3])
        wins = [(2.58, 2.45), (2.45, 2.30), (2.30, 2.15), (2.15, 1.80)]
        a, out = window_sens(var, floor, wins)
        print('%-4s floor %.2f: theta0=%.9f' % (var, floor, a))
        for (w, t, s) in out:
            print('   R shifted for L in [%.2f,%.2f]: theta=%.9f  dtheta/dR=%.4e' % (w[1], w[0], t, s), flush=True)
