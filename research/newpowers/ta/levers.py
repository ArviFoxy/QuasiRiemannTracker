"""Q2: size of one extra improvement that closes the gap of a scenario (ODE limit, role split re-optimised).
Chain-side levers (re-integrated):  dR (count exponent R -> R - dR everywhere), eps (step slope s0 -> (1-eps) s0),
c6 (the packed-envelope rate 6 -> 6 - d), dL0 (native barrier / start face L0 -> L0 - dL0).
Face-side lever: dBP (physical face B_P -> B_P + d at its L_P).   Return-side (tc/levers_pr86.py, exact): dE, dRret, dC, CI, KL.
usage: python3 levers.py VAR FLOOR BOOT DFAC [levers...]"""
import sys, os, json, time
from fractions import Fraction as Fr
import numpy as np
import ode, run_ode, split, exact

TARGET = 0.8739058


def theta_run(var, floor, boot, dfac, **kw):
    r = run_ode.run_ode(var, boot, dfac, floors=(floor,), verbose=False, tag='_lev', **kw)[0]
    return r['theta'], r


def solve(fun, g, x1, name, tol=2e-8, maxit=4):
    """find x with theta0 - fun(x) = g  (fun returns theta); secant from x1; theta0 given implicitly via fun(0)."""
    t0 = fun(0.0)
    t1 = fun(x1)
    sl = (t0 - t1) / x1                    # gain per unit lever
    x = g / sl
    pts = [(0.0, t0), (x1, t1)]
    for _ in range(maxit):
        tx = fun(x)
        pts.append((x, tx))
        err = (tx - (t0 - g))
        if abs(err) < tol:
            break
        # secant using the last two points
        (xa, ta), (xb, tb) = pts[-2], pts[-1]
        if tb == ta:
            break
        x = xb + ((t0 - g) - tb) * (xb - xa) / (tb - ta)
    return x, sl, pts


def main():
    var, floor, boot, dfac = sys.argv[1], float(sys.argv[2]), bool(int(sys.argv[3])), float(sys.argv[4])
    which = sys.argv[5:] or ['dR', 'eps', 'c6', 'dL0', 'dBP', 'ret']
    t0, r0 = theta_run(var, floor, boot, dfac)
    g = t0 - TARGET
    print('%s floor %.2f boot %d dfac %.3f: theta0=%.9f gap=%+.3e (C L=%.4f s0=%.4f; P L=%.3f)' % (var, floor, boot, dfac, t0, g, r0['C']['L'], r0['C']['s0'], r0['P']['L']), flush=True)
    out = {'theta0': t0, 'gap': g}
    if 'dR' in which:
        f = lambda x: theta_run(var, floor, boot, dfac, shift_R=x)[0] if x else t0
        x, sl, pts = solve(f, g, 1e-3, 'dR')
        print('  count exponent R lowered everywhere by dR = %.5f   (dtheta/dR = %.3e)' % (x, sl), flush=True); out['dR'] = (x, sl)
    if 'eps' in which:
        f = lambda x: theta_run(var, floor, boot, dfac, s0scale=1 - x)[0] if x else t0
        x, sl, pts = solve(f, g, 0.02, 'eps')
        print('  step slope s0 smaller by %.3f %%   (dtheta per 1%% = %.3e)' % (100 * x, sl / 100), flush=True); out['eps'] = (x, sl)
    if 'c6' in which:
        f = lambda x: theta_run(var, floor, boot, dfac, c6=6.0 - x)[0] if x else t0
        x, sl, pts = solve(f, g, 0.03, 'c6')
        print('  packed-envelope rate 6 -> %.4f   (dtheta per 0.01 = %.3e)' % (6 - x, sl / 100), flush=True); out['c6'] = (x, sl)
    if 'dL0' in which:
        f = lambda x: theta_run(var, floor, boot, dfac, dL0=x)[0] if x else t0
        x, sl, pts = solve(f, g, 0.02, 'dL0')
        print('  native barrier / start face L0 lowered by %.4f (rel %.2f %%)   (dtheta per 0.001 = %.3e)' % (x, 100 * x / 2.5715, sl / 1000), flush=True); out['dL0'] = (x, sl)
    if 'dBP' in which:
        C, P = r0['C'], r0['P']
        def fP(x):
            if not x:
                return t0
            rr = exact.theta_exact(C['B'], C['L'], P['B'] + x, P['L'], guess=t0, unit=10**9, span=2000)
            return rr[0]
        x, sl, pts = solve(fP, g, 5e-4, 'dBP')
        print('  physical face B_P (at L_P=%.3f) raised by %.5f   (dtheta/dB_P = %.3e)' % (P['L'], x, -sl), flush=True); out['dBP'] = (x, sl)
        def fC(x):
            if not x:
                return t0
            rr = exact.theta_exact(C['B'] + x, C['L'], P['B'], P['L'], guess=t0, unit=10**9, span=2000)
            return rr[0]
        x, sl, pts = solve(fC, g, 5e-4, 'dBC')
        print('  count face B_C (at L_C=%.4f) raised by %.5f   (dtheta/dB_C = %.3e)' % (C['L'], x, -sl), flush=True); out['dBC'] = (x, sl)
    if 'ret' in which:
        sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'tc'))
        import levers_pr86 as LV
        import best, pr86
        C, P = r0['C'], r0['P']
        cfg = exact.make_cfg(C['B'], C['L'], P['B'], P['L'])
        def th(c):
            r = best.theta_best(c, unit=10**9, anchor=int(round((t0 + 4e-6) * 1e9)), lo=int(round((t0 - 3e-5) * 1e9)), step=1000, maxstep=80)
            return None if r is None else r[0] / 1e9
        LV.set_lev(); tb = th(cfg)
        print('  [return-side, exact] base %.9f' % tb)
        for name, key, x1 in (('E exponent', 'dE', Fr(-1, 100000)), ('return count R (all improved branches)', 'dR', Fr(1, 10000)), ('capacity C_N', 'dC', Fr(1, 1000))):
            LV.set_lev(**{key: x1}); t1 = th(cfg); LV.set_lev()
            sl = (tb - t1) / float(abs(x1))
            need = g / sl
            xn = Fr(-need) if key == 'dE' else Fr(need)
            LV.set_lev(**{key: xn}); t2 = th(cfg); LV.set_lev()
            print('    %-38s slope %.4e per unit  -> needed %.3e  (theta at needed: %.9f)' % (name, sl, need, t2), flush=True)
            out['ret_' + key] = (need, sl)
    json.dump(out, open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results', 'lev_%s_f%.2f_b%d_d%.3f.json' % (var, floor, int(boot), dfac)), 'w'), indent=1)


if __name__ == '__main__':
    main()
