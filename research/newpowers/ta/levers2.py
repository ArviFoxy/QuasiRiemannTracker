"""Q2: size of one extra improvement that closes (or is tolerated by) the gap of a scenario (ODE limit, role split re-optimised).
Chain-side levers (re-integrated):  dR (count exponent R -> R - dR everywhere: the gate gains + dR*Q), eps (s0 -> (1-eps) s0),
c6 (packed-envelope rate 6 -> 6 - d), dL0 (native barrier / start face L0 -> L0 - dL0), gscale (the repeated-mark gain times lam).
Face-side levers (exact):  dBP (physical face B_P -> B_P + d at its L_P), dBC (count face).  Return-side (tc/levers_pr86.py, exact):
dE (return exponent), dRret (return count R on the non-old branches), dC (capacity).
usage: python3 levers2.py GAIN FLOOR BOOT DFAC [levers...]      (default levers: dR eps c6 dL0 gscale dBP ret)
Negative needed values mean the scenario passes the bar and the lever could be *worsened* by |x| before failing."""
import sys, os, json, time
from fractions import Fraction as Fr
import numpy as np
import ode2, run_ode2, split, exact

TARGET = 0.8739058
HERE = os.path.dirname(os.path.abspath(__file__))


def theta_run(gain, floor, boot, dfac, **kw):
    r = run_ode2.run_ode(gain, boot, dfac, floors=(floor,), verbose=False, tag='_lev', scan_extra=False, **kw)[0]
    return r['theta'], r


def solve(fun, g, x1, tol=2e-8, maxit=5):
    """x with theta(x) = theta0 - g, i.e. theta0 - fun(x) = g;  secant from x1;  fun(0) must be theta0"""
    t0 = fun(0.0)
    t1 = fun(x1)
    sl = (t0 - t1) / x1
    x = g / sl
    pts = [(0.0, t0), (x1, t1)]
    for _ in range(maxit):
        tx = fun(x)
        pts.append((x, tx))
        if abs(tx - (t0 - g)) < tol:
            break
        (xa, ta), (xb, tb) = pts[-2], pts[-1]
        if tb == ta:
            break
        x = xb + ((t0 - g) - tb) * (xb - xa) / (tb - ta)
    return x, sl, pts


def main():
    gain, floor, boot, dfac = float(sys.argv[1]), float(sys.argv[2]), bool(int(sys.argv[3])), float(sys.argv[4])
    which = sys.argv[5:] or ['dR', 'eps', 'c6', 'dL0', 'gscale', 'dBP', 'ret']
    t0, r0 = theta_run(gain, floor, boot, dfac)
    g = t0 - TARGET
    print('gain %g floor %.2f boot %d dfac %.3f: theta0=%.9f gap=%+.3e (C L=%.4f s0=%.4f; P L=%.3f)' % (
        gain, floor, boot, dfac, t0, g, r0['C']['L'], r0['C']['s0'], r0['P']['L']), flush=True)
    out = {'theta0': t0, 'gap': g}
    if 'dR' in which:
        f = lambda x: theta_run(gain, floor, boot, dfac, shift_R=x)[0] if x else t0
        x, sl, pts = solve(f, g, 1e-3)
        print('  count exponent R lowered everywhere by dR = %.5f   (dtheta/dR = %.3e)' % (x, sl), flush=True); out['dR'] = (x, sl)
    if 'eps' in which:
        f = lambda x: theta_run(gain, floor, boot, dfac, s0scale=1 - x)[0] if x else t0
        x, sl, pts = solve(f, g, 0.02)
        print('  step slope s0 smaller by %.3f %%   (dtheta per 1%% = %.3e)' % (100 * x, sl / 100), flush=True); out['eps'] = (x, sl)
    if 'c6' in which:
        f = lambda x: theta_run(gain, floor, boot, dfac, c6=6.0 - x)[0] if x else t0
        x, sl, pts = solve(f, g, 0.03)
        print('  packed-envelope rate 6 -> %.4f   (dtheta per 0.01 = %.3e)' % (6 - x, sl / 100), flush=True); out['c6'] = (x, sl)
    if 'dL0' in which:
        f = lambda x: theta_run(gain, floor, boot, dfac, dL0=x)[0] if x else t0
        x, sl, pts = solve(f, g, 0.02)
        print('  native barrier / start face L0 lowered by %.4f (rel %.2f %%)   (dtheta per 0.001 = %.3e)' % (x, 100 * x / 2.5715, sl / 1000), flush=True); out['dL0'] = (x, sl)
    if 'gscale' in which:
        # gain multiplied by lam: lam = 1 is the scenario; find lam* with theta = TARGET (lam < 1: fraction of the Lean gain needed)
        f1 = lambda lam: theta_run(lam * gain, floor, boot, dfac)[0]
        lam = 1.0
        pts = [(1.0, t0)]
        for lam_try in (0.9, 0.8, 0.7):
            pts.append((lam_try, f1(lam_try)))
            if pts[-1][1] > TARGET:
                break
        # linear/secant interpolation on the last two points
        (xa, ta), (xb, tb) = pts[-2], pts[-1]
        lam = xa + (TARGET - ta) * (xb - xa) / (tb - ta)
        for _ in range(3):
            tl = f1(lam)
            pts.append((lam, tl))
            if abs(tl - TARGET) < 2e-8:
                break
            (xa, ta), (xb, tb) = pts[-2], pts[-1]
            lam = xb + (TARGET - tb) * (xb - xa) / (tb - ta)
        print('  repeated-mark gain scaled to %.3f of its Lean value reaches the bar   (points %s)' % (lam, ['%.2f:%.8f' % p for p in pts]), flush=True); out['gscale'] = (lam, pts)
    if 'dBP' in which:
        C, P = r0['C'], r0['P']
        def fP(x):
            if not x:
                return t0
            return exact.theta_exact(C['B'], C['L'], P['B'] + x, P['L'], guess=t0, unit=10**9, span=2000)[0]
        x, sl, pts = solve(fP, g, 5e-4)
        print('  physical face B_P (at L_P=%.3f) raised by %.5f   (dtheta/dB_P = %.3e)' % (P['L'], x, -sl), flush=True); out['dBP'] = (x, sl)
        def fC(x):
            if not x:
                return t0
            return exact.theta_exact(C['B'] + x, C['L'], P['B'], P['L'], guess=t0, unit=10**9, span=2000)[0]
        x, sl, pts = solve(fC, g, 5e-4)
        print('  count face B_C (at L_C=%.4f) raised by %.5f   (dtheta/dB_C = %.3e)' % (C['L'], x, -sl), flush=True); out['dBC'] = (x, sl)
    if 'ret' in which:
        sys.path.insert(0, os.path.join(HERE, 'tc'))
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
            print('    %-38s slope %.4e per unit  -> needed %.3e  (theta at needed: %s)' % (name, sl, need, t2), flush=True)
            out['ret_' + key] = (need, sl)
    json.dump(out, open(os.path.join(HERE, 'results', 'lev2_g%g_f%.2f_b%d_d%.3f.json' % (gain, floor, int(boot), dfac)), 'w'), indent=1)


if __name__ == '__main__':
    main()
