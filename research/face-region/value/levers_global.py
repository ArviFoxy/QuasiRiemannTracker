"""The levers of levers.py re-evaluated with globalcheck.theta_global (whole (edge, delta, p) grid, merged faces
and weakenings of the new count face available).  Usage: python3 levers_global.py <case>"""
import sys
from levers import curve, d
from scipy.optimize import brentq, minimize_scalar
from globalcheck import theta_global
from levers import y2, dp


def phys_face(Bc, Lq):
    """the curve's face of largest physical capacity (as levers.evaluate)"""
    cap = lambda L: (y2 - (2 - Bc(L)) * dp) / L
    Lp = minimize_scalar(lambda L: -cap(L), bounds=(max(Lq, 2.0), 2.5), method='bounded').x
    return (Bc(Lp), Lp)


def run(name, Bc, Lq, cap=0.09999):
    PF = phys_face(Bc, Lq)
    best = None
    for L in (Lq, Lq + 0.03, Lq + 0.08):
        t, where = theta_global((Bc(L), L, cap), PF)
        if best is None or t < best[0]:
            best = (t, L, where)
    t, L, where = best
    print('%-28s count face (B=%.6f, L=%.5f, cap=%.3f)  global theta*=%.8f  %+.2e  binding %s d=%.2f p=%.2f %s'
          % ((name, Bc(L), L, cap, t, t - 0.8738723399) + where), flush=True)


if __name__ == '__main__':
    case = sys.argv[1]
    Lq_of = lambda Bc, qs, lo, hi: brentq(lambda L: d * L / (6 * Bc(L) - L) - qs, lo, hi)
    if case.startswith('k'):
        dk = float(case[1:])
        Bc = curve(2.5715, 0.99999, dk)
        run('kappa + %.3f' % dk, Bc, Lq_of(Bc, 0.5, 1.75, 2.5))
    elif case.startswith('b'):
        Lb = float(case[1:])
        Bc = curve(Lb, 0.99999)
        run('boot Lb = %.3f' % Lb, Bc, Lq_of(Bc, 0.5, 1.75, Lb))
        run('boot Lb = %.3f, cap 0.12' % Lb, Bc, Lq_of(Bc, 0.5, 1.75, Lb), cap=0.12)
    elif case.startswith('q'):
        qs = float(case[1:])
        Bc = curve(2.5715, 0.99999)
        run('past floor q_stop = %.2f' % qs, Bc, Lq_of(Bc, qs, 1.5, 2.5))
