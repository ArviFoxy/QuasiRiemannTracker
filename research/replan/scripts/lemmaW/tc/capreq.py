# minimal count-face cap (to 1e-3) that leaves theta* unchanged, as a function of the face position on the ODE frontier: Collet-structure (PR 86 constants) vs Lemma W
from multiprocessing import Pool
from fractions import Fraction as Fr
import pr86, best, ode_faces as OF
six = ['old','C','Ccap','C-7','P','Pcap']
PH = (OF.frac(OF.B_ode(2.38)), OF.frac(2.38))
def theta(L, cap, win):
    fc = (OF.frac(OF.B_ode(L)), OF.frac(L))
    cfg = pr86.Cfg(windows=win, branches=six if win == 'lemmaW' else ['old','C','Pcap'], BC=fc[0], LC=fc[1], BP=PH[0], LP=PH[1], capC=cap)
    r = best.theta_best(cfg, unit=10**9, anchor=873960000, lo=873900000, step=2000, maxstep=60)
    return None if r is None else r[0]
def job(a):
    L, win = a
    ref = theta(L, Fr(1, 10), win)
    lo, hi = Fr(6, 100), Fr(1, 10)       # hi passes (ref); find smallest cap (1e-3 grid) with theta == ref + 2e-9
    caps = [Fr(x, 1000) for x in range(60, 101)]
    # bisection on the grid: pass(cap) := theta(cap) <= ref + 2
    a_, b_ = 0, len(caps) - 1
    while b_ - a_ > 1:
        m = (a_ + b_)//2
        t = theta(L, caps[m], win)
        if t is not None and t <= ref + 2: b_ = m
        else: a_ = m
    return a, ref, float(caps[b_])
if __name__ == '__main__':
    Ls = [2.34, 2.30, 2.25, 2.20, 2.15, 2.10]
    jobs = [(L, w) for L in Ls for w in ('collet', 'lemmaW')]
    with Pool(4) as p: res = {a: (ref, cap) for a, ref, cap in p.map(job, jobs)}
    print('face on ODE at L | B | s0 | min count cap keeping theta*: Collet-structure | Lemma W   (theta* at cap 0.1)')
    for L in Ls:
        B = OF.B_ode(L)
        print('L=%.2f B=%.5f s0=%.4f | %.3f | %.3f   (theta*=%.9f)' % (L, B, OF.rhs(L, [B])[0], res[(L,'collet')][1], res[(L,'lemmaW')][1], res[(L,'lemmaW')][0]/1e9))
