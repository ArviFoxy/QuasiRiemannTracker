# Lowered density floor (q >= 0.60): ODE faces beyond the PR 86 wall, exact theta* (floor-coupled h), Collet-structure (PR86 constants) vs Lemma W
import json, sys, time
from multiprocessing import Pool
from fractions import Fraction as Fr
import pr86, best, ode_faces as OF
base = pr86.Cfg()
BAR = 0.8739358
chain = json.load(open('chain86.json'))
def ode(L): return (OF.frac(OF.B_ode(L)), OF.frac(L))
PH = ode(2.380)          # physical face near its break-even slope s0* ~ 0.06
def job(a):
    L, win, branches, role = a
    fc = ode(L)
    fp = fc if role == 'single' else PH
    cfg = base.copy(windows=win, branches=branches, BC=fc[0], LC=fc[1], BP=fp[0], LP=fp[1])
    r = best.theta_best(cfg, unit=10**9, anchor=873960000, lo=873900000, step=1000)
    if r is None: return (a, None, None, None)
    return (a, r[0], float(r[1]), best.why(cfg, r[0]-1, unit=10**9))
if __name__ == '__main__':
    Ls = [2.3415, 2.3383, 2.33, 2.32, 2.30, 2.28, 2.26, 2.24, 2.22, 2.20, 2.18, 2.16, 2.14]
    six = ['old','C','Ccap','C-7','P','Pcap']
    jobs = []
    for L in Ls:
        for win, br in (('collet', ['old','C','Pcap']), ('collet', six), ('lemmaW', six)):
            for role in ('single', 'split'):
                jobs.append((L, win, tuple(br), role))
    res = {}
    with Pool(4) as pool:
        for a, t, h, why in pool.imap_unordered(job, jobs):
            res[a] = (t, h, why)
    print('L      B_ode      s0     q_inf | role   PR86-set Collet | six-branch Collet | six-branch LemmaW  (theta*, gap to bar %.7f)' % BAR)
    for L in Ls:
        B = OF.B_ode(L); s0 = OF.rhs(L, [B])[0]; q = OF.q_of(B, L)
        row = []
        for role in ('single', 'split'):
            cells = []
            for win, br in (('collet', ('old','C','Pcap')), ('collet', tuple(six)), ('lemmaW', tuple(six))):
                t = res[(L, win, br, role)][0]
                cells.append('%.9f (%+.2e)' % (t/1e9, t/1e9 - BAR) if t else 'none')
            row.append('%-6s ' % role + ' | '.join(cells))
        print('%.4f %.7f %.5f %.4f | ' % (L, B, s0, q) + '\n                                    '.join(row))
        w = res[(L, 'lemmaW', tuple(six), 'split')]
        print('        binding (LemmaW split): %s, h=%.6f' % (w[2], w[1]))
    json.dump({str(k): v for k, v in res.items()}, open('../lowfloor_ode.json', 'w'))
