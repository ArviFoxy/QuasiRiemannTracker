"""Exact (kernel-mirror, all four return edges) check of the conditional end faces priced by conditional_gains.py.

Mirror: `fresh-look/scripts/mirror3.py` + `cover3.py`. It reproduces the bank: N = 6330886 (theta 0.87338228)
covers every edge, N + 1 fails on newTop. Design constants as in the bank (sMinus 27/1000, mMinus 3/10,
eleven 11/25, numCap 3/40, w 1/100), both faces (99999/100000, Lambda, cap line), physical cap 3/25 as in the bank, h = 7-digit floor of the bank
fork's floor-margin ceiling (margin 1/1000, h < 81/100). Windows are regenerated at each face with
exact_run.windows. Prints the best N (theta = 1 - N/5e7) whose cover passes on all edges.  [exact rationals]
usage: python3 conditional_exact.py Lambda1,Lambda2,...
"""
import sys, math, time
from fractions import Fraction as Fr
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/fresh-look/scripts')
sys.dont_write_bytecode = True
import mirror3 as M, cover3
from exact_run import windows

PR99 = Fr(8733819666133, 10 ** 13)
BAR = PR99 - Fr(5, 10 ** 5)
CONSTS = dict(mMinus=Fr(3, 10), sMinus=Fr(27, 1000), eleven=Fr(11, 25))
M.set_constants(**CONSTS)
PLOS = [Fr(0), Fr(1, 4), Fr(3, 8), Fr(7, 16), Fr(15, 32), Fr(31, 64), Fr(63, 128), Fr(127, 256), Fr(255, 512)]


def hceil_fork(theta, margin=Fr(1, 1000), hu=Fr(81, 100)):
    ell = Fr(11, 3) - 4 * theta
    def fm(h):
        x = 1 + ell - h; y = h - 2 * ell; dP = h + Fr(1, 10 ** 10)
        sig = x / 2 + (y - x) / 12
        return sig - margin - (Fr(4, 25) * x - Fr(3, 20) - Fr(51, 100) * y + Fr(67, 100) * dP - Fr(3, 20) * ell)
    f0, f1 = fm(Fr(0)), fm(Fr(1))
    return min(-f0 / (f1 - f0), hu - Fr(1, 10 ** 6))


def K_of(N, L, cap, h=None):
    c = Fr(N, 50000000); theta = 1 - c
    hc = Fr(math.floor(hceil_fork(theta) * 10 ** 7), 10 ** 7)
    h = hc if h is None else min(h, hc)
    pB = Fr(99999, 100000)
    return M.Const(c=c, h=h, reserve=Fr(1, 10 ** 8), cB=pB, cL=L, cCap=cap, pB=pB, pL=L, pCap=Fr(3, 25),
                   numCap=Fr(3, 40), dm=Fr(19, 25), w=Fr(1, 100)), h


HGRID = [Fr(7950 + 5 * i, 10000) for i in range(0, 30)]   # 0.7950 ... 0.8095, step 0.0005
BANK_WS = [('C', Fr(5729, 16384), Fr(8189, 16384), Fr(0)), ('C', Fr(5729, 16384), Fr(297, 512), Fr(3, 8)),
           ('capP', Fr(1, 16384), Fr(5971, 16384), Fr(1, 4))]


def scan_windows(O, den=512):
    """maximal delta-intervals [a, b] with WinQ.ok (exact 15 guards) per branch and p-floor, refined to 1/16384"""
    out = [w for w in BANK_WS if O.window_ok(*w)]
    for b in ('C', 'capC', 'capP'):
        for plo in PLOS:
            cells = [O.window_ok(b, Fr(i, den), Fr(i + 1, den), plo) for i in range(int(Fr(3, 4) * den))]
            i = 0
            while i < len(cells):
                if not cells[i]:
                    i += 1; continue
                j = i
                while j + 1 < len(cells) and cells[j + 1]:
                    j += 1
                lo, hi = Fr(i, den), Fr(j + 1, den)
                while hi - lo > Fr(1, den) and not O.window_ok(b, lo, hi, plo):
                    hi -= Fr(1, den)
                if O.window_ok(b, lo, hi, plo):
                    out.append((b, lo, hi, plo))
                i = j + 1
    return out


def best_N(L, N_guess, span=6000):
    """windows once per face (they depend on the face, not on h or c); then the best (N, h) over HGRID"""
    cap = Fr(1, 10) + Fr(3, 50) * (Fr(5143, 2000) - L)
    K0, _ = K_of(N_guess, L, cap, Fr(8097, 10000))
    ws = scan_windows(cover3.Oracle(K0))
    best = (None, None)
    for hh in HGRID:
        def ok(N):
            K, _ = K_of(N, L, cap, hh)
            return cover3.Oracle(K).run(ws)[0]
        lo, hi = 6328000, 6346000          # theta in [0.87308, 0.87344]; the lower end passes at every face tried
        if best[0] is not None:
            lo = max(lo, best[0])
            if not ok(lo):
                continue
        elif not ok(lo):
            continue
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if ok(mid): lo = mid
            else: hi = mid
        if best[0] is None or lo > best[0]:
            best = (lo, K_of(lo, L, cap, hh)[1])
    return best[0], best[1], ws, cap


if __name__ == '__main__':
    Ls = [Fr(x) for x in (sys.argv[1] if len(sys.argv) > 1 else '20001/10000,1967/1000,19669/10000,196/100,18/10').split(',')]
    for L in Ls:
        t = time.time()
        th_guess = {Fr(20001, 10000): 0.87338228}.get(L, 0.8733 - 0.0016 * (2 - float(L)))
        N_guess = int(round((1 - th_guess) * 5e7))
        N, h, ws, cap = best_N(L, N_guess)
        if N is None:
            print('Lambda %s: lower end of the search fails (windows %d)' % (L, len(ws)), flush=True)
            continue
        th = 1 - Fr(N, 50000000)
        print('Lambda %.4f cap %.5f: best N %d  theta %.8f  h %s  vs PR99 %+.2e  vs bar %+.2e  windows %d  (%.0fs)'
              % (float(L), float(cap), N, float(th), h, float(th - PR99), float(th - BAR), len(ws), time.time() - t),
              flush=True)
