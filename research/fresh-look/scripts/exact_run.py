"""Exact (kernel-mirror) cover for the relaxed-guard design: Lean constants sMinus, mMinus, 11/25 -> eleven;
branches C/capC = E5 end face, capP = E5 end face capped at pCap; windows from the float profile, refined exactly."""
import math, sys, time
import numpy as np
from fractions import Fraction as Fr
import mirror3 as M
import cover3
from model import hceiling
from leanregime import count_lean

def hfloor(theta, digits=7):
    hc = hceiling(theta)
    return Fr(math.floor(hc * 10 ** digits), 10 ** digits)

def buildK(N, des, reserve=Fr(1, 10 ** 8)):
    c = Fr(N, 50000000); theta = 1 - c; h = hfloor(theta)
    return M.Const(c=c, h=h, reserve=reserve, cB=des['cB'], cL=des['cL'], cCap=des['cCap'], pB=des['pB'], pL=des['pL'],
                   pCap=des['pCap'], numCap=des['numCap'], dm=Fr(19, 25), w=des['w']), theta, h

DS = np.round(np.arange(0.0, 0.7501, 0.0005), 6)
PS = np.round(np.arange(0.0, 0.5001, 0.0025), 6)

def pmin_profile(face, consts):
    B, L, cap, capped = (float(face[0]), float(face[1]), float(face[2]), face[3])
    D, P_ = np.meshgrid(DS, PS, indexing='ij')
    ok, _ = count_lean(D, P_, B, L, cap, capped, sMinus=float(consts['sMinus']), mMinus=float(consts['mMinus']), eleven=float(consts['eleven']))
    pm = np.full(len(DS), np.inf)
    for i in range(len(DS)):
        col = ok[i]
        if not col[-1]: continue
        bad = np.where(~col)[0]
        pm[i] = PS[(bad.max() + 1) if len(bad) else 0]
    return pm

def runs(pm, plo):
    good = pm <= plo + 1e-12
    out = []; i = 0
    while i < len(DS):
        if good[i]:
            j = i
            while j + 1 < len(DS) and good[j + 1]: j += 1
            out.append((DS[i], DS[j])); i = j + 1
        else: i += 1
    return out

def refine(O, branch, a0, b0, plo, den=2 ** 14, span=40):
    lo = Fr(math.ceil(a0 * den), den); hi = Fr(math.floor(b0 * den), den)
    n = 0
    while not O.window_ok(branch, lo, hi, plo, 0):
        lo += Fr(1, den); hi -= Fr(1, den); n += 1
        if hi <= lo or n > 2 * span: return None
    for side in ('lo', 'hi'):
        step = span
        while step >= 1:
            while True:
                nlo, nhi = (lo - Fr(step, den), hi) if side == 'lo' else (lo, hi + Fr(step, den))
                if nlo < 0 or nhi > Fr(3, 4): break
                if O.window_ok(branch, nlo, nhi, plo, 0): lo, hi = nlo, nhi
                else: break
            step //= 2
    return lo, hi

def windows(O, consts, branches, plos):
    res = []
    for b in branches:
        face = O.K.toQ(b)
        pm = pmin_profile(face, consts)
        for plo in plos:
            for (a, bb) in runs(pm, float(plo)):
                if bb - a < 0.004: continue
                r = refine(O, b, a, bb, plo)
                if r: res.append((b, r[0], r[1], plo))
    return res

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'relaxed'
    if mode == 'merged-check':
        consts = dict(mMinus=Fr(377, 1000), sMinus=Fr(3, 100), eleven=Fr(11, 25))
        M.set_constants(**consts)
        des = dict(cB=Fr(3913, 4000), cL=Fr(101, 50), cCap=Fr(21, 200), w=Fr(22, 625), pB=Fr(99999, 100000), pL=Fr(101, 50), pCap=Fr(1097, 10000), numCap=Fr(3, 40))
        ws = [('C', Fr(5, 12), Fr(182, 335), Fr(1, 3)), ('capC', Fr(45, 128), Fr(3, 8), Fr(15, 32)), ('weakC7', Fr(3, 10), Fr(199, 356), Fr(1, 3)),
              ('capP', Fr(17, 47), Fr(9, 20), Fr(3, 8)), ('capP', Fr(2, 5), Fr(13, 27), Fr(6, 13)), ('capP', Fr(2, 5), Fr(39, 79), Fr(28, 57)),
              ('capP', Fr(63, 128), Fr(2031, 4096), Fr(255, 512)), ('capP', Fr(2031, 4096), Fr(8139, 16384), Fr(1023, 2048))]
        for N in (6324867, 6324868):
            K, th, h = buildK(N, des)
            O = cover3.Oracle(K)
            print('merged-check N', N, 'windows ok', all(O.window_ok(*w) for w in ws))
            ok, res = O.run(ws, verbose=True)
            print('  -> cover', ok)
        sys.exit()
    Lend = Fr(sys.argv[2]) if len(sys.argv) > 2 else Fr(101, 50)
    capL = Fr(1, 10) + Fr(3, 50) * (Fr(5143, 2000) - Lend)
    consts = dict(mMinus=Fr(3, 10), sMinus=Fr(1, 10000), eleven=Fr(1, 2))
    M.set_constants(**consts)
    des = dict(cB=Fr(99999, 100000), cL=Lend, cCap=capL, w=Fr(1, 100), pB=Fr(99999, 100000), pL=Lend, pCap=Fr(12, 100), numCap=Fr(3, 40))
    plos = [Fr(0), Fr(1, 4), Fr(3, 8), Fr(7, 16), Fr(15, 32), Fr(31, 64), Fr(63, 128), Fr(127, 256), Fr(255, 512)]
    t = time.time()
    th_est = {Fr(101, 50): 0.873432378, Fr(401, 200): 0.873411973, Fr(20001, 10000): 0.873405237}.get(Lend, 0.8734)
    N0 = int((1 - th_est) * 5e7) - 30
    K, th, h = buildK(N0, des)
    O = cover3.Oracle(K)
    ws = windows(O, consts, ('C', 'capC', 'capP'), plos)
    print('Lend', Lend, 'windows', len(ws), '%.0fs' % (time.time() - t), flush=True)
    for w in ws: print('   ', w[0], float(w[1]), float(w[2]), w[3])
    best = None
    for N in range(N0, N0 + 60, 3):
        K, th, h = buildK(N, des)
        O = cover3.Oracle(K)
        ok, res = O.run(ws, edges=['newTop'])
        print('  N', N, 'theta %.8f' % float(th), 'newTop ok' if ok else 'FAIL at %s' % [float(v) for v in res['newTop']['fail']], flush=True)
        if ok: best = N
        else: break
    if best:
        K, th, h = buildK(best, des)
        O = cover3.Oracle(K)
        ok, res = O.run(ws, verbose=True)
        print('BEST N', best, 'theta = %.8f' % float(1 - Fr(best, 50000000)), 'all edges ok', ok)
