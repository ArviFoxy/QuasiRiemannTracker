"""Simulate EdgeCertificates' kernel cover (first fit: old, then any containing window; else split) with the mirror."""
import sys, time
from fractions import Fraction as Fr
import mirror as M
from windows import parse_windows

K = M.Const()
HALF = Fr(1, 2)
CACHE = {}


def rowpoly(e, cand):
    k = (e, cand)
    if k not in CACHE:
        CACHE[k] = M.rowOld(K, e) if cand == 'old' else M.rowBr(K, e, K.toQ(cand))
    return CACHE[k]


def leafOK(e, ws, a, b, c, d, log):
    if M.bernCheck(rowpoly(e, 'old'), a, b, c, d):
        log.append(('old', a, b, c, d))
        return True
    for i, w in enumerate(ws):
        if w[1] <= a and b <= w[2] and w[3] <= c and d <= HALF:
            if M.bernCheck(rowpoly(e, w[0]), a, b, c, d):
                log.append((i, a, b, c, d))
                return True
    return False


def coverOK(e, ws, k, a, b, c, d, log, depth=0, stat=None):
    stat['maxdepth'] = max(stat['maxdepth'], depth)
    if leafOK(e, ws, a, b, c, d, log):
        return True
    if k == 0:
        return False
    if 3 * (d - c) <= 2 * (b - a):
        m = (a + b) / 2
        return coverOK(e, ws, k - 1, a, m, c, d, log, depth + 1, stat) and coverOK(e, ws, k - 1, m, b, c, d, log, depth + 1, stat)
    m = (c + d) / 2
    return coverOK(e, ws, k - 1, a, b, c, m, log, depth + 1, stat) and coverOK(e, ws, k - 1, a, b, m, d, log, depth + 1, stat)


def run(ws, k=30, verbose=False):
    tot = 0
    res = {}
    for e in ['oldSmall', 'oldSwitch', 'newSwitch', 'newTop']:
        M.STATS['bern'] = 0
        log = []
        stat = {'maxdepth': 0}
        t = time.time()
        ok = coverOK(e, ws, k, Fr(0), Fr(3, 4), Fr(0), HALF, log, 0, stat)
        used = sorted(set(l[0] for l in log if l[0] != 'old'))
        res[e] = (ok, len(log), M.STATS['bern'], stat['maxdepth'], used)
        tot += M.STATS['bern']
        print(f'  {e:9s} ok={ok} leaves={len(log)} bernstein tests={M.STATS["bern"]} maxdepth={stat["maxdepth"]} '
              f'windows used={used} ({time.time() - t:.1f}s)')
    return res, tot


if __name__ == '__main__':
    old31 = [(w['branch'], w['dlo'], w['dhi'], w['plo']) for w in parse_windows()]
    print('existing 31 windows:')
    run(old31)
    small = [('C', Fr(27, 64), Fr(35, 64), Fr(1, 4)),
             ('capP', Fr(1, 4), Fr(7, 16), Fr(1, 4)),
             ('capC', Fr(21, 64), Fr(51, 128), Fr(7, 16)),
             ('capC', Fr(21, 64), Fr(25, 64), Fr(13, 32)),
             ('weakC7', Fr(51, 128), Fr(7, 16), Fr(3, 8)),
             ('capP', Fr(69, 128), Fr(141, 256), Fr(31, 64))]
    print('small window set:')
    for w in small:
        print('   ', w[0], [str(v) for v in w[1:]], M.windowCheck(K.toQ(w[0]), 6, w[1], w[2], w[3]))
    run(small)
