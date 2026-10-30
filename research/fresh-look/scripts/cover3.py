"""Exact kernel-cover oracle (mirror of CoverQ.lean) for an arbitrary constant set K = mirror2.Const(...)."""
import time
from fractions import Fraction as Fr
import mirror3 as M

HALF = Fr(1, 2)
EDGES = ['oldSmall', 'oldSwitch', 'newSwitch', 'newTop']


class Oracle:
    def __init__(self, K):
        self.K = K
        self.cache = {}
        self.gcache = {}

    def rowpoly(self, e, cand):
        k = (e, cand)
        if k not in self.cache:
            self.cache[k] = M.rowOld(self.K, e) if cand == 'old' else M.rowBr(self.K, e, self.K.toQ(cand))
        return self.cache[k]

    def window_ok(self, branch, dlo, dhi, plo, k=0):
        """WinQ.ok k  (bounds + 15 guards by posBox depth k)"""
        if not (branch != 'old' and 0 <= dlo and dhi <= Fr(3, 4) and 0 <= plo <= HALF):
            return False
        return M.windowCheck(self.K.toQ(branch), k, dlo, dhi, plo)

    def leafOK(self, e, ws, a, b, c, d, log):
        if M.bernCheck(self.rowpoly(e, 'old'), a, b, c, d):
            log.append(('old', a, b, c, d))
            return True
        for i, w in enumerate(ws):
            if w[1] <= a and b <= w[2] and w[3] <= c and d <= HALF:
                if M.bernCheck(self.rowpoly(e, w[0]), a, b, c, d):
                    log.append((i, a, b, c, d))
                    return True
        return False

    def coverOK(self, e, ws, k, a, b, c, d, log, depth, stat):
        stat['maxdepth'] = max(stat['maxdepth'], depth)
        if self.leafOK(e, ws, a, b, c, d, log):
            return True
        if k == 0:
            stat.setdefault('fail', (a, b, c, d))
            return False
        if 3 * (d - c) <= 2 * (b - a):
            m = (a + b) / 2
            return (self.coverOK(e, ws, k - 1, a, m, c, d, log, depth + 1, stat) and
                    self.coverOK(e, ws, k - 1, m, b, c, d, log, depth + 1, stat))
        m = (c + d) / 2
        return (self.coverOK(e, ws, k - 1, a, b, c, m, log, depth + 1, stat) and
                self.coverOK(e, ws, k - 1, a, b, m, d, log, depth + 1, stat))

    def run(self, ws, k=30, edges=EDGES, verbose=False):
        res = {}
        allok = True
        for e in edges:
            M.STATS['bern'] = 0
            log = []
            stat = {'maxdepth': 0}
            t = time.time()
            ok = self.coverOK(e, ws, k, Fr(0), Fr(3, 4), Fr(0), HALF, log, 0, stat)
            used = sorted(set(l[0] for l in log if l[0] != 'old'))
            res[e] = dict(ok=ok, leaves=len(log), tests=M.STATS['bern'], maxdepth=stat['maxdepth'], used=used,
                          fail=stat.get('fail'), log=log)
            allok &= ok
            if verbose:
                print('  %-9s ok=%s leaves=%d tests=%d maxdepth=%d windows used=%s%s (%.1fs)' % (
                    e, ok, len(log), M.STATS['bern'], stat['maxdepth'], used,
                    '' if ok else ' FAIL at ' + str(stat.get('fail')), time.time() - t))
        return allok, res
