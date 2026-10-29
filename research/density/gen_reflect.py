"""Reflective certificates for the marked HIGH gate of a density step (Lean: `Cert/Reflect.lean`).

For a step `S = (B0, L0, c0, B, L, A, D, r)` and a branch `(i, j)`, `Reflect.fOf S (brIJ S)` is the
trivariate polynomial `F(v, t, p) = cNumY - r E cDenY` (lists of lists of lists of rationals: `t`-index,
`p`-index, `v`-coefficients).  `F > 0` on `[0, a] x [0, 1] x [0, 1/2]` (`a = c - s0`) gives `r <= gHighM`.
The kernel checks `Reflect.checkF (fOf S (brIJ S)) a Dn X L T`: the coefficients of `Dn F(a y, t, p)` are
integers and PR 76's `IPoly.checkZ` accepts them with the tree `T` (bisections in `u = t` and `p`; at every
leaf, each of the 16 tensor Bernstein coefficients, a polynomial in `y`, is positive on `[0, 1]` by `tm1`
on a list of dyadic intervals).

This module mirrors the Lean list arithmetic exactly (list lengths included), searches the trees and
computes `Dn`, `X`, `L`; `render_marked` writes the Lean text of `markedHigh` for a step file.
"""
from fractions import Fraction as Fr
from math import lcm
import sys

sys.path.insert(0, __file__.rsplit('/', 2)[0] + '/faceless-chain')
import ipoly as IP  # noqa: E402  (integer polynomial mirror of PR 76's `IPoly`)

# ---------------------------------------------------------------------------------------------------
# Exact mirror of `Faceless.Poly`, `Reflect.P2`, `Reflect.P3` (structural recursion, no trimming)


def p_add(p, q):
    if not p:
        return list(q)
    if not q:
        return list(p)
    return [p[0] + q[0]] + p_add(p[1:], q[1:])


def p_smul(c, p):
    return [c * x for x in p]


def p_mul(p, q):
    if not p:
        return []
    return p_add(p_smul(p[0], q), [Fr(0)] + p_mul(p[1:], q))


def p2_add(p, q):
    if not p:
        return list(q)
    if not q:
        return list(p)
    return [p_add(p[0], q[0])] + p2_add(p[1:], q[1:])


def p2_smul(c, p):
    return [p_mul(c, x) for x in p]


def p2_mul(p, q):
    if not p:
        return []
    return p2_add(p2_smul(p[0], q), [[]] + p2_mul(p[1:], q))


def p3_add(p, q):
    if not p:
        return list(q)
    if not q:
        return list(p)
    return [p2_add(p[0], q[0])] + p3_add(p[1:], q[1:])


def p3_smul(c, p):
    return [p2_mul(c, x) for x in p]


def p3_mul(p, q):
    if not p:
        return []
    return p3_add(p3_smul(p[0], q), [[]] + p3_mul(p[1:], q))


def p3_cmul(c, p):
    return p3_smul([[Fr(c)]], p)


def p3_sub(p, q):
    return p3_add(p, p3_cmul(-1, q))


def lv(q):
    return [[list(q)]]


def lc(c):
    return [[[Fr(c)]]]


TP = [[], [[Fr(1)]]]
PP_ = [[[], [Fr(1)]]]


class StepQ:
    def __init__(self, B0, L0, c0, B, L, A, D, r):
        self.B0, self.L0, self.c0, self.B, self.L, self.A, self.D, self.r = map(Fr, (B0, L0, c0, B, L, A, D, r))

    @property
    def s0(self):
        return (self.B0 - self.B) / (self.L0 - self.L)

    @property
    def K(self):
        return Fr(999, 1000) * self.L0 * self.A

    @property
    def Xv(self):
        return [Fr(1), self.D]

    @property
    def Av(self):
        return [Fr(0), self.A]

    @property
    def Wv(self):
        return [self.s0, Fr(1)]

    @property
    def Ev(self):
        return [(self.L0 - self.L) + (6 * self.B0 - self.L0) * self.A, (self.L0 - self.L) * self.D]


def Ypoly(S):
    return p3_add(lc(S.K), p3_mul(TP, p3_sub(p3_cmul(Fr(3, 4), lv(S.Ev)), lc(S.K))))


def Fpoly(S, U, aU, bU, eU):
    X = lv(S.Xv)
    AV = lv(S.Av)
    W = lv(S.Wv)
    E = lv(S.Ev)
    Y = Ypoly(S)
    XA6 = p3_sub(X, p3_cmul(6, AV))
    WXA = p3_sub(p3_mul(W, X), AV)
    five = p3_sub(p3_cmul(5, E), p3_cmul(6, Y))
    den = p3_add(p3_sub(p3_cmul(Fr(15, 2), p3_mul(E, U)), p3_cmul(3, p3_mul(Y, U))), p3_mul(five, eU))
    t1 = p3_mul(Y, p3_add(p3_cmul(5, p3_mul(p3_mul(XA6, U), E)),
                          p3_mul(five, p3_add(p3_mul(aU, WXA), p3_mul(bU, XA6)))))
    one2p = p3_sub(lc(1), p3_cmul(2, PP_))
    t2 = p3_mul(p3_mul(Y, p3_sub(p3_mul(one2p, WXA),
                                 p3_sub(p3_mul(p3_sub(lc(S.B), p3_mul(lc(S.L - 1), W)), X), AV))), den)
    t3 = p3_mul(p3_mul(E, AV), den)
    return p3_sub(p3_add(p3_add(t1, t2), t3), p3_cmul(S.r, p3_mul(p3_mul(E, X), den)))


def branch_data(S, k):
    """`Reflect.brIJ S` as (U, aU, bU, eU)."""
    if k == (0, 0):
        return lc(1), p3_cmul(17, PP_), [], []
    if k == (0, 1):
        return lc(1), p3_cmul(16, PP_), p3_cmul(S.c0, PP_), []
    if k == (0, 2):
        u = p3_sub(lc(S.L0), p3_cmul(2, PP_))
        return u, p3_cmul(16, p3_mul(PP_, u)), p3_cmul(S.B0, PP_), PP_
    if k == (1, 0):
        u = p3_sub(lc(1), PP_)
        return u, p3_mul(PP_, u), PP_, PP_
    if k == (1, 1):
        u = p3_sub(lc(1), PP_)
        return u, [], p3_add(PP_, p3_cmul(S.c0, p3_mul(PP_, u))), PP_
    if k == (1, 2):
        u = p3_sub(lc(1), PP_)
        w = p3_sub(lc(S.L0), p3_cmul(2, PP_))
        return (p3_mul(u, w), [], p3_add(p3_mul(PP_, w), p3_cmul(S.B0, p3_mul(PP_, u))),
                p3_add(p3_mul(PP_, w), p3_mul(PP_, u)))
    raise ValueError(k)


BRANCHES = ((0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2))


def fOf(S, k):
    return Fpoly(S, *branch_data(S, k))


def coefF(P, i, j):
    row = P[i] if i < len(P) else []
    return row[j] if j < len(row) else []


def scaleArg(a, q):
    if not q:
        return []
    return [q[0]] + p_smul(a, scaleArg(a, q[1:]))


def degOK(P):
    return len(P) <= 4 and all(len(r) <= 4 for r in P)


def p3_eval(P, v, t, x):
    s = Fr(0)
    for i, row in enumerate(P):
        for j, q in enumerate(row):
            s += sum(c * Fr(v) ** k for k, c in enumerate(q)) * Fr(t) ** i * Fr(x) ** j
    return s


# ---------------------------------------------------------------------------------------------------
# Integer data and the tree search (mirrors `IPoly.checkZ`, `treeZ`, `leafZ`, `posOnY`, `tm1Y`)


def int_data(P, a):
    """(Dn, c): `c[i][j] = Dn * coefF P i j (a y)` as integer lists (`Reflect.intC`)."""
    sc = [[scaleArg(a, coefF(P, i, j)) for j in range(4)] for i in range(4)]
    Dn = 1
    for i in range(4):
        for j in range(4):
            for c in sc[i][j]:
                Dn = lcm(Dn, c.denominator)
    c = [[[int(x * Dn) for x in sc[i][j]] for j in range(4)] for i in range(4)]
    return Dn, c


def parts1(c):
    """`PP.pack`'s `pos1`, `neg1` of every input polynomial: sums of positive and negative parts."""
    return ([[[sum(x for x in c[i][j] if x > 0)] for j in range(4)] for i in range(4)],
            [[[sum(-x for x in c[i][j] if x < 0)] for j in range(4)] for i in range(4)])


def cover(q, maxe):
    """Contiguous dyadic intervals of [0, 1] on which `tm1` holds for `q` (`posOnY ... 0 0 l`)."""
    return IP.dyadic_cover(q, 0, 0, maxe)


class Search:
    def __init__(self, c, maxe=24, maxdepth=14, max_leaves=4000):
        self.c = c
        self.p1, self.n1 = parts1(c)
        self.maxe, self.maxdepth, self.max_leaves = maxe, maxdepth, max_leaves
        self.leaves = 0
        self.need = []          # (e, k, M): constraints 2^{e(L-1)} M < 2^e X - k
        self.L = max(len(c[i][j]) for i in range(4) for j in range(4))

    def leaf(self, ka, m, kb, n):
        B = IP.ib33(self.c, ka, m, kb, n)
        P1 = IP.ib33(self.p1, ka, m, kb, n)
        N1 = IP.ib33(self.n1, ka, m, kb, n)
        br, need = [], []
        for I in range(4):
            for J in range(4):
                q = B[I][J]
                if not any(q):
                    return None
                l = cover(q, self.maxe)
                if l is None:
                    return None
                M = max(P1[I][J][0] if P1[I][J] else 0, N1[I][J][0] if N1[I][J] else 0)
                for (k, e) in l:
                    need.append((e, k, M))
                br.append(l)
        return br, need

    def find(self, ka, m, kb, n, depth=0):
        r = self.leaf(ka, m, kb, n)
        if r is not None:
            self.leaves += 1
            if self.leaves > self.max_leaves:
                raise RuntimeError('too many leaves')
            self.need += r[1]
            return ('leaf', r[0])
        if depth >= self.maxdepth:
            return None
        # interval widths: u has 2^-m, p has 2^-n (p in [0,1/2] at n = 1); split the wider first
        order = ('u', 'p') if m <= n - 1 else ('p', 'u')
        for dim in order:
            saved = (self.leaves, len(self.need))
            if dim == 'u':
                left = self.find(2 * ka, m + 1, kb, n, depth + 1)
                right = left and self.find(2 * ka + 1, m + 1, kb, n, depth + 1)
            else:
                left = self.find(ka, m, 2 * kb, n + 1, depth + 1)
                right = left and self.find(ka, m, 2 * kb + 1, n + 1, depth + 1)
            if left and right:
                return (dim, left, right)
            self.leaves, k = saved
            del self.need[k:]
        return None

    def run(self):
        T = self.find(0, 0, 0, 1)
        if T is None:
            raise RuntimeError('no tree found')
        L = max(self.L, 2)
        X = 2
        for (e, k, M) in self.need:
            X = max(X, (2 ** (e * (L - 1)) * M + k) // 2 ** e + 1)
        return T, L, X


def certify_branch(S, k, a, **kw):
    P = fOf(S, k)
    if not degOK(P):
        raise RuntimeError(f'branch {k}: degree check fails')
    Dn, c = int_data(P, a)
    T, L, X = Search(c, **kw).run()
    return {'branch': k, 'Dn': Dn, 'c': c, 'T': T, 'L': L, 'X': X}


# ---------------------------------------------------------------------------------------------------
# Independent checks of a certificate (exact replay of the kernel computation, in Python)


def tm1Y_ok(pos, neg, pos1, neg1, X, L, k, e):
    """`IPoly.tm1Y` on the packed parts (lists of naturals `pos`, `neg`, padded to `L`)."""
    s = 2 ** (e * (L - 1))
    Y = 2 ** e * X - k
    if not (k + 1 <= 2 ** e and s * pos1 < Y and s * neg1 < Y):
        return False
    # digits of s*A(X) in base Y are the coefficients of 2^{e(L-1)} A((k + t)/2^e) scaled to `t`
    def digits(v):
        out = []
        for _ in range(L):
            out.append(v % Y)
            v //= Y
        return out if v == 0 else None
    def packX(A):
        return sum(x * X ** i for i, x in enumerate(A))
    a, b = digits(s * packX(pos)), digits(s * packX(neg))
    if a is None or b is None:
        return False
    S_ = sum(abs(x - y) for x, y in zip(a[2:], b[2:]))
    return b[0] + S_ < a[0] and b[0] + b[1] + S_ < a[0] + a[1]


def replay(cert):
    """Replay `checkZ` exactly as the kernel does: packed parts through `pb33`, `posOnY`, `tm1Y`."""
    c, X, L, T = cert['c'], cert['X'], cert['L'], cert['T']
    if max(len(c[i][j]) for i in range(4) for j in range(4)) > L:
        return False
    pos = [[[max(x, 0) for x in c[i][j]] for j in range(4)] for i in range(4)]
    neg = [[[max(-x, 0) for x in c[i][j]] for j in range(4)] for i in range(4)]

    def node(T, ka, m, kb, n):
        if T[0] == 'leaf':
            P, N = IP.ib33(pos, ka, m, kb, n), IP.ib33(neg, ka, m, kb, n)
            for I in range(4):
                for J in range(4):
                    l = T[1][4 * I + J]
                    if not l:
                        return False
                    A = (P[I][J] + [0] * L)[:L]
                    Bn = (N[I][J] + [0] * L)[:L]
                    k0, e0 = 0, 0
                    for (k, e) in l:
                        if k0 * 2 ** e != k * 2 ** e0:
                            return False
                        if not tm1Y_ok(A, Bn, sum(A), sum(Bn), X, L, k, e):
                            return False
                        k0, e0 = k + 1, e
                    if k0 != 2 ** e0:
                        return False
            return True
        if T[0] == 'u':
            return node(T[1], 2 * ka, m + 1, kb, n) and node(T[2], 2 * ka + 1, m + 1, kb, n)
        return node(T[1], ka, m, 2 * kb, n + 1) and node(T[2], ka, m, 2 * kb + 1, n + 1)

    return node(T, 0, 0, 0, 1)


# ---------------------------------------------------------------------------------------------------
# Lean text


def lean_q(x):
    x = Fr(x)
    s = str(x.numerator) if x.denominator == 1 else f'{x.numerator}/{x.denominator}'
    return f'({s} : ℚ)' if x >= 0 else f'(({s}) : ℚ)'


def lean_tree(T):
    if T[0] == 'leaf':
        return '(.leaf [' + ', '.join('[' + ', '.join(f'({k}, {e})' for k, e in l) + ']' for l in T[1]) + '])'
    return f'(.{T[0]} {lean_tree(T[1])} {lean_tree(T[2])})'


def tree_size(T):
    if T[0] == 'leaf':
        return 1, sum(len(l) for l in T[1])
    a, b = tree_size(T[1]), tree_size(T[2])
    return a[0] + b[0], a[1] + b[1]


# ---------------------------------------------------------------------------------------------------
# Step files: replace the box-certified marked HIGH section of a gen_hybrid step file


REFLECT_IMPORT = 'import Submissions.arvi_density.Cert.Reflect'
UTREE = 'QRH.RepeatedMarks.Faceless.IPoly.UTreeI'
RESERVE = Fr(1, 10 ** 12)


def lean_rat(x):
    x = Fr(x)
    s = str(abs(x.numerator)) if x.denominator == 1 else f'{abs(x.numerator)} / {x.denominator}'
    return s if x >= 0 else f'-({s})'


def certify_step(st, r=RESERVE, **kw):
    S = StepQ(st['B0'], st['L0'], st['c0'], st['B'], st['L'], st['A'], st['D'], r)
    a = Fr(st['c']) - S.s0
    if a <= 0:
        raise RuntimeError('empty excess range')
    certs = [certify_branch(S, k, a, **kw) for k in BRANCHES]
    L = max(c['L'] for c in certs)
    X = max(c['X'] for c in certs)
    for c in certs:
        c['L'], c['X'] = L, X
        if not replay(c):
            raise AssertionError(f"replay of branch {c['branch']} failed")
    return S, a, certs, L, X


def render_reflect(S, a, certs, L, X, statement):
    """The Lean text replacing the marked HIGH section (inside the step namespace)."""
    out = []
    A = out.append
    A('/-! #### Marked HIGH gate: reflective certificates (`Cert/Reflect.lean`) -/')
    A('')
    A('/-- The rational data of the step: parent `G(B0, L0, c0)`, child `(B, L)`, selection `A, D`, reserve `r`. -/')
    A('def stepQ : Reflect.StepQ :=')
    A('  ⟨' + ', '.join(lean_rat(x) for x in (S.B0, S.L0, S.c0, S.B, S.L, S.A, S.D, S.r)) + '⟩')
    A('')
    for c in certs:
        i, j = c['branch']
        A(f'def tree{i}{j} : {UTREE} :=')
        A('  ' + lean_tree(c['T']))
        A('')
        A(f'theorem check{i}{j} : Reflect.checkF (Reflect.fOf stepQ (Reflect.br{i}{j} stepQ)) ({lean_rat(a)})')
        A(f"    {c['Dn']}")
        A(f'    {X} {L} tree{i}{j} = true := by')
        A('  decide +kernel')
        A('')
    A('/-! #### The marked HIGH field -/')
    A('')
    A(statement.rstrip() + '\n  Reflect.high_marked_of_checks stepQ'
      + ' (by norm_num [stepQ])' * 7
      + f' ({lean_rat(a)})\n    (by rw [cross_eq]; norm_num) (by norm_num) (by norm_num [stepQ])'
      + ' (by norm_num)' * 5
      + '\n    (fun v h0 _ => x_pos v h0) (fun v h0 _ => E_pos v h0) unifQLower unifQUpper unifRetainedWidth unifHLower'
      + f'\n    {X} {L} ' + ' '.join(str(c['Dn']) for c in certs)
      + '\n    ' + ' '.join(f'tree{i}{j}' for (i, j) in BRANCHES)
      + '\n    ' + ' '.join(f'check{i}{j}' for (i, j) in BRANCHES))
    A('')
    return '\n'.join(out)


def patch_step(text, st, **kw):
    """Replace the marked section of a gen_hybrid step file by reflective certificates."""
    start = text.index('/-! #### Marked HIGH gate')
    end = text.index('\nend Step_', start)
    old = text[start:end]
    s0 = old.index('theorem markedHigh')
    s1 = old.index(':= by\n', s0)
    statement = old[s0:s1] + ':='
    S, a, certs, L, X = certify_step(st, **kw)
    new = render_reflect(S, a, certs, L, X, statement)
    text = text[:start] + new + text[end:]
    if REFLECT_IMPORT not in text:
        text = text.replace('import Submissions.arvi_density.Source.HybridGatesMarked',
                            'import Submissions.arvi_density.Source.HybridGatesMarked\n' + REFLECT_IMPORT, 1)
    # header: describe the reflective marked gate instead of the boxes
    h0 = text.index('marked HIGH gate (repeated-mark gain, K = 8)')
    h1 = text.index('Arithmetic only.', h0)
    sizes = ', '.join(f"({c['branch'][0]},{c['branch'][1]}): {tree_size(c['T'])[0]} leaf/"
                      f"{tree_size(c['T'])[1]} intervals" for c in certs)
    text = (text[:h0] + f'marked HIGH gate (repeated-mark gain, K = 8) by reflective certificates '
            f'(`Cert/Reflect.lean`, research/density/gen_reflect.py) on v in [0, {lean_rat(a)}], t in [0, 1], '
            f'p in [0, 1/2]: {sizes}; reserve {lean_rat(S.r)}. ' + text[h1:])
    return text, certs


def main():
    import argparse, json, os, time
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('steps', help='steps json (research/chain/steps_*.json)')
    ap.add_argument('src', help='directory of the gen_hybrid step files (Step_NNN.lean)')
    ap.add_argument('dest', help='output directory')
    ap.add_argument('--only', type=str, default=None, help='comma-separated step numbers')
    a = ap.parse_args()
    steps = json.load(open(a.steps))
    os.makedirs(a.dest, exist_ok=True)
    only = None if a.only is None else {int(x) for x in a.only.split(',')}
    for n, st in enumerate(steps, 1):
        if only is not None and n not in only:
            continue
        name = f'Step_{n:03d}.lean'
        t0 = time.time()
        text = open(os.path.join(a.src, name), encoding='utf-8').read()
        new, certs = patch_step(text, st)
        open(os.path.join(a.dest, name), 'w', encoding='utf-8').write(new)
        sz = [tree_size(c['T']) for c in certs]
        print(f'{name}: leaves {[s[0] for s in sz]} intervals {[s[1] for s in sz]} '
              f'{len(new) / 1e3:.0f} kB ({time.time() - t0:.1f}s)', flush=True)


if __name__ == '__main__':
    main()
