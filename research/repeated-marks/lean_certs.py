"""Exact checker and Lean emitter for the repeated-mark source graph (SourceValid2).

Mirrors the Lean definitions exactly (all arithmetic in Fractions):
* Collet's `SourceValid` conjuncts (Record1252270103Finite/SourceFormulas.lean) with the six
  HIGH facet gates (densityGate j < 6) replaced by the constant 1 when a HIGH parent is present;
* the repeated-mark HIGH gate `gateG` (Finite/HighGate.lean), its bicubic interpolation
  `bicubic`, and the bisection checker `checkBox` (Gain/Bernstein2.lean).

usage: python3 lean_certs.py CHAIN.json COPIES OUTDIR
"""
import sys, json, os
from fractions import Fraction as Fr

ALLOW, LOWFEE, HIGHFEE = Fr(1, 10**12), Fr(1, 10**8), Fr(1, 10**7)
NATURAL = dict(B=Fr(1), L=Fr(11243277, 2500000), cap=Fr(11, 200), q=Fr(0),
               allowance=ALLOW, lowFee=LOWFEE, highFee=HIGHFEE)
KN = Fr(11243277, 2500000)

def crossing(n, low): return (low['B'] - n['B'])/(low['L'] - n['L'])
def sourceDen(n, low): return 1 - 6*n['q']*low['B']/low['L']
def sourceT(n, b): return n['B'] - n['L']*(b - n['allowance'])
def sourceA(n, low, b):
    return (n['q']*(b + (sourceT(n, b) - low['B'])/low['L']) + n['lowFee'])/sourceDen(n, low)
def sourceF(n, low, b): return 1 - 6*sourceA(n, low, b)

def scalarGate(n, low, b):
    a = sourceA(n, low, b); t = sourceT(n, b); T = t + b; F = sourceF(n, low, b); e = n['allowance']
    Lref = Fr(49, 100) - KN*b
    return [sourceDen(n, low), b - 2*e, a, Fr(1, 75) - a, F - T/2 - 4*e,
            low['B']*F - t - b - 4*e, 1 - n['q']*low['cap'],
            n['lowFee'] - (n['q']*low['B']/low['L'] + n['q']*low['cap'] + 4)*e - 10*e,
            a - 20*e, Lref, 1 - Lref - Fr(1, 2) - KN*b - 10*e,
            Fr(5, 6) + Fr(499, 1000)*Lref - T - 9*a - n['highFee'],
            1 - T - 5*a - n['highFee'], 1 - Fr(1, 50) - T - 4*a - n['highFee'],
            1 - Fr(1, 50) - T - Fr(9, 2)*a - n['highFee'], Lref - 7*a - n['highFee']]

def weakCap(n, low, b):
    F = sourceF(n, low, b)
    return low['cap']*F - (low['B']*F - sourceT(n, b))/low['L']

def densityGate2(n, low, high, b, nu, j):
    a = sourceA(n, low, b); T = sourceT(n, b) + b; S = b - 2*n['allowance']
    F = sourceF(n, low, b) - n['allowance']; fee = n['highFee']
    t = 15 - 6*nu; w = 5 - 6*nu
    H = (a - nu*T)*t + (10 - 60*a)*nu
    fixed = H + (nu*F/2 - (1 - nu)*b - fee)*t
    core = H + (Fr(5, 6)*F - (1 - nu)*b - fee)*t - 10*nu*F
    tiny = H + (nu*(F - Fr(1, 50))/2 - (1 - nu)*b - fee)*t - 10*nu*Fr(1, 50)
    if high is None:
        D2 = 115 - 54*nu; D3 = 185 - 138*nu
        return [H + 3*nu*w*S - fee*t, H*D2 + 14*nu*w*S*t + 2*nu*w*w*F - fee*t*D2,
                H*D3 + 16*nu*w*w*F - fee*t*D3, fixed, core, tiny, 1, 1, 1][j]
    return [1, 1, 1, 1, 1, 1, fixed, core, tiny][j]

def cubic4(f):
    f0, f1, fm, f2 = f(Fr(0)), f(Fr(1)), f(Fr(-1)), f(Fr(2))
    return [f0, (-f2 + 6*f1 - 3*f0 - 2*fm)/6, (f1 + fm - 2*f0)/2, (f2 - 3*f1 + 3*f0 - fm)/6]

def cubicBernstein(f, l, r):
    c = cubic4(f)
    a0 = c[0] + c[1]*l + c[2]*l**2 + c[3]*l**3
    a1 = (r - l)*(c[1] + 2*c[2]*l + 3*c[3]*l**2)
    a2 = (r - l)**2*(c[2] + 3*c[3]*l)
    a3 = (r - l)**3*c[3]
    return [a0, a0 + a1/3, a0 + 2*a1/3 + a2/3, a0 + a1 + a2 + a3]

# ---------- the repeated-mark HIGH gate ----------
BRANCHES = [(i, j) for i in range(2) for j in range(3)]

def gateG(a, T, S, F, fee, K, B, L, hc, nu, p, k):
    i, j = k
    dI = [1, 1 - p][i]; eP = [1, 1, L - 2*p][j]; gP = [1, 1, L][j]
    bI = [2*p*K*S, p*F][i]; hP = [2*p*S, 2*p*hc*F, 2*p*B*F][j]
    M = 12*nu*(dI*eP) + (5 - 6*nu)*(2*eP + dI*gP)
    N = 10*F*(dI*eP) + (5 - 6*nu)*(2*eP*bI + dI*hP)
    t = 15 - 6*nu
    return M*((a - nu*T)*t + (10 - 60*a)*nu + t*(1 - 2*p)*nu*S - 10*nu*F - fee*t) + nu*t*N

def highGate(n, low, h, copies, b, nu, p, k):
    return gateG(sourceA(n, low, b), sourceT(n, b) + b, b - 2*n['allowance'],
                 sourceF(n, low, b) - n['allowance'], n['highFee'], copies,
                 h['B'], h['L'], h['cap'], nu, p, k)

def bicubic(f):
    # c[i][j] = cubic4 (fun x => cubic4 (fun y => f x y) j) i
    cols = {}
    def g(x):
        if x not in cols:
            cols[x] = cubic4(lambda y: f(x, y))
        return cols[x]
    return [[cubic4(lambda x: g(x)[j])[i] for j in range(4)] for i in range(4)]

def shift3(c, a, s):
    return [c[0] + c[1]*a + c[2]*a**2 + c[3]*a**3, s*(c[1] + 2*c[2]*a + 3*c[3]*a**2),
            s**2*(c[2] + 3*c[3]*a), s**3*c[3]]

def bern3(e):
    return [e[0], e[0] + e[1]/3, e[0] + 2*e[1]/3 + e[2]/3, e[0] + e[1] + e[2] + e[3]]

def bern33(c, a, s, b, t):
    # bern33 c a s b t I J = bern3 (fun j => bern3 (fun i => shift3 (fun i' => shift3 (c i') b t j) a s i) I) J
    sy = [shift3(c[i1], b, t) for i1 in range(4)]          # sy[i'][j]
    inner = []                                               # inner[j][I]
    for j in range(4):
        col = [sy[i1][j] for i1 in range(4)]
        inner.append(bern3(shift3(col, a, s)))
    return [[bern3([inner[j][I] for j in range(4)])[J] for J in range(4)] for I in range(4)]

def leafOK(c, a, s, b, t):
    return all(x > 0 for row in bern33(c, a, s, b, t) for x in row)

def minbern(c, a, s, b, t):
    return min(x for row in bern33(c, a, s, b, t) for x in row)

def find_tree(c, a, s, b, t, s0, t0, depth=0, maxdepth=40):
    """returns a nested tuple tree ('leaf' | ('nu', l, r) | ('p', l, r)) or None.
    The split direction is chosen greedily: the one whose worse child has the larger
    minimum Bernstein coefficient."""
    if leafOK(c, a, s, b, t):
        return 'leaf'
    if depth >= maxdepth:
        return None
    mn = min(minbern(c, a, s/2, b, t), minbern(c, a + s/2, s/2, b, t))
    mp = min(minbern(c, a, s, b, t/2), minbern(c, a, s, b + t/2, t/2))
    if mn >= mp:
        l = find_tree(c, a, s/2, b, t, s0, t0, depth + 1, maxdepth)
        if l is None: return None
        r = find_tree(c, a + s/2, s/2, b, t, s0, t0, depth + 1, maxdepth)
        if r is None: return None
        return ('nu', l, r)
    else:
        l = find_tree(c, a, s, b, t/2, s0, t0, depth + 1, maxdepth)
        if l is None: return None
        r = find_tree(c, a, s, b + t/2, t/2, s0, t0, depth + 1, maxdepth)
        if r is None: return None
        return ('p', l, r)

def tree_lean(T):
    if T == 'leaf':
        return '.leaf'
    return f"(.{T[0]} {tree_lean(T[1])} {tree_lean(T[2])})"

def tree_leaves(T):
    return 1 if T == 'leaf' else tree_leaves(T[1]) + tree_leaves(T[2])

def check_node(n, low, high, copies):
    """Collet's conjuncts with densityGate2, then the HIGH trees. Returns (ok, msgs, trees)."""
    msgs = []
    cr = crossing(n, low)
    conj = [0 < n['B'], n['B'] <= 1, 1 < n['L'], 0 <= n['cap'], n['cap'] < 1,
            Fr(1, 2) <= n['q'], n['q'] <= Fr(3, 4), n['L'] < low['L'],
            0 <= cr, cr <= n['cap'], cr <= low['cap']]
    if high is not None:
        h = high
        conj.append(Fr(22, 23) <= h['B'] and h['B'] <= 1 and 1 < h['L'] and 0 <= h['cap'] and h['cap'] < 1)
    for idx, c in enumerate(conj):
        if not c: msgs.append(f"conjunct {idx} fails")
    trees = {}
    for b in (cr, n['cap']):
        sg = scalarGate(n, low, b)
        for j, v in enumerate(sg):
            if not v > 0: msgs.append(f"scalar gate {j} at b={float(b):.6f}: {float(v):.3e}")
        wc = weakCap(n, low, b)
        if not wc >= 0: msgs.append(f"weak cap at b={float(b):.6f}: {float(wc):.3e}")
        for j in range(9):
            bc = cubicBernstein(lambda nu: densityGate2(n, low, high, b, nu, j), n['q'], Fr(3, 4))
            if not all(x > 0 for x in bc):
                msgs.append(f"density gate {j} at b={float(b):.6f}: min {float(min(bc)):.3e}")
        if high is not None:
            for k in BRANCHES:
                c = bicubic(lambda x, y: highGate(n, low, high, copies, b, x, y, k))
                s0 = Fr(3, 4) - n['q']; t0 = Fr(1, 2)
                T = find_tree(c, n['q'], s0, Fr(0), t0, s0, t0)
                if T is None:
                    msgs.append(f"HIGH branch {k} at b={float(b):.6f}: no tree")
                trees[(b, k)] = T
    return (len(msgs) == 0), msgs, trees

def load_chain(path):
    ch = json.load(open(path))
    nodes = []
    for nd in ch:
        nodes.append(dict(B=Fr(nd['B']), L=Fr(nd['L']), cap=Fr(nd['cap']), q=Fr(nd['q']),
                          allowance=ALLOW, lowFee=LOWFEE, highFee=HIGHFEE, pivot=nd['pivot']))
    return nodes

if __name__ == '__main__':
    chain = load_chain(sys.argv[1]); copies = Fr(int(sys.argv[2]))
    outdir = sys.argv[3] if len(sys.argv) > 3 else None
    prev = NATURAL
    allok = True
    results = []
    for idx, n in enumerate(chain):
        ok, msgs, trees = check_node(n, prev, prev, copies)
        nl = sum(tree_leaves(T) for T in trees.values() if T is not None)
        print(f"node {idx:02d} pivot {n['pivot']}: {'OK' if ok else 'FAIL'} leaves={nl} {msgs[:4]}", flush=True)
        allok &= ok
        results.append((n, prev, trees))
        prev = n
    print("ALL OK" if allok else "SOME FAILED")
    if outdir:
        json.dump([{ 'node': idx, 'trees': {f"{float(b)}|{k}": tree_lean(T) for (b, k), T in tr.items()}}
                   for idx, (n, p, tr) in enumerate(results)], open(os.path.join(outdir, 'trees.json'), 'w'), indent=0)
