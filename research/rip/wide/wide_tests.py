"""Fresh-look tests for the randomized-dictionary (wide atoms) proposal.  See FRESH_LOOK.md.

The sextic table is built from prime factorizations: a source x (primary, squarefree norm, coprime to 6) is
x = (-1)^(k-1) * pi_1...pi_k with primary split primes pi_i, so
    chi_z(x) = chi_z(-1)^(k-1) * prod_i chi_z(pi_i),   chi_z(pi) = prod_{rho | z} (pi/rho)_6.
That lets the random models below share the sextic family's slot data exactly (so W is the same set) and
randomize only the Frobenius data at non-slot source primes.

Dictionaries compared on the slot-selected row set W (top rho*R rows by |T(z)|, T = sum over split slot primes
of norm in [P0, 2 P0], as in ../zfamily.py):
  sextic : the true rows.
  RMM-S  : random completely multiplicative rows, independent across z, slot values and the mask (pi | z) exact.
  BRM-S  : bi-multiplicative random model: (pi/rho)_6 replaced by i.i.d. sixth roots of unity for every row prime
           rho and non-slot source prime pi (rows sharing prime factors stay correlated, as in the true family).
  HYB    : design D2, quadratic part exact, cubic part random multiplicative (slot-exact).
  SCHUR  : design D2', quadratic part exact times i.i.d. cube roots of unity per entry (a random Schur multiplier).
Quantities (Gram normalized to unit diagonal): top eigenvalue; trace moments tr(G_W^p); the Hadamard powers
||G_W^{o m} - I|| (design D3); coherence.  Run: python3 -I wide_tests.py B L P0 [nsamp] [seed] [models] [hadamard 0/1] [rho list]"""
import sys, os, math, json, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
from zomega import norm, primes_list  # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2]); P0 = int(sys.argv[3])
NS = int(sys.argv[4]) if len(sys.argv) > 4 else 40
SEED = int(sys.argv[5]) if len(sys.argv) > 5 else 11
MODELS = sys.argv[6].split(',') if len(sys.argv) > 6 else ['RMM', 'BRM', 'HYB', 'SCHUR']
HAD = (sys.argv[7] != '0') if len(sys.argv) > 7 else True
RHOS = [float(v) for v in sys.argv[8].split(',')] if len(sys.argv) > 8 else [0.5, 0.25, 0.1, 0.05]
rng = np.random.default_rng(SEED)
zeta6 = np.exp(2j * np.pi * np.arange(6) / 6)
t0 = time.time()
PR = primes_list(max(2 * B, L)); PR.sort(key=lambda x: x.N)
rows = []
def rec(start, N, facs):
    if B <= N <= 2 * B: rows.append(tuple(facs))
    for j in range(start, len(PR)):
        if N * PR[j].N > 2 * B: break
        rec(j + 1, N * PR[j].N, facs + [j])
rec(0, 1, [])
R = len(rows)
above = {}
for j, pr in enumerate(PR):
    if pr.split: above.setdefault(pr.p, []).append(j)
def factor(n):
    out, d = [], 3
    while d * d <= n:
        while n % d == 0: out.append(d); n //= d
        d += 2
    if n > 1: out.append(n)
    return out
m = int(math.isqrt(4 * L)) + 3
src, sfac = [], []
gens = {}  # PR index of a split prime ideal -> its primary generator
for a in range(-m, m + 1):
    if a % 3 != 2: continue
    for b in range(-(m // 3) * 3, m + 1, 3):   # b = 0 mod 3 (primary)
        n = norm(a, b)
        if not (1 < n <= L) or n % 2 == 0 or n % 3 == 0: continue
        ps = factor(n)
        if len(set(ps)) < len(ps): continue
        f = []
        for p in ps:
            js = [j for j in above[p] if (a + b * PR[j].r) % p == 0]
            assert len(js) == 1
            f.append(js[0])
        src.append((a, b)); sfac.append(f)
        if len(ps) == 1: gens[f[0]] = (a, b)
S = len(src)
sp = sorted(gens); spi = {j: i for i, j in enumerate(sp)}; nP = len(sp)
A = np.zeros((S, nP)); kk = np.zeros(S)
for s, f in enumerate(sfac):
    for j in f: A[s, spi[j]] = 1
    kk[s] = len(f)
used = sorted({j for r in rows for j in r}); ui = {j: i for i, j in enumerate(used)}
Rinc = np.zeros((R, len(used)))
for r, f in enumerate(rows):
    for j in f: Rinc[r, ui[j]] = 1
SY = np.zeros((len(used), nP)); SZ = np.zeros((len(used), nP))
for i, j in enumerate(used):
    for q, jj in enumerate(sp):
        k = PR[j].sym(gens[jj])
        if k is None: SZ[i, q] = 1
        else: SY[i, q] = k
em1 = np.array([PR[j].sym((-1, 0)) for j in used], float)
ez = (Rinc @ em1) % 6
Zz = (Rinc @ SZ) > 0                       # pi | z
slot = np.array([P0 <= PR[j].N <= 2 * P0 for j in sp])
zeroE = (Zz.astype(float) @ A.T) > 0       # gcd(x, z) != 1
def table(K):  # K: R x nP exponents (ignored where pi | z)
    ex = (K @ A.T + np.outer(ez, kk - 1)) % 6
    return np.where(zeroE, 0, zeta6[np.rint(ex).astype(int) % 6])
Ktrue = (Rinc @ SY) % 6
E = table(Ktrue)
# validation against the direct symbol computation of ../zfamily.py on a sample of rows
chk = rng.choice(R, min(40, R), replace=False); bad = 0
for r in chk:
    for s in rng.choice(S, 60, replace=False):
        tot, z = 0, False
        for j in rows[r]:
            k = PR[j].sym(src[s])
            if k is None: z = True; break
            tot += k
        v = 0 if z else zeta6[tot % 6]
        bad += abs(v - E[r, s]) > 1e-9
assert bad == 0, 'factorized table disagrees with direct symbols'
T = np.where(Zz[:, slot], 0, zeta6[np.rint(Ktrue[:, slot]).astype(int) % 6]).sum(1)
order = np.argsort(-np.abs(T))
def rand_exps(shape, step=1):
    return step * rng.integers(0, 6 // step, size=shape).astype(float)
def model(kind):
    if kind == 'RMM':
        K = np.where(slot[None, :], Ktrue, rand_exps((R, nP)))
    elif kind == 'BRM':
        SYr = np.where(slot[None, :], SY, rand_exps(SY.shape))
        K = (Rinc @ SYr) % 6
    elif kind == 'HYB':
        cub = np.where(slot[None, :], (-2 * Ktrue) % 6, rand_exps((R, nP), 2))
        K = (3 * Ktrue + cub) % 6
    elif kind == 'SCHUR':
        Eq = table((3 * Ktrue) % 6)
        return Eq * zeta6[2 * rng.integers(0, 3, size=Eq.shape)]
    return table(K)
def stats(Ew, plist, mlist):
    G = Ew @ Ew.conj().T; d = np.real(np.diag(G)); Gn = G / np.sqrt(np.outer(d, d))
    lam = np.linalg.eigvalsh(Gn)
    mom = {p: float(np.sum(lam ** p)) for p in plist}
    cmom = {q: float(np.sum((lam - 1) ** (2 * q))) for q in (1, 2, 3)}   # tr((G_W - I)^(2q)), centered
    off = Gn - np.diag(np.diag(Gn)); mu = float(np.max(np.abs(off)))
    # split tr(E^4) (E = off-diagonal part) into backtracking walks and genuine 4-cycles (z1 != z3, z2 != z4)
    E2 = off @ off; r = np.real(np.diag(E2)); a4 = float(np.sum(np.abs(off) ** 4))
    bt = 2 * float(np.sum(r ** 2)) - a4; cy = cmom[2] - bt
    A = np.abs(off); A2 = A @ A; cyabs = float(np.sum(A2 * A2)) - (2 * float(np.sum(np.diag(A2) ** 2)) - a4)
    cyc = dict(bt=bt, cy=cy, cyabs=cyabs, rmax=float(r.max()), rmean=float(r.mean()))
    had = {}
    for mm in (mlist if HAD else []):
        H = Gn ** mm; np.fill_diagonal(H, 0)
        had[mm] = float(np.max(np.abs(np.linalg.eigvalsh(H))))
    return dict(top=float(lam[-1]), mom=mom, cmom=cmom, cyc=cyc, mu=mu, had=had, diag=float(d.mean()))
plist = [2, 3, 4, 6, 8, 12, 16, 24, 35]; mlist = [1, 2, 3, 4, 6]
print('B=%d L=%d P0=%d  rows R=%d  sources S=%d  source primes %d (slot %d)  build %.1fs' %
      (B, L, P0, R, S, nP, int(slot.sum()), time.time() - t0), flush=True)
out = dict(B=B, L=L, P0=P0, R=R, S=S, nslot=int(slot.sum()), NS=NS, seed=SEED, rho={})
Ws = {rho: order[:max(3, int(rho * R))] for rho in RHOS}
res = {}
for rho in RHOS:
    W = Ws[rho]; k = len(W)
    st = stats(E[W], plist, mlist)
    seff = st['diag']; mp = (1 + math.sqrt(k / seff)) ** 2
    rnd = [stats(E[rng.choice(R, k, replace=False)], plist, [])['top'] for _ in range(8)]
    res[rho] = dict(k=k, mp=mp, sextic=st, randW_top=[float(np.mean(rnd)), float(np.std(rnd))])
ens = {(kind, rho): [] for kind in MODELS for rho in RHOS}
for kind in MODELS:          # one random table per sample, evaluated on every W
    for _ in range(NS):
        Em = model(kind)
        for rho in RHOS: ens[(kind, rho)].append(stats(Em[Ws[rho]], plist, mlist))
for rho in RHOS:
    r = res[rho]; st = r['sextic']; k = r['k']
    print('\nrho=%.3f |W|=%d  S_eff=%.0f  MP edge %.3f   sextic top %.3f   random-W top %.3f+-%.3f   mu_W*sqrt(S)=%.2f'
          % (rho, k, st['diag'], r['mp'], st['top'], r['randW_top'][0], r['randW_top'][1], st['mu'] * math.sqrt(st['diag'])))
    for kind in MODELS:
        e = ens[(kind, rho)]; tops = np.array([x['top'] for x in e])
        pct = float(np.mean(tops >= st['top']))
        Emom = {p: float(np.mean([x['mom'][p] for x in e])) for p in plist}
        ratio = {p: st['mom'][p] / Emom[p] for p in plist}
        hadm = {mm: float(np.mean([x['had'][mm] for x in e])) for mm in (mlist if HAD else [])}
        Ecm = {q: float(np.mean([x['cmom'][q] for x in e])) for q in (1, 2, 3)}
        r[kind] = dict(top_mean=float(tops.mean()), top_std=float(tops.std()), frac_ge_sextic=pct,
                       Emom=Emom, mom_ratio=ratio, had_mean=hadm, mu_mean=float(np.mean([x['mu'] for x in e])),
                       Ecmom=Ecm, cmom_ratio={q: st['cmom'][q] / Ecm[q] for q in (1, 2, 3)})
        print('  %-5s top %.3f+-%.3f  P(model>=sextic)=%.2f  tr ratio sextic/model p=4:%.3f p=12:%.3f p=35:%.3f'
              '  | centered tr((G-I)^2q) ratio q=1:%.3f q=2:%.3f q=3:%.3f'
              % (kind, tops.mean(), tops.std(), pct, ratio[4], ratio[12], ratio[35],
                 r[kind]['cmom_ratio'][1], r[kind]['cmom_ratio'][2], r[kind]['cmom_ratio'][3]))
    if HAD and 'RMM' in MODELS:
        print('  Hadamard ||G^(o m)-I||, m=1..6 sextic:', ' '.join('%d:%.3f' % (mm, st['had'][mm]) for mm in mlist),
              '| RMM:', ' '.join('%d:%.3f' % (mm, r['RMM']['had_mean'][mm]) for mm in mlist),
              '| Gershgorin (k-1)mu^m:', ' '.join('%d:%.2g' % (mm, (k - 1) * st['mu'] ** mm) for mm in mlist))
    c4 = st['cmom'][2]; pred4 = 2 * k ** 3 / st['diag'] ** 2
    print('  centered 4th moment tr((G_W-I)^4): sextic %.4g  random-scale 2|W|^3/S^2 %.4g  ->  certified top 1+tr^(1/4) = %.3f'
          ' (actual %.3f); 2nd: sextic %.4g vs |W|^2/S %.4g' % (c4, pred4, 1 + c4 ** 0.25, st['top'], st['cmom'][1], k * k / st['diag']))
    r['cert4'] = dict(c4=c4, pred4=pred4, cert_top=1 + c4 ** 0.25)
    cy = st['cyc']; mcy = {key: float(np.mean([x['cyc'][key] for x in ens[(MODELS[0], rho)]])) for key in cy}
    sdcy = float(np.std([x['cyc']['cy'] for x in ens[(MODELS[0], rho)]]))
    print('  4-cycles: sextic backtrack %.4g  cycles %.4g  |cycles|-no-cancel %.4g (ratio %.3f) ; row msq max %.3g mean %.3g (|W|/S %.3g)'
          % (cy['bt'], cy['cy'], cy['cyabs'], cy['cy'] / cy['cyabs'], cy['rmax'], cy['rmean'], k / st['diag']))
    print('            %s backtrack %.4g  cycles %.4g+-%.3g  no-cancel %.4g ; row msq max %.3g mean %.3g'
          % (MODELS[0], mcy['bt'], mcy['cy'], sdcy, mcy['cyabs'], mcy['rmax'], mcy['rmean']), flush=True)
    r['cycles'] = dict(sextic=cy, model_mean=mcy, model_cy_std=sdcy)
    cert = {p: (r[MODELS[0]]['Emom'][p]) ** (1 / p) for p in plist}
    print('  D1 certified bound (E_%s tr H^p)^(1/p) / sextic top:' % MODELS[0],
          ' '.join('p=%d:%.3f' % (p, cert[p] / st['top']) for p in plist), flush=True)
    r['cert_over_top'] = {p: cert[p] / st['top'] for p in plist}
    out['rho'][str(rho)] = r
fn = os.path.join(HERE, 'wide_B%d_L%d_P%d_s%d.json' % (B, L, P0, SEED))
with open(fn, 'w') as fh: json.dump(out, fh, indent=1)
print('\nsaved', os.path.basename(fn), ' total %.1fs' % (time.time() - t0))
