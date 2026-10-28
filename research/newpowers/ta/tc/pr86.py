"""Exact (Fraction) model of the final return of PR 83/86 (Sil) inside OUR certificate toolchain.

Adapted from research/mixed-step/return_cut/theta_star.py (copied to ./theta_star.py) and
research/repeated-marks/{cert_return,gen_return_lean}.py (copied here, unchanged except for nothing;
every PR-86 specific constant is set by monkey-patching the copies at run time).

What is configurable (class Cfg):
  * constants of Return/Constants.lean of PR 86: c (theta), h, faces (BC, LC, capC) and (BP, LP, capP),
    numerator cap sP (numeratorCap), dm (fixed switch), d0, reserve, naturalK, mMinus, sMinus, mPlus;
  * the edge set: 'pr86' = [oldSmall(d0), oldSwitch(dm), newSwitch(dm), newTop(dp)] (PR 83 Conductor.lean)
    or 'ours' = our six edges with the capacity-join switch ds;
  * the branch set (names of cert_return.candidates: old, C, Ccap, C-7, P, Pcap; PR 86 = old, C, Pcap);
  * windows: 'collet' (FR8 windows with m_- = mMinus, s_- = sMinus, m_+ = mPlus, join at naturalM) or
    'lemmaW' (cert_return.admission_polys_W);
  * transport box: BoundsN of PR 83 (873/1000 < theta, h < 806/1000, y < 467/1000, ell < 171/1000) or any triple.

Everything is exact rational arithmetic; certifiable() succeeds iff the Bernstein cover of every edge exists
(the same test as theta_star.certifiable = what gen_return_lean.py checks before it emits the certificate).
"""
import os, sys, json
os.environ.setdefault('QRH_K', '9/2')
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from fractions import Fraction as Fr
import cert_return as CR
import gen_return_lean as GR

assert CR.K_I == Fr(9, 2), CR.K_I
ETA = CR.ETA


class Cfg:
    def __init__(self, **kw):
        # --- PR 86 Return/Constants.lean
        self.th = Fr(4369779, 5000000)
        self.h = Fr(8051, 10000)
        self.BC = Fr(9888151, 10**7); self.LC = Fr(4683001, 2 * 10**6); self.capC = Fr(9999, 100000)
        self.BP = Fr(9888151, 10**7); self.LP = Fr(4683001, 2 * 10**6); self.capP = Fr(31, 500)
        self.wC = None            # window cap s_+ of the C branch   (None: = capC, the Lean branchCap)
        self.wP = None            # window cap of the capped branch   (None: = capP)
        self.sP = Fr(3, 50)       # numeratorCap
        self.dm = Fr(19, 25)      # fixed switch; None = capacity join ds (ours)
        self.mMinus = Fr(377, 1000)
        self.sMinus = Fr(3, 100)
        self.mPlus = Fr(11, 25)
        self.reserve = Fr(1, 10**8)
        self.edges = 'pr86'       # 'pr86' | 'ours'
        self.branches = ['old', 'C', 'Pcap']
        self.windows = 'collet'   # 'collet' | 'lemmaW'
        self.bounds = (Fr(873, 1000), Fr(806, 1000), Fr(467, 1000), Fr(171, 1000))  # theta>, h<, y<, ell<
        self.dMinusLower = Fr(3, 4)
        self.maxdepth = 34
        self.drop_receipts = ()   # names of receipts to ignore (pricing only, e.g. ('floor', 'floor_margin'))
        self.extra = ()           # extra count faces (name, B, L, window cap) priced as affine+capped branches
        self.__dict__.update(kw)

    def copy(self, **kw):
        c = Cfg(); c.__dict__.update(self.__dict__); c.__dict__.update(kw); return c

    @property
    def wc(self):
        return self.capC if self.wC is None else self.wC

    @property
    def wp(self):
        return self.capP if self.wP is None else self.wP


_STATE = [None]


def apply_globals(cfg):
    """set the module constants of cert_return that the Collet / Lemma W admission polynomials read"""
    key = (cfg.mMinus, cfg.sMinus, cfg.mPlus, cfg.reserve, cfg.windows, cfg.BC, cfg.LC, cfg.wc, cfg.BP, cfg.LP, cfg.wp,
           tuple(cfg.extra))
    if _STATE[0] != key:
        CR.M_MINUS = cfg.mMinus
        CR.S_MINUS = cfg.sMinus
        CR.M_PLUS = cfg.mPlus
        CR.M_H = (1 - CR.K_I * cfg.sMinus) / 2
        CR.R0 = cfg.reserve
        CR.WINDOWS = cfg.windows
        CR.ADM_CACHE.clear()
        _STATE[0] = key


def geometry(cfg):
    G = CR.geometry(cfg.th, cfg.h, cfg.BP, cfg.LP, cfg.sP)
    return G


def edge_list(cfg, G):
    y, kap, sP = G['y'], G['kap'], G['sP']
    BP, LP = cfg.BP, cfg.LP
    CO = lambda d: min(d, 2 * y - d) / (6 * kap)
    CN = lambda d: min(sP * d, (2 * y - (2 - BP) * d) / LP)
    d0, dp = G['d0'], G['dplus']
    if cfg.edges == 'pr86':
        dm = cfg.dm
        return [('oldSmall', d0, CO(d0)), ('oldSwitch', dm, CO(dm)), ('newSwitch', dm, CN(dm)), ('newTop', dp, CN(dp))]
    # ours: capacity join ds, peak and kink
    ds, dk = G['ds'], G['dk']
    E = [('oldSmall', d0, CO(d0)), ('oldPeak', y, CO(y)), ('oldSwitch', ds, CO(ds)), ('newSwitch', ds, CN(ds))]
    if dk < dp:
        E.append(('newKink', dk, CN(dk)))
    E.append(('newTop', dp, CN(dp)))
    return E


def receipts(cfg, G):
    """name -> margin (must be > 0 unless noted); the scalar side conditions of the Lean return"""
    th, h, ell, x, y, kap = (G[k] for k in ('theta', 'h', 'ell', 'x', 'y', 'kap'))
    dp, d0 = G['dplus'], G['d0']
    BP, LP, sP = cfg.BP, cfg.LP, cfg.sP
    rec = CR.receipt(G, BP, LP, cfg.capC, cfg.capP, cfg.wc, Fr(43, 1000), CR.THETA_I)
    drop = set(CR.GLOBAL_DROP) | {'source_lambda_low', 'source_C_cap', 'source_P_cap'}   # last two: our countWindow/physicalWindow faces
    # conductor / switch side conditions depend on the edge set
    for k in ('conductor_peak_before_switch', 'conductor_switch_before_kink', 'conductor_kink_before_top',
              'conductor_switch_before_top', 'kink_not_before_top', 'dMinus_lower_3_4'):
        drop.add(k)
    rec = {k: v for k, v in rec.items() if k not in drop}
    if cfg.edges == 'pr86':
        dm = cfg.dm
        rec.update({'dMinus_lower': dm - cfg.dMinusLower, 'dMinus_before_top': dp - dm, 'y_before_switch': dm - y,
                    'switch_before_twoy': 2 * y - dm})
    else:
        ds, dk = G['ds'], G['dk']
        rec.update({'dMinus_lower': ds - cfg.dMinusLower, 'conductor_peak_before_switch': ds - y,
                    'conductor_switch_before_top': dp - ds})
    # BoundsN / BoundsR
    tl, hu, yu, eu = cfg.bounds
    signal = x / 2 + (y - x) / 12
    rec.update({'theta>lo': th - tl, 'theta<7/8': Fr(7, 8) - th, 'h>793/1000': h - Fr(793, 1000), 'h<hu': hu - h,
                'y>458/1000': y - Fr(458, 1000), 'y<yu': yu - y, 'ell>1672/10000': ell - Fr(1672, 10000),
                'ell<eu': eu - ell,
                'small_saving': y / 2 - h * (Fr(17, 50) - Fr(1, 6)) - Fr(1, 50) - Fr(7, 100),
                'floor_margin': signal - Fr(1, 200) - (Fr(4, 25) * x - Fr(3, 20) - Fr(51, 100) * y + Fr(67, 100) * dp
                                                       - Fr(3, 20) * ell) + Fr(1, 10**30)})
    # the window caps must not exceed the face caps; the physical numerator cap must not exceed the physical cap
    rec['wC<=capC'] = cfg.capC - cfg.wc + Fr(1, 10**30)
    rec['wP<=capP'] = cfg.capP - cfg.wp + Fr(1, 10**30)
    rec['sP<=capP'] = cfg.capP - sP + Fr(1, 10**30)
    return rec


def candidate_list(cfg, G):
    if cfg.windows == 'lemmaW':
        GR.lemma_w_branches(cfg.BC, cfg.LC, cfg.BP, cfg.LP)
    fdict = {'C': (cfg.BC, cfg.LC, cfg.wc), 'P': (cfg.BP, cfg.LP, cfg.wp)}
    cands = [cd for cd in CR.candidates(fdict, G['kap']) if cd[0] in cfg.branches]
    order = {n: i for i, n in enumerate(cfg.branches)}
    cands.sort(key=lambda cd: order[cd[0]])
    for name, B_, L_, w_ in cfg.extra:
        more = CR.candidates({name: (B_, L_, w_)}, G['kap'])
        cands += [cd for cd in more if cd[0] in (name, name + 'cap')]
    return cands


def certifiable(cfg, why=False, edges_only=None):
    apply_globals(cfg)
    G = geometry(cfg)
    rec = receipts(cfg, G)
    bad = {k: float(v) for k, v in rec.items() if v <= 0 and k not in cfg.drop_receipts}
    if bad:
        return (False, f'receipts {bad}') if why else False
    cands = candidate_list(cfg, G)
    edges = edge_list(cfg, G)
    for nm, d, C in edges:
        if edges_only and nm not in edges_only:
            continue
        try:
            GR.cover_tree(G, d, C, cands, maxdepth=cfg.maxdepth)
        except ValueError:
            return (False, f'cover of edge {nm}') if why else False
    return (True, 'ok') if why else True


def theta_star(cfg, anchor=None, lo=8650000, step=10, maxstep=60):
    """least passing theta in units of 1e-7 (bisection), searched from the anchor; None if none.
    Passing is assumed monotone in theta."""
    if anchor is None:
        anchor = -(-cfg.th.numerator * 10**7 // cfg.th.denominator)
    hi = anchor
    n = 0
    while not certifiable(cfg.copy(th=Fr(hi, 10**7))):
        n += 1
        if n > maxstep:
            return None
        lo, hi = hi, hi + step
    # also make sure lo fails (else move lo down)
    while certifiable(cfg.copy(th=Fr(lo, 10**7))):
        hi = lo
        lo -= 2000
        if lo < 8000000:
            return None
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if certifiable(cfg.copy(th=Fr(mid, 10**7))):
            hi = mid
        else:
            lo = mid
    return hi


def report(cfg, t):
    why = certifiable(cfg.copy(th=Fr(t - 1, 10**7)), why=True)
    return why[1]


# ------------------------------------------------------------------ diagnostics: failing boxes
def failing_boxes(cfg, edge, maxdepth=14):
    """boxes of the dyadic cover of `edge` that no admitted candidate certifies at depth maxdepth"""
    apply_globals(cfg)
    G = geometry(cfg)
    cands = candidate_list(cfg, G)
    edges = {nm: (d, C) for nm, d, C in edge_list(cfg, G)}
    d, C = edges[edge]
    out = []

    def rec_(box, depth):
        (d0, d1), (p0, p1) = box
        for name, br, meta in cands:
            rp = CR.return_poly(br, G, d, C)
            if CR.bernstein_min(rp, box) <= 0:
                continue
            if meta is not None:
                ok, _ = CR.admitted(name, br, meta, ((d0, d1), (p0, Fr(1, 2))))
                if not ok:
                    continue
            return
        if depth >= maxdepth:
            out.append(box)
            return
        if (d1 - d0) / Fr(3, 4) >= (p1 - p0) / Fr(1, 2):
            mid = (d0 + d1) / 2
            rec_(((d0, mid), (p0, p1)), depth + 1)
            rec_(((mid, d1), (p0, p1)), depth + 1)
        else:
            mid = (p0 + p1) / 2
            rec_(((d0, d1), (p0, mid)), depth + 1)
            rec_(((d0, d1), (mid, p1)), depth + 1)

    rec_(((Fr(0), Fr(3, 4)), (Fr(0), Fr(1, 2))), 0)
    return out


if __name__ == '__main__':
    cfg = Cfg()
    print('declared PR 86 theta', cfg.th, float(cfg.th), '->', certifiable(cfg, why=True))
