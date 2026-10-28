"""Every Lean statement of PR 83 (ReturnD/, built) that consumes a field of `BoundsN`, with the inequality that
the proof really needs, evaluated

  (abs) on the *abstract* box: the proof only sees the box numerals (linarith/nlinarith over the field hypotheses),
        margin = min over the corners of the intervals the proof uses;
  (par) on the actual parameter polygon in the (theta,h) plane, where ell = 11/3-4 theta, x = 1+ell-h, y = h-2 ell
        (these identities are available as `ell_eq`, `x_eq`, `y_eq`, but most proofs below do not use them).

A statement holds in a box iff its margin is > 0 (>= 0 where the Lean inequality is non-strict).
Each row also carries the *threshold* of every box numeral it uses: the value at which the margin hits 0
(everything else kept at its PR 83 value), i.e. how far that numeral can move without touching the proof.

usage: python3 tb_statements.py            (prints the tables; no side effects)
"""
from fractions import Fraction as F
from tb_common import *

R = F  # shorthand


class St:
    def __init__(self, sid, loc, text, how, uses, mabs, thr=None, par=None, note=''):
        self.sid, self.loc, self.text, self.how, self.uses, self.mabs = sid, loc, text, how, uses, mabs
        self.thr = thr or {}
        self.par = par            # function (theta, h) -> margin on the actual parameters
        self.note = note


ts = TEN10
# ---- statements -------------------------------------------------------------------------------------------------
S = []
add = S.append

# TransportGeometry.lean --------------------------------------------------------------------------------------------
add(St('A1', 'TransportGeometry.lean:58-62 (four_ell_lt_h)', '4*ell < h', 'linarith [h_interval.1, ell_interval.2]',
       ('h_lo', 'ell_hi'), lambda b: b.h_lo - 4 * b.ell_hi,
       thr={'ell_hi': 'h_lo/4'}, par=lambda t, h: h - 4 * ell_of(t)))
add(St('A2', 'TransportGeometry.lean:54 (half_lt_h)', '1/2 < h', 'linarith [h_interval]', ('h_lo',),
       lambda b: b.h_lo - F(1, 2), thr={'h_lo': F(1, 2)}, par=lambda t, h: h - F(1, 2)))
add(St('A3', 'TransportGeometry.lean:55 (h_lt_two_y)', 'h < 2*y', 'linarith [h_interval, ly_coarse]', ('h_hi', 'y_lo'),
       lambda b: 2 * b.y_lo - b.h_hi, thr={'y_lo': 'h_hi/2', 'h_hi': '2*y_lo'}, par=lambda t, h: 2 * y_of(t, h) - h))
add(St('A4', 'TransportGeometry.lean:64 (dPlus_lt_one), :97 (extended_h_lt_one)', 'h + 1e-10 < 1',
       'linarith [h_interval.2]', ('h_hi',), lambda b: 1 - b.h_hi - ts, thr={'h_hi': F(1)},
       par=lambda t, h: 1 - h - ts, note='used by GenericFeedback:52, SourceLedger:105, CubeFloorSaving:86'))
add(St('A5', 'TransportGeometry.lean:80 (theta_gt_half)', '1/2 < theta', 'linarith [theta_bounds.1]', ('theta_lo',),
       lambda b: b.theta_lo - F(1, 2), thr={'theta_lo': F(1, 2)}, par=lambda t, h: t - F(1, 2)))
add(St('A6', 'TransportGeometry.lean:96 (h_pos)', '0 < h', 'linarith [h_interval.1]', ('h_lo',),
       lambda b: b.h_lo, thr={'h_lo': F(0)}, par=lambda t, h: h))
# FinalFixedHigh.lean -----------------------------------------------------------------------------------------------
add(St('B1', 'Transport/FinalFixedHigh.lean:64-70 and :107-113 (hsig)', '1/10 < signal theta = (5x+y)/12 with x > ell_lo, y > y_lo',
       'linarith [signal_at_boundary, ell_interval.1.trans ell_lt_x, ly_coarse.1] (numerals 1672/10000, 458/1000 hard-coded at :66,:67,:109,:110)',
       ('ell_lo', 'y_lo'), lambda b: (5 * b.ell_lo + b.y_lo) / 12 - F(1, 10),
       thr={'y_lo': 'F(6,5)-5*ell_lo', 'ell_lo': '(1.2-y_lo)/5'}, par=lambda t, h: signal_of(t, h) - F(1, 10)))
add(St('B2', 'Transport/FinalFixedHigh.lean:71-74 and :114-117 (hcap)', 'h + 5e-11 <= 7/8 - 1/100',
       'have hb : h<806/1000 (hard-coded numeral at :72,:115) ; linarith', ('h_hi',),
       lambda b: F(7, 8) - F(1, 100) - b.h_hi - F(1, 2 * 10**10), thr={'h_hi': F(865, 1000)},
       par=lambda t, h: F(7, 8) - F(1, 100) - h - F(1, 2 * 10**10)))
# GenericFeedback.lean ----------------------------------------------------------------------------------------------
add(St('C1', 'GenericFeedback.lean:23 and :44', '7/10 <= kappa = 2 theta - 1', 'linarith [theta_bounds.1]', ('theta_lo',),
       lambda b: 2 * b.theta_lo - 1 - F(7, 10), thr={'theta_lo': F(85, 100)}, par=lambda t, h: 2 * t - 1 - F(7, 10)))
add(St('C2', 'GenericFeedback.lean:26 (hcoef)', '5*dp/288 <= 1/50', 'linarith [h_interval.2]', ('h_hi',),
       lambda b: F(1, 50) - 5 * (b.h_hi + ts) / 288, thr={'h_hi': F(144, 125)},
       par=lambda t, h: F(1, 50) - 5 * (h + ts) / 288))
# PhysicalDirect ----------------------------------------------------------------------------------------------------
add(St('D1', 'PhysicalDirect/Geometry.lean:87 (shiftBase_nonneg)', 'dp < 2*y', 'linarith [h_interval.2, ly_coarse.1]',
       ('h_hi', 'y_lo'), lambda b: 2 * b.y_lo - b.h_hi - ts, thr={'y_lo': 'h_hi/2'},
       par=lambda t, h: 2 * y_of(t, h) - h - ts))
add(St('D2', 'PhysicalDirect/SourceParameters.lean:51 (hy: y <= 19/40)', 'y <= 19/40 (then y/d <= 19/20 for d >= 1/2)',
       'linarith [ly_coarse.1, ly_coarse.2]', ('y_hi',), lambda b: F(19, 40) - b.y_hi, thr={'y_hi': F(475, 1000)},
       par=lambda t, h: F(19, 40) - y_of(t, h)))
add(St('D3', 'PhysicalDirect/Active.lean:57 (eventually_new_cutoff_le_base)', 'y/d <= 19/20 for d > 1/2, i.e. y <= 19/40',
       'linarith [ly_coarse.2]', ('y_hi',), lambda b: F(19, 40) - b.y_hi, thr={'y_hi': F(475, 1000)},
       par=lambda t, h: F(19, 40) - y_of(t, h)))
add(St('D4', 'PhysicalDirect/OldGeometry.lean:66 (physical_y_range), OldActive.lean:45', 'y/d <= 99 for d >= 1/200, i.e. y <= 99/200',
       'linarith [ly_coarse.2]', ('y_hi',), lambda b: F(99, 200) - b.y_hi, thr={'y_hi': F(495, 1000)},
       par=lambda t, h: F(99, 200) - y_of(t, h)))
add(St('D5', 'PhysicalDirect/OldGeometry.lean:155-160 (hyell)', 'y <= ell*(6*kappa), kappa >= 7/10: y <= 4.2*ell',
       'linarith [ell_interval.1, ly_coarse.2] + one product', ('y_hi', 'ell_lo'),
       lambda b: F(42, 10) * b.ell_lo - b.y_hi, thr={'y_hi': '4.2*ell_lo'}, par=lambda t, h: F(42, 10) * ell_of(t) - y_of(t, h)))
add(St('D6', 'PhysicalDirect/OldActive.lean:160', '0 < y', 'linarith [ly_coarse.1, ly_coarse.2]', ('y_lo',),
       lambda b: b.y_lo, thr={'y_lo': F(0)}, par=lambda t, h: y_of(t, h)))
add(St('D7', 'PhysicalDirect/Finite/Bridge.lean:39 (target_positive)', '1/10 < theta + signalShift = theta - 5/6 + x/3 + ell/6, x > ell > ell_lo',
       'linarith [theta_bounds.1, ell_interval.1, ell_lt_x]', ('theta_lo', 'ell_lo'),
       lambda b: b.theta_lo - F(5, 6) + b.ell_lo / 3 + b.ell_lo / 6 - F(1, 10),
       thr={'theta_lo': '5/6+1/10-ell_lo/2'}, par=lambda t, h: t - F(5, 6) + x_of(t, h) / 3 + ell_of(t) / 6 - F(1, 10)))
add(St('D8', 'PhysicalDirect/Finite/Summation.lean:82, Finite/Geometry.lean:63, SourceLedger.lean:81', 'dp <= 1',
       'linarith [h_interval.2]', ('h_hi',), lambda b: 1 - b.h_hi - ts, thr={'h_hi': F(1)}, par=lambda t, h: 1 - h - ts))
add(St('D9', 'PhysicalDirect/SourceActual.lean:111', 'dp <= 7/8', 'linarith [h_interval.2]', ('h_hi',),
       lambda b: F(7, 8) - b.h_hi - ts, thr={'h_hi': F(875, 1000)}, par=lambda t, h: F(7, 8) - h - ts))
add(St('D10', 'PhysicalDirect/JointHeight.lean:37, SourceActual.lean:83', '51/100 < theta', 'linarith [theta_bounds.1]',
       ('theta_lo',), lambda b: b.theta_lo - F(51, 100), thr={'theta_lo': F(51, 100)}, par=lambda t, h: t - F(51, 100)))
add(St('D11', 'PhysicalDirect/Chosen.lean:52', '85/100 < theta', 'linarith [theta_bounds.1]', ('theta_lo',),
       lambda b: b.theta_lo - F(85, 100), thr={'theta_lo': F(85, 100)}, par=lambda t, h: t - F(85, 100)))
add(St('D12', 'PhysicalDirect/FiniteError/FullW.lean:39, Transport/CentralErrorSaving.lean:31', 'crude exponent 0.16*x + 1.34 - y(a+6e) <= 2 (a,e >= 0), x <= 1-ell_lo-y_lo',
       'nlinarith [length_sum, ly_coarse, ell_interval] (products y*a, y*e >= 0)', ('ell_lo', 'y_lo'),
       lambda b: F(2) - F(134, 100) - F(16, 100) * (1 - b.ell_lo - b.y_lo), thr={}, par=lambda t, h: F(2) - F(134, 100) - F(16, 100) * x_of(t, h)))
add(St('D13', 'FullW.lean:57,170,176; CubeFiniteError.lean:52,58; CentralErrorSaving.lean:49', 'h + zeta <= 1 and ell <= 1',
       'linarith [h_interval.2] / [ell_interval]', ('h_hi', 'ell_hi'), lambda b: min(1 - b.h_hi - ts, 1 - b.ell_hi),
       thr={'h_hi': F(1), 'ell_hi': F(1)}, par=lambda t, h: min(1 - h - ts, 1 - ell_of(t))))
add(St('D14', 'CommonProbe.lean:67, CanonicalReduction.lean:54, NonfloorTransport.lean:136', '1/100 <= h + zeta (rpow exponent order)',
       'linarith [h_interval.1]', ('h_lo',), lambda b: b.h_lo - F(1, 100), thr={'h_lo': F(1, 100)}, par=lambda t, h: h - F(1, 100)))
# exponent-type -----------------------------------------------------------------------------------------------------
add(St('E1', 'Transport/Transport/FloorExponent.lean:40 (floor_loss_bound)', '(16-6 ly) e <= 14 e (e>=0): ly >= 1/3',
       'nlinarith [ly_coarse, e*(ly-1/3) >= 0]', ('y_lo',), lambda b: b.y_lo - F(1, 3), thr={'y_lo': F(1, 3)},
       par=lambda t, h: y_of(t, h) - F(1, 3)))
add(St('E2', 'Transport/Transport/NormalizedTransportSaving.lean:97 (h1)', '7/8 - S + 8e + nu + sigma <= theta  with sigma+8e+nu <= 1/20: theta + S >= 0.925, S = y/2-h(17/50-1/6)-1/50',
       'linarith [small_saving, theta_lower] (+ hypotheses hbetalo, _hgeometric)', ('theta_lo', 'ss'),
       lambda b: b.theta_lo + b.ss - F(925, 1000), thr={'ss': '0.925-theta_lo', 'theta_lo': '0.925-ss'},
       par=lambda t, h: t + small_saving_val(t, h) - F(925, 1000),
       note='the 1/20 comes from the TransportParameters field geometric_budget; true sigma+8e+nu is ~1e-10 so the real need is S > 7/8-theta'))
add(St('E3', 'Transport/Transport/PrincipalRemainderBounds.lean:589 (source_w_strict_exponent), :617,:621 (same hint)', 'e(1+h) - y/20 + 1/4000 <= 0 for e <= 1/1000',
       'nlinarith [h_interval, ly_coarse, theta_bounds]', ('h_hi', 'y_lo'),
       lambda b: b.y_lo / 20 - (1 + b.h_hi) / 1000 - F(1, 4000), thr={'y_lo': '20*((1+h_hi)/1000+1/4000)'},
       par=lambda t, h: y_of(t, h) / 20 - (1 + h) / 1000 - F(1, 4000)))
add(St('E4', 'Transport/Transport/PrincipalRemainderBounds.lean:592 (source_z_strict_exponent)', 'e <= h/600 - 1/4000 for e <= 1/1000',
       'nlinarith [h_interval, ly_coarse, theta_bounds] (linear in effect)', ('h_lo',),
       lambda b: b.h_lo / 600 - F(1, 1000) - F(1, 4000), thr={'h_lo': F(3, 4)}, par=lambda t, h: h / 600 - F(1, 1000) - F(1, 4000)))
add(St('E5a', 'Transport/Transport/PrincipalRemainderRegion.lean:25-90 remainder_unramified_bound, hR (used by PrincipalSlots.lean principal_correction_defect, region_correction_defect and via marked_bound/local_norm_bound by FiniteProduct)',
       '4 - 6 theta - 6*(4/25) <= -219/100  (coordR_norm_le exponent 4-6x-6z)', 'Real.rpow_le_rpow_of_exponent_le .. (by linarith) with hx: theta <= x.re (theta_bounds.1)', ('theta_lo',),
       lambda b: 6 * b.theta_lo + F(24, 25) - 4 - F(219, 100), thr={'theta_lo': F(5230, 6000)},
       par=lambda t, h: 6 * t + F(24, 25) - 4 - F(219, 100),
       note='SHARPEST theta-lower-end use: needs theta >= 0.871667'))
add(St('E5b', 'PrincipalRemainderRegion.lean:25-90, hK', '1 - theta - 9/10 <= -77/100 (coordK_norm_le exponent 1-x-w)', 'linarith [theta_bounds]', ('theta_lo',),
       lambda b: b.theta_lo + F(9, 10) - 1 - F(77, 100), thr={'theta_lo': F(87, 100)}, par=lambda t, h: t + F(9, 10) - 1 - F(77, 100)))
add(St('E6', 'PrincipalSlots.lean (principal_marked_error_bounds hBR, hRT; region_marked_error_bounds hBR hRT)', '3-5s <= -theta, 3-6s <= -theta with s >= theta: theta >= 3/4',
       'linarith [theta_bounds] with hs: theta <= s.re', ('theta_lo',), lambda b: 4 * b.theta_lo - 3, thr={'theta_lo': F(3, 4)}, par=lambda t, h: 4 * t - 3))
add(St('E7', 'PrincipalSlots.lean region_marked_error_bounds hBKV (1 - w - 6z <= -theta: theta <= 0.94)', 'theta <= 0.94', 'linarith [theta_bounds.2]', ('theta_hi',),
       lambda b: F(94, 100) - b.theta_hi, thr={'theta_hi': F(94, 100)}, par=lambda t, h: F(94, 100) - t))
# theta-only soft uses ----------------------------------------------------------------------------------------------
add(St('F1', 'PrincipalRemainder{Contours,FiniteProduct,FiniteProductX,Transport,Bounds,Region,RayThresholds,Normalized,Physical,PhysicalBounds}.lean, PrincipalSlots.lean, PrincipalSignal.lean:63, SignalShift.lean:58, TransportParameters.lean:95,191',
       '0 < Q, 1 <= Q, 4 <= Q (from 480 <= Q), 0 < theta, 4/25 <= xi from 1/6 < xi, Z^(...) monotone: theta > 0 .. 1/2',
       'linarith [theta_bounds] used only as a weak positivity hint', ('theta_lo',), lambda b: b.theta_lo - F(1, 2), thr={'theta_lo': F(1, 2)},
       par=lambda t, h: t - F(1, 2), note='~110 call sites, none sharp (largest need among them: E5a, E5b, E6)'))
add(St('F2', 'Transport/FinalCommonProbe.lean:45-46', '1/2 <= theta and theta <= 7/8', 'theta_bounds.1 / theta_bounds.2.le', ('theta_lo', 'theta_hi'),
       lambda b: min(b.theta_lo - F(1, 2), b.theta_hi - F(7, 8)), thr={}, par=lambda t, h: F(7, 8) - t))
# fields as hypotheses of the instance -------------------------------------------------------------------------------
add(St('G1', 'Transport/Transport/FloorExponent.lean:25 (floor_source_margin)', 'floorSourceExponent(v) <= signal theta - 1/200 for v <= h+1e-10, i.e. 0.01 + 1.03 ell <= (5+3 ell-4h)/12 - fm',
       'the field floor_margin itself (dsimp + linarith; it is a restatement)', ('fm',), lambda b: F(0), thr={}, par=lambda t, h: floor_slack(t, h),
       note='h <= 1.205 - 2.34*ell = 9.36*theta - 7.375 (fm=1/200); h-coefficient of the left side cancels'))
add(St('G2', 'TransportGeometry.lean:24 (field small_saving) -> NormalizedTransportSaving.lean:97 only', '7/100 < y/2 - h(17/50-1/6) - 1/50', 'field', ('ss',),
       lambda b: F(0), thr={}, par=lambda t, h: small_saving_val(t, h) - F(7, 100)))


def boxes():
    return [PR83, W_MIN, W_CALLER, W_WIDE, W_FUT]


def main():
    bl = boxes()
    print('ABSTRACT-BOX MARGINS (proof sees only the numerals).  columns: ' + ' | '.join(b.name for b in bl))
    print('%-5s %-34s' % ('id', 'inequality') + ''.join('%14s' % ('box%d' % i) for i in range(len(bl))))
    for s in S:
        row = [s.mabs(b) for b in bl]
        print('%-5s %-34s' % (s.sid, s.text[:34]) + ''.join('%14.5f' % float(v) for v in row) +
              ('   FAILS' if any(v < 0 for v in row) else ''))
    print()
    # parameter-polygon margins at vertices and targets
    pts = [('PR83 actual', F(174799, 200000), F(8053, 10000)), ('PR86 actual', F(4369779, 5000000), F(8051, 10000)),
           ('T 0.8739058,h=.8047', F(8739058, 10**7), F(8047, 10000)), ('T 0.8738,h=.8037', F(8738, 10**4), F(8037, 10000))]
    print('PARAMETER MARGINS at actual points')
    print('%-5s' % 'id' + ''.join('%22s' % p[0] for p in pts))
    for s in S:
        if s.par is None:
            continue
        print('%-5s' % s.sid + ''.join('%22.5f' % float(s.par(t, h)) for _, t, h in pts))
    print()
    for b in bl:
        P = polygon(b)
        print('POLYGON', b.name, 'theta_min = %.7f' % float(min(p[0] for p in P)) if P else 'EMPTY')
        worst = {}
        for s in S:
            if s.par is None or s.sid in ('G1', 'G2'):     # G1/G2 are the fields themselves (0 on the floor ridge by construction)
                continue
            m = min(s.par(t, h) for t, h in P) if P else None
            worst[s.sid] = m
        print('   worst parameter margins over the polygon: ' + ', '.join('%s %.4f' % (k, float(v)) for k, v in worst.items() if v is not None and v < F(1, 50)))


if __name__ == '__main__':
    main()
