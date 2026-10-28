"""Relation theta <-> (ell, h, y, x) at the optimum, and the (theta,h) window left by the functional fields.

Exact identities (Lean: TransportGeometry.lean:39-44):  ell = 11/3-4 theta ; x = 1+ell-h ; y = h-2 ell ; dPlus = h+1e-10.
floor_margin (field, FloorExponent.lean:25):  h <= 1.205 - 2.34 ell - 2e-10  = 9.36 theta - 7.375 - 2e-10   (fm = 1/200)
small_saving (field, E2 only)               :  h > (0.09+ss-0.07+... ) -> h > 150 (ss + 1/50 + ell)/49
y > y_lo (field)                              :  h > y_lo + 2 ell
The model (research/newpowers/r3/pm.py pick_h, research/.../tc/best.py h_for) takes h = the largest h on a 1e-6 grid with
floor_margin >= 0 (theta*(h) decreases by ~1.07e-3 per unit h, hscan_both.log), so h = floor(h_floor_max, 1e-6).
"""
import math
from fractions import Fraction as F
from tb_common import *


def floor_grid(x, g=10**6):
    return F(math.floor(x * g), g)


def main():
    thetas = [('PR83', F(174799, 200000)), ('PR86', F(4369779, 5000000)), ('', F(8739167, 10**7)), ('bar 5e-5', F(8739058, 10**7)),
              ('', F(87390, 10**5)), ('', F(8738, 10**4)), ('', F(8737, 10**4)), ('', F(8736, 10**4)), ('', F(8735, 10**4)), ('', F(873, 1000))]
    print('%-9s %-10s %-9s | %-9s %-9s %-9s | h(1e-6) y        x        S(small_sav) fl-slack | window (y>.458, ss=.07 .. floor)' % ('', 'theta', 'ell', 'h_floor', 'h_ss_min', 'h_y_min'))
    for nm, t in thetas:
        ell = ell_of(t)
        hf = h_floor_max(t); hs = h_small_saving_min(t); hy = h_y_lo_min(t)
        h = floor_grid(hf)
        ok = hf >= max(hs, hy)
        print('%-9s %-10s %-9s | %-9s %-9s %-9s | %-9s %-8s %-8s %-9s %-9s | %s' % (
            nm, fl(t, 7), fl(ell, 7), fl(hf, 6), fl(hs, 6), fl(hy, 6), fl(h, 6), fl(y_of(t, h), 5), fl(x_of(t, h), 5),
            fl(small_saving_val(t, h), 5), fl(floor_slack(t, h), 6), ('[%s, %s]' % (fl(max(hs, hy), 5), fl(hf, 5))) if ok else 'EMPTY'))
    print()
    print('closed forms:  ell = 11/3 - 4 theta;  h_floor = 9.36 theta - 7.375 (fm=1/200);  at h = h_floor:  y = 17.36 theta - 14.708333,  x = 12.041667 - 13.36 theta')
    # check numerically
    t = F(8739058, 10**7)
    hfl = F(936, 100) * t - F(7375, 1000)
    print('check at 0.8739058: 9.36 theta-7.375 = %s vs exact %s ; difference %s' % (fl(hfl, 9), fl(h_floor_max(t), 9), fl(hfl - h_floor_max(t), 12)))
    print()
    print('theta_min of the (theta,h) polygon as a function of the functional constants (box otherwise PR83, ell_hi=.175, theta_lo=.8, h_lo=.793):')
    base = PR83.w(theta_lo=F(8, 10), ell_hi=F(175, 1000))
    print('   ss \\ y_lo ' + ''.join('%10s' % fl(y, 3) for y in [F(458, 1000), F(450, 1000), F(445, 1000), F(440, 1000), F(420, 1000), F(403, 1000)]))
    for ss in [F(70, 1000), F(66, 1000), F(65, 1000), F(60, 1000), F(55, 1000), F(52, 1000)]:
        row = []
        for y in [F(458, 1000), F(450, 1000), F(445, 1000), F(440, 1000), F(420, 1000), F(403, 1000)]:
            P = polygon(base.w(ss=ss, y_lo=y))
            row.append(fl(min(p[0] for p in P), 5) if P else 'empty')
        print('   %-10s' % fl(ss, 3) + ''.join('%10s' % r for r in row))
    print()
    print('theta_min vs the floor constant fm (loss budget 1/200 of CubeFloorSaving.htotal), ss=.06,y_lo=.44:')
    for fm in [F(1, 200), F(1, 250), F(1, 300), F(1, 400)]:
        P = polygon(base.w(ss=F(60, 1000), y_lo=F(440, 1000), fm=fm))
        print('   fm=%-8s theta_min=%s  h_floor(0.8739058)=%s' % (str(fm), fl(min(p[0] for p in P), 5), fl(h_floor_max(F(8739058, 10**7), fm), 6)))
    print()
    print('h_floor as a function of ell for the three margins: h <= 1.25 - 3*(fm + 0.01) - 0.78*3*ell... check:')
    for fm in [F(1, 200), F(1, 400)]:
        ell = F(1710435, 10**7)
        t = (F(11, 3) - ell) / 4
        print('   fm=%s ell=0.1710435: h_floor=%s' % (fm, fl(h_floor_max(t, fm), 6)))


if __name__ == '__main__':
    main()
