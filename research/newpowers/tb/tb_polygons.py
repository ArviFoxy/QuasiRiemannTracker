"""Vertices of the feasible (theta,h) polygon of each box (exact), with the active constraints."""
from tb_common import *


def main():
    for b in (PR83, W_MIN, W_WIDE, W_FUT):
        P = polygon(b)
        print('%s   [theta>%s h<%s y>%s y<%s ell<%s ss=%s fm=%s]' % (b.name, fl(b.theta_lo, 4), fl(b.h_hi, 4), fl(b.y_lo, 4), fl(b.y_hi, 4), fl(b.ell_hi, 4), fl(b.ss, 3), str(b.fm)))
        print('   theta_min = %s' % fl(min(p[0] for p in P), 7))
        for t, h in P:
            print('   theta=%s h=%s ell=%s y=%s x=%s  active: %s' % (fl(t, 7), fl(h, 6), fl(ell_of(t), 6), fl(y_of(t, h), 6), fl(x_of(t, h), 6), ', '.join(active_at(b, t, h))))
        print()
    # PR86 and PR83 actual points: slack to each box constraint
    for nm, t, h in (('PR86', F(4369779, 5000000), F(8051, 10000)), ('PR83', F(174799, 200000), F(8053, 10000))):
        print('%s actual point: ' % nm + ', '.join('%s %.2e' % (n, float(a * t + bb * h + c)) for n, a, bb, c in constraints(PR83)))


if __name__ == '__main__':
    main()
