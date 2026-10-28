"""For each box numeral: the value at which each statement (tb_statements.S) stops being derivable by its proof,
all other numerals kept at their PR 83 values.  (margins are affine in each numeral, so two evaluations suffice.)

numerals: theta_lo, theta_hi, h_lo, h_hi, y_lo, y_hi, ell_lo, ell_hi, ss (small_saving constant)
"""
from fractions import Fraction as F
from tb_common import *
from tb_statements import S

NUM = ['theta_lo', 'theta_hi', 'h_lo', 'h_hi', 'y_lo', 'y_hi', 'ell_lo', 'ell_hi', 'ss']


def limit(s, k, base=PR83):
    v0 = getattr(base, k)
    m0 = s.mabs(base)
    m1 = s.mabs(base.w(**{k: v0 + F(1, 100)}))
    if m1 == m0:
        return None
    slope = (m1 - m0) / F(1, 100)
    return v0 - m0 / slope, slope


def main():
    res = {k: [] for k in NUM}
    for s in S:
        for k in NUM:
            if k not in s.uses and not (k == 'ss' and 'ss' in s.uses):
                continue
            r = limit(s, k)
            if r is None:
                continue
            lim, slope = r
            res[k].append((s.sid, lim, slope))
    for k in NUM:
        v0 = getattr(PR83, k)
        print('%-9s current %-8s' % (k, fl(v0, 4)))
        # the binding limit is the one closest to the current value on the side the box would be widened
        lo_side = [(sid, lim) for sid, lim, sl in res[k] if sl > 0]   # margin increases with numeral -> a lower limit (numeral must stay above)
        hi_side = [(sid, lim) for sid, lim, sl in res[k] if sl < 0]   # numeral must stay below
        if lo_side:
            m = max(lo_side, key=lambda t: t[1])
            print('   must stay ABOVE %s  (binding statement %s); others: %s' % (fl(m[1], 5), m[0], ', '.join('%s %.4f' % (a, float(b)) for a, b in sorted(lo_side, key=lambda t: -t[1])[:5])))
        if hi_side:
            m = min(hi_side, key=lambda t: t[1])
            print('   must stay BELOW %s  (binding statement %s); others: %s' % (fl(m[1], 5), m[0], ', '.join('%s %.4f' % (a, float(b)) for a, b in sorted(hi_side, key=lambda t: t[1])[:5])))


if __name__ == '__main__':
    main()
