"""Markdown tables for TB_transport_box.md (generated from tb_statements.S; no side effects except stdout)."""
from fractions import Fraction as F
from tb_common import *
from tb_statements import S
from tb_thresholds import limit

NAME = {'theta_lo': 'θ_lo', 'theta_hi': 'θ_hi', 'h_lo': 'h_lo', 'h_hi': 'h_hi', 'y_lo': 'y_lo', 'y_hi': 'y_hi',
        'ell_lo': 'ℓ_lo', 'ell_hi': 'ℓ_hi', 'ss': 'ss'}


def lim_text(s):
    out = []
    for k in s.uses:
        if k == 'fm':
            continue
        r = limit(s, k)
        if r is None:
            continue
        v, slope = r
        if v < 0 or v > F(12, 10):      # far outside the box: not a limit in practice
            continue
        out.append('%s %s %s' % (NAME[k], '≥' if slope > 0 else '≤', fl(v, 4)))
    return '; '.join(out) if out else '—'


def main():
    cols = [PR83, W_WIDE, W_FUT]
    print('| id | where (`ReturnD/…`, PR 83) | inequality the proof needs | proof | margin now | ℓ<.175 | future-proof | limit of the numerals it uses |')
    print('|---|---|---|---|---|---|---|---|')
    for s in S:
        if s.sid in ('G1', 'G2'):
            ms = ['field', 'field', 'field']
        else:
            ms = ['%.4f' % float(s.mabs(b)) if s.mabs(b) >= F(1, 10**4) or s.mabs(b) == 0 else '%.1e' % float(s.mabs(b)) for b in cols]
        print('| %s | %s | %s | %s | %s | %s | %s | %s |' % (s.sid, s.loc.replace('|', '/'), s.text.replace('|', '/'),
              s.how.replace('|', '/'), ms[0], ms[1], ms[2], lim_text(s)))


if __name__ == '__main__':
    main()
