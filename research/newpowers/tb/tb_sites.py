"""Index of every consumer of a BoundsN field in PR 83's ReturnD/ (and PR 83/86 Return/): file:line:field.

A site is a line mentioning a field projection  `BoundsN.<field>`  or one of its `Transport.*` aliases
(theta_bounds, theta_lower, h_interval, ly_coarse, ell_interval, small_saving, floor_margin), or one of the derived
lemmas of TransportGeometry.lean that are proved from the box (half_lt_h, h_lt_two_y, four_ell_lt_h, dPlus_lt_one,
extended_h_lt_one, h_pos, theta_gt_half, theta_lt_seven_eighths).
usage: python3 tb_sites.py > sites.txt
"""
import re, os, collections
ROOT = '/home/user/lean-env/qrh/Submissions/sil_density_split_20261026'
FIELDS = ['theta_bounds', 'theta_lower', 'h_interval', 'ly_coarse', 'ell_interval', 'small_saving', 'floor_margin']
DERIVED = ['half_lt_h', 'h_lt_two_y', 'four_ell_lt_h', 'dPlus_lt_one', 'extended_h_lt_one', r'Transport\.h_pos', 'theta_gt_half', 'theta_lt_seven_eighths']
pat = re.compile(r'\b(' + '|'.join(FIELDS) + r')\b')
dpat = re.compile(r'(' + '|'.join(DERIVED) + r')')
rows = []
for sub in ('ReturnD', 'Return'):
    for dp, _, fs in os.walk(os.path.join(ROOT, sub)):
        for f in sorted(fs):
            if not f.endswith('.lean'):
                continue
            p = os.path.join(dp, f)
            rel = os.path.relpath(p, ROOT)
            for i, line in enumerate(open(p, encoding='utf-8'), 1):
                if 're-elaborated against the widened coarse box' in line:
                    continue
                for m in pat.finditer(line):
                    rows.append((rel, i, m.group(1), 'field'))
                for m in dpat.finditer(line):
                    rows.append((rel, i, m.group(1), 'derived'))
rows.sort()
cnt = collections.Counter((r[2]) for r in rows)
fcnt = collections.Counter((r[0]) for r in rows)
print('# sites (file:line:name) -- %d total' % len(rows))
for k, v in sorted(cnt.items(), key=lambda t: -t[1]):
    print('# %-26s %4d' % (k, v))
print('# files: %d' % len(fcnt))
for r in rows:
    print('%s:%d:%s' % r[:3])


def grouped(path='sites_grouped.txt'):
    """per-file compact listing  name:lines  (θ=theta_bounds, θlo=theta_lower, h, y, ell, ss, fm, derived lemmas)"""
    short = {'theta_bounds': 'θ', 'theta_lower': 'θlo', 'h_interval': 'h', 'ly_coarse': 'y', 'ell_interval': 'ell',
             'small_saving': 'ss', 'floor_margin': 'fm', 'dPlus_lt_one': 'dP<1', 'extended_h_lt_one': 'h+ext<1',
             'Transport.h_pos': 'h>0', 'half_lt_h': 'h>1/2', 'h_lt_two_y': 'h<2y', 'four_ell_lt_h': '4ell<h',
             'theta_lt_seven_eighths': 'θ<7/8', 'theta_gt_half': 'θ>1/2'}
    byfile = collections.OrderedDict()
    for f, ln, nm, _ in rows:
        byfile.setdefault(f, {}).setdefault(short.get(nm, nm), set()).add(ln)
    with open(path, 'w', encoding='utf-8') as out:
        for f, d in byfile.items():
            out.write('%-60s %s\n' % (f.replace('ReturnD/', ''), '; '.join('%s:%s' % (k, ','.join(str(x) for x in sorted(v))) for k, v in d.items())))


if __name__ == '__main__' and os.environ.get('TB_GROUPED'):
    grouped()
