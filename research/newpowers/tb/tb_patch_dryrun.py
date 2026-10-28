"""Dry run: the exact textual edit of PR 83's ReturnD that widens `BoundsN` to a new set of numerals.

Reads (never writes) PR 83's  ReturnD/TransportGeometry.lean  and  ReturnD/Transport/FinalFixedHigh.lean, applies the
numeral replacements for the requested box in memory, prints a unified diff, and checks that no occurrence of a replaced
numeral is left over in the whole ReturnD/ + Return/ tree (the numerals only occur in those two files, see
TB_transport_box.md section 1; PR 76 -> PR 83 was exactly this edit).

usage:  python3 tb_patch_dryrun.py [--theta-lo 873/1000] [--h-lo 793/1000] [--h-hi 806/1000] [--y-lo 458/1000]
                                   [--y-hi 467/1000] [--ell-lo 1672/10000] [--ell-hi 175/1000] [--ss 7/100]
        (omitted numerals keep their PR 83 value)
"""
import argparse, difflib, os, re, sys

ROOT = '/home/user/lean-env/qrh/Submissions/sil_density_split_20261026'
TG = 'ReturnD/TransportGeometry.lean'
FFH = 'ReturnD/Transport/FinalFixedHigh.lean'
OLD = dict(theta_lo='873/1000', h_lo='793/1000', h_hi='806/1000', y_lo='458/1000', y_hi='467/1000',
           ell_lo='1672/10000', ell_hi='171/1000', ss='7/100')

# (file, regex of the whole line, which numeral keys appear on it and how)
TG_RULES = [
    # class fields
    (TG, r'^ theta_bounds :', [('theta_lo', r'(?<![\d/])873/1000(?=<)')]),
    (TG, r'^ h_interval :', [('h_lo', r'(?<![\d/])793/1000(?=<)'), ('h_hi', r'(?<=<)806/1000$')]),
    (TG, r'^ ly_coarse :', [('y_lo', r'(?<![\d/])458/1000(?=<)'), ('y_hi', r'(?<=<)467/1000$')]),
    (TG, r'^ ell_interval :', [('ell_lo', r'(?<![\d/])1672/10000(?=<)'), ('ell_hi', r'(?<=<)171/1000$')]),
    (TG, r'^ small_saving :', [('ss', r'(?<![\d/])7/100(?=<)')]),
    # four_ell_lt_h
    (TG, r'^ have hh : 793/1000<h', [('h_lo', r'793/1000')]),
    (TG, r'^ have he : ell<171/1000', [('ell_hi', r'171/1000')]),
    # aliases in namespace Transport
    (TG, r'^theorem ell_interval :', [('ell_lo', r'1672/10000'), ('ell_hi', r'171/1000')]),
    (TG, r'^theorem theta_lower :', [('theta_lo', r'873/1000')]),
    (TG, r'^theorem theta_bounds :', [('theta_lo', r'873/1000')]),
    (TG, r'^theorem h_interval :', [('h_lo', r'793/1000'), ('h_hi', r'806/1000')]),
    (TG, r'^theorem ly_coarse :', [('y_lo', r'458/1000'), ('y_hi', r'467/1000')]),
    (TG, r'^theorem small_saving :', [('ss', r'7/100')]),
    # FinalFixedHigh
    (FFH, r'have hx : 1672/10000<Geometry.x', [('ell_lo', r'1672/10000')]),
    (FFH, r'have hy : 458/1000<Geometry.y', [('y_lo', r'458/1000')]),
    (FFH, r'have hb : h<806/1000', [('h_hi', r'806/1000')]),
]


def main():
    ap = argparse.ArgumentParser()
    for k in OLD:
        ap.add_argument('--' + k.replace('_', '-'), default=OLD[k])
    a = ap.parse_args()
    new = {k: getattr(a, k) for k in OLD}
    texts = {f: open(os.path.join(ROOT, f), encoding='utf-8').read().split('\n') for f in (TG, FFH)}
    out = {f: list(v) for f, v in texts.items()}
    changed = 0
    for f, lre, subs in TG_RULES:
        for i, line in enumerate(out[f]):
            if re.search(lre, line):
                l2 = line
                for key, rx in subs:
                    if new[key] != OLD[key]:
                        l2 = re.sub(rx, new[key], l2)
                if l2 != line:
                    out[f][i] = l2
                    changed += 1
    for f in out:
        d = list(difflib.unified_diff(texts[f], out[f], 'a/' + f, 'b/' + f, lineterm='', n=0))
        for line in d:
            print(line[:230])
    print('\n%d lines changed' % changed)
    # leftover check: any old numeral that was replaced and still occurs (outside comments/doc)
    bad = []
    for key, val in OLD.items():
        if new[key] == val:
            continue
        for sub in ('ReturnD', 'Return'):
            for dp, _, fs in os.walk(os.path.join(ROOT, sub)):
                for fn in fs:
                    if not fn.endswith('.lean'):
                        continue
                    p = os.path.join(dp, fn)
                    rel = os.path.relpath(p, ROOT)
                    lines = open(p, encoding='utf-8').read().split('\n')
                    if rel in out:
                        lines = out[rel]
                    for i, line in enumerate(lines, 1):
                        if 're-elaborated against' in line or line.startswith('/-') or line.startswith('the upper ends') or line.startswith('`theta ='):
                            continue
                        if re.search(r'(?<![\d/])' + re.escape(val) + r'(?!\d)', line):
                            bad.append((key, rel, i, line.strip()[:110]))
    if bad:
        print('LEFTOVER occurrences of replaced numerals (check by hand):')
        for b in bad:
            print('  ', b)
    else:
        print('no leftover occurrences of the replaced numerals in ReturnD/ + Return/')


if __name__ == '__main__':
    main()
