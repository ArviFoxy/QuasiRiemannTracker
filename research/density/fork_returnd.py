#!/usr/bin/env python3
"""Fork PR 83's `ReturnD/` (Sil, Submissions.sil_density_split_20261026) into Submissions.arvi_density.ReturnD.

* module prefix  Submissions.sil_density_split_20261026  ->  Submissions.arvi_density
* namespaces     SilDensitySplit (QRH.SilDensitySplit.Return, ...ReturnT, OAI.SevenEighths.SilDensitySplitReturn...,
                 SilDensitySplitTransportLow)  ->  ArviDensity
  (a plain token rename of the *code*; the leading notice comments of every file are copied verbatim)
* the transport box `BoundsN` (ReturnD/TransportGeometry.lean) is widened as in research/newpowers/TB_transport_box.md,
  option B:  ell < 175/1000 (was 171/1000),  y > 440/1000 (was 458/1000),  small_saving 6/100 (was 7/100);
  the two consumers of the hard-coded numeral 458/1000 (Transport/FinalFixedHigh.lean:67,110) follow.
  Nothing else is edited (every consumer of the box is a linarith/nlinarith with positive margin, TB report section 2).
* one notice block is appended to the header of every file.

usage: python3 fork_returnd.py [SRC [DST [NEWPKG [NEWNS]]]]      (DST must not exist)
  defaults: SRC = PR 83's ReturnD, DST = .../Submissions/arvi_density/ReturnD, NEWPKG = arvi_density (the directory name
  under Submissions/, Lean prefix Submissions.<NEWPKG>), NEWNS = ArviDensity (Lean namespace QRH.<NEWNS>)
"""
import os, re, sys

SRC = sys.argv[1] if len(sys.argv) > 1 else '/home/user/lean-env/qrh/Submissions/sil_density_split_20261026/ReturnD'
DST = sys.argv[2] if len(sys.argv) > 2 else '/home/user/lean-env/qrh/Submissions/arvi_density/ReturnD'
NEWPKG = sys.argv[3] if len(sys.argv) > 3 else 'arvi_density'
NEWNS = sys.argv[4] if len(sys.argv) > 4 else 'ArviDensity'

RENAMES = [('sil_density_split_20261026', NEWPKG), ('SilDensitySplit', NEWNS)]

NOTICE_PLAIN = ('/- Modified by ArviFoxy (2026-10-28): module prefix and namespaces renamed to '
                f'Submissions.{NEWPKG}.ReturnD and QRH.{NEWNS}.Return (no other change). -/')
NOTICE_BOX = ('/- Modified by ArviFoxy (2026-10-28): module prefix and namespaces renamed to '
              f'Submissions.{NEWPKG}.ReturnD and QRH.{NEWNS}.Return, and the coarse box `BoundsN` widened to '
              'ell<175/1000, y>440/1000 and small_saving 6/100 (every consumer is unchanged). -/')

# exact textual edits on the ORIGINAL (pre-rename) code, each must match exactly `n` times
EDITS = {
    'TransportGeometry.lean': [
        (' ly_coarse : 458/1000<QRH.Record1252270103Return.Geometry.y ∧ QRH.Record1252270103Return.Geometry.y<467/1000\n',
         ' ly_coarse : 440/1000<QRH.Record1252270103Return.Geometry.y ∧ QRH.Record1252270103Return.Geometry.y<467/1000\n', 1),
        (' ell_interval : 1672/10000<QRH.Record1252270103Return.Geometry.ell ∧ QRH.Record1252270103Return.Geometry.ell<171/1000\n',
         ' ell_interval : 1672/10000<QRH.Record1252270103Return.Geometry.ell ∧ QRH.Record1252270103Return.Geometry.ell<175/1000\n', 1),
        (' small_saving : 7/100<QRH.Record1252270103Return.Geometry.y/2-QRH.Record1252270103Return.Geometry.h*(17/50-1/6)-1/50\n',
         ' small_saving : 6/100<QRH.Record1252270103Return.Geometry.y/2-QRH.Record1252270103Return.Geometry.h*(17/50-1/6)-1/50\n', 1),
        (' have he : ell<171/1000 := ', ' have he : ell<175/1000 := ', 1),
        ('theorem ell_interval : 1672/10000<ell ∧ ell<171/1000 := ', 'theorem ell_interval : 1672/10000<ell ∧ ell<175/1000 := ', 1),
        ('theorem ly_coarse : 458/1000<ly ∧ ly<467/1000 := ', 'theorem ly_coarse : 440/1000<ly ∧ ly<467/1000 := ', 1),
        ('theorem small_saving : 7/100<ly/2-h*(17/50-1/6)-1/50 := ', 'theorem small_saving : 6/100<ly/2-h*(17/50-1/6)-1/50 := ', 1),
        ('`theta = 174799/200000`, `h = 8053/10000`. The two functional fields are unchanged. -/',
         '`theta = 174799/200000`, `h = 8053/10000`. The functional field `floor_margin` is unchanged.\n'
         'ArviDensity fork: `ell` is widened once more to `< 175/1000` (`theta > 873/1000` forces `ell < 0.17467`), and the\n'
         'other functional field and the lower end of `y` are relaxed to `small_saving` threshold `6/100` (was `7/100`)\n'
         'and `y > 440/1000` (was `458/1000`), so that the box is cut only by `theta > 873/1000` and `floor_margin`. -/', 1),
    ],
    'Transport/FinalFixedHigh.lean': [
        ('have hy : 458/1000<Geometry.y := ', 'have hy : 440/1000<Geometry.y := ', 2),
    ],
}


def split_header(text):
    """(header, rest): header = the leading run of `/- ... -/` notice blocks (not `/--` doc comments)."""
    pos = 0
    while True:
        m = re.match(r'[ \t]*\n?', text[pos:])
        start = pos + (m.end() if m else 0)
        if text.startswith('/-', start) and not text.startswith('/--', start):
            end = text.index('-/', start) + 2
            nl = text.find('\n', end)
            pos = (nl + 1) if nl != -1 else len(text)
        else:
            break
    return text[:pos], text[pos:]


def rename(s):
    for a, b in RENAMES:
        s = s.replace(a, b)
    return s


def main():
    assert os.path.isdir(SRC), SRC
    assert not os.path.exists(DST), f'{DST} exists'
    n = 0
    for dp, _, fs in os.walk(SRC):
        for f in sorted(fs):
            if not f.endswith('.lean'):
                continue
            src = os.path.join(dp, f)
            rel = os.path.relpath(src, SRC)
            text = open(src, encoding='utf-8').read()
            head, rest = split_header(text)
            assert head.strip(), rel
            for old, new, cnt in EDITS.get(rel, []):
                assert rest.count(old) == cnt, (rel, old, rest.count(old))
                rest = rest.replace(old, new)
            notice = NOTICE_BOX if rel in EDITS else NOTICE_PLAIN
            body = rename(rest)
            assert not re.search(r'SilDensitySplit|sil_density_split', body), f'{rel}: old names left in the code'
            out = head + notice + '\n' + body
            dst = os.path.join(DST, rel)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            open(dst, 'w', encoding='utf-8').write(out)
            n += 1
    print(f'{n} modules written to {DST}')


if __name__ == '__main__':
    main()
