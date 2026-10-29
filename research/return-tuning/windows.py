"""The 31 windows of Return/Windows.lean and the 47 row leaves of EdgeCertificates.lean (parsed)."""
import re
from fractions import Fraction as Fr

LEAN = '/home/user/lean-env/qrh/Submissions/arvi_density/Return'


def parse_windows(path=LEAN + '/Windows.lean'):
    txt = open(path).read()
    out = []
    for m in re.finditer(r'def returnWindow(\d+) : ReturnCountWindow where\n branch := \.(\w+)\n.*?deltaLo := \(([\d/]+):ℝ\)\n deltaHi := \(([\d/]+):ℝ\)\n pLo := \(([\d/]+):ℝ\)', txt, re.S):
        out.append(dict(idx=int(m.group(1)), branch=m.group(2), dlo=Fr(m.group(3)), dhi=Fr(m.group(4)), plo=Fr(m.group(5))))
    return out


def parse_rows(path=LEAN + '/EdgeCertificates.lean'):
    txt = open(path).read()
    rows = []
    for m in re.finditer(r'theorem envelope_row(\d+) \{δ p:ℝ\} \(hδ:δ∈Set\.Icc \(([\d/]+):ℝ\) \(([\d/]+):ℝ\)\) \(hp:p∈Set\.Icc \(([\d/]+):ℝ\) \(([\d/]+):ℝ\)\) : Ebase \(edgeD \.(\w+)\)', txt):
        idx = int(m.group(1))
        # body: which window / old
        body = txt[m.end(): txt.find('theorem', m.end())]
        w = re.search(r'returnWindow(\d+)\.Available', body)
        rows.append(dict(idx=idx, edge=m.group(6), box=((Fr(m.group(2)), Fr(m.group(3))), (Fr(m.group(4)), Fr(m.group(5)))),
                         window=int(w.group(1)) if w else None))
    return rows


if __name__ == '__main__':
    ws = parse_windows()
    print(len(ws), 'windows')
    from collections import Counter
    print(Counter(w['branch'] for w in ws))
    rs = parse_rows()
    print(len(rs), 'rows', Counter(r['edge'] for r in rs), 'with window:', sum(r['window'] is not None for r in rs))
    for r in rs:
        print(r['idx'], r['edge'], [(float(a), float(b)) for a, b in r['box']], r['window'],
              ws[r['window'] - 1]['branch'] if r['window'] else 'old')
