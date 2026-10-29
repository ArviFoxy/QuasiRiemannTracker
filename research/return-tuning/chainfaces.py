"""All faces G(B_k, L_k, cap_k) proven by ChainF50/Chain.lean (source_k), k = 0..129."""
import re
from fractions import Fraction as Fr

CHAIN = '/home/user/lean-env/qrh/Submissions/arvi_density/ChainF50/Chain.lean'


def chain_faces(path=CHAIN):
    txt = open(path).read()
    faces = {}
    for m in re.finditer(r'theorem (source_(\d+)|boot_source|final_source)[^\n]*\n\s*QRH\.Record1252270103Source\.GlobalSource \(([\d ]+)/ ?([\d ]+) : ℝ\) \(([\d ]+) / ([\d ]+) : ℝ\) \(([\d ]+) / ([\d ]+) : ℝ\)', txt):
        pass
    # simpler: every GlobalSource literal following a theorem header
    for m in re.finditer(r'theorem (\w+) \(hβ[^\n]*\n\s*QRH\.Record1252270103Source\.GlobalSource \((\d+) / (\d+) : ℝ\) \((\d+) / (\d+) : ℝ\) \((\d+) / (\d+) : ℝ\)', txt):
        name = m.group(1)
        B = Fr(int(m.group(2)), int(m.group(3)))
        L = Fr(int(m.group(4)), int(m.group(5)))
        cap = Fr(int(m.group(6)), int(m.group(7)))
        faces[name] = (B, L, cap)
    return faces


if __name__ == '__main__':
    f = chain_faces()
    print(len(f))
    for k in list(f)[:3] + list(f)[-3:]:
        print(k, [float(v) for v in f[k]])
