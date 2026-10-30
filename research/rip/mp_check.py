"""Compare measured top eigenvalues with the Marchenko-Pastur edge (1 + sqrt(|W|/S_eff))^2, S_eff = mean diag."""
import subprocess, sys, re
for B, L, P0 in ((3000, 6000, 40), (3000, 3000, 40), (3000, 12000, 40), (1500, 3000, 120)):
    out = subprocess.run(['python3', '-I', 'zfamily.py', str(B), str(L), str(P0)], capture_output=True, text=True, timeout=3000).stdout
    lines = out.strip().splitlines()
    head = lines[0]; print(head)
    m = re.search(r'rows R=(\d+)\s+sources S=(\d+)\s+mean diag (\d+)\s+full top/diag = ([\d.]+)', head)
    R, S, dm, full = int(m.group(1)), int(m.group(2)), float(m.group(3)), float(m.group(4))
    print('   full: measured %.3f   MP edge (R/diag) %.3f' % (full, (1 + (R / dm) ** .5) ** 2))
    print('  ', lines[1].strip())
    print('  ', lines[2].strip())
    for ln in lines[3:]:
        mm = re.search(r'\|W\|=\s*(\d+)\s+random ([\d.]+)\s+large-value\(slot\) ([\d.]+)\s+bias-aligned ([\d.]+)', ln)
        k = int(mm.group(1)); mp = (1 + (k / dm) ** .5) ** 2
        print('   |W|=%4d  MP %.3f | random %s  slot-LV %s  bias-aligned %s' % (k, mp, mm.group(2), mm.group(3), mm.group(4)), flush=True)
