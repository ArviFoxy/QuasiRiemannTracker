import json, os, re, shutil
LE = '/home/user/lean-env/qrh'
SL = LE + '/Submissions/arvi_selected_leaf'
UP = '/home/user/sub-sl/submissions'
g = json.load(open(os.path.expandvars('$SCRATCH/pr/final_graph.json')))
jd = sorted(m for m in g if m.startswith('Candidate.Local.Qrh.JointDetector.'))
ret = sorted(m for m in g if m.startswith('Submissions.arvi_density.Return.'))
tun = sorted(m for m in g if m.startswith('Submissions.arvi_return_tuning.'))
retX = {m.split('.')[-1] for m in ret}
assert len(jd) == 114 and len(ret) == 14 and len(tun) == 15, (len(jd), len(ret), len(tun))
def p(m): return os.path.join(LE, *m.split('.')) + '.lean'
def rewrite(src):
    out = []
    for line in src.split('\n'):
        s = line
        if s.startswith('import '):
            mods = s[7:].split()
            new = []
            for x in mods:
                if x.startswith('Candidate.Local.Qrh.JointDetector.'):
                    x = 'Submissions.arvi_selected_leaf.JointDetector.' + x[len('Candidate.Local.Qrh.JointDetector.'):]
                elif x.startswith('Submissions.arvi_return_tuning.'):
                    x = 'Submissions.arvi_selected_leaf.Tuning.' + x[len('Submissions.arvi_return_tuning.'):]
                elif x.startswith('Submissions.arvi_density.Return.') and x.split('.')[-1] in retX and x.count('.') == 3:
                    x = 'Submissions.arvi_selected_leaf.Return.' + x.split('.')[-1]
                elif x.startswith('Candidate.'):
                    raise SystemExit('unexpected Candidate import ' + x)
                new.append(x)
            s = 'import ' + ' '.join(new)
        out.append(s)
    return '\n'.join(out)
plan = []
for m in jd: plan.append((p(m), SL + '/JointDetector/' + '/'.join(m.split('.')[4:]) + '.lean'))
for m in ret: plan.append((p(m), SL + '/Return/' + m.split('.')[-1] + '.lean'))
for m in tun: plan.append((p(m), SL + '/Tuning/' + m.split('.')[-1] + '.lean'))
for a, b in plan:
    assert not os.path.exists(b), b
    os.makedirs(os.path.dirname(b), exist_ok=True)
    open(b, 'w', encoding='utf-8').write(rewrite(open(a, encoding='utf-8').read()))
# own modules
own = sorted(m for m in g if m.startswith('Submissions.arvi_selected_leaf.'))
for m in own:
    f = p(m); s = open(f, encoding='utf-8').read(); s2 = rewrite(s)
    if s2 != s: open(f, 'w', encoding='utf-8').write(s2)
# notices of PR 93, verbatim
shutil.copy(UP + '/2026-10-28-joint-detector-fine-chain/src/Candidate/Notices.lean', SL + '/JointDetector/Notices.lean')
print('copied', len(plan), 'modules; own rewritten', len(own))
