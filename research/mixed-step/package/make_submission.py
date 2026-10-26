"""Assemble the upstream submission directory for arvi-mixed-step-20261026.

Layout (as PR 76): DEST/metadata.json, DEST/src/Candidate/Main.lean,
DEST/src/Submissions/arvi_mixed_step_20261026/<the import closure of Candidate/Main.lean inside the package>.

Only modules in the closure are copied (other agents' work in progress in the package directory is left
out); the script refuses a closure that reaches the development prefix Submissions.arvi_mixed_step (not
packaged) or PR 76's return (namespace clash). It prints the module count and the total size.

usage: python3 make_submission.py LAKE DEST
  LAKE: the Lake project holding Submissions/arvi_mixed_step_20261026 (already refreshed by package_mixed.py)
  DEST: e.g. <upstream worktree>/submissions/arvi-mixed-step-20261026 (its src/ is replaced)
"""
import os, re, sys, shutil

HERE = os.path.dirname(os.path.abspath(__file__))
SUB = os.path.join(HERE, 'arvi-mixed-step-20261026')
PKG = 'Submissions.arvi_mixed_step_20261026'
DEV = 'Submissions.arvi_mixed_step.'
PR76_RET = ('Submissions.arvi_repeated_marks_on_sil_face_20261025.ReturnD',
            'Submissions.arvi_repeated_marks_on_sil_face_20261025.FinalReturn')
IMPORT = re.compile(r'^import\s+(\S+)', re.M)


def main():
    lake, dest = sys.argv[1], sys.argv[2]
    cand = os.environ.get('QRH_CANDIDATE', os.path.join(SUB, 'src', 'Candidate', 'Main.lean'))  # override: tests only
    todo = IMPORT.findall(open(cand).read())
    seen, mods = set(), []
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        if m.startswith(DEV):
            raise SystemExit(f'closure reaches the development tree: {m}')
        if m.startswith(PR76_RET):
            raise SystemExit(f"closure reaches PR 76's return: {m}")
        if not (m == PKG or m.startswith(PKG + '.')):
            continue
        p = os.path.join(lake, m.replace('.', '/') + '.lean')
        if not os.path.exists(p):
            raise SystemExit(f'missing module {m}')
        mods.append(m)
        todo += IMPORT.findall(open(p).read())
    bad = []
    forbidden = re.compile(r'\bsorry\b|\badmit\b|^\s*axiom\s|native_decide|^\s*#exit', re.M)
    for m in mods:
        text = open(os.path.join(lake, m.replace('.', '/') + '.lean')).read()
        text = re.sub(r'/-.*?-/', '', text, flags=re.S)          # drop comments before the scan
        text = re.sub(r'--[^\n]*', '', text)
        if forbidden.search(text):
            bad.append(m)
    if bad:
        raise SystemExit(f'forbidden constructs (sorry/admit/axiom/native_decide/#exit) in: {bad[:10]}')
    # header policy (fork/headers.py): no "Modifications Copyright" line anywhere, and a third-party copyright line
    # only on modified copies (ForkMx, and the return forks inherited from PR 76), never on a module we wrote
    copies = ('.ForkMx.', '.ReturnD.', '.FinalReturn.')
    stamped = []
    for m in mods:
        text = open(os.path.join(lake, m.replace('.', '/') + '.lean')).read()
        head = text.split('\nimport ', 1)[0]
        third = re.search(r'Copyright \(c\) 2026 (?!ArviFoxy)', head) is not None
        if 'Modifications Copyright' in head or (third and not any(c in m for c in copies)):
            stamped.append(m)
    if stamped:
        raise SystemExit(f'header policy broken (run fork/headers.py on the development tree): {stamped[:10]}')
    src = os.path.join(dest, 'src')
    if os.path.exists(src):
        shutil.rmtree(src)
    total = 0
    for m in sorted(mods):
        rel = m.replace('.', '/') + '.lean'
        out = os.path.join(src, rel)
        os.makedirs(os.path.dirname(out), exist_ok=True)
        shutil.copy2(os.path.join(lake, rel), out)
        total += os.path.getsize(out)
    os.makedirs(os.path.join(src, 'Candidate'), exist_ok=True)
    shutil.copy2(cand, os.path.join(src, 'Candidate', 'Main.lean'))
    shutil.copy2(os.path.join(SUB, 'metadata.json'), os.path.join(dest, 'metadata.json'))
    print(f'{len(mods)} package modules + Candidate/Main.lean, {total/1e6:.1f} MB of Lean source -> {dest}')


if __name__ == '__main__':
    main()
