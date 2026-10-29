"""Assemble the upstream submission folder for the floor-1/2 marked density chain.

Copies the import closure of ROOT inside the development package Submissions.arvi_density into
DEST/src/Submissions/<lean prefix>/..., renames the module prefix, writes DEST/src/Candidate/Main.lean
(`Candidate.bound`) and DEST/metadata.json. Checks: no sorry/admit/axiom/native_decide/#exit outside comments,
every .lean <= 2 MiB, folder <= 64 MiB and <= 8191 files, imports of other submissions only from DEPS.

usage: python3 make_package.py DEST [--id arvi-marked-density] [--root Submissions.arvi_density.FinalF50]
DEST is e.g. <upstream worktree>/submissions/2026-10-29-arvi-marked-density (its src/ is replaced).
"""
import argparse, json, os, re, shutil, sys

LAKE = '/home/user/lean-env/qrh'
DEV = 'Submissions.arvi_density'
IMPORT = re.compile(r'^import\s+(\S+)', re.M)
# stable ids of the dependencies and their Lean prefixes
DEPS = {
    'openai-baseline': 'Submissions.openai_baseline',
    'hailey-collet-1252270103': 'Submissions.hailey_collet_1252270103',
    'arvi-repeated-marks-on-sil-face-20261025': 'Submissions.arvi_repeated_marks_on_sil_face_20261025',
    'sil-density-split-20261026': 'Submissions.sil_density_split_20261026',
    'density-split-fine-chain': 'Submissions.density_split_fine_chain',
}
FORBIDDEN = re.compile(r'\bsorry\b|\badmit\b|^\s*axiom\s|native_decide|^\s*#exit', re.M)

MAIN = """/- All-moduli Dirichlet nonvanishing for Re(s) > 43693617/50000000 = 0.87387234 (principal pole excluded):
the floor-1/2 marked density chain (repeated-mark HIGH leaf) and the five-branch return. -/
import {prefix}.FinalF50
set_option autoImplicit false
namespace Candidate
theorem bound {{q : ℕ}} [NeZero q]
    (χ : _root_.DirichletCharacter ℂ q) {{s : ℂ}}
    (hs : (43693617 / 50000000 : ℝ) < s.re)
    (hpole : ¬ (χ = 1 ∧ s = 1)) :
    _root_.DirichletCharacter.LFunction χ s ≠ 0 :=
  QRH.ArviDensity.dirichlet_nonvanishing_f50 χ hs hpole
end Candidate
"""


def closure(root):
    todo, seen, mods = [root], set(), []
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        if not (m == DEV or m.startswith(DEV + '.')):
            continue
        p = os.path.join(LAKE, m.replace('.', '/') + '.lean')
        if not os.path.exists(p):
            raise SystemExit(f'missing module {m}')
        mods.append(m)
        todo += IMPORT.findall(open(p, encoding='utf-8').read())
    return sorted(mods), seen


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('dest')
    ap.add_argument('--id', default='arvi-marked-density')
    ap.add_argument('--root', default=DEV + '.FinalF50')
    ap.add_argument('--metadata', default=os.path.join(os.path.dirname(os.path.abspath(__file__)), 'metadata.json'))
    a = ap.parse_args()
    prefix = 'Submissions.' + a.id.replace('-', '_')
    folder = os.path.basename(os.path.normpath(a.dest))
    if not re.fullmatch(r'\d{4}-\d{2}-\d{2}-' + re.escape(a.id), folder):
        raise SystemExit(f'folder {folder} is not YYYY-MM-DD-{a.id}')
    mods, seen = closure(a.root)
    ext = sorted({m for m in seen if not m.startswith(DEV)})
    allowed = tuple(DEPS.values()) + ('Mathlib', 'PrimeNumberTheoremAnd', 'RellichKondrachov', 'Init', 'Lean', 'Std')
    bad = [m for m in ext if not m.startswith(allowed)]
    if bad:
        raise SystemExit(f'imports outside the declared dependencies: {bad[:10]}')
    src = os.path.join(a.dest, 'src')
    if os.path.exists(src):
        shutil.rmtree(src)
    total, nfiles = 0, 0
    for m in mods:
        text = open(os.path.join(LAKE, m.replace('.', '/') + '.lean'), encoding='utf-8').read()
        code = re.sub(r'/-.*?-/', '', text, flags=re.S)
        code = re.sub(r'--.*', '', code)
        if FORBIDDEN.search(code):
            raise SystemExit(f'forbidden token in {m}: {FORBIDDEN.search(code).group(0)!r}')
        text = re.sub(r'\b' + re.escape(DEV) + r'\b', prefix, text)
        rel = (prefix + m[len(DEV):]).replace('.', '/') + '.lean'
        out = os.path.join(src, rel)
        os.makedirs(os.path.dirname(out), exist_ok=True)
        open(out, 'w', encoding='utf-8').write(text)
        size = len(text.encode('utf-8'))
        if size > 2 * 1024 * 1024:
            raise SystemExit(f'{rel} exceeds 2 MiB ({size} bytes)')
        total += size
        nfiles += 1
    main_path = os.path.join(src, 'Candidate', 'Main.lean')
    os.makedirs(os.path.dirname(main_path), exist_ok=True)
    open(main_path, 'w', encoding='utf-8').write(MAIN.format(prefix=prefix))
    shutil.copy(a.metadata, os.path.join(a.dest, 'metadata.json'))
    md = json.load(open(a.metadata))
    used = sorted({d for d, p in DEPS.items() if any(m.startswith(p) for m in ext)})
    if sorted(md['dependencies']) != used:
        print(f'warning: metadata dependencies {sorted(md["dependencies"])} differ from the imported ones {used}')
    nfiles += 2
    if total > 64 * 1024 * 1024 or nfiles > 8191:
        raise SystemExit(f'folder too large: {total} bytes, {nfiles} files')
    print(f'{len(mods)} modules + Candidate/Main.lean, {total / 1e6:.1f} MB, prefix {prefix}; dependencies imported: {used}')


if __name__ == '__main__':
    main()
