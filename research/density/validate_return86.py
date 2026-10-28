#!/usr/bin/env python3
"""Validation of gen_return86.py against PR 86's own `Return/` (Submissions.density_split_fine_chain.Return, 44 modules).

 (1) regenerate PR 86's constants in PR 86's names (--no-notice): the 44 modules must equal PR 86's byte for byte;
 (2) regenerate in the names of Submissions.arvi_density (single-source endpoint, PR 86's cover): after mapping the
     module prefixes / namespaces back and removing our one-line modification notices, equal to PR 86's;
 (3) the generated package files (if present) are the (2)-output except for Endpoint.lean (two-source), i.e. the files on
     disk equal a fresh generation;
 (4) the cover spec extracted from PR 86 is stable (extract -> regenerate -> extract);
 (5) auto cover (greedy) on PR 86's constants: certified, row/window counts; least 7-digit theta of PR 86's faces.

usage: python3 validate_return86.py [PACKAGE_RETURN_DIR]
"""
import filecmp, json, os, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
GEN = os.path.join(HERE, 'gen_return86.py')
PR86 = '/home/user/lean-env/qrh/Submissions/density_split_fine_chain/Return'
PKG_RETURN = sys.argv[1] if len(sys.argv) > 1 else '/home/user/lean-env/qrh/Submissions/arvi_density/Return'


def run(*args):
    r = subprocess.run([sys.executable, GEN, *args], capture_output=True, text=True)
    if r.returncode:
        print(r.stdout, r.stderr)
        raise SystemExit(1)
    return r.stdout.strip()


def tree(root):
    out = {}
    for dp, _, fs in os.walk(root):
        for f in fs:
            if f.endswith('.lean'):
                out[os.path.relpath(os.path.join(dp, f), root)] = open(os.path.join(dp, f), encoding='utf-8').read()
    return out


def unname(text):
    """map our names back to PR 86's and drop our notice lines"""
    text = text.replace('Submissions.arvi_density.ReturnD', 'Submissions.sil_density_split_20261026.ReturnD')
    text = text.replace('Submissions.arvi_density.Return', 'Submissions.density_split_fine_chain.Return')
    text = text.replace('QRH.ArviDensity', 'QRH.SilDensitySplit')
    return '\n'.join(l for l in text.split('\n') if not l.startswith('/- Modified by ArviFoxy'))


ref = tree(PR86)
ok = True
with tempfile.TemporaryDirectory() as td:
    # (1)
    d1 = os.path.join(td, 'pr86names')
    print(run(d1, '--preset', 'pr86', '--pkg', 'Submissions.density_split_fine_chain', '--returnd-pkg',
              'Submissions.sil_density_split_20261026', '--ns', 'QRH.SilDensitySplit', '--endpoint', 'single',
              '--cover', 'pr86', '--box', 'pr83', '--no-notice'))
    t1 = tree(d1)
    same = set(t1) == set(ref) and all(t1[k] == ref[k] for k in ref)
    print(f'(1) PR 86 names: {len(t1)} modules vs {len(ref)}; byte-identical: {same}')
    ok &= same
    # (2)
    d2 = os.path.join(td, 'arvi')
    print(run(d2, '--preset', 'pr86', '--pkg', 'Submissions.arvi_density', '--ns', 'QRH.ArviDensity', '--endpoint', 'single',
              '--cover', 'pr86'))
    t2 = tree(d2)
    # the regenerated header lines of our notices are single lines starting with '/- Modified by ArviFoxy'
    diffs = [k for k in ref if unname(t2[k]).rstrip('\n') != ref[k].rstrip('\n')]
    nnote = sum(sum(1 for l in v.split('\n') if l.startswith('/- Modified by ArviFoxy')) for v in t2.values())
    print(f'(2) arvi names: {len(t2)} modules; {nnote} notice lines; differing after un-naming: {diffs}')
    ok &= not diffs and set(t2) == set(ref)
    # (3)
    d3 = os.path.join(td, 'arvi2')
    run(d3, '--preset', 'pr86', '--pkg', 'Submissions.arvi_density', '--ns', 'QRH.ArviDensity', '--cover', 'pr86')
    if os.path.isdir(PKG_RETURN):
        t3, tp = tree(d3), tree(PKG_RETURN)
        bad = sorted(k for k in t3 if tp.get(k) != t3[k]) + sorted(set(tp) - set(t3))
        print(f'(3) {PKG_RETURN}: {len(tp)} modules, differing from a fresh generation: {bad}')
        ok &= not bad
    # (4)
    spec1 = json.load(open(os.path.join(HERE, 'return86_tpl', 'cover_pr86.json')))
    p4 = os.path.join(td, 'cover.json')
    run('--extract-cover', os.path.join(d1, 'EdgeCertificates.lean'), os.path.join(d1, 'Windows.lean'), p4)
    spec2 = json.load(open(p4))
    print('(4) cover spec re-extracted from the regenerated PR 86 modules equals the stored one:', spec1 == spec2)
    ok &= spec1 == spec2
    # (5)
    d5 = os.path.join(td, 'auto')
    print('(5)', run(d5, '--preset', 'pr86', '--pkg', 'Submissions.arvi_density', '--cover', 'auto'))
    print('(5) least 7-digit theta of PR 86\'s faces, h = floor ceiling to 4 digits:',
          run('--preset', 'pr86', '--find-theta', '0.8739', '0.87405', '--h', 'auto:4'))
print('ALL OK' if ok else 'MISMATCH')
sys.exit(0 if ok else 1)
