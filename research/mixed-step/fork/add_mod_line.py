#!/usr/bin/env python3
"""Add our modification notice to every derived file (Apache-2.0 §4).

A file that keeps somebody else's copyright line (Collet's, Sil's) or is a ForkMx module is a derivative
work: the original copyright line stays first, verbatim, and the changes carry our own notice
    Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.
placed in front of the fork note (`Mixed step ...`) or, when the file has no such note, directly under the
copyright line. Files without a third-party copyright line that are not under ForkMx/ are new files and are
left alone (as in PR 76). Idempotent. Source mtimes are preserved (a comment edit does not make the oleans stale).
usage: add_mod_line.py [--dry] DEVROOT   (DEVROOT = Submissions/arvi_mixed_step or a copy of it)
"""
import os, re, sys
LINE = 'Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.'
NOTE = re.compile(r'^(/- )?Mixed step\b')


def patch(text, fork=False):
    lines = text.split('\n')
    ks = [i for i, l in enumerate(lines) if l.startswith('import ')]
    if not ks:
        return None, 'no import'
    k = ks[0]
    H = lines[:k]
    if any('ArviFoxy' in l for l in H):
        return None, 'already'
    third = bool(H) and H[0].startswith('/- Copyright (c) 2026')
    if not (third or fork):
        return None, 'new file'
    j = next((i for i, l in enumerate(H) if NOTE.match(l)), None)
    if j is not None:
        how = 'before-note'
        H[j] = '/- ' + LINE + '\n' + H[j][3:] if H[j].startswith('/- ') else LINE + '\n' + H[j]
    elif third:
        how = 'after-copyright'
        if H[0].rstrip().endswith('-/'):
            H[0] = H[0].rstrip()[:-2].rstrip() + '\n' + LINE + ' -/'
        else:
            H.insert(1, LINE)
    else:
        return None, 'new file'
    return '\n'.join(H + lines[k:]), how


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    dry = '--dry' in sys.argv
    root = args[0]
    stats = {}
    for d, _, fs in os.walk(root):
        for f in sorted(fs):
            if not f.endswith('.lean'):
                continue
            p = os.path.join(d, f)
            t = open(p).read()
            new, how = patch(t, os.path.relpath(p, root).startswith('ForkMx' + os.sep))
            stats[how] = stats.get(how, 0) + 1
            if new is None:
                if how == 'no import':
                    print('NO IMPORT', os.path.relpath(p, root))
                continue
            if not dry:
                st = os.stat(p)
                open(p, 'w').write(new)
                os.utime(p, (st.st_atime, st.st_mtime))
    print(stats)


main()
