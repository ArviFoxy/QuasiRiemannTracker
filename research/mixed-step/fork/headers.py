#!/usr/bin/env python3
"""Header policy for the mixed-step Lean tree (one tool; idempotent; source mtimes are kept).

* A module we wrote (everything outside `ForkMx/`) carries NO copyright line and no license boilerplate.
  A third-party `Copyright (c) 2026 <name>. Apache-2.0.` line is removed from it, together with any
  `Modifications Copyright ...` line. A plain sentence "adapted from X" in the docstring stays.
* A module under `ForkMx/` is a modified copy of somebody's file. It keeps ONE copyright line that lists the
  holders, `Copyright (c) 2026 Hailey Collet, ArviFoxy. Apache-2.0.` (no separate "Modifications" line).
* License boilerplate inside the fork notes ("Apache-2.0; inherited notices retained") is dropped.
  Provenance blocks inherited from PR 76 (`Adapted from Zhongpai Gao ...`) are left as they are.

usage: headers.py [--dry] DEVROOT   (DEVROOT = Submissions/arvi_mixed_step or a copy of it)
"""
import os, re, sys

MOD = 'Modifications Copyright (c) 2026 ArviFoxy. Apache-2.0.'
THIRD = re.compile(r'Copyright \(c\) 2026 (Hailey Collet|Sil)\. Apache-2\.0\.')
LIST_LINE = 'Copyright (c) 2026 Hailey Collet, ArviFoxy. Apache-2.0.'

# boilerplate inside the notes, most specific first
BOILER = [
    (r"\(Hailey Collet, Apache-2\.0;\s+inherited notices retained\)", "(Hailey Collet)"),
    (r"\(PR 76 fork of Hailey Collet's module, Apache-2\.0\)", "(PR 76 fork of Hailey Collet's module)"),
    (r"\(Hailey Collet, Apache-2\.0\)", "(Hailey Collet)"),
    (r",?\s*Apache-2\.0;\s+inherited notices retained", ""),
    (r";\s+inherited notices retained", ""),
    (r"\s+inherited notices retained", ""),
    (r", Apache-2\.0\)", ")"),
    (r", Apache-2\.0([.;,])", r"\1"),
    (r"Apache-2\.0; ", ""),
    (r",? Apache-2\.0\.? -/", " -/"),
]


def split_header(text):
    """(header, rest): header = everything before the first line that starts with `import `."""
    m = re.search(r'^import ', text, re.M)
    if not m:
        return None, text
    return text[:m.start()], text[m.start():]


def blocks(header):
    """The leading `/- ... -/` blocks of the header as (start, end) spans."""
    spans, i = [], 0
    while True:
        j = header.find('/-', i)
        if j < 0:
            break
        k = header.find('-/', j + 2)
        if k < 0:
            break
        spans.append((j, k + 2))
        i = k + 2
    return spans


def transform(text, fork):
    header, rest = split_header(text)
    if header is None:
        return None
    out = header
    # 1. drop our own "Modifications" line (first line of a block, or inside one)
    out = re.sub(r'^/- ' + re.escape(MOD) + r'[ \t]*\n', '/- ', out, flags=re.M)
    out = re.sub(r'^' + re.escape(MOD) + r'[ \t]*\n', '', out, flags=re.M)
    out = re.sub(r'^/- ' + re.escape(MOD) + r' -/[ \t]*\n', '', out, flags=re.M)
    # 2. third-party copyright line
    def third(m):
        who = m.group(1)
        if fork and who == 'Hailey Collet':
            return LIST_LINE
        return None
    # single-line block `/- Copyright ... -/`
    def single(m):
        return ('/- ' + LIST_LINE + ' -/\n') if (fork and m.group(1) == 'Hailey Collet') else ''
    out = re.sub(r'^/- ' + THIRD.pattern + r' -/[ \t]*\n', single, out, flags=re.M)
    # first line of a longer block
    def first(m):
        return ('/- ' + LIST_LINE + '\n') if (fork and m.group(1) == 'Hailey Collet') else '/- '
    out = re.sub(r'^/- ' + THIRD.pattern + r'[ \t]*\n', first, out, flags=re.M)
    # 3. boilerplate in the notes (not in inherited provenance blocks)
    pieces, last = [], 0
    for (a, b) in blocks(out):
        pieces.append(out[last:a])
        blk = out[a:b]
        if 'tracker snapshot' not in blk and not blk.startswith('/- Adapted from Zhongpai Gao'):
            keep = LIST_LINE in blk
            if keep:
                blk = blk.replace(LIST_LINE, '@@HOLDERS@@')
            for pat, rep in BOILER:
                blk = re.sub(pat, rep, blk)
            if keep:
                blk = blk.replace('@@HOLDERS@@', LIST_LINE)
        pieces.append(blk)
        last = b
    pieces.append(out[last:])
    out = ''.join(pieces)
    # tidy: a block opening `/-` followed directly by a newline
    out = re.sub(r'^/-\s*\n(?!\s*-/)', '/- ', out, flags=re.M)
    return out + rest


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
            rel = os.path.relpath(p, root)
            fork = rel.startswith('ForkMx' + os.sep)
            t = open(p, encoding='utf-8').read()
            new = transform(t, fork)
            if new is None:
                stats['no import'] = stats.get('no import', 0) + 1
                print('NO IMPORT', rel)
                continue
            how = 'same' if new == t else ('fork' if fork else 'own')
            stats[how] = stats.get(how, 0) + 1
            if new != t and not dry:
                st = os.stat(p)
                open(p, 'w', encoding='utf-8').write(new)
                os.utime(p, (st.st_atime, st.st_mtime))
    print(stats)


if __name__ == '__main__':
    main()
