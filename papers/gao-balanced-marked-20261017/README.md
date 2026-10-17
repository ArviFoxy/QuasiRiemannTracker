# Balanced source energies and adaptive marked moments

[Read the four-page paper](paper.pdf) · [TeX source](paper.tex)

The paper proves uniform affine source estimates for two planes, using the
common geometric surplus and density-adaptive marked moments. A finite count
envelope then gives the all-moduli Dirichlet nonvanishing boundary
**87483/100000 = 0.874830**, with the principal pole excluded.

The main text, including references, is four pages. Companion arithmetic tables
and source bindings are provided separately:

- [Five-row rational certificate](arithmetic/five-row-certificate.json).
- [Full-width source scalar controls](arithmetic/source-certificate.json).
- [Ten upward availability windows](arithmetic/availability-windows.json).
- [Formula and theorem bindings](formula-bindings.json).
- [Document receipt](paper-receipt.json).
- [Canonical all-Dirichlet theorem](../../submissions/gao-balanced-marked-20261017/src/Candidate/Target830/Final.lean).

The complete source and final endpoint passed local Lean checks with cached
accepted dependencies, using only `propext`, `Classical.choice`, and
`Quot.sound`. Local full replay is skipped. GitHub's exact-head source replay,
Comparator, and independent-kernel checks determine tracker admission.

The rational certificates are unchanged scalar certificates; the source and
endpoint bindings identify the Lean theorems that complete the analytic proof.
Render with Tectonic 0.15.0 using `tectonic --keep-logs paper.tex`.

Zhongpai Gao, with AI assistance. References are in the paper;
inherited source attribution and license notices accompany the submission.
