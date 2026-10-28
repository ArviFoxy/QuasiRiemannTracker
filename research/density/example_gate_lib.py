"""Example `--gate-lib` file for gen_hybrid.py: how to replace / add / remove a gate.

    gen_hybrid.py --from-header HybridK15_01.lean --module Gen_01 --namespace QRH.ArviDensityLab \\
                  --gate-lib example_gate_lib.py -o Gen_01_inflated.lean

The file is executed with the module `gen_hybrid` available as `gh`.  It must define either
`LIB` (a `gh.GateLib`) or `modify(lib) -> gh.GateLib`.

This example does NOT change any mathematics.  It re-certifies two gates through a *different but
equivalent* cleared pair, multiplying numerator and denominator by (1 + D v)^k:  the Lean lemma
(`gQLower_mul`) and the generated `ring` step (`Ng * d = n * Dg`) are unchanged and remain true, but
the polynomials get degree 1+k, which exercises Bernstein degrees above PR 83's `bern4` (the
generator then emits local `lbernN` lemmas).  Use it as a template:

  * REPLACE a gate  : lib.replace('high_at_q', gh.Gate(key='high_at_q', short='HighAtQ', ...))
  * ADD a gate      : lib.add(gh.Gate(key='my_gate', ...), after='high_at_q')   # also needs the Lean
                      structure field `my_gate`, the function `gMyGate` and the lemma `gMyGate_mul`
  * REMOVE a gate   : lib.without('q_floor')                                    # field is dropped too
  * extra hypotheses: lib.with_hyp('hG', "  have hG := (G_pos v h0).ne'")  and put the lemma `G_pos`
                      into `lib.preamble_lemmas` (templates; `{D}`, `{A}`... are Lean literals)
"""
from dataclasses import replace


def _inflate(g, k):
    def cleared(P):
        Ng, Dg = g.cleared(P)
        return Ng * P.X ** k, Dg * P.X ** k
    return replace(g, cleared=cleared)


def modify(lib):
    by_key = {g.key: g for g in lib.gates}
    lib = lib.replace('q_lower', _inflate(by_key['q_lower'], 4))        # degrees 5/5  -> lbern5
    lib = lib.replace('H_lower', _inflate(by_key['H_lower'], 2))        # degrees 3/3  -> bern3
    return lib
