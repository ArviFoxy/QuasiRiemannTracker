# The combined proof: our face family on Sil's fourth-power source face

Upstream PR 74 (Sil, `sil-fourth-power-20261025`, 0.8746935) is the new bar. This directory builds
our repeated-mark face family on top of Sil's source face, instead of on Collet's natural face.
The package is `arvi-fourth-power-chain-20261025`.

**Result.** The exact θ* is **349843/400000 = 0.8746075**:
- 8.6e-5 below PR 74 (0.8746935);
- 7.6e-5 below the target 0.8746835 (1e-5 under the bar).

## 1. Why it works

- **Sil's face.** Sil proves one strong source face, `GlobalSource (99999/100000) (93/25) (3/50)`,
  with slot cost 3.72 against Collet's natural 4.5. His return uses only faces implied by it.
- **Our chain.** Our chain is a continuum of source steps (repeated-mark HIGH count, Lemma F) that
  lowers the slope of the face as `s` grows. It can start from any global source face.
- **The interface matches exactly.** Collet's graph predicate `Graph.P s` is
  `GlobalSource s.B s.L s.cap`, the conclusion of Sil's theorem.
- **Where to start.** Before the tangency, where the flow's slope equals the start face's slope
  (3.72), the start face is better than anything the flow produces. So the family starts there:
  `s₀* = 0.0329364` (`closed_flow.slope`), against 0.01228 for the natural face.

## 2. Three exact constraints found on the way

1. **Start exactly at the tangency.**
   - The first step, from Sil's face to the first face of the family, has the amplifier
     `a = (q·(L_S − L)(b − s₀)/L_S + fee)/(1 − 6qB_S/L_S)`.
   - Its denominator is about the family's `2^-15` plus `(L_S − L₀)·E/(B·L_S)`. Away from the
     tangency both the numerator and the denominator are linear in the slope gap, so `a` tends to
     `q(b − s₀)B/E ≈ 0.7(b − s₀)`. That is 0.0155 at `b = cap`, above the gate `a < 1/75`.
   - Only within about 1e-5 of the tangency in slope does the family's own `2^-15` dominate the
     denominator.
   - Measured: at `s₀ = 0.0331` the step fails gates 3 and 11. At `s₀ = 0.0329365` (6.5e-8 after
     the tangency) `a(cap) = 0.0010`, and the step is valid.
2. **The HIGH parent floor `B ≥ 22/23`.** The family cannot run past `s ≈ 0.0515`.
3. **The q floor `q ≥ 1/2` (Collet's conjunct).**
   - The family's `q = (1 − den)·L₀/(6B₀)`, so the family must end before `L/B < 3`.
   - With end 0.0500, nodes fail at `y ≥ 0.78` of the last piece (exact check). End 0.0472 keeps
     `q ≥ 0.50135`.
   - This costs 1.1e-6: θ* = 8746064 at end 0.0500, if the floor were not there, against 8746075.

## 3. The family and the return

- **Family.**
  - Breakpoints `σ = 0.0329365, 0.0376, 0.0423, 0.0472`: 3 pieces (the single stage has 5).
  - All checks pass: exact checks at random nodes, the first step and the junctions.
- **Final faces.**
  - count face `C = (0.96775, 2.91120)`, the last face;
  - physical face `P = (0.97187, 3.00000)`, at piece 2, grid index 42777.
- **Return.** `h = 401/500`, `sC = 13/250`, `sP = 9/200`. A scan of `h`, `sC` and `sP` finds at
  most 1e-7 more. 42 rows, 17 windows.

## 4. Sil's source theorem, vendored and forked

- **Why vendor.** Upstream imports only modules under `src/Submissions/<id>/`, and Sil's code is in
  `src/Candidate/FourthPower/`. So the import closure of his theorem (421 of his 478 modules,
  82k lines) is copied into our package as `Submissions.arvi_fourth_power_chain_20261025.FourthPower.*`.
  It is Apache-2.0, and the headers are kept.
- **The fork (`fork_sil.py`).**
  - Sil's statement assumes `theta < β` (his `theta = 0.8746935`). The construction uses that only
    through `contrary_inputs hcontra).1 : 51/100 ≤ β`.
  - The script replaces the hypothesis by `51/100 ≤ β` in the eight files that state or pass it.
    Two of those edits are `have hβ := hcontra`.
  - It asserts each replacement count, and that no other module uses the hypothesis.
  - The namespaces and proofs are otherwise untouched (`diff -I '^import '` shows only these lines).
- **What the start uses.** `Graph/Start.lean` proves `start_source : 51/100 ≤ β → P start` from the
  forked `actual_global_source`. `Graph/StartFace.lean` only names the face, so the step
  certificates do not depend on the 421 modules.

## 5. Generators (single source of truth)

- `research/combined/fourth_power_chain.env` holds every parameter. `QRH_START` gives the first
  parent's (B, L, cap), which `chain_params.py` reads.
- `gen_steps.py` with `QRH_ASSEMBLY=1` also writes `Faceless/Gen/Chain.lean`, which contains:
  - the chain for any number of pieces;
  - the faces C and P (`family2.face_C/face_P`, which `theta_family2.py` also uses), with their
    exact values;
  - the faces file for the return.
- `Graph/Chain.lean` keeps only the generic lemmas.

## Regenerate

```sh
source fourth_power_chain.env
cd ../faceless-chain
python3 theta_family2.py $QRH_SIG                     # θ* = 8746075
python3 exact_check.py $QRH_SIG && python3 exact_junctions.py $QRH_SIG
python3 fork_sil.py ...                               # see its docstring (PR 74 head bf20f0d3)
# Data module, then the packed extractions (need the built Data module):
python3 -c "import gen_all as G, family2 as F2; fam,_=F2.build2(G.SIG, m=G.M); G.gen_data(fam, 'GEN')"
python3 gen_certk.py <lake project> ck.txt && python3 gen_certs.py <lake project> cs.txt
QRH_CK=ck.txt QRH_CS=cs.txt python3 gen_all.py GEN && python3 gen_steps.py GEN faces.json
cd ../repeated-marks
python3 gen_return_lean.py faces.json $QRH_THETA $QRH_H 0 1 RET $QRH_SC $QRH_SP global
python3 fork_return.py RET OUT $QRH_CAP $QRH_CAP $QRH_SC $QRH_SP transport
```

From `fork_return.py`'s output, only `CountWindows.lean` and `FinalEdgeCertificates.lean` change.
They go in together with `RET/FinalReturn/ReturnConstants.lean` and `RET/FinalReturn/Rows`. The
other forked modules are byte-identical to the single stage's.
