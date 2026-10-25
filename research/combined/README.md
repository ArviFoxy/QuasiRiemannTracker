# The combined proof: our face family on Sil's fourth-power source face

Upstream PR 74 (Sil, `sil-fourth-power-20261025`, 0.8746935) is the new bar. This directory builds
our repeated-mark face family on top of Sil's source face, instead of on Collet's natural face.
The package is `arvi-repeated-marks-on-sil-face-20261025`.

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
  82k lines) is copied into our package as `Submissions.arvi_repeated_marks_on_sil_face_20261025.FourthPower.*`.
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

## 5. Can Sil's slope 93/25 be lowered? No (agent study, read-only)

- **Where 93/25 comes from.** It is exactly `2 + 4φ`, where `φ = 43/100` is the greedy
  slot-selection fraction (`GlobalSlotSelection.lean`). In the mixed gate, unselected width costs 2
  and selected width costs 4 + 2 − 2.
- **Binding lemma.** `OuterFreshMixedCapacity.actual_allocated_large_gate` needs `L ≥ 2 + 4φ`, with
  zero slack at φ = 43/100.
- **Why φ cannot drop.** The native gate `(3/4)·s < d` forces `φ > 3/7`. The 3/4 is
  `2β − 1 ≤ 3/4`, from the baseline's β ≤ 7/8.
- **Floor of the argument.** So the argument is limited to `L > 26/7 = 3.7142857`, which is
  `(2 + 6κ)/(1 + κ)` at κ = 3/4.
- **Gain from retuning φ.** At most 1/175 in slope, about 1e-6 in θ* (the price is about 1.7e-4
  per unit of slope). Bootstrapping κ from our own θ moves the floor by another 0.001 only.
- Not worth a fork.

## 6. Build and checks

- **Build.** `lake build Candidate.SilFace` in the PR 73 Lake project (Lean 4.34.1, Mathlib
  `d13f23b7`): 14,030 jobs. All 699 package modules are compiled.
- **Axioms.** `Candidate.bound` (Re s > 349843/400000) depends on `propext`, `Classical.choice`
  and `Quot.sound`.
- **Return transport bound.** At θ = 0.8746075, `ℓ = 11/3 − 4θ = 0.16824`, above the transport
  fork's `ℓ < 0.1678` (set for PR 73's θ). `fork_transport.py` now reads `QRH_RELAXED`.
  - With `ℓ < 0.1690` the regenerated `ReturnD` differs from the single stage's in three lines of
    `TransportGeometry.lean`. With the defaults it is byte-identical.
  - That upper bound only feeds `4ℓ < h` and `ℓ ≤ 1`.
- **Pitfall.** Never start a second `lake build` while one is running in the same project. Two
  builds raced on `.olean` files ("no such file" errors) until both were stopped.

## 7. Generators (single source of truth)

- `research/combined/sil_face.env` holds every parameter. `QRH_START` gives the first
  parent's (B, L, cap), which `chain_params.py` reads.
- `gen_steps.py` with `QRH_ASSEMBLY=1` also writes `Faceless/Gen/Chain.lean`, which contains:
  - the chain for any number of pieces;
  - the faces C and P (`family2.face_C/face_P`, which `theta_family2.py` also uses), with their
    exact values;
  - the faces file for the return.
- `Graph/Chain.lean` keeps only the generic lemmas.

## Regenerate

```sh
source sil_face.env
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
python3 fork_transport.py RD $QRH_SP      # ReturnD with QRH_RELAXED; module prefix renamed to the package
```

From `fork_return.py`'s output, only `CountWindows.lean` and `FinalEdgeCertificates.lean` change.
They go in together with `RET/FinalReturn/ReturnConstants.lean` and `RET/FinalReturn/Rows`. The
other forked modules are byte-identical to the single stage's.

## 8. A fresh look at Sil's development (maps in `fourthpower_map/`)

Nine read-only scans, one per module group (`fourthpower_map/A_core.md` … `I_return.md`), map all
478 modules at the level of statements.

- **The transfer is exact.**
  - For a fifth-power-free modulus `a`, `G_a(D⁴k) = χ_a(D)²·G_a(k)`, and it is 0 when `D` shares a
    prime with `a` (`GaussTransfer.fourth_power`, `fifth_free_nonunit_zero`).
  - The phase depends on `(D, a)`, not on the frequency `k`. So the whole slot family becomes one
    polynomial evaluated at `D⁴k` (`whole_column`).
  - The losses are only the density `1/W` of the D-average and `(16KW⁴)^ε` divisor fibres
    (`PositiveFamily.actual_average`).
  - The classical route instead uses `D⁶`: exact invariance, but D-dependent masks, root weight
    `N(D)^-3`, and the sextic sieve majorant.
- **The ledger.**
  - The mixed gate `P + 2S + 4d < R` charges 2 per unit of live slot width and 4 more per unit of
    selected width.
  - The unselected rest is deleted at the native cost 3/4 per unit, so the selected share must
    satisfy `(3/4)(1 − φ) < φ`, i.e. `φ > 3/7`.
  - Hence `2 + 4φ`, with infimum 26/7, against the classical `6κ = 9/2`.
- **A formal sextic large sieve is now available.** The `Sieve*` files prove an unconditional
  sextic large sieve (`OptimalBound`, constant 512C). The scalar iteration
  `α → (12α − 7)/(6α − 1)` runs from 2 to `7/6 + δ`.
  - Our round-11 scope study had found no sextic sieve in the formal library.
  - It is the missing input of the single-mark route (`F_P ≪ N·K^{7/6}`).
- **Sil's return cannot take our faces.** His return admits only faces implied by his source face
  (`Face.Included`), and it sits within 1.4e-7 of its certificate's limit.
- **It overturns one recorded barrier.** `../barriers/README.md` (2) says twisted multipliers
  "orthogonalize rather than amplify". Sil's twist is a function of the multiplier and the modulus
  only. It is constant along each column, so coherence survives.
- **A priced next step: a mixed step.**
  - In the continuum flow, our step's slot cost is `6q*`. The same selection argument at density
    `q` would cost `(2 + 6q)/(1 + q)`, which is smaller when `q > 1/√3`.
  - Float model (`q*` unchanged): count face (0.96920, 2.90788), physical face intercept 0.97354,
    **θ\* ≈ 0.8745898**, i.e. 1.75e-5 below this submission.
