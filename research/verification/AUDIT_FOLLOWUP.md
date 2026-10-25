# Proof-efficiency audit for the follow-up submission (2026-10-25)

PR 73 (`arvi-repeated-marks-20261024`) is frozen and will be merged as it is. This audit looks for
verification speedups for the next submission: inherited analytic theorems that are
overcomplicated or inefficiently proved, and our own code.

All numbers are for the closure of `Candidate.bound` and `Candidate.bound_sharp` of PR 73:
157,349 constants, 4315 MB of `lean4export` output.

Measurements:
- **Bytes.** `tools/attribute.py` (low-memory variant `attr_lean.py`, in the scratchpad) counts the
  export bytes each declaration introduces.
- **Kernel time.** `tools/KernelTime.lean` re-checks a declaration in the Lean kernel under a fresh
  name and times it, on 4 threads.
- **Closure cuts.** `tools/ClosureSplit.lean` computes what remains when one root is treated as a
  leaf.

## 1. Where the bytes go

| development | MB | share |
|---|---|---|
| Collet's admitted dependency | 2336 | 54.1% |
| OpenAI baseline | 836 | 19.4% |
| Mathlib | 804 | 18.6% |
| ours | 290 | 6.7% |

Collet's part, by directory:

| directory | MB |
|---|---|
| `Record1252270103Bootstrap.PR67Source` | 1024 |
| `Record1252270103Return.C30` | 438 |
| `Record1252270103Source.Admission` | 389 |
| `Record1252270103Source.High` | 111 |
| `Record1252270103Bootstrap.PR67Weighted` | 72 |

Bytes are cheap for the Lean kernel: the 60 heaviest declarations (599 MB) re-check in 67 s
(about 0.1 s per MB). They matter for the export step (511 s for 4.3 GB on 4 cores) and for the
memory of the external kernels. nanoda and con-ron were both killed by the 15 GB memory limit on
the full export (after 471 s and 731 s).

## 2. Where the kernel time goes

Lean kernel, every theorem and definition of the closure re-checked once. The total is
**4708 s single-thread** (1322 s wall on 4 threads).

| part | kernel s | after the cut of §3 |
|---|---|---|
| ours | 2730 | 2730 |
| — Faceless HIGH trees (60) | 2120 | |
| — Faceless scalar certificates | 479 | |
| — final-return rows | 46 | |
| Collet | 1080 | 241 |
| — `Bootstrap.PR67Source` | 581 | 0 |
| — `Return.C30` | 181 | 0 |
| — `Source.Admission` | 69 | 69 |
| baseline | 501 | 501 |
| Mathlib | 380 | 379 |
| **total** | **4708** | **3867** |

- **Our HIGH-tree certificates dominate.**
  - They are 60 `decide +kernel` proofs that a bicubic gate is positive on a face family.
  - The first 30 trees take 954 s, and all 60 are estimated at about 1900 s.
  - That is more than all of Collet's, the baseline's and Mathlib's declarations measured so far
    together.
  - Time per tree is about 14 s + 1.2 s × leaves + 0.23 s × intervals (fit over 30 trees). Even a
    one-leaf tree takes 12–42 s.
  - So the cost is the per-tree computation of the 16 coefficient polynomials (`highU`), which is
    done in `Rat` polynomial arithmetic inside the kernel. The tree checks themselves (integer
    Kronecker tests) are not the cost.
  - Every kernel repeats this work: Lean at compile time, Comparator, nanoda and con-ron.
- **Collet's plumbing is heavy in bytes but light in time.** The five `Admission.SelectedLow*`
  theorems (300 MB) re-check in 27 s.

## 3. The structural cut: one stage at the natural cost K = 9/2

**Why PR 73 carries three bootstrap levels.**
- The source steps and the final return need the cap `6(2β − 1) ≤ K`, where K is the natural cost.
- Collet's design proves it in stages:
  1. **PR 67 re-proof.** `Record1252270103Bootstrap.incumbent_beta` is a complete re-proof of PR 67
     (β ≤ 0.874817065, 1 GB). It supplies `6(2β − 1) ≤ seedK = 4.4978269`.
  2. **Seed step and intermediate return.** Collet's seed step and intermediate return (`C30`,
     437 MB) prove β ≤ 0.8747759. That gives our final `K = 4.4973108`.
  3. **Final stage.** Our chain and return.

**Why we do not need them.**
- Our face family starts on Collet's natural face `GlobalSource 1 K (11/200)`, which
  `natural_global_source` accepts for any `21/5 ≤ K ≤ 9/2`.
- Its end faces are insensitive to K: the chain's end is set by the LOW/HIGH dynamics, not by the
  seed (re-feed measurement in `../LOG.md`).
- So `K = 9/2 = 6(2·7/8 − 1)` works. Its cap is the baseline's own theorem β ≤ 7/8.

**What it saves** (closure cut, all three treated as leaves):

| removed | MB |
|---|---|
| PR 67 re-proof (`incumbent_beta`) | 1099 |
| intermediate return | 481 |
| seed step | 79 |
| **total, 4315 → 2656 MB** | **1659 (−38.5%)** |

Collet's share falls from 2336 MB to 681 MB.

**What it costs.**
- The family is regenerated with K = 9/2:
  - start `σ₀ = 0.0122820`, where the flow's slope reaches K;
  - end `σ₅ = 0.0424122`, the last point with parent `B₀ ≥ 22/23`;
  - physical face at grid index 41756.
- θ* moves from 0.8747250 to 0.8747252 (+2e-7).
- The exact checks pass:
  - SourceValid2 at sample faces of all five pieces;
  - the natural → piece 0 step and the four junctions.
- The return regenerates with 32 rows and 9 windows (before: 34 and 11).
- The value 2186813/2500000 = 0.8747252 is still below PR 73's declared 0.8747289.

**Lean.**
- The local package `arvi_followup` (not a submission yet) is the PR 73 package with these changes:
  - `natK = 9/2` and the natural face `natural92`;
  - the baseline premise in `Graph/NaturalCap.lean`;
  - a single-stage `Graph/Endpoint.lean` and `FinalReturn/EndpointFromGlobalSources.lean`;
  - regenerated `Faceless/Gen` and `FinalReturn`;
  - the NF step without the bootstrap import.
- Candidate: `Candidate/Followup.lean` (`CandidateFollowup.bound_sharp` at 2186813/2500000).
- It builds (13,624 jobs) and depends only on the three standard axioms.
- Its closure has 136,162 constants. `incumbent_beta`, the seed step and the intermediate return
  are absent.

| export | PR 73 | follow-up |
|---|---|---|
| total | 4315 MB in 511 s | **2727 MB in 245 s** |
| baseline | 836 MB | 835 MB |
| Mathlib | 804 MB | 801 MB |
| Collet | 2336 MB | 714 MB |
| ours | 290 MB | 329 MB (now includes `scalarGate92` and its cast lemma) |

The sources are in `../followup/` (README there).

The generators take `QRH_K`, `QRH_SIG`, `QRH_PKG` and `QRH_NATURAL`. With their defaults they
reproduce PR 73's files byte for byte: `Steps.lean` and all of `FinalReturn` were checked.

## 4. Proof-level findings

1. **HIGH certificates (ours): the largest kernel cost.**
   - Compute the 16 coefficient polynomials in integer arithmetic. The family data is scaled to
     integer polynomials once, the scale factors are proved generically, and the products are
     integer, so the kernel needs no `Rat` normalization.
   - Optionally, use Kronecker-packed big-number multiplication.
   - The trees stay valid under positive constant scaling.
2. **Collet's `Admission` plumbing (300 MB, 27 s).**
   - Each of the five theorems restates a 300-line ∀∃ statement with about 150 hypotheses and lets,
     and proves it from the previous one by passing every argument through.
   - The statement is reinstantiated at different binder depths, so de Bruijn indices differ and
     nothing is shared. This happens through `Classical.choose` chains (each motive is the rest of
     the statement), `have` with inferred types, `refine ⟨_, ?_⟩` motives, `filter_upwards`, and
     the final `simpa`.
   - Fixes: bundle hypotheses into structures or definitions, use `obtain` instead of
     `Classical.choose`, and merge the five layers. The gain is export bytes and external-kernel
     memory, not Lean kernel time.
3. **Our `fin_cases` + `ring` lemmas (59 MB, 5 s).**
   - `highGateReal_affine` (24 MB), `bicubic_eval_bern` (21 MB) and `gateG_bicubic` (14 MB) expand
     big polynomial identities case by case.
   - `bicubic_eval_bern` follows from the univariate `cubic_eval_bern` twice, plus sum exchanges.
   - `highGateReal_affine` follows from affinity of the composition (the gate is linear in the
     width atoms).
   - `gateG_bicubic` follows from "bicubic interpolation reproduces bidegree-(3,3) polynomials".

## 5. What the faces/ODE work did for the proof size

- **What it replaced.** The face family (`Faceless/`) replaced the 59 certified nodes of the
  source graph with one curve and a uniform certificate.
- **How small that part is now.** Our whole submission is 290 MB of 4315 MB.
  - Return rows: 103 MB.
  - HighGate and Bernstein lemmas: 63 MB.
  - Forked source plumbing: 54 MB.
  - Faceless certificates: about 30 MB.
- **Its byte saving is not where the time goes.**
  - The size problem is the inherited stages (section 3).
  - The time problem is the HIGH certificates (section 2), which the family made uniform but still
    computes in `Rat`.
- **What it did enable.** The structural cut depends on a property of the flow: the end faces do
  not depend on the seed.

## 6. The HIGH certificates in packed integer arithmetic (done)

Kernel time of the 60 HIGH certificates of the follow-up, re-checked one by one
(`tools/KernelTime.lean`, single thread):

| version | kernel s | heaviest certificate |
|---|---|---|
| PR 73 (`certI`: `Rat` polynomials, then the tree) | about 2120 | about 100 s |
| packed coefficients, PR 73's tree check | 563 | 70 s |
| packed coefficients and packed interval tests | **107** | 5.1 s |

The whole follow-up candidate rebuilds in 142 s wall on 4 cores (the 60 HIGH files: 418 s of build
time, at most 11 s each). Both `CandidateFollowup` theorems still depend only on `propext`,
`Classical.choice` and `Quot.sound`.

**Two phases.** Each certificate is now three theorems: `{tag}_dec` (phase 1, about 1 s),
`{tag}_tree` (phase 2) and `{tag}_pos`, which combines them (`Pk.coeffPos_of_decKgXZ`).

1. **Phase 1: the coefficients, packed** (`Faceless/Packed.lean`, `Faceless/TreeZ.lean`).
   - Every polynomial of the HIGH formula is carried as
     `⟨A(X), B(X), A(1), B(1), e, len, ok⟩`, which stands for `(A − B)/Δ^e`.
     Here `A, B` are natural coefficient lists and `Δ` is a common denominator of the piece's data.
   - A product is four big-number products. A sum aligns the powers of `Δ`. A rational constant
     `c` is applied as the integer `c.num · Δ/c.den`.
   - The formula is mirrored operation by operation (`valPZ`, `bicubicZ`, `cuZ`, `highUZ`). Each
     mirror is proved to represent the `Rat` formula (`rep_highUZ`).
   - The certificate checks that the packed result, read back as base-`X` digits, is `g` times
     the literal data `cK` (`decKgX`). Both the base `X` and the common factor `g` are literals.
2. **Phase 2: the tree, on the literal data** (`IPoly.checkZ`).
   - The 16 inputs are packed once per tree, at one base `X` given as data.
   - Each leaf's Bernstein transform acts on the packed numbers.
   - **The interval test reads the packed number directly.** If `r` packs `A − B` at base `X`
     and `k + 1 ≤ 2^e`, then `t ↦ 2^{e(L−1)} A((k + t)/2^e)` takes the value `2^{e(L−1)} A(X)` at
     `Y = 2^e X − k`. So its coefficients are the base-`Y` digits of `2^{e(L−1)}·r.pos`. This is
     exact once their sum `2^{e(L−1)} A((k+1)/2^e) ≤ 2^{e(L−1)}·r.pos1` is below `Y`.
   - The test `tm1` then runs on these digits in natural numbers. No list of integers is built,
     and nothing is re-packed.

**What was slow before.** It was not the arithmetic. The kernel spent its time on list and `Int`
operations around the arithmetic:
- unpacking every leaf polynomial (degree 43, about 175 digits per coefficient);
- re-scaling and re-packing that polynomial for every interval;
- `|·|` from Mathlib's lattice instances;
- recomputing the inputs' coefficient sums for every leaf.

Profiles of the hardest tree (`p2_high_0_12`, 13 leaves, 299 intervals):
- PR 73's tree check: 70 s;
- base change without lists: 38 s;
- with the inputs packed once per tree and the bound given as data: 6 s.

The generators: `faceless-chain/gen_certk.py` extracts `Δ`, `X` and `cK`. Then
`QRH_CK=<its output> gen_all.py` emits the two-phase files. The proportionality of `cK` to the
`certI` array is asserted, so PR 73's trees are reused unchanged.

## 7. The sector certificates, packed the same way (done)

The scalar certificates of the follow-up took 290 s of kernel time. 257 s of that was the 120
special-sector certificates (`Piece.secB`, about 2.1 s each, `Rat` arithmetic again).
- **Mirror and check.** `Faceless/ScalarZ.lean` mirrors `secN` and `secB` on packed numbers
  (`secNZ`, `secBZ`, with `rep_secBZ`). It checks the result against literal data
  (`decS`, base and factor as data).
- **Positivity on the data.** The existing `IPoly.posOn` runs on the literal, with the same cover.
  A cover of `secB` serves its positive multiples, since `tm1` is homogeneous.
- **The certificate field.** `Certs.sec` is now stated as positivity on `[0, 1]` (`PosOn01`),
  like `Certs.high`.
- **Data extraction.** `faceless-chain/gen_certs.py`; `gen_all.py` emits the sector files with
  `QRH_CS`.

| scalar certificates | before | after |
|---|---|---|
| sectors (120) | 256.5 s | 28.7 s (24.3 s phase 1, 4.4 s phase 2) |
| scalar gates `sgN` (160) | 26.0 s | 26.0 s (not packed) |
| field, weak, cell | 6.7 s | 6.0 s |
| **total** | **289.5 s** | **60.7 s** |

## 8. External kernels on the submission (`arvi-single-stage-20261025`)

Local, 4 cores, 15 GB. The hosted runner has 4 vCPU and 16 GB, with a 600 s export limit and one
kernel job.

| step | PR 73 | single stage |
|---|---|---|
| `lean4export` of `Candidate.bound` | 4315 MB, 511 s, 12.3 GB peak | **2734 MB, 300 s, 11.8 GB peak** |
| con-ron `--verified`, 4 jobs, from the file | killed (out of memory) at 731 s | **accepted, 134,933 declarations, 894 s, 8.5 GB peak** |
| nanoda, 4 threads, from the file | killed at 471 s | killed at 301 s (13.0 GB) |
| nanoda, export streamed on stdin, 4 threads | passed in 20 min 17 s | killed at 581 s (13.5 GB with the exporter) |
| nanoda, 2 threads, streamed | — | (running) |

- **Our certificates are cheap for nanoda.**
  - The heaviest packed HIGH certificate (`p2_high_0_12_pos`, 10,733 declarations with its
    dependencies) checks in 8 s at 438 MB.
  - All five pieces' certificates together (`piece{0..4}_certs`, 12,376 declarations: the 60 HIGH,
    120 sector and remaining scalar certificates) check in 39 s at 835 MB.
- **The memory goes to the rest of the closure.** Mathlib, the baseline and Collet's large admission
  declarations are checked several at a time. PR 73's streamed pass was presumably close to the
  same limit.
- **Admission is not at risk.** Maintainers verify offline with raised budgets, and every hosted
  run since PR 63 has timed out anyway.

## 9. Status

- **Our face-family certificates:** 168 s of kernel time in total, against about 2600 s in
  PR 73. HIGH is 107 s, scalar 61 s.
- **Final-return rows:** 46 s.
- **Remaining kernel time, mostly outside our package:** Collet 241 s, baseline 501 s,
  Mathlib 379 s.
- **The follow-up candidate** rebuilds in about 200 s wall on 4 cores, and both theorems use
  only the three standard axioms.
