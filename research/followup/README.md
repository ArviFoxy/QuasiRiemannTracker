# Follow-up package: the repeated-mark proof in one stage (K = 9/2)

This is a working copy of the PR 73 submission (`arvi-repeated-marks-20261024`, frozen) for the
next submission. It is not a submission yet: the next record still needs a new mathematical gain.
What it changes is the verification cost (`../verification/AUDIT_FOLLOWUP.md`).

## What changes against PR 73

- **The natural cost is `K = 9/2 = 6(2·7/8 − 1)`.**
  - The cap `6(2β − 1) ≤ K` needed by the source step and the final return is then the
    baseline's theorem β ≤ 7/8 (`Graph/NaturalCap.lean`).
  - Collet's seed step, the intermediate return and the PR 67 re-proof (`incumbent_beta`) are no
    longer in the proof.
- **The chain starts at the natural face at `K = 9/2`.**
  - The natural face is `natural92 = ⟨1, 9/2, 11/200, …⟩`, from `natural_global_source`.
  - `natK` replaces Collet's `finalK` everywhere.
  - `scalarGate92` replaces Collet's `scalarGate`, which has K built in.
- **The face family and the final return are regenerated for `K = 9/2`.**
  - Breakpoints `σ = 0.0122820, 0.01942, 0.0252, 0.0310, 0.0367, 0.0424122`.
  - Physical face at grid index 41756.
  - Return: 32 rows and 9 windows.
- **Value.** `CandidateFollowup.bound_sharp` is 2186813/2500000 = 0.8747252 (PR 73: 0.8747250).
  `CandidateFollowup.bound` states 8747289/10^7, as PR 73 does.
- **New or rewritten files.**
  - `Graph/NaturalCap.lean`, `Graph/Endpoint.lean` (single stage);
  - `FinalReturn/EndpointFromSources.lean` (two-stage theorems removed);
  - `FinalReturn/EndpointFromGlobalSources.lean` (single stage);
  - `Finite/SourceValid2.lean` (`scalarGate92`);
  - `Source/NFStep2.lean` (no bootstrap import);
  - generated `Faceless/Gen/*` and `FinalReturn/*`.

- **HIGH and sector certificates in packed integer arithmetic.**
  - Files: `Faceless/Packed.lean`, `Faceless/TreeZ.lean`, `Faceless/ScalarZ.lean`.
  - Each certificate is a coefficient check plus a positivity check on literal data.
  - Kernel time of the face-family certificates: 168 s (PR 73: about 2600 s).
  - Details: `../verification/AUDIT_FOLLOWUP.md` §6–7.

## Measured (local, 4 cores, 15 GB)

| | PR 73 | follow-up |
|---|---|---|
| closure constants | 157,349 | 136,162 |
| `lean4export` output | 4315 MB | 2727 MB |
| export time | 511 s | 245 s |
| Collet's share | 2336 MB | 714 MB |

- Axioms of both `CandidateFollowup` theorems: `propext`, `Classical.choice`, `Quot.sound`.
- `incumbent_beta`, Collet's `seed_step` and `Intermediate.beta_of_global_sources` are not in the
  closure.

## Build

Copy `src/Submissions/arvi_followup` into the Lake project's `Submissions/` and
`src/Candidate/Followup.lean` into `Candidate/`, then run `lake build Candidate.Followup`. The
project is the one of PR 73: Lean 4.34.1, Mathlib `d13f23b7`, with the OpenAI baseline and Collet's
`hailey-collet-1252270103`.

## Regenerate

The generators take the natural cost, breakpoints, package and natural-node name from the
environment. Their defaults reproduce PR 73 byte for byte.

```sh
export QRH_K=9/2 QRH_SIG=0.0122820,0.01942,0.0252,0.0310,0.0367,0.0424122
export QRH_PKG=Submissions.arvi_followup QRH_NATURAL=QRH.RepeatedMarks.natural92
cd ../faceless-chain
python3 gen_certk.py <lake project> ck.txt   # packed HIGH data (needs the built package)
python3 gen_certs.py <lake project> cs.txt   # packed sector data
QRH_CK=ck.txt QRH_CS=cs.txt python3 gen_all.py OUT/Faceless/Gen && python3 gen_steps.py OUT/Faceless/Gen
python3 theta_family2.py $QRH_SIG          # θ* = 8747252
python3 exact_check.py $QRH_SIG && python3 exact_junctions.py $QRH_SIG
cd ../repeated-marks          # faces92.json: faces C (y = 1 − Dy) and P (y = 41756 Dy) of piece 4
python3 gen_return_lean.py faces92.json 8747252/10000000 401/500 0 1 RET 13/250 9/200 global
python3 fork_return.py RET OUT 549989/10000000 549989/10000000 13/250 9/200 transport
```

Then copy `RET/FinalReturn/*.lean` and `RET/FinalReturn/Rows` over the forked `OUT/FinalReturn`,
and replace `EndpointFromSources.lean` and `EndpointFromGlobalSources.lean` with the single-stage
versions here.
