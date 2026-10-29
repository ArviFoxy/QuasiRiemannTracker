# Face region: the Cauchy–Schwarz midpoint rule (D8a) and where faces are consumed (2026-10-29)

Question: does Cauchy–Schwarz on the face energy convexify the proven region and move θ?
Tags: **[Lean]** read or proved in Lean (path:line), **[derived]** by hand, **[numerical]** script and log here.
Paths: `OAI/` = `/home/user/lean-env/qrh/Submissions/openai_baseline/OAI/NumberTheory/DirichletL/`,
`COL/` = `.../Submissions/hailey_collet_1252270103/`, `SIL/` = `.../Submissions/sil_density_split_20261026/`,
`AD/` = `.../Submissions/arvi_density/`, `RM/` = `.../Submissions/arvi_repeated_marks_20261024/`.
Region properties and the continuum ODE (questions 5–6) are handled separately; section 7 records only the numerics
done before that split. The D8 mathematics itself is in `research/D8_NOTES.md` and is not repeated here.

## 0. Bottom line

1. **The midpoint rule is valid** [Lean]. `Submissions/arvi_face_region/Midpoint.lean` proves, with axioms
   `propext, Classical.choice, Quot.sound` only:
   - `energy(W₁,W₂,X₁,X₂; A⊔B)² ≤ energy(W₁,W₁,X₁,X₁; A⊔A) · energy(W₂,W₂,X₂,X₂; B⊔B)` for the literal energy;
   - `midpoint_source`: two `UnitFaceSource`s give a diagonal bound on every configuration `(m₁, m₂, sA + sB)` whose
     squared configurations `(m₁, m₁, 2sA)`, `(m₂, m₂, 2sB)` they admit.
2. **The gain exists only for unequal plain lengths** [Lean `balanced_no_gain`, derived]. With equal plains the rule
   reproduces E(s).
3. **Every face evaluation in the return and in the density steps has equal plain lengths at its binding point**
   [Lean, section 3]. Count: both factors are the same detector block `S_m`. Physical numerator: one packet to the
   fourth power, so the binding corner of its length box is `(n, n)`. Chain: the child's own pair is passed to the
   parent, and the HIGH counts use `S_m` twice.
4. **No unequal pairing is available** [Lean, section 4]. The detector witness carries one plain block per row.
5. **θ effect: exactly 0** [derived]. A consumer of unequal pairs does not exist. As a hypothetical price: if the
   physical numerator could use the best unequal pair at its binding point, θ would fall by 6.4e-6 at
   `numeratorCap = 3/50`, or 6.3e-5 with that cap raised to 63/1000. The count face would gain nothing even
   hypothetically [numerical].
6. **The claimed hull is too large** [derived, numerical]. The closure is a midpoint set, not the convex hull. The
   true gains at s = 0.02/0.04/0.05/0.06/0.08 are +0.0003/+0.0064/+0.0112/+0.0085/+0.0018, not
   +0.0054/+0.0101/+0.0112/+0.0112/+0.0075.

## 1. The energy and the squared configurations

- `energy = ∑'_z [keep z]·‖positiveSlotRow‖²·Re Φ(‖z‖²/K)` (`OAI/Moments/InductionEnergy.lean:16-20`).
- `positiveSlotRow = (√(X₁X₂∏P))⁻¹ · (R₁·R₂·∏ rowSlot)` (`OAI/Moments/RetainedEnergy.lean:14-19`). The plains enter
  as a literal product. The normalization is a scalar that factors.
- `Re Φ ≥ 0` is a hypothesis of the face statement (`COL/Record12518109Source/InitialMoment.lean:104`).
- The keep mask `initialKeep η Q z = z ≠ 0 ∧ ¬FixedInducingRow …` (`OAI/Moments/DetectorEnergyInitialState.lean:21`)
  depends only on the row. It is the same for the target and for both squared configurations.

The face accepts squared configurations [Lean]:
- profiles: `Profiles a b` is any pair with per-profile support (`OAI/Moments/FiniteProfileExceptionalPair.lean:14-16`);
- `control = sourceControl(W₁)·sourceControl(W₂)` (`:18-19`), so the controls combine exactly;
- slots: `∀ T : Finset α` with arbitrary `θ, w, σ, v` (`InitialMoment.lean:97-101`), and pools that depend only on the
  width (`:108`), so duplicated pools are allowed;
- `UnitFaceSource` quantifies over the slot type α (`COL/Record12518109Existence/UniformSource.lean:20`), so the
  doubled types `ιA ⊕ ιA`, `ιB ⊕ ιB` are available. Their constants are chosen after the type.

## 2. The Cauchy–Schwarz region, exactly

Let `s*(P)` be the face capacity at total plain length P. The one-step closure is [derived]

  `s_CS(m₁, m₂) = max( s*(m₁+m₂), (s*(2m₁) + s*(2m₂))/2 )`  (when `2m₁, 2m₂ ≤ E(0)`).

- Iterating adds nothing: the equal slice is unchanged, and only equal configurations are squared.
- Integer Hölder adds nothing either. Each factor must carry exactly two plains, so the types `(m₁,m₁)` and
  `(m₂,m₂)` enter with equal weights. That gives a midpoint, never a general convex combination.
- Interpolating only in the slot variable is a horizontal midpoint, and the region is monotone in s.

So in the (s, P) plane the closure is the midpoint set `P_CS(s) = max_{s'+s''=2s} (E(s')+E(s''))/2`. It is not the
chord. The gain is realised only by the pair `(m₁, m₂) = (P'/2, P''/2)` [numerical, `logs/cs_region.log`]:

| s | E(s) | P_CS − E | claimed chord − E | optimal (s', s'') |
|---|---|---|---|---|
| 0.02 | 0.948560 | +0.000328 | +0.005368 | (0, 0.04) |
| 0.04 | 0.897786 | +0.006352 | +0.010079 | (0, 0.08) |
| 0.05 | 0.873643 | +0.011192 | +0.011192 | (0, 0.10) |
| 0.06 | 0.850582 | +0.008534 | +0.011221 | (0.02, 0.10) |
| 0.08 | 0.808286 | +0.001844 | +0.007455 | (0.06, 0.10) |

The same data as capacity at fixed P:

| P | s*(P) | s_CS(P) | best pair |
|---|---|---|---|
| 0.88 | 0.04733 | 0.05188 | (0.495, 0.385) |
| 0.8512 (physical binding) | 0.05972 | 0.06308 | (0.466, 0.385) |
| 0.80 | 0.08426 | 0.08463 | (0.415, 0.385) |
| ≤ 0.785 (count binding) | s* | = s* | (P/2, P/2) |

## 3. (i) Every face evaluation and its plain lengths

| # | site | (X₁, X₂) evaluated | slot total | equal? |
|---|---|---|---|---|
| R1 | count, branches C/capC/weakC7/capP: transport `COL/Record12518109Count/InitialTransport.lean:137` (and `:117`) | `(Z^d)^{F.m}`, `(Z^d)^{F.m}` | `∑_{selected} F.widths`, `F.m+F.m+f.lam·∑ ≤ f.B` (`:143`) | equal |
| R1a | the moment it feeds: `COL/Record12518109Count/MarkedFiber.lean:20-33` (`AffineMarkedMoment`: both factors `polynomial … (U^F.m)`, `:29,:31`; budget `:26`), count `:35-44` (`hzbudget : f.lam·z ≤ f.B − 2·F.m`) | `U^{F.m}` twice | selected ⊆ fiber slots | equal |
| R1b | return call site: `AD/ReturnD/PhysicalDirect/SourceClosure.lean:41-43` (one call per window face); faces `countingSource b = broadFace (branchB b) (branchL b) (branchCap b)` (`AD/Return/WindowSources.lean:15-16`), supplied by `countGlobal`/`physicalGlobal` (`:17-20`, `AD/Return/SourceInlet.lean:17-18`); scheme `AD/Return/FinalScheme.lean:21-31` | as R1 | as R1 | equal |
| R2 | count, branch `old`: natural moment `Moments.plain_marked` (`OAI/Hecke/DetectorRawFiber.lean:72-77`); not a face | `U^{F.m}` twice | `2F.m + 6(3/4+2Δ)∑ ≤ 1` | equal |
| R3 | physical numerator, source evaluation: `finite_physical_pair_affine` (`AD/ReturnD/PhysicalDirect/Input.lean:50-70`; face `physicalFace` `:37`) | arbitrary, each length in [0, 1/2], budget on the sum (`:70`) | `∑ width ≤ cap` | interface allows unequal |
| R3a | `affine_fourier` (`Fourier.lean:36`) ← `hybrid_fourier` (`Hybrid.lean:31-50`): every `X₁, X₂ ≤ U^n` (`:50`), with face admissibility from `2n + Λ_P ∑ ≤ B_P` (`:79`, `affine_shortening` `:89`, `Geometry.lean:60`) | the box `[0,n]²` | `∑ ≤ clippedCapacity d t = min(cap, (B_P − 2·plainScale)/Λ_P)` (`Geometry.lean:35-38`), `n = plainScale d t = 1 − y/d + t` | box; binding corner `(n, n)` equal |
| R3b | where the box comes from: `Retained.lean:68` (`‖retainedSchwartz‖⁴` of one packet), `:103` (`hmoment` for all x, y ∈ [0, n log U]); `COL/Cycle25/Numerator/ReflectionRetained.lean:25-44` (`actual_retained_uniform_fourth`: x, y are Fourier variables of one column's row-dependent scale; `hselected` `:55-56` is `∑‖f i (u i)‖⁴`, one column per row); Hölder `COL/Cycle25/Numerator/Holder.lean:35` (one packet `S` to the fourth power); scalar form `AD/Return/Constants.lean:38` (`newCapacity` = `(2y − (2 − B_P)d)/Λ_P`, i.e. `2·plainScale`) | one packet twice | as R3a | equal |
| R4 | transport `AD/ReturnD/Transport/*` | no face evaluated (the only hits are `HeightAdmissible`, `FinalHeight.lean:26`) | — | — |
| S1 | step, rows narrower than s₀: `restricted_rows_of_parent` (`SIL/CubeFree/Assembly/ParentRows.lean:126`); leaves `(pr.1, pr.2)` below the child's `(Y₁,Y₂) ≤ (X₁,X₂)` (`:258`); parent admissibility from the total (`:279` `hchild`, `:283` `hadmP`) | every pair in the child's box | sub-family `A''`, `∑ ≤ rowWidth < s₀` | inherits the child's pair; corner equal for an equal child |
| S2 | step, Seam A leaf: `parent_priced_source` (`SIL/CubeFree/Leaf/Parent.lean:119`; need from `length X₁ + length X₂` `:190`; parent at the child's `(X₁, X₂)` `:215` `hadm`, `:244`); marked density LOW branch `AD/Density/LeafMarked.lean:452-468`; unmarked `AD/Density/Leaf.lean:497`; contract `SIL/CubeFree/Leaf/Contract.lean:38-56` (each length ≤ `Lplain`, price `price.f w₀ (length X₁ + length X₂) …`) | the child's own `(X₁, X₂)` | retained slots, `∑ = s − deleted` | inherits; price depends only on the sum |
| S3 | step, HIGH count: `high_branch_marked` (`AD/Density/LeafHighEnergyMarked.lean:119`; price through `length X₁ + length X₂`, `:158`) → `high_class_sum_marked` (`AD/Density/LeafHighMarked.lean:130`) → `RM/Fork/Record1252270103Source/PositiveRadius/SomeDictionary.lean`; plain line `RM/Source/FiberK.lean:177` (`hPM`, `2·m + lam·z ≤ B`) from `plainMarked` (`COL/Record1252270103Source/High/ActualFiber.lean:41-48`: both factors `U^{log 2^K}`); also `COL/Record1252270103Source/High/PlainEnergy.lean:25,41,77-78` (`ordinary_plain_field`, `(length U (U^m), length U (U^m))`) via `UniformPlain.lean:72` | the HIGH witness's block `U^m` twice | selected slots, `2m + lam·∑ ≤ B` | equal |
| S4 | step assembly: `SIL/CubeFree/Step.lean:30` → `SIL/CubeFree/Assembly/Combine.lean:56` (S1 for `rowWidth < s₀`, the root chain with the S2/S3 leaf otherwise) | — | — | — |

Summary [Lean + derived]:
- Plain lengths are unequal only inside boxes (R3a/R3b, S1, the S2 contract).
- Every such box contains its equal corner, and the bound must hold uniformly over the box.
- Every place where a plain is produced from data (R1, R2, R3b, S3) uses one block twice.
- On the equal slice, `balanced_no_gain` [Lean] shows the closure adds nothing.

## 4. (ii) Could the detector's dyadic plain blocks be paired unequally?

- **Count side: no** [Lean].
  - The witness of a bad row has one plain block: `right`, with scale `U^m = 2^right` and one `plain_spike`, a lower
    bound on `‖polynomial … positiveAnnular (U^m) …‖²` (`OAI/Hecke/DetectorWitnessRows.lean:18-19,25,34-35`). The
    supported witness adds `tstar − r − ε ≤ m` (`OAI/Hecke/DetectorSupportedWitness.lean:11-14`).
  - The fiber fixes one `right` (`OAI/Hecke/DetectorRawFiber.lean:24`, `Fiber.m` `:55`). Its plain moments carry
    two log-derivative profiles of the same block (`:72-82`).
  - Chebyshev with `S_{m₁}S_{m₂}` needs a lower bound for a second block `S_{m₂}` on the same rows. No witness
    provides one.
  - [derived] A squared identity `(LM)² = 1 + …` does not help. Whenever `(r, m)` is lit, the equal quadruple
    `(r, r, m, m)` is lit, so an adversary can always force equal blocks.
  - An unequal count needs new analytic input: two simultaneously saturated plain blocks of different lengths at the
    same zero.
- **Physical side: unequal pairs occur, but they cannot bind.**
  - `hmoment` (`Retained.lean:103`) asks for every `(x, y)` in `[0, n log U]²`.
  - These are Fourier variables of one column's scale (`ReflectionRetained.lean:37-42`). The underlying object is
    `‖f_u‖⁴`, one column per row (`:55-56`).
  - Even a bilinear expansion `|∑_u f_u|⁴ = |∑_{u,u'} f_u f_{u'}|²` keeps the diagonal term `|f_top|⁴` at
    `(n, n)`, and that term binds.
  - An unequal top pair needs two different numerator packets per row. The Hölder step raises one packet `S` to the
    fourth power (`Holder.lean:35`).

## 5. (iii) Interface for a face with separate plain ranges

Source side (easy):
- `SourceFace` has one plain range `[plainLo, plainHi]` for both plains and a budget on `m₁ + m₂`
  (`COL/Record12518109Source/InitialMoment.lean:19-31`).
- `InitialAffineAt` uses the face only through `face.Admissible` (`:106`). A predicate-valued version is
  definitionally the old one at `adm := face.Admissible`. So are `initialAffineAt_restrict` (`:115`) and
  `UnitFaceSource` (`UniformSource.lean:19`).
- A two-range face needs `Restricts` and `admissible_of_restricts` (`:35-59`) for the new structure.
- `MidpointAt` in `Midpoint.lean` is such a predicate-level statement.

Consumer side (the obstruction):
- **Count.**
  - `AffineMarkedMoment` (`MarkedFiber.lean:20-33`) hard-codes one length `F.m` for both factors and for both range
    checks. Its count `affine_marked_count` uses the exponent `1 − 2(2a−1)F.m − 2qz` and `hzbudget` (`:44`).
  - The transport (`InitialTransport.lean:117,137,143`) passes `X₁ = X₂`.
  - Needed: `Fiber` with two plain indices (`DetectorRawFiber.lean:16-44`), a two-block witness
    (`DetectorWitnessRows.lean:12-35`), two-length `Moments`, and a two-length transport.
  - In the scalar layer, `Return/Formulas.lean:35-40` (`D = 3 − p − 4p/L`, `A = 2 − 4p/L`, `C0 = 1 − 2pB/L`) and
    the window guards (`(B − L·cap)/2` in `gen_return86.py` `guards`) encode `z(m) = (B − 2m)/Λ` and would change
    to `z(m₁, m₂)`.
- **Physical.**
  - `finite_physical_pair_affine` already takes `X₁ ≠ X₂` (`Input.lean:50-70`).
  - `hybrid_fourier` (`Hybrid.lean:31-50`) and the capacity layer (`plainScale`, `affineCapacity`,
    `clippedCapacity`, `Geometry.lean:35-38`; `newCapacity`, `Constants.lean:38`) have one scale `n`. The numerator
    is one packet (`Fixed.lean`, `Retained.lean:68`, `Holder.lean:35`).
  - Needed: two numerator packets per row and two scales.
- **Windows.** `countingSource`, `broadFace` (`WindowSources.lean:15-16`, `COL/Record1252270103Return/SourceInlet.lean:25`)
  and `FinalScheme.lean:21-31` carry one range per window.

## 6. θ

- **Actual: Δθ = 0** [derived from section 3 + `balanced_no_gain`].
- Baseline reproduced: `gen_return86.py --branches five --find-theta` gives 0.8738724 for the faces of
  `AD/Return/Constants.lean`. The submitted value is 0.87387234 [numerical, `logs/price_hypothetical.log`].
- **Count: no gain even hypothetically** [numerical].
  - It binds at P ≈ 0.78. Rotating the count face about P₀ changes θ by −5e-7 at P₀ = 0.78, +2.3e-6 at 0.80 and
    +7.9e-6 at 0.84.
  - For P ≤ 0.785 both squared configurations lie on the last face, so `s_CS = s*`.
- **Physical: hypothetical only** [numerical]. If the numerator could use the pair (0.466, 0.385) at the newTop edge
  (P = 0.8512), its capacity would be 0.0631 instead of 0.0597. Modelled as a parallel shift of the physical face to
  `B_P = 0.993214`:
  - with `numeratorCap = 3/50`, θ = 0.8738660 (−6.4e-6);
  - with `numeratorCap = physicalCap = 63/1000`, θ = 0.8738094 (−6.3e-5);
  - raising the cap alone gives 0.8738724, no change.
- The hypothetical needs a numerator that is a product of two different plain packets. Section 4 says no such
  object exists.

## 7. Before the scope split: Legendre and continuum numerics

`legendre.py`, `logs/legendre_ode.log` [numerical]:
- **Legendre.** The 129 crossings `s_k = (B_{k−1}−B_k)/(Λ_{k−1}−Λ_k)` rise strictly from 0.027750 to 0.083352, and
  ΔΛ = 0.005 throughout. All 130 faces are active. On each piece `Λ_k = −E′` and `B_k = E − sE′` exactly, and
  `dB/dΛ = s_k` by definition.
- **Continuum.** The chain agrees with `research/newpowers/ta/ode2.py` (`dB/dΛ = s₀(B,Λ)`, `q = 0.999Λ/(6B−Λ)`,
  v = 0 marked gate, parent = self).
  - For k ≤ 128, `s_k` equals the ODE slope at the child state to within 1.9e-6: an implicit-Euler step.
  - The last step is floor-limited (q = 0.5002): +3.45e-4 in slope.
  - `B_ODE − B_chain` grows to +1.0e-4 at Λ = 1.9265.

## 8. Files

| file | content |
|---|---|
| `faces.py` | loads the 130 faces exactly; envelope E(s) |
| `cs_region.py` | closure, midpoint set vs chord, `s_CS(P)` and the best pairs (`logs/cs_region.log`) |
| `price_hypothetical.py` | θ of the baseline and the hypothetical physical capacity (`logs/price_hypothetical.log`) |
| `legendre.py` | Legendre checks (exact); `--ode` compares with `ode2.py` (`logs/legendre_ode.log`) |
| `lean/Midpoint.lean` | copy of `/home/user/lean-env/qrh/Submissions/arvi_face_region/Midpoint.lean` |
| `logs/lean_midpoint.log` | `#print axioms` of the five theorems |

Lean module `Submissions.arvi_face_region.Midpoint` (485 lines, about 14 s with `lake env lean`, no `sorry`, no new
axioms, no `native_decide`):
- `tsum_cs`: weighted Cauchy–Schwarz for `tsum`;
- `energy_sum_cs`: the energy inequality; summability comes from `product_bounded` and `bounded_radial_summable`;
- `energy_univ`: reindexing over `Finset.univ`;
- `MidpointAt`, `midpoint_at`, `midpoint_source`: the face-level rule;
- `balanced_no_gain`: no gain on the equal slice.

Reproduce:
```
cd research/face-region && python3 cs_region.py && python3 legendre.py --ode && python3 price_hypothetical.py
cd /home/user/lean-env/qrh && lake env lean Submissions/arvi_face_region/Midpoint.lean
```
