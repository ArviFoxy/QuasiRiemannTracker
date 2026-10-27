/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M (concrete second step, Seam 0): the balance of the two first raw sides.

STOP-RULE REPORT (normalization mismatch with CF (6.4)). The cube-free second step bounds the
C-side non-fixed Gauss norm at exponent `A - c + q_C`, `q_C = q + c - d` (CF Section 6), in
the volume-normalised units of CF (5.3) / `Packet.Grouped.gFrame` (energy `= Z^k/X² ·
labelEnergy`, i.e. raw energy `= X_C · norm`, `X_C = V/N(C) = Z^{A-c}`). In raw units the
C side is therefore `Z^{2A + q - c - d}`, and so is the D side: the twist imbalance
`q_C - q_D = 2(c - d)` exactly compensates the column-volume imbalance (`cfRaw_symm`).

Seam 0 (`First.RawSidesContract`, FP instance) instead asks for EACH side separately the
FP reference budget `jointBudget s τ G opp = A·N(τ)·(V/N G)²·Z^{allowance G opp}·Z^loss`,
whose exponents are `q + 2(A - c) + allow(C,D)` and `q + 2(A - d) + allow(D,C)`. For every
first common pair with `c > d` the C side exceeds its budget by
`Z^{(c - d) - allow(C,D)}` with positive exponent (`excess_pos`); for a common prime pattern
of multiplicities `(2,1)` (`c = 2d`, active radical `r = d`) the excess is exactly `Z^d`
(`excess_two_one`), a polynomial loss that no `ε` absorbs. The D side has the same slack.
Only the PRODUCT of the two sides matches (CF (3.1)/(6.4)).

The consumer does not care: `First.JointKernel.summed_kernel_from_raw` uses the two budgets
only through `windowBudget J t EL * windowBudget J t ER = √EL √ER · (…)`, which is invariant
under `EL ↦ λ EL`, `ER ↦ ER/λ` (`windowBudget_balance`, `summed_kernel_balanced`). With
`λ = N(C)/N(D)` both rebalanced budgets become the symmetric geometric-mean reference
`A·N(τ)·V²/(N C·N D)·Z^{allow}·Z^loss` (`balanced_left_eq`, `balanced_right_eq`), which is
exactly what CF supplies on both sides (`balanced_exponent_left/right`). The proposed
contract is `BalancedSummedRawSideBounds`; `balanced_kernel` shows it gives WP-K's joint
kernel bound with the SAME right-hand side `Ckernel·windowBudget(jointBudget_C)·
windowBudget(jointBudget_D)` as the original per-side Seam 0.

Second (minor) mismatch: `First.jointBudget` / `FPSummedRawSideBounds` are typed on FP's
unforked `Candidate.FourthPower` `Source`, while the cube-free `rawEnergy` lives on the forked
`CubeFree.FP` `Source`; `concreteJointBudget` restates the budget on the fork. -/
import Submissions.density_split_third_20261026.CubeFree.First.JointKernel
import Submissions.density_split_third_20261026.CubeFree.First.RawSidesContract

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.Second.Concrete
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap
open OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve CompletedGauss
open ConcreteTraceCRT ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst CenteredMomentSourceRow
open CenteredMomentSecondWindowBudget CenteredMomentFirstMixedAllowance
open QRH.DensitySplitThird.CubeFree.First
open QRH.DensitySplitThird.CubeFree.FP.MixedPrincipalPair QRH.DensitySplitThird.CubeFree.FP.RepairedFirstRawSides
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
variable {ι : Type u} [Fintype ι] {a b : ℝ}

/-! ### 1. Scalar form of the mismatch -/

/-- CF's side exponent `A - c + q_C` converted to raw energy (times `X_C = Z^{A-c}`). -/
def cfRawExponent (A c d q : ℝ) : ℝ := (A - c) + (A - c + (q + c - d))

/-- Exponent of the per-side Seam 0 budget `N(τ)·(V/N C)²·Z^{allow(C,D)}`
(`log_Z N(τ) = q`, `log_Z V = A`, `r` the active radical width). -/
def jointExponent (A c d q r : ℝ) : ℝ := q + 2*(A - c) + max (3*c - 5*d - r) 0 / 6

/-- The two CF sides have the same raw exponent `2A + q - c - d`. -/
theorem cfRaw_symm (A c d q : ℝ) : cfRawExponent A c d q = cfRawExponent A d c q := by
  unfold cfRawExponent; ring

theorem excess_eq (A c d q r : ℝ) :
    cfRawExponent A c d q - jointExponent A c d q r = (c - d) - max (3*c - 5*d - r) 0 / 6 := by
  unfold cfRawExponent jointExponent; ring

/-- On the side with the larger first common factor the CF bound strictly exceeds the
Seam 0 budget. -/
theorem excess_pos (A c d q r : ℝ) (hd : 0 ≤ d) (hcd : d < c) (hr : 0 ≤ r) :
    0 < cfRawExponent A c d q - jointExponent A c d q r := by
  rw [excess_eq]
  rcases le_total (3*c - 5*d - r) 0 with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

/-- Multiplicities `(2,1)` at every common prime: `c = 2d`, active radical `r = d`; the
excess is exactly `d`. -/
theorem excess_two_one (A d q : ℝ) :
    cfRawExponent A (2*d) d q - jointExponent A (2*d) d q d = d := by
  rw [excess_eq]
  have : 3*(2*d) - 5*d - d = 0 := by ring
  rw [this, max_self]; ring

/-- The rebalanced budgets (`λ = N C/N D`) cover CF on both sides. -/
theorem balanced_exponent_left (A c d q r : ℝ) :
    cfRawExponent A c d q ≤ jointExponent A c d q r + (c - d) := by
  unfold cfRawExponent jointExponent
  have : 0 ≤ max (3*c - 5*d - r) 0 / 6 := div_nonneg (le_max_right _ _) (by norm_num)
  linarith

theorem balanced_exponent_right (A c d q r : ℝ) :
    cfRawExponent A d c q ≤ jointExponent A d c q r - (c - d) := by
  unfold cfRawExponent jointExponent
  have : 0 ≤ max (3*d - 5*c - r) 0 / 6 := div_nonneg (le_max_right _ _) (by norm_num)
  linarith

/-! ### 2. The joint kernel consumer is invariant under rebalancing -/

theorem windowBudget_balance (J : ℕ) (t EL ER l : ℝ) (hl : 0 < l) (hEL : 0 ≤ EL) :
    windowBudget J t (l*EL) * windowBudget J t (ER/l) =
      windowBudget J t EL * windowBudget J t ER := by
  unfold windowBudget
  have h : Real.sqrt (l*EL) * Real.sqrt (ER/l) = Real.sqrt EL * Real.sqrt ER := by
    rw [← Real.sqrt_mul (mul_nonneg hl.le hEL), ← Real.sqrt_mul hEL]
    congr 1
    field_simp
  calc Real.sqrt (l*EL) * heightEnvelope t ^ J * profileMoment J *
        (Real.sqrt (ER/l) * heightEnvelope t ^ J * profileMoment J)
      = (Real.sqrt (l*EL) * Real.sqrt (ER/l)) * (heightEnvelope t ^ J * profileMoment J)^2 := by
        ring
    _ = (Real.sqrt EL * Real.sqrt ER) * (heightEnvelope t ^ J * profileMoment J)^2 := by rw [h]
    _ = _ := by ring

/-- `summed_kernel_from_raw` with rebalanced side budgets `λ·EL`, `ER/λ` gives the bound of
the unbalanced pair `EL`, `ER`. -/
theorem summed_kernel_balanced (Φ : 𝓢(ℝ,ℂ)) (J : ℕ) :
    ∃ Ckernel : ℝ, 0 ≤ Ckernel ∧
    ∀ s : Source ι a b, ∀ ha : 0 < a,
    ∀ (C D : Id) (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D)),
    ∀ (Us : Finset Id) (τL τR : Character) (t K K₀ H₀ A₀ B₀ KL KR : ℝ),
      0 < K₀ → 0 < H₀ → 0 < A₀ → 0 < B₀ → 0 < KL → 0 < KR →
    ∀ rows : Finset O, (∀ z ∈ rows, ‖eisEmbedding z‖^2 ≤ KL) →
      (∀ z ∈ rows, ‖eisEmbedding z‖^2 ≤ KR) →
    ∀ EL ER l : ℝ, 0 ≤ EL → 0 ≤ ER → 0 < l →
    (∀ v : ℝ, ∑ u ∈ Us, rawEnergy s ha D C hC u τL v KL ≤ (l*EL)*(1+‖v‖)^(2*J)) →
    (∀ v : ℝ, ∑ u ∈ Us, rawEnergy s ha C D hD u τR v KR ≤ (ER/l)*(1+‖v‖)^(2*J)) →
      ‖summedMatrix s ha C D hC hD E Us τL τR t rows Φ K K₀ H₀ A₀ B₀‖ ≤
        Ckernel*(windowBudget J t EL*windowBudget J t ER) := by
  obtain ⟨Ckernel, hC0, hker⟩ := summed_kernel_from_raw (ι := ι) (a := a) (b := b) Φ J
  refine ⟨Ckernel, hC0, ?_⟩
  intro s ha C D hC hD E Us τL τR t K K₀ H₀ A₀ B₀ KL KR hK₀ hH₀ hA₀ hB₀ hKL hKR rows hrL hrR
    EL ER l hEL hER hl h1 h2
  have h := hker s ha C D hC hD E Us τL τR t K K₀ H₀ A₀ B₀ KL KR hK₀ hH₀ hA₀ hB₀ hKL hKR rows
    hrL hrR (l*EL) (ER/l) (mul_nonneg hl.le hEL) (div_nonneg hER hl.le) h1 h2
  rwa [windowBudget_balance J t EL ER l hl hEL] at h

/-! ### 3. The balanced concrete Seam 0 (proposed contract) -/

/-- `First.jointBudget` restated on the forked (cube-free) `Source`. -/
def concreteJointBudget (s : Source ι a b) (τ : Character) (G opposite : Id) (A Z loss : ℝ) : ℝ :=
  A * QRH.DensitySplitThird.CubeFree.FP.MixedFirstExceptionalNormalization.reference τ G opposite
    (QRH.DensitySplitThird.CubeFree.FP.MixedInnerExceptionalBlock.sourceVolume s) Z * Z^loss

/-- The symmetric (geometric-mean) side budget: `A·N(τ)·V²/(N G·N opp)·Z^{allow(G,opp)}·Z^loss`. -/
def balancedBudget (s : Source ι a b) (τ : Character) (G opposite : Id) (A Z loss : ℝ) : ℝ :=
  A * ((τ.modulus.absNorm:ℝ) *
    (QRH.DensitySplitThird.CubeFree.FP.MixedInnerExceptionalBlock.sourceVolume s)^2 /
      ((G.absNorm:ℝ) * (opposite.absNorm:ℝ)) * Z^(allowance G opposite Z)) * Z^loss

private theorem norm_ne (I : Id) (hI : I ≠ 0) : (I.absNorm:ℝ) ≠ 0 := by
  exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr hI)

/-- Left side: `λ = N C/N D` turns the per-side budget into the symmetric one. -/
theorem balanced_left_eq (s : Source ι a b) (τ : Character) (C D : Id) (hC : C ≠ 0)
    (hD : D ≠ 0) (A Z loss : ℝ) :
    ((C.absNorm:ℝ)/(D.absNorm:ℝ)) * concreteJointBudget s τ C D A Z loss =
      balancedBudget s τ C D A Z loss := by
  unfold concreteJointBudget balancedBudget
    QRH.DensitySplitThird.CubeFree.FP.MixedFirstExceptionalNormalization.reference
  have h1 := norm_ne C hC
  have h2 := norm_ne D hD
  field_simp

/-- Right side: the same symmetric budget with the opposite allowance. -/
theorem balanced_right_eq (s : Source ι a b) (τ : Character) (C D : Id) (hC : C ≠ 0)
    (hD : D ≠ 0) (A Z loss : ℝ) :
    concreteJointBudget s τ D C A Z loss / ((C.absNorm:ℝ)/(D.absNorm:ℝ)) =
      balancedBudget s τ D C A Z loss := by
  unfold concreteJointBudget balancedBudget
    QRH.DensitySplitThird.CubeFree.FP.MixedFirstExceptionalNormalization.reference
  have h1 := norm_ne C hC
  have h2 := norm_ne D hD
  field_simp

/-- Squarefree first artificial divisors of the forked source. -/
def concreteArtificial (s : Source ι a b) (C D : Id) (hD : D ≠ 0) : Finset Id :=
  (QRH.DensitySplitThird.CubeFree.FP.MixedFirstPhysicalApplication.artificialDivisors s C D hD).filter
    (fun u => (UniqueFactorizationMonoid.moebius u : ℂ) ≠ 0)

/-- **Proposed Seam 0 for the cube-free step**: the generic `SummedRawSideBounds` on the forked
raw energies with the symmetric budgets on both sides. -/
def BalancedSummedRawSideBounds (s : Source ι a b) (ha : 0 < a) (η : Character)
    (C D : Id) (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (KL KR A Z loss : ℝ) (J : ℕ) : Prop :=
  SummedRawSideBounds (concreteArtificial s C D hD.1)
    (rawEnergy s ha D C hC) (rawEnergy s ha C D hD)
    (fun χ ξ => (fixedPair η C D hC E χ (ξ⁻¹)).left)
    (fun χ ξ => (fixedPair η C D hC E χ (ξ⁻¹)).right)
    (fun τ => balancedBudget s τ C D A Z loss) (fun τ => balancedBudget s τ D C A Z loss) KL KR J

theorem concreteJointBudget_nonneg (s : Source ι a b) (τ : Character) (G opp : Id)
    (A Z loss : ℝ) (hA : 0 ≤ A) (hZ : 0 ≤ Z) : 0 ≤ concreteJointBudget s τ G opp A Z loss := by
  unfold concreteJointBudget QRH.DensitySplitThird.CubeFree.FP.MixedFirstExceptionalNormalization.reference
  positivity

/-- **The balanced Seam 0 feeds the joint kernel with the original right-hand side**: for
every pair of ray characters, the summed matrix is bounded by
`Ckernel · windowBudget(jointBudget_C) · windowBudget(jointBudget_D)`, exactly the bound the
per-side Seam 0 would give. -/
theorem balanced_kernel (Φ : 𝓢(ℝ,ℂ)) (J : ℕ) :
    ∃ Ckernel : ℝ, 0 ≤ Ckernel ∧
    ∀ s : Source ι a b, ∀ ha : 0 < a, ∀ η : Character,
    ∀ (C D : Id) (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D)),
    ∀ (t K K₀ H₀ A₀ B₀ KL KR A Z loss : ℝ),
      0 < K₀ → 0 < H₀ → 0 < A₀ → 0 < B₀ → 0 < KL → 0 < KR → 0 ≤ A → 0 ≤ Z →
    ∀ rows : Finset O, (∀ z ∈ rows, ‖eisEmbedding z‖^2 ≤ KL) →
      (∀ z ∈ rows, ‖eisEmbedding z‖^2 ≤ KR) →
    BalancedSummedRawSideBounds s ha η C D hC hD E KL KR A Z loss J →
    ∀ χ ξ : RayCharacter,
      ‖summedMatrix s ha C D hC hD E (concreteArtificial s C D hD.1)
          (fixedPair η C D hC E χ (ξ⁻¹)).left (fixedPair η C D hC E χ (ξ⁻¹)).right
          t rows Φ K K₀ H₀ A₀ B₀‖ ≤
        Ckernel*(windowBudget J t
            (concreteJointBudget s (fixedPair η C D hC E χ (ξ⁻¹)).left C D A Z loss) *
          windowBudget J t
            (concreteJointBudget s (fixedPair η C D hC E χ (ξ⁻¹)).right D C A Z loss)) := by
  obtain ⟨Ckernel, hC0, hker⟩ := summed_kernel_balanced (ι := ι) (a := a) (b := b) Φ J
  refine ⟨Ckernel, hC0, ?_⟩
  intro s ha η C D hC hD E t K K₀ H₀ A₀ B₀ KL KR A Z loss hK₀ hH₀ hA₀ hB₀ hKL hKR hA hZ rows
    hrL hrR hbal χ ξ
  obtain ⟨h1, h2⟩ := hbal χ ξ
  have hCn : 0 < (C.absNorm:ℝ) :=
    lt_of_le_of_ne (Nat.cast_nonneg _) (norm_ne C hC.1).symm
  have hDn : 0 < (D.absNorm:ℝ) :=
    lt_of_le_of_ne (Nat.cast_nonneg _) (norm_ne D hD.1).symm
  have hl : 0 < (C.absNorm:ℝ)/(D.absNorm:ℝ) := div_pos hCn hDn
  refine hker s ha C D hC hD E _ _ _ t K K₀ H₀ A₀ B₀ KL KR hK₀ hH₀ hA₀ hB₀ hKL hKR rows hrL hrR
    _ _ _ (concreteJointBudget_nonneg _ _ _ _ _ _ _ hA hZ)
    (concreteJointBudget_nonneg _ _ _ _ _ _ _ hA hZ) hl (fun v => ?_) (fun v => ?_)
  · rw [balanced_left_eq s _ C D hC.1 hD.1]; exact h1 v
  · rw [balanced_right_eq s _ C D hC.1 hD.1]; exact h2 v

end
end QRH.DensitySplitThird.CubeFree.Second.Concrete
