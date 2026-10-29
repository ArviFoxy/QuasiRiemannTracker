/-
Scratch proof of concept (research/face-region): the Cauchy–Schwarz midpoint rule for the
literal initial energy of the source faces.

* `tsum_cs`: Cauchy–Schwarz for nonnegatively weighted `tsum`s.
* `energy_sum_cs`: for slot families indexed by `ιA ⊕ ιB`,
  `energy(W₁,W₂,X₁,X₂; A ⊔ B)² ≤ energy(W₁,W₁,X₁,X₁; A ⊔ A) · energy(W₂,W₂,X₂,X₂; B ⊔ B)`.
  Only the support of the two profiles and `0 < X`, `0 < P`, `0 < K`, `0 ≤ Re Φ` are used.
* `midpoint_at` / `midpoint_source`: two face sources (at the doubled slot types `ιA ⊕ ιA`,
  `ιB ⊕ ιB`) bound the energy of every configuration `(m₁, m₂, sA + sB)` whose squared
  configurations `(m₁, m₁, 2 sA)` and `(m₂, m₂, 2 sB)` they admit.
* `balanced_no_gain`: on the balanced slice `m₁ = m₂` the rule adds nothing to two global faces.

Nothing here is used by the proof of the main theorem.
-/
import Submissions.hailey_collet_1252270103.Record12518109Existence.UniformSource
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.Contract
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.PositiveSummability
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.DivisorRawEnergy
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.BandMonotonicity

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace QRH.FaceRegion
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy CenteredMomentPositiveSummability
open CenteredMomentHeckeHeight CenteredMomentHeckeSlots ConcreteTraceCRT
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState ConcretePrimeRowBridge CenteredMomentPrimeSlot
open QRH.Record12518109Source QRH.Record12518109Existence
local notation "O" => HeckeFamily.O

/-! ### Cauchy–Schwarz for weighted `tsum`s -/

/-- Cauchy–Schwarz for nonnegatively weighted `tsum`s of nonnegative functions. -/
theorem tsum_cs {ι : Type*} (w a b : ι → ℝ) (hw : ∀ z, 0 ≤ w z) (ha : ∀ z, 0 ≤ a z)
    (hb : ∀ z, 0 ≤ b z)
    (hA : Summable fun z => w z * a z ^ 2) (hB : Summable fun z => w z * b z ^ 2) :
    (∑' z, w z * (a z * b z)) ^ 2 ≤ (∑' z, w z * a z ^ 2) * (∑' z, w z * b z ^ 2) := by
  set A := ∑' z, w z * a z ^ 2 with hAdef
  set B := ∑' z, w z * b z ^ 2 with hBdef
  set T := ∑' z, w z * (a z * b z) with hTdef
  have hA0 : 0 ≤ A := tsum_nonneg fun z => mul_nonneg (hw z) (sq_nonneg _)
  have hB0 : 0 ≤ B := tsum_nonneg fun z => mul_nonneg (hw z) (sq_nonneg _)
  have hT0 : 0 ≤ T := tsum_nonneg fun z => mul_nonneg (hw z) (mul_nonneg (ha z) (hb z))
  -- for every `l > 0`: `2 l T ≤ l² A + B`
  have key : ∀ l : ℝ, 0 < l → 2 * l * T ≤ l ^ 2 * A + B := by
    intro l hl
    have hpt : ∀ z, 2 * l * (w z * (a z * b z)) ≤ l ^ 2 * (w z * a z ^ 2) + w z * b z ^ 2 := by
      intro z
      have h0 : 0 ≤ w z * (l * a z - b z) ^ 2 := mul_nonneg (hw z) (sq_nonneg _)
      nlinarith [h0]
    have hS : Summable fun z => l ^ 2 * (w z * a z ^ 2) + w z * b z ^ 2 :=
      (hA.mul_left _).add hB
    have hT : Summable fun z => 2 * l * (w z * (a z * b z)) := by
      refine Summable.of_nonneg_of_le (fun z => ?_) hpt hS
      exact mul_nonneg (by positivity) (mul_nonneg (hw z) (mul_nonneg (ha z) (hb z)))
    have h := hT.tsum_le_tsum hpt hS
    rw [tsum_mul_left, (hA.mul_left _).tsum_add hB, tsum_mul_left] at h
    linarith
  rcases eq_or_lt_of_le hT0 with hT | hT
  · rw [← hT]
    have : (0:ℝ) ^ 2 = 0 := by norm_num
    rw [this]
    exact mul_nonneg hA0 hB0
  · rcases eq_or_lt_of_le hA0 with hA | hA
    · exfalso
      have h := key ((B + 1) / T) (by positivity)
      rw [← hA] at h
      have e : 2 * ((B + 1) / T) * T = 2 * (B + 1) := by field_simp
      rw [e] at h
      nlinarith
    · have h := key (T / A) (div_pos hT hA)
      have e1 : 2 * (T / A) * T = 2 * (T ^ 2 / A) := by ring
      have e2 : (T / A) ^ 2 * A = T ^ 2 / A := by field_simp
      rw [e1, e2] at h
      have h2 : T ^ 2 / A ≤ B := by linarith
      rw [div_le_iff₀ hA] at h2
      linarith [mul_comm A B]

/-! ### The literal initial energy as a weighted sum of squares -/

/-- The nonnegative row weight of `energy`. -/
def rowWeight (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (z : O) : ℝ :=
  if keep z then (Φ (‖eisEmbedding z‖ ^ 2 / K)).re else 0

theorem rowWeight_nonneg (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hΦ : ∀ x, 0 ≤ (Φ x).re) (z : O) : 0 ≤ rowWeight keep Φ K z := by
  unfold rowWeight; split_ifs
  · exact hΦ _
  · exact le_rfl

theorem energy_eq_weighted {ι : Type*} [Fintype ι] (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (X₁ X₂ : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K =
      ∑' z, rowWeight keep Φ K z * ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖ ^ 2 := by
  unfold energy rowWeight
  congr 1
  funext z
  split_ifs <;> ring

theorem energy_nonneg {ι : Type*} [Fintype ι] (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ) (X₁ X₂ : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hΦ : ∀ x, 0 ≤ (Φ x).re) :
    0 ≤ energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K := by
  rw [energy_eq_weighted]
  exact tsum_nonneg fun z => mul_nonneg (rowWeight_nonneg keep Φ K hΦ z) (sq_nonneg _)

/-- The summand of an energy is summable (bounded rows, Schwartz radial weight). -/
theorem energy_summable {ι : Type*} [Fintype ι] (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable fun z => rowWeight keep Φ K z *
      ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖ ^ 2 := by
  obtain ⟨Bd, hBd⟩ := product_bounded η m A t (Real.sqrt (X₁ * X₂ * ∏ i, P i) : ℂ)⁻¹
    W₁ W₂ b₁ b₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ S β
  have h := bounded_radial_summable
    (fun z => positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂) Bd
    (fun z => by simpa only [positiveSlotRow] using hBd z) keep Φ K hK
  refine h.congr fun z => ?_
  unfold rowWeight
  split_ifs <;> ring

/-! ### Splitting the slot product -/

section Split
variable {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]

theorem prod_elim {M : Type*} [CommMonoid M] (f : ιA → M) (g : ιB → M) :
    ∏ i, Sum.elim f g i = (∏ i, f i) * ∏ i, g i := by
  rw [Fintype.prod_sum_type]
  rfl

theorem sum_elim {M : Type*} [AddCommMonoid M] (f : ιA → M) (g : ιB → M) :
    ∑ i, Sum.elim f g i = (∑ i, f i) + ∑ i, g i := by
  rw [Fintype.sum_sum_type]
  rfl

/-- `‖row‖²` of a split configuration, with the slot product and its normalization split. -/
theorem row_sq_split (η : Character) (m A z : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (SA : ιA → Finset (Ideal O)) (βA : ιA → Ideal O → ℂ) (PA : ιA → ℝ) (hPA : ∀ i, 0 < PA i)
    (SB : ιB → Finset (Ideal O)) (βB : ιB → Ideal O → ℂ) (PB : ιB → ℝ) (hPB : ∀ i, 0 < PB i) :
    ‖positiveSlotRow η m A z W₁ W₂ (Sum.elim SA SB) (Sum.elim βA βB) (Sum.elim PA PB) t X₁ X₂‖ ^ 2 =
      (‖rowTwistedSum η m A z W₁ t X₁ * ∏ i, rowSlot η m A z (SA i) (βA i) t‖ ^ 2 /
          (X₁ * ∏ i, PA i)) *
        (‖rowTwistedSum η m A z W₂ t X₂ * ∏ i, rowSlot η m A z (SB i) (βB i) t‖ ^ 2 /
          (X₂ * ∏ i, PB i)) := by
  have hpA : 0 < ∏ i, PA i := Finset.prod_pos fun i _ => hPA i
  have hpB : 0 < ∏ i, PB i := Finset.prod_pos fun i _ => hPB i
  have hslot : (∏ i, rowSlot η m A z (Sum.elim SA SB i) (Sum.elim βA βB i) t) =
      (∏ i, rowSlot η m A z (SA i) (βA i) t) * ∏ i, rowSlot η m A z (SB i) (βB i) t := by
    rw [Fintype.prod_sum_type]
    rfl
  have hP : (∏ i, Sum.elim PA PB i) = (∏ i, PA i) * ∏ i, PB i := prod_elim PA PB
  have hT : 0 < X₁ * X₂ * ∏ i, Sum.elim PA PB i := by
    rw [hP]; positivity
  unfold positiveSlotRow
  rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ hT, hslot, hP]
  simp only [norm_mul, mul_pow]
  field_simp

end Split

/-! ### Cauchy–Schwarz for the energy -/

/-- **Cauchy–Schwarz midpoint inequality for the literal energy.** The configuration with plains
`(W₁, X₁)`, `(W₂, X₂)` and slot family `A ⊔ B` is controlled by the two squared configurations
`(W₁, W₁, X₁, X₁; A ⊔ A)` and `(W₂, W₂, X₂, X₂; B ⊔ B)`. -/
theorem energy_sum_cs {ιA ιB : Type*} [Fintype ιA] [Fintype ιB]
    (η : Character) (m A : O) (t : ℝ) (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (SA : ιA → Finset (Ideal O)) (βA : ιA → Ideal O → ℂ) (PA : ιA → ℝ) (hPA : ∀ i, 0 < PA i)
    (SB : ιB → Finset (Ideal O)) (βB : ιB → Ideal O → ℂ) (PB : ιB → ℝ) (hPB : ∀ i, 0 < PB i)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K) (hΦ : ∀ x, 0 ≤ (Φ x).re) :
    (energy η m A t W₁ W₂ (Sum.elim SA SB) (Sum.elim βA βB) (Sum.elim PA PB) X₁ X₂ keep Φ K) ^ 2 ≤
      energy η m A t W₁ W₁ (Sum.elim SA SA) (Sum.elim βA βA) (Sum.elim PA PA) X₁ X₁ keep Φ K *
      energy η m A t W₂ W₂ (Sum.elim SB SB) (Sum.elim βB βB) (Sum.elim PB PB) X₂ X₂ keep Φ K := by
  let a : O → ℝ := fun z =>
    ‖rowTwistedSum η m A z W₁ t X₁ * ∏ i, rowSlot η m A z (SA i) (βA i) t‖ ^ 2 / (X₁ * ∏ i, PA i)
  let b : O → ℝ := fun z =>
    ‖rowTwistedSum η m A z W₂ t X₂ * ∏ i, rowSlot η m A z (SB i) (βB i) t‖ ^ 2 / (X₂ * ∏ i, PB i)
  have hpA : 0 < ∏ i, PA i := Finset.prod_pos fun i _ => hPA i
  have hpB : 0 < ∏ i, PB i := Finset.prod_pos fun i _ => hPB i
  have ha : ∀ z, 0 ≤ a z := fun z => by positivity
  have hb : ∀ z, 0 ≤ b z := fun z => by positivity
  have hT : ∀ z, ‖positiveSlotRow η m A z W₁ W₂ (Sum.elim SA SB) (Sum.elim βA βB)
      (Sum.elim PA PB) t X₁ X₂‖ ^ 2 = a z * b z := fun z =>
    row_sq_split η m A z t W₁ W₂ X₁ X₂ hX₁ hX₂ SA βA PA hPA SB βB PB hPB
  have hAA : ∀ z, ‖positiveSlotRow η m A z W₁ W₁ (Sum.elim SA SA) (Sum.elim βA βA)
      (Sum.elim PA PA) t X₁ X₁‖ ^ 2 = a z ^ 2 := fun z => by
    rw [row_sq_split η m A z t W₁ W₁ X₁ X₁ hX₁ hX₁ SA βA PA hPA SA βA PA hPA]; ring
  have hBB : ∀ z, ‖positiveSlotRow η m A z W₂ W₂ (Sum.elim SB SB) (Sum.elim βB βB)
      (Sum.elim PB PB) t X₂ X₂‖ ^ 2 = b z ^ 2 := fun z => by
    rw [row_sq_split η m A z t W₂ W₂ X₂ X₂ hX₂ hX₂ SB βB PB hPB SB βB PB hPB]; ring
  have sA := energy_summable η m A t W₁ W₁ b₁ b₁ X₁ X₁ hs₁ hs₁ hX₁ hX₁
    (Sum.elim SA SA) (Sum.elim βA βA) (Sum.elim PA PA) keep Φ K hK
  have sB := energy_summable η m A t W₂ W₂ b₂ b₂ X₂ X₂ hs₂ hs₂ hX₂ hX₂
    (Sum.elim SB SB) (Sum.elim βB βB) (Sum.elim PB PB) keep Φ K hK
  simp only [hAA] at sA
  simp only [hBB] at sB
  rw [energy_eq_weighted, energy_eq_weighted, energy_eq_weighted]
  simp only [hT, hAA, hBB]
  exact tsum_cs (rowWeight keep Φ K) a b (rowWeight_nonneg keep Φ K hΦ) ha hb sA sB

/-! ### Reindexing by `Finset.univ` -/

theorem energy_univ {κ : Type*} [Fintype κ] (η : Character) (m A : O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (S : κ → Finset (Ideal O)) (β : κ → Ideal O → ℂ) (P : κ → ℝ) (X₁ X₂ : ℝ)
    (keep : O → Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) :
    energy η m A t W₁ W₂ (fun i : (Finset.univ : Finset κ) => S i.val) (fun i => β i.val)
        (fun i => P i.val) X₁ X₂ keep Φ K =
      energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K := by
  have hP : (∏ i : (Finset.univ : Finset κ), P i.val) = ∏ i, P i :=
    Finset.prod_coe_sort Finset.univ P
  have hS : ∀ z, (∏ i : (Finset.univ : Finset κ), rowSlot η m A z (S i.val) (β i.val) t) =
      ∏ i, rowSlot η m A z (S i) (β i) t := fun z =>
    Finset.prod_coe_sort Finset.univ (fun i => rowSlot η m A z (S i) (β i) t)
  simp only [energy, positiveSlotRow, hP, hS]

theorem elim_forall {α β γ : Type*} {f : α → γ} {g : β → γ} (P : γ → Prop)
    (hf : ∀ i, P (f i)) (hg : ∀ i, P (g i)) : ∀ i, P (Sum.elim f g i)
  | Sum.inl i => hf i
  | Sum.inr i => hg i

/-! ### The midpoint rule for face sources -/

local instance faceRegionQuotientFinite (rayM : Ideal O) [NeZero rayM] : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)

/-- The Cauchy–Schwarz closure of two faces, evaluated on a configuration whose slots are split
into the families `ιA` (paired with the first plain) and `ιB` (paired with the second plain):
`faceA` must admit `(m₁, m₁, 2 sA)` and `faceB` must admit `(m₂, m₂, 2 sB)`. The energy and the
bound are literally those of `InitialAffineAt`, for the slot family `ιA ⊕ ιB`. -/
def MidpointAt (ιA ιB : Type) [Fintype ιA] [Fintype ιB]
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) (faceA faceB : SourceFace) (W : ℝ → ℂ)
    (bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z : ℝ) (η η₀ : Character) (Q : Ideal O)
    (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ (θA : ιA → RayQuotient.Characters rayM H) (wA σA vA : ιA → ℝ)
    (θB : ιB → RayQuotient.Characters rayM H) (wB σB vB : ιB → ℝ) (t height : ℝ),
    (∀ i, 0 ≤ wA i) → (∀ i, wA i ≤ mesh) → (∀ i, σlo ≤ σA i) → (∀ i, σA i ≤ σhi) →
    (∀ i, |vA i| ≤ height) →
    (∀ i, 0 ≤ wB i) → (∀ i, wB i ≤ mesh) → (∀ i, σlo ≤ σB i) → (∀ i, σB i ≤ σhi) →
    (∀ i, |vB i| ≤ height) → 0 ≤ height →
  ∀ M : ℝ, Mmin ≤ M → M ≤ Mmax →
  ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ → (∀ x, 0 ≤ (Φ x).re) →
  ∀ p : Profiles a b, ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ →
    faceA.Admissible (length Z X₁) (length Z X₁) (2 * ∑ i, wA i) M →
    faceB.Admissible (length Z X₂) (length Z X₂) (2 * ∑ i, wB i) M →
    energy η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool rayM H bslot (Z^(Sum.elim wA wB i)))
      (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (Sum.elim θA θB i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(Sum.elim wA wB i)) (Sum.elim σA σB i)
          (Sum.elim vA vB i) I)
      (fun i => Z^(Sum.elim wA wB i)) X₁ X₂ (initialKeep η (internalQ Q η₀)) Φ (Z^M) ≤
      C*diagonalControl Φ*(p.control S)^2*(1+|t|+height)^degree*Z^(M+ε)

set_option maxHeartbeats 1600000 in
/-- **Midpoint rule.** Face bounds at the doubled slot types give the Cauchy–Schwarz closure. -/
theorem midpoint_at {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM ≤ H) (faceA faceB : SourceFace) (W : ℝ → ℂ)
    (bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z : ℝ) (hZ : 0 < Z)
    (η η₀ : Character) (Q : Ideal O) (dA dB : ℕ) (CtA CtB : Finset (ℕ × ℕ)) (CA CB : ℝ)
    (hCA : 0 ≤ CA) (_hCB : 0 ≤ CB)
    (hA : InitialAffineAt (α := ιA ⊕ ιA) rayM H hH faceA W bslot a b bΦ mesh σlo σhi
      Mmin Mmax ε Z η η₀ Q dA CtA CA)
    (hB : InitialAffineAt (α := ιB ⊕ ιB) rayM H hH faceB W bslot a b bΦ mesh σlo σhi
      Mmin Mmax ε Z η η₀ Q dB CtB CB) :
    MidpointAt ιA ιB rayM H hH faceA faceB W bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z η η₀ Q
      (dA + dB) (CtA ∪ CtB) (max CA CB) := by
  intro θA wA σA vA θB wB σB vB t height hwA hwmA hσlA hσhA hvA hwB hwmB hσlB hσhB hvB hh
    M hM₁ hM₂ Φ hΦs hΦ p X₁ X₂ hX₁ hX₂ hadmA hadmB
  -- the two slot families as functions of their own index
  let SA : ιA → Finset (Ideal O) := fun i => primePool rayM H bslot (Z^(wA i))
  let βA : ιA → Ideal O → ℂ := fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θA i)) I *
    HeckePrimeAnnular.annularWeight W (Z^(wA i)) (σA i) (vA i) I
  let PA : ιA → ℝ := fun i => Z^(wA i)
  let SB : ιB → Finset (Ideal O) := fun i => primePool rayM H bslot (Z^(wB i))
  let βB : ιB → Ideal O → ℂ := fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (θB i)) I *
    HeckePrimeAnnular.annularWeight W (Z^(wB i)) (σB i) (vB i) I
  let PB : ιB → ℝ := fun i => Z^(wB i)
  have hPA : ∀ i, 0 < PA i := fun i => Real.rpow_pos_of_pos hZ _
  have hPB : ∀ i, 0 < PB i := fun i => Real.rpow_pos_of_pos hZ _
  let keep := initialKeep η (internalQ Q η₀)
  let mk := fixedBadMask*idealGenerator 1
  let W₁ : ℝ → ℂ := p.profile 0
  let W₂ : ℝ → ℂ := p.profile 1
  have hs₁ : Function.support W₁ ⊆ Set.Iic b := (p.support 0).trans Set.Icc_subset_Iic_self
  have hs₂ : Function.support W₂ ⊆ Set.Iic b := (p.support 1).trans Set.Icc_subset_Iic_self
  have hK : 0 < Z^M := Real.rpow_pos_of_pos hZ _
  -- the squared profiles
  let pA : Profiles a b := ⟨fun _ => p.profile 0, fun _ => p.support 0⟩
  let pB : Profiles a b := ⟨fun _ => p.profile 1, fun _ => p.support 1⟩
  -- the target is the `Sum.elim` configuration
  have eS : (fun i => primePool rayM H bslot (Z^(Sum.elim wA wB i))) = Sum.elim SA SB := by
    funext i; cases i <;> rfl
  have eβ : (fun i I => idealCoeff (relativeCharacter rayM H hH η₀ (Sum.elim θA θB i)) I *
      HeckePrimeAnnular.annularWeight W (Z^(Sum.elim wA wB i)) (Sum.elim σA σB i)
        (Sum.elim vA vB i) I) = Sum.elim βA βB := by
    funext i; cases i <;> rfl
  have eP : (fun i => Z^(Sum.elim wA wB i)) = Sum.elim PA PB := by
    funext i; cases i <;> rfl
  rw [eS, eβ, eP]
  -- the face bound on the squared configuration `(m₁, m₁, 2 sA)`
  have hsumA : (∑ i : (Finset.univ : Finset (ιA ⊕ ιA)), Sum.elim wA wA i.val) =
      2 * ∑ i, wA i := by
    rw [Finset.sum_coe_sort Finset.univ (Sum.elim wA wA), sum_elim]; ring
  have hsumB : (∑ i : (Finset.univ : Finset (ιB ⊕ ιB)), Sum.elim wB wB i.val) =
      2 * ∑ i, wB i := by
    rw [Finset.sum_coe_sort Finset.univ (Sum.elim wB wB), sum_elim]; ring
  have hAA : energy η mk 1 t W₁ W₁ (Sum.elim SA SA) (Sum.elim βA βA) (Sum.elim PA PA) X₁ X₁
      keep Φ (Z^M) ≤ CA*diagonalControl Φ*(pA.control CtA)^2*(1+|t|+height)^dA*Z^(M+ε) := by
    have h := hA Finset.univ (fun i => Sum.elim θA θA i.val) (fun i => Sum.elim wA wA i.val)
      (fun i => Sum.elim σA σA i.val) (fun i => Sum.elim vA vA i.val) t height
      (fun i => elim_forall (fun x => 0 ≤ x) hwA hwA i.val)
      (fun i => elim_forall (fun x => x ≤ mesh) hwmA hwmA i.val)
      (fun i => elim_forall (fun x => σlo ≤ x) hσlA hσlA i.val)
      (fun i => elim_forall (fun x => x ≤ σhi) hσhA hσhA i.val) hh
      (fun i => elim_forall (fun x => |x| ≤ height) hvA hvA i.val)
      M hM₁ hM₂ Φ hΦs hΦ pA X₁ X₁ hX₁ hX₁ (by rw [hsumA]; exact hadmA)
    have e1 := energy_univ η mk 1 t W₁ W₁
      (fun j => primePool rayM H bslot (Z^(Sum.elim wA wA j)))
      (fun j I => idealCoeff (relativeCharacter rayM H hH η₀ (Sum.elim θA θA j)) I *
        HeckePrimeAnnular.annularWeight W (Z^(Sum.elim wA wA j)) (Sum.elim σA σA j)
          (Sum.elim vA vA j) I)
      (fun j => Z^(Sum.elim wA wA j)) X₁ X₁ keep Φ (Z^M)
    have h' := e1.symm.trans_le h
    have eS' : (fun j => primePool rayM H bslot (Z^(Sum.elim wA wA j))) = Sum.elim SA SA := by
      funext i; cases i <;> rfl
    have eβ' : (fun j I => idealCoeff (relativeCharacter rayM H hH η₀ (Sum.elim θA θA j)) I *
        HeckePrimeAnnular.annularWeight W (Z^(Sum.elim wA wA j)) (Sum.elim σA σA j)
          (Sum.elim vA vA j) I) = Sum.elim βA βA := by
      funext i; cases i <;> rfl
    have eP' : (fun j => Z^(Sum.elim wA wA j)) = Sum.elim PA PA := by
      funext i; cases i <;> rfl
    rw [eS', eβ', eP'] at h'
    exact h'
  have hBB : energy η mk 1 t W₂ W₂ (Sum.elim SB SB) (Sum.elim βB βB) (Sum.elim PB PB) X₂ X₂
      keep Φ (Z^M) ≤ CB*diagonalControl Φ*(pB.control CtB)^2*(1+|t|+height)^dB*Z^(M+ε) := by
    have h := hB Finset.univ (fun i => Sum.elim θB θB i.val) (fun i => Sum.elim wB wB i.val)
      (fun i => Sum.elim σB σB i.val) (fun i => Sum.elim vB vB i.val) t height
      (fun i => elim_forall (fun x => 0 ≤ x) hwB hwB i.val)
      (fun i => elim_forall (fun x => x ≤ mesh) hwmB hwmB i.val)
      (fun i => elim_forall (fun x => σlo ≤ x) hσlB hσlB i.val)
      (fun i => elim_forall (fun x => x ≤ σhi) hσhB hσhB i.val) hh
      (fun i => elim_forall (fun x => |x| ≤ height) hvB hvB i.val)
      M hM₁ hM₂ Φ hΦs hΦ pB X₂ X₂ hX₂ hX₂ (by rw [hsumB]; exact hadmB)
    have e1 := energy_univ η mk 1 t W₂ W₂
      (fun j => primePool rayM H bslot (Z^(Sum.elim wB wB j)))
      (fun j I => idealCoeff (relativeCharacter rayM H hH η₀ (Sum.elim θB θB j)) I *
        HeckePrimeAnnular.annularWeight W (Z^(Sum.elim wB wB j)) (Sum.elim σB σB j)
          (Sum.elim vB vB j) I)
      (fun j => Z^(Sum.elim wB wB j)) X₂ X₂ keep Φ (Z^M)
    have h' := e1.symm.trans_le h
    have eS' : (fun j => primePool rayM H bslot (Z^(Sum.elim wB wB j))) = Sum.elim SB SB := by
      funext i; cases i <;> rfl
    have eβ' : (fun j I => idealCoeff (relativeCharacter rayM H hH η₀ (Sum.elim θB θB j)) I *
        HeckePrimeAnnular.annularWeight W (Z^(Sum.elim wB wB j)) (Sum.elim σB σB j)
          (Sum.elim vB vB j) I) = Sum.elim βB βB := by
      funext i; cases i <;> rfl
    have eP' : (fun j => Z^(Sum.elim wB wB j)) = Sum.elim PB PB := by
      funext i; cases i <;> rfl
    rw [eS', eβ', eP'] at h'
    exact h'
  -- Cauchy–Schwarz over the rows
  have hcs := energy_sum_cs η mk 1 t W₁ W₂ b b X₁ X₂ hs₁ hs₂ hX₁ hX₂ SA βA PA hPA SB βB PB hPB
    keep Φ (Z^M) hK hΦ
  -- the scalar bookkeeping
  set U := CtA ∪ CtB with hU
  set D := diagonalControl Φ with hD
  set hb := (1+|t|+height) with hhb
  set Zp := Z^(M+ε) with hZp
  set C := max CA CB with hC
  set c₁ := sourceControl U (p.profile 0) with hc₁
  set c₂ := sourceControl U (p.profile 1) with hc₂
  have hD0 : 0 ≤ D := diagonalControl_nonneg Φ
  have hb1 : 1 ≤ hb := by have := abs_nonneg t; linarith
  have hb0 : 0 ≤ hb := by linarith
  have hZp0 : 0 ≤ Zp := (Real.rpow_pos_of_pos hZ _).le
  have hc₁0 : 0 ≤ c₁ := sourceControl_nonneg _ _
  have hc₂0 : 0 ≤ c₂ := sourceControl_nonneg _ _
  have hC0 : 0 ≤ C := hCA.trans (le_max_left _ _)
  have hpAc : pA.control CtA ≤ c₁ * c₁ :=
    CenteredMomentEnergyBandMonotonicity.profile_control_mono pA Finset.subset_union_left
  have hpBc : pB.control CtB ≤ c₂ * c₂ :=
    CenteredMomentEnergyBandMonotonicity.profile_control_mono pB Finset.subset_union_right
  have hpA0 : 0 ≤ pA.control CtA := pA.control_nonneg _
  have hpB0 : 0 ≤ pB.control CtB := pB.control_nonneg _
  have hpc : p.control U = c₁ * c₂ := rfl
  have hRA : CA*D*(pA.control CtA)^2*hb^dA*Zp ≤ C*D*(c₁*c₁)^2*hb^dA*Zp := by
    have h1 : CA ≤ C := le_max_left _ _
    have h2 : (pA.control CtA)^2 ≤ (c₁*c₁)^2 := pow_le_pow_left₀ hpA0 hpAc 2
    gcongr
  have hRB : CB*D*(pB.control CtB)^2*hb^dB*Zp ≤ C*D*(c₂*c₂)^2*hb^dB*Zp := by
    have h1 : CB ≤ C := le_max_right _ _
    have h2 : (pB.control CtB)^2 ≤ (c₂*c₂)^2 := pow_le_pow_left₀ hpB0 hpBc 2
    gcongr
  have hEA0 := energy_nonneg η mk 1 t W₁ W₁ (Sum.elim SA SA) (Sum.elim βA βA) (Sum.elim PA PA)
    X₁ X₁ keep Φ (Z^M) hΦ
  have hEB0 := energy_nonneg η mk 1 t W₂ W₂ (Sum.elim SB SB) (Sum.elim βB βB) (Sum.elim PB PB)
    X₂ X₂ keep Φ (Z^M) hΦ
  have hET0 := energy_nonneg η mk 1 t W₁ W₂ (Sum.elim SA SB) (Sum.elim βA βB) (Sum.elim PA PB)
    X₁ X₂ keep Φ (Z^M) hΦ
  have hpow : hb^dA * hb^dB ≤ (hb^(dA+dB))^2 := by
    rw [← pow_add, ← pow_mul]
    exact pow_le_pow_right₀ hb1 (by omega)
  have hprod : C*D*(c₁*c₁)^2*hb^dA*Zp * (C*D*(c₂*c₂)^2*hb^dB*Zp) ≤
      (C*D*(p.control U)^2*hb^(dA+dB)*Zp)^2 := by
    rw [hpc]
    have e : C*D*(c₁*c₁)^2*hb^dA*Zp * (C*D*(c₂*c₂)^2*hb^dB*Zp) =
        (C*D*(c₁*c₂)^2*Zp)^2 * (hb^dA * hb^dB) := by ring
    have e' : (C*D*(c₁*c₂)^2*hb^(dA+dB)*Zp)^2 = (C*D*(c₁*c₂)^2*Zp)^2 * (hb^(dA+dB))^2 := by ring
    rw [e, e']
    exact mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
  have hsq : (energy η mk 1 t W₁ W₂ (Sum.elim SA SB) (Sum.elim βA βB) (Sum.elim PA PB) X₁ X₂
      keep Φ (Z^M))^2 ≤ (C*D*(p.control U)^2*hb^(dA+dB)*Zp)^2 := by
    refine hcs.trans (le_trans ?_ hprod)
    exact mul_le_mul (hAA.trans hRA) (hBB.trans hRB) hEB0
      (by have := hEA0.trans (hAA.trans hRA); exact this)
  have hR0 : 0 ≤ C*D*(p.control U)^2*hb^(dA+dB)*Zp := by positivity
  exact (sq_le_sq₀ hET0 hR0).mp hsq

/-- **Midpoint rule for unit face sources.** For two unit face sources with a common mesh, every
pair of slot types `ιA`, `ιB` has constants (chosen before `Z`) for which the energy of the
configurations of the Cauchy–Schwarz closure is of diagonal order. -/
theorem midpoint_source (faceA faceB : SourceFace) {mesh ε : ℝ}
    (hA : UnitFaceSource faceA mesh ε) (hB : UnitFaceSource faceB mesh ε) :
    ∀ (ιA : Type) [Fintype ιA] [DecidableEq ιA] (ιB : Type) [Fintype ιB] [DecidableEq ιB],
    ∀ (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
      (hH : RayOrthogonality.globalUnits rayM ≤ H),
    ∀ (W : ℝ → ℂ), ContDiff ℝ ∞ W → Function.support W ⊆ Set.Icc (1:ℝ) 2 →
    ∀ bΦ : ℝ, 2 ≤ bΦ → ∀ (η η₀ : Character) (Q : Ideal O),
      Q ≤ rayM → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72:O)} →
      ∃ degree : ℕ, ∃ controls : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
        ∀ᶠ Z : ℝ in atTop,
          MidpointAt ιA ιB rayM H hH faceA faceB W 2 (1/4) (9/4) bΦ mesh
            (33/50) (33/50) 1 1 ε Z η η₀ Q degree controls C := by
  intro ιA _ _ ιB _ _ rayM _ H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨dA, CtA, CA, hCA, hevA⟩ :=
    hA (ιA ⊕ ιA) rayM H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨dB, CtB, CB, hCB, hevB⟩ :=
    hB (ιB ⊕ ιB) rayM H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  refine ⟨dA + dB, CtA ∪ CtB, max CA CB, lt_max_of_lt_left hCA, ?_⟩
  filter_upwards [hevA, hevB, eventually_gt_atTop (0:ℝ)] with Z hZA hZB hZ
  exact midpoint_at rayM H hH faceA faceB W 2 (1/4) (9/4) bΦ mesh (33/50) (33/50) 1 1 ε Z hZ
    η η₀ Q dA dB CtA CtB CA CB hCA.le hCB.le hZA hZB

/-! ### No gain on the balanced slice -/

/-- On the balanced slice `m₁ = m₂ = m` the Cauchy–Schwarz closure of two global faces adds
nothing: one of the two faces already admits the target `(m, m, sA + sB)`. -/
theorem balanced_no_gain {B lam cap B' lam' cap' m sA sB M : ℝ}
    (hlam : 0 ≤ lam) (hlam' : 0 ≤ lam') (hm : 0 ≤ m) (hsA : 0 ≤ sA) (hsB : 0 ≤ sB)
    (hA : (QRH.Record1252270103Source.globalFace B lam cap).Admissible m m (2*sA) M)
    (hB : (QRH.Record1252270103Source.globalFace B' lam' cap').Admissible m m (2*sB) M) :
    (QRH.Record1252270103Source.globalFace B lam cap).Admissible m m (sA+sB) M ∨
      (QRH.Record1252270103Source.globalFace B' lam' cap').Admissible m m (sA+sB) M := by
  rcases le_total sA sB with h | h
  · right
    exact QRH.Record1252270103Source.globalFace_downward hlam' hm hm (by linarith) hB hm hm
      (by linarith) le_rfl le_rfl (by linarith)
  · left
    exact QRH.Record1252270103Source.globalFace_downward hlam hm hm (by linarith) hA hm hm
      (by linarith) le_rfl le_rfl (by linarith)

end
end QRH.FaceRegion

#print axioms QRH.FaceRegion.tsum_cs
#print axioms QRH.FaceRegion.energy_sum_cs
#print axioms QRH.FaceRegion.midpoint_at
#print axioms QRH.FaceRegion.midpoint_source
#print axioms QRH.FaceRegion.balanced_no_gain
