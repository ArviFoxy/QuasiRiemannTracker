/- Copyright (c) 2026 Sil. Apache-2.0.
WP-L: the restricted input split into single restored rows.

`RestrictedInitialAtT … T w` (WP-R) quantifies over the collision setoid `r` on `T` and the
inverse-deleted singletons `A`; the restored row then lives on the remaining singletons, of
marked width `rowWidth T w r A ≤ ∑_T w`. `RestrictedRowAt … T w r A` is the same statement
for one `(r, A)`. The cube-free step treats the rows by their own width: rows narrower than
`s₀` come from the parent (`ParentRows`), the others from the root chain. -/
import Submissions.density_split_third_20261026.CubeFree.FP.RestoredInitialSource
import Submissions.density_split_third_20261026.CubeFree.FP.RestoredRootDictionary
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.BandMonotonicity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.Assembly
noncomputable section
open Candidate.FourthPower
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve QRH.Record1252270103TwoIdeal QRH.Record1252270103KernelMass
open QRH.Record12518109Source QRH.Record12518109Existence QRH.Record1252270103Source
open CenteredMomentEnergyBands CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot CenteredMomentRetainedEnergy CenteredMomentLattice
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentRayMaskedFloor QuadraticInitialBound CenteredMomentEnergyBandMonotonicity
open QRH.DensitySplitThird.CubeFree.FP
open RestorationFamily KernelCollisionEnergy KernelRowPools KernelRowProfiles
open ReferencePrimeEnclosure RestoredInitialSource
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O

section
variable {α : Type} [Fintype α] [DecidableEq α]
variable (rayM : Id) [NeZero rayM]
local instance finiteRayQuotient : Finite (O⧸rayM) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayM)
variable (H : Subgroup (O⧸rayM)ˣ) (hH : RayOrthogonality.globalUnits rayM ≤ H)

/-- Marked width of the restored row `(r, A)` of `(T, w)`: the remaining singletons. -/
def rowWidth (T : Finset α) (w : T → ℝ) (r : Setoid T) (A : Finset {q // singletonBlock r q}) :
    ℝ :=
  ∑ q : {q : {q // singletonBlock r q} // q ∉ A}, w (singletonRepresentative r q.val)

/-- The restricted input for one restored row `(r, A)` of `(T, w)`. -/
def RestrictedRowAt (face : SourceFace) (W : ℝ → ℂ)
    (bΦ mesh ε Z : ℝ) (η η₀ : Character) (Q : Id)
    (degree : ℕ) (controls : Finset (ℕ×ℕ)) (C : ℝ) (T : Finset α) (w : T → ℝ)
    (r : Setoid T) (A : Finset {q // singletonBlock r q}) : Prop :=
  ∀ (θ : T → RayQuotient.Characters rayM H) (σ v : T → ℝ) (t height : ℝ),
    (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
    (∀ i, (33/50:ℝ) ≤ σ i) → (∀ i, σ i ≤ (33/50:ℝ)) →
    0 ≤ height → (∀ i, |v i| ≤ height) →
  ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ →
    (∀ x, 0 ≤ (Φ x).re) →
  ∀ (p : Profiles (1/4) (9/4)) (X₁ X₂ : ℝ), 0 < X₁ → 0 < X₂ →
    face.Admissible (length Z X₁) (length Z X₂) (∑ i, w i) 1 →
  ∀ (rows : Finset O) (tc : {q // ¬singletonBlock r q} → primeEnclosure Z)
    (ti : A → primeEnclosure Z),
    Function.Injective ti →
  ∀ Y₁ Y₂ : ℝ, 0 < Y₁ → Y₁ ≤ X₁ → 0 < Y₂ → Y₂ ≤ X₂ →
    (∑ z ∈ rows, initialWeight η η₀ Q Φ Z z *
      ‖row false (primeEnclosure Z) (naturalCharacter η z)
        (fun q : {q : {q // singletonBlock r q} // q ∉ A} =>
          initialPool rayM H w Z (singletonRepresentative r q.val))
        (crossBeta A (primeEnclosure Z) ti
          (RestorationCollisionEnergy.collisionBeta r (primeEnclosure Z) tc
            (initialCoefficient rayM H hH η₀ θ W w σ v Z t)))
        (fun q => Z^(w (singletonRepresentative r q.val)))
        (raisedProfile p t 0) (raisedProfile p t 1) (9/4) Y₁ Y₂‖^2) ≤
      C*diagonalControl Φ*(p.control controls)^2*
        (1+|t|+height)^degree*Z^(1+ε)

theorem restrictedInitialAtT_of_rows (face : SourceFace) (W : ℝ → ℂ)
    (bΦ mesh ε Z : ℝ) (η η₀ : Character) (Q : Id)
    (degree : ℕ) (controls : Finset (ℕ×ℕ)) (C : ℝ) (T : Finset α) (w : T → ℝ)
    (h : ∀ r A, RestrictedRowAt rayM H hH face W bΦ mesh ε Z η η₀ Q degree controls C T w r A) :
    RestrictedInitialAtT (α:=α) rayM H hH face W bΦ mesh ε Z η η₀ Q degree controls C T w :=
  fun θ σ v t height hw hwm hσlo hσhi hh hv Φ hΦ hΦp p X₁ X₂ hX₁ hX₂ hadm rows r tc A ti hti =>
    h r A θ σ v t height hw hwm hσlo hσhi hh hv Φ hΦ hΦp p X₁ X₂ hX₁ hX₂ hadm rows tc ti hti

/-- The scalar right-hand side is monotone in the constant, the control set and the degree. -/
theorem rhs_mono {a b : ℝ} (p : Profiles a b) (Φ : 𝓢(ℝ,ℂ)) {C C' : ℝ} {S S' : Finset (ℕ×ℕ)}
    {d d' : ℕ} (t height e : ℝ) (hC : 0 ≤ C) (hCC : C ≤ C') (hS : S ⊆ S') (hd : d ≤ d')
    (hh : 0 ≤ height) (he : 0 ≤ e) :
    C*diagonalControl Φ*(p.control S)^2*(1+|t|+height)^d*e ≤
      C'*diagonalControl Φ*(p.control S')^2*(1+|t|+height)^d'*e := by
  have hdg := diagonalControl_nonneg Φ
  have hc0 := Profiles.control_nonneg p S
  have hcS : (p.control S)^2 ≤ (p.control S')^2 :=
    pow_le_pow_left₀ hc0 (profile_control_mono p hS) 2
  have hb1 : 1 ≤ 1+|t|+height := by have := abs_nonneg t; linarith
  have hbd : (1+|t|+height)^d ≤ (1+|t|+height)^d' := pow_le_pow_right₀ hb1 hd
  have h1 : C*diagonalControl Φ ≤ C'*diagonalControl Φ := mul_le_mul_of_nonneg_right hCC hdg
  have h2 := mul_le_mul h1 hcS (sq_nonneg _) (mul_nonneg (hC.trans hCC) hdg)
  have h3 := mul_le_mul h2 hbd (pow_nonneg (by linarith) _)
    (mul_nonneg (mul_nonneg (hC.trans hCC) hdg) (sq_nonneg _))
  exact mul_le_mul_of_nonneg_right h3 he

theorem RestrictedRowAt.mono {face : SourceFace} {W : ℝ → ℂ}
    {bΦ mesh mesh' ε Z : ℝ} {η η₀ : Character} {Q : Id}
    {degree degree' : ℕ} {controls controls' : Finset (ℕ×ℕ)} {C C' : ℝ} {T : Finset α}
    {w : T → ℝ} {r : Setoid T} {A : Finset {q // singletonBlock r q}}
    (h : RestrictedRowAt rayM H hH face W bΦ mesh ε Z η η₀ Q degree controls C T w r A)
    (hm : mesh' ≤ mesh) (hC : 0 ≤ C) (hCC : C ≤ C') (hS : controls ⊆ controls')
    (hd : degree ≤ degree') (hZ : 0 < Z) :
    RestrictedRowAt rayM H hH face W bΦ mesh' ε Z η η₀ Q degree' controls' C' T w r A := by
  intro θ σ v t height hw hwm hσlo hσhi hh hv Φ hΦ hΦp p X₁ X₂ hX₁ hX₂ hadm rows tc ti hti
    Y₁ Y₂ hY₁ hYX₁ hY₂ hYX₂
  exact (h θ σ v t height hw (fun i => (hwm i).trans hm) hσlo hσhi hh hv Φ hΦ hΦp p X₁ X₂
    hX₁ hX₂ hadm rows tc ti hti Y₁ Y₂ hY₁ hYX₁ hY₂ hYX₂).trans
    (rhs_mono p Φ t height _ hC hCC hS hd hh (Real.rpow_nonneg hZ.le _))

end

end
end QRH.DensitySplitThird.CubeFree.Assembly
