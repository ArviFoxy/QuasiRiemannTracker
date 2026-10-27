/- Copyright (c) 2026 Sil. Apache-2.0.
Uniform actual root dispatch with a single moving-profile control.
Reference terms are proved; remaining full-ball energies are literal
low/centered expressions, not assumed bounded. 
Modified by Sil (2026-10-26): WP-K2a: threaded through the parametric root: StepData D and StepGates G (RootParameters.omegaLoss/omega_spec/NeedsCentering/centeredExponent/reference_gates G in place of the FP RepairedRootParameters face literals), Setup M H D, the explicit root input hs₀ : s₀ ≤ markedWidth, and the face cap c ≤ 1/6 (Setup.hD) in place of 3/50; numeric omega bound 1/10⁷ (RootParameters) in place of 1/10¹⁰; the low (non-centering) branch needs no s₀ input.
-/
import Submissions.density_split_third_20261026.CubeFree.FP.RecenteredRootFixedMajorant

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.DensitySplitThird.CubeFree.FP.RecenteredRootFamilyDispatch
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentUncenteredTerminal
open CenteredMomentAllocatedNaturalRadial QuadraticInitialBound
open CenteredMomentFiniteProfileExceptional
open MixedFirstRebase MixedFirstReferenceEnergy
open RestoredRootEnergy RestoredInitialSource RecenteredRootSetup RecenteredRootRows
open RecenteredRootSource RecenteredRootDispatch RecenteredRootReferenceFamily RecenteredRootFixedMajorant
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
variable {α : Type u} [Fintype α]
variable (M : Id) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
variable {D:QRH.DensitySplitThird.CubeFree.StepData}(G:QRH.DensitySplitThird.CubeFree.StepGates D)

def profileCost (s : Setup M H D α) (ε : ℝ) (J : ℕ) (control : Finset (ℕ×ℕ)) (C : ℝ) : ℝ :=
  C*(sourceControl control (s.p.profile 0)*sourceControl control (s.p.profile 1))^2*
    (MixedFirstProfileEnvelope.height 0 0 s.t s.t)^J*
    s.Z^(1+QRH.DensitySplitThird.CubeFree.RootParameters.omegaLoss G ε+ε/100)

theorem profileCost_nonneg (s : Setup M H D α) (ε : ℝ) (J : ℕ) (control : Finset (ℕ×ℕ))
    (C : ℝ) (hC : 0 ≤ C) : 0 ≤ profileCost M H G s ε J control C := by
  have hh : 0 ≤ MixedFirstProfileEnvelope.height 0 0 s.t s.t := by
    unfold MixedFirstProfileEnvelope.height
    positivity
  have hz := zero_lt_one.trans s.hZ
  unfold profileCost
  positivity

theorem referenceCost_le_diagonal (s : Setup M H D α) (ε : ℝ) (J : ℕ) (control : Finset (ℕ×ℕ))
    (C : ℝ) (hC : 0 ≤ C) (Φ : 𝓢(ℝ,ℂ)) :
    referenceCost M H G s ε J control C Φ ≤ diagonalControl Φ*profileCost M H G s ε J control C :=
  mul_le_mul_of_nonneg_right (radialControl_le_diagonalControl Φ)
    (profileCost_nonneg M H G s ε J control C hC)

set_option maxHeartbeats 1000000 in
/-- Every original outer T0 and restored root follows ONE family of
controls and constants. Only the genuinely centered energy is used in
the long high branch; the old uncentered source occurs only in the low
branch. The reference retains initialKeep and is already paid here. -/
theorem uniform_root_family_dispatch
    (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W) (hWs : Function.support W ⊆ Icc (1:ℝ) 2)
    (Lcap ε : ℝ) (hLcap : 8 ≤ Lcap) (hε : 0 < ε) :
    ∃ J : ℕ, ∃ control : Finset (ℕ×ℕ), ∃ C : ℝ, 0 < C ∧
    ∀ (η : Character) (bΦ : ℝ), 2 ≤ bΦ → ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
    ∀ T0 : Finset α, ∀ s : Setup M H D T0, s.Z=Z → s.W=W → s.Lcap=Lcap →
    ∀ hn₁ : comparisonScale (9/4) < s.Y₁, ∀ hn₂ : comparisonScale (9/4) < s.Y₂,
    ∀ Q : Id, ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ:ℝ→ℂ) ⊆ Iic bΦ → (∀ x, 0 ≤ (Φ x).re) → ∀ rows : Finset O,
    ((¬QRH.DensitySplitThird.CubeFree.RootParameters.NeedsCentering G ε (ordinaryExponent M H s) (markedWidth M H s)) →
      (∑z∈rows,initialWeight η s.η₀ Q Φ Z z*‖s.literalRow hH (naturalCharacter η z)‖^2) ≤
        diagonalControl Φ*fullBallCost (s.rootSource hH hn₁ hn₂) (by norm_num) η (bΦ*Z)) ∧
    (∀ hs₀ : D.s₀≤markedWidth M H s, ∀ hhigh : QRH.DensitySplitThird.CubeFree.RootParameters.NeedsCentering G ε (ordinaryExponent M H s) (markedWidth M H s),
      ((s.Y₁ ≤ rootReference M H G s ε ∨ s.Y₂ ≤ rootReference M H G s ε) →
        (∑z∈rows,initialWeight η s.η₀ Q Φ Z z*‖s.literalRow hH (naturalCharacter η z)‖^2) ≤
          diagonalControl Φ*profileCost M H G s ε J control C) ∧
      (∀ h₁ : rootReference M H G s ε ≤ s.Y₁, ∀ h₂ : rootReference M H G s ε ≤ s.Y₂,
        (∑z∈rows,initialWeight η s.η₀ Q Φ Z z*‖s.literalRow hH (naturalCharacter η z)‖^2) ≤
          2*diagonalControl Φ*(
            fullBallCost (centeredRoot M H hH G s ε hε hn₁ hn₂ hs₀ hhigh h₁ h₂) (by norm_num) η (bΦ*Z)+
              profileCost M H G s ε J control C))) := by
  obtain ⟨J,control,C,hC,href⟩ := uniform_original_reference_family (α:=α) M H hH G W hW hWs Lcap ε hLcap hε
  refine ⟨J,control,C,hC,?_⟩
  intro η bΦ hbΦ
  filter_upwards [href η bΦ hbΦ] with Z hrefZ
  refine ⟨hrefZ.1,?_⟩
  intro T0 s hsZ hsW hsLc hn₁ hn₂ Q Φ hΦs hΦ rows
  subst Z
  let r := s.rootSource hH hn₁ hn₂
  have hz := zero_lt_one.trans s.hZ
  have hb : 0 < bΦ := by linarith
  have hdiag := diagonalControl_nonneg Φ
  constructor
  · intro hlow
    rw [s.initial_energy_source hH hn₁ hn₂ η Q Φ rows]
    exact finite_kept_le_fixed_ball r (by norm_num) η s.η₀ Q Φ s.Z bΦ hz hb hΦs rows
  · intro hs₀ hhigh
    have hq := reference_geometry M H G s ε hε hs₀ hhigh
    have hbound := hrefZ.2 T0 s rfl hsW hsLc hn₁ hn₂ hs₀ hhigh
    have herror := referenceCost_le_diagonal M H G s ε J control C hC.le Φ
    constructor
    · intro hshort
      rw [original_energy_rectangle M H hH s hn₁ hn₂ η Q Φ rows]
      exact (hbound s.Y₁ s.Y₂ s.hY₁ s.hY₂ rfl r.hXU₁ r.hXU₂ hshort Q Φ hΦs hΦ rows).trans herror
    · intro h₁ h₂
      let rc := centeredRoot M H hH G s ε hε hn₁ hn₂ hs₀ hhigh h₁ h₂
      have hqU : rootReference M H G s ε ≤ r.U₁ := h₁.trans r.hXU₁
      have hqY : (s.Y₁*s.Y₂)/rootReference M H G s ε ≤ r.Y₂ :=
        reference_second_le r (rootReference M H G s ε) hq.1 hq.2.2.1
      have hqYU : (s.Y₁*s.Y₂)/rootReference M H G s ε ≤ r.U₂ := hqY.trans r.hYU₂
      have hprod : rootReference M H G s ε*((s.Y₁*s.Y₂)/rootReference M H G s ε)=s.Y₁*s.Y₂ := by
        field_simp [hq.1.ne']
      have hreference := (hbound (rootReference M H G s ε) ((s.Y₁*s.Y₂)/rootReference M H G s ε)
        hq.1 (div_pos (mul_pos s.hY₁ s.hY₂) hq.1) hprod hqU hqYU (Or.inl le_rfl) Q Φ hΦs hΦ rows).trans herror
      have hcenter := finite_kept_le_fixed_ball rc (by norm_num) η s.η₀ Q Φ s.Z bΦ hz hb hΦs rows
      have hsplit := actual_initial_triangle M H hH G s ε hε hn₁ hn₂ hs₀ hhigh h₁ h₂ η Q Φ hΦ rows
      apply hsplit.trans
      have he := mul_le_mul_of_nonneg_left (add_le_add hcenter hreference) (by norm_num : (0:ℝ) ≤ 2)
      exact he.trans_eq (by ring)

end
end QRH.DensitySplitThird.CubeFree.FP.RecenteredRootFamilyDispatch
