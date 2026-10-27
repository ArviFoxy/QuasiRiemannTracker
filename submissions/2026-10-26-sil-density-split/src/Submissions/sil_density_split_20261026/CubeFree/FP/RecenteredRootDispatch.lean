/- Copyright (c) 2026 Sil. Apache-2.0.
Actual high-volume root dispatch: short originals are paid by the kept
reference theorem, long originals are genuinely recentered. The only
unevaluated term displayed is the literal centered energy, not an
assumed bound for it. 
Modified by Sil (2026-10-26): WP-K2a: threaded through the parametric root: StepData D and StepGates G (RootParameters.omegaLoss/omega_spec/NeedsCentering/centeredExponent/reference_gates G in place of the FP RepairedRootParameters face literals), Setup M H D, the explicit root input hs₀ : s₀ ≤ markedWidth, and the face cap c ≤ 1/6 (Setup.hD) in place of 3/50; numeric omega bound 1/10⁷ (RootParameters) in place of 1/10¹⁰.
-/
import Submissions.sil_density_split_20261026.CubeFree.FP.RecenteredRootReferenceBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace QRH.SilDensitySplit.CubeFree.FP.RecenteredRootDispatch
open Candidate.FourthPower
universe u
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter Set OAI OAI.SevenEighths HeckeFamily CanonicalQuadraticSieve
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentUncenteredTerminal
open CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional
open MixedPrincipalPair MixedFirstRebase MixedFirstPuncturedReference MixedFirstReferenceEnergy
open RestoredRootEnergy RestoredInitialSource RecenteredRootSource RecenteredRootSetup
open RecenteredRootRows RecenteredRootReferenceBound
local notation "O" => HeckeFamily.O
local notation "Id" => Ideal O
local instance {κ:Type*} : DecidableEq κ := Classical.decEq _
variable {α:Type u}[Fintype α]
variable (M:Id)[NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M ≤ H)
variable {D:QRH.SilDensitySplit.CubeFree.StepData}(G:QRH.SilDensitySplit.CubeFree.StepGates D)

def referenceCost (s:Setup M H D α)(ε:ℝ)(J:ℕ)(control:Finset (ℕ×ℕ))(C:ℝ)(Φ:𝓢(ℝ,ℂ)) : ℝ :=
  radialControl Φ*(C*(sourceControl control (s.p.profile 0)*sourceControl control (s.p.profile 1))^2*
    (MixedFirstProfileEnvelope.height 0 0 s.t s.t)^J*
    s.Z^(1+QRH.SilDensitySplit.CubeFree.RootParameters.omegaLoss G ε+ε/100))

theorem original_energy_rectangle (s:Setup M H D α)
    (hn₁:comparisonScale (9/4) < s.Y₁)(hn₂:comparisonScale (9/4) < s.Y₂)
    (η:Character)(Q:Id)(Φ:𝓢(ℝ,ℂ))(rows:Finset O) :
    (∑z∈rows,initialWeight η s.η₀ Q Φ s.Z z*‖s.literalRow hH (naturalCharacter η z)‖^2)=
      ∑z∈rows,initialWeight η s.η₀ Q Φ s.Z z*
        ‖rectangle (s.rootSource hH hn₁ hn₂) (by norm_num) (naturalCharacter η z) s.Y₁ s.Y₂‖^2 := by
  rw [s.initial_energy_source hH hn₁ hn₂ η Q Φ rows]
  apply Finset.sum_congr rfl
  intro z hz
  rw [weighted_row_uncentered (s.rootSource hH hn₁ hn₂) (by norm_num) rfl rfl (naturalCharacter η z)]
  rfl

set_option maxHeartbeats 1000000 in
/-- This applies the proven reference estimate internally in BOTH
branches. No reference-energy or original-source bound is a premise. -/
theorem uniform_high_root_dispatch
    (W:ℝ → ℂ)(hW:ContDiff ℝ ∞ W)(hWs:Function.support W⊆Icc (1:ℝ) 2)
    (Lcap ε:ℝ)(hLcap:8 ≤ Lcap)(hε:0 < ε) :
    ∃J:ℕ,∃control:Finset (ℕ×ℕ),∃C:ℝ,0 < C ∧
    ∀(η:Character)(bΦ:ℝ),2 ≤ bΦ  →  ∀ᶠZ:ℝ in atTop,1 < Z ∧
    ∀s:Setup M H D α,s.Z=Z  →  s.W=W  →  s.Lcap=Lcap  → 
    ∀hn₁:comparisonScale (9/4) < s.Y₁,∀hn₂:comparisonScale (9/4) < s.Y₂,
    ∀hs₀:D.s₀≤markedWidth M H s,∀hhigh:QRH.SilDensitySplit.CubeFree.RootParameters.NeedsCentering G ε (ordinaryExponent M H s) (markedWidth M H s),
    ∀Q:Id,∀Φ:𝓢(ℝ,ℂ),Function.support (Φ:ℝ → ℂ)⊆Iic bΦ  →  (∀x,0 ≤ (Φ x).re)  →  ∀rows:Finset O,
    ((s.Y₁ ≤ rootReference M H G s ε ∨ s.Y₂ ≤ rootReference M H G s ε)  → 
      (∑z∈rows,initialWeight η s.η₀ Q Φ Z z*‖s.literalRow hH (naturalCharacter η z)‖^2) ≤ 
        referenceCost M H G s ε J control C Φ) ∧
    (∀h₁:rootReference M H G s ε ≤ s.Y₁,∀h₂:rootReference M H G s ε ≤ s.Y₂,
      (∑z∈rows,initialWeight η s.η₀ Q Φ Z z*‖s.literalRow hH (naturalCharacter η z)‖^2) ≤ 
      2*((∑z∈rows,initialWeight η s.η₀ Q Φ Z z*
        ‖weightedRow (centeredRoot M H hH G s ε hε hn₁ hn₂ hs₀ hhigh h₁ h₂)
          (by norm_num) 1 (idealCoeff (naturalCharacter η z))‖^2)+
        referenceCost M H G s ε J control C Φ)) := by
  obtain ⟨J,control,C,hC,href⟩:=uniform_original_reference (α:=α) M H hH G W hW hWs Lcap ε hLcap hε
  refine ⟨J,control,C,hC,?_⟩
  intro η bΦ hbΦ
  filter_upwards [href η bΦ hbΦ] with Z hrefZ
  refine ⟨hrefZ.1,?_⟩
  intro s hsZ hsW hsLc hn₁ hn₂ hs₀ hhigh Q Φ hΦs hΦ rows
  subst Z
  let r:=s.rootSource hH hn₁ hn₂
  have hq:=reference_geometry M H G s ε hε hs₀ hhigh
  have hbound:=hrefZ.2 s rfl hsW hsLc hn₁ hn₂ hs₀ hhigh
  constructor
  · intro hshort
    rw [original_energy_rectangle M H hH s hn₁ hn₂ η Q Φ rows]
    exact hbound s.Y₁ s.Y₂ s.hY₁ s.hY₂ rfl r.hXU₁ r.hXU₂ hshort Q Φ hΦs hΦ rows
  · intro h₁ h₂
    have hqU:rootReference M H G s ε ≤ r.U₁:=h₁.trans r.hXU₁
    have hqY:(s.Y₁*s.Y₂)/rootReference M H G s ε ≤ r.Y₂:=
      reference_second_le r (rootReference M H G s ε) hq.1 hq.2.2.1
    have hqYU:(s.Y₁*s.Y₂)/rootReference M H G s ε ≤ r.U₂:=hqY.trans r.hYU₂
    have hprod:rootReference M H G s ε*((s.Y₁*s.Y₂)/rootReference M H G s ε)=s.Y₁*s.Y₂:=by
      field_simp [hq.1.ne']
    have hreference:=hbound (rootReference M H G s ε) ((s.Y₁*s.Y₂)/rootReference M H G s ε)
      hq.1 (div_pos (mul_pos s.hY₁ s.hY₂) hq.1) hprod hqU hqYU (Or.inl le_rfl) Q Φ hΦs hΦ rows
    have hsplit:=actual_initial_triangle M H hH G s ε hε hn₁ hn₂ hs₀ hhigh h₁ h₂ η Q Φ hΦ rows
    apply hsplit.trans
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hreference) (by norm_num)

end
end QRH.SilDensitySplit.CubeFree.FP.RecenteredRootDispatch
