/-
Energy regions, energy region estimates and the Arvi Zone.

A configuration is `(m₁, m₂, s, M)`: plain lengths, total slot length and family exponent. The literal
initial-energy statement of the source faces (`InitialAffineAt`, Collet `Record12518109Source/InitialMoment`)
uses its face only through `face.Admissible m₁ m₂ s M`. Replacing that predicate by membership in an arbitrary
set of configurations gives the same statement for any *shape*:

* `RegionAffineAt R …`: the energy bound for every configuration in `R` (same quantifiers as `InitialAffineAt`);
* `IsEstimate R`: an energy region estimate, i.e. `R` with uniform constants (`∀ ε > 0, ∃ mesh > 0, …`),
  the same form as `UniformUnitFaceSource`;
* a face is the special case `R = faceRegion face` (`isEstimate_faceRegion_iff`, `isEstimate_globalFace_iff`,
  definitional);
* estimates are closed under subsets and under unions (`IsEstimate.mono`, `IsEstimate.union`): they form a
  lattice, with join = union of the proven shapes;
* the **Arvi Zone** is the union of all estimates (`arviZone`). It is the least upper bound of the estimates
  (`arviZone_isLUB`); a configuration lies in it iff the one-point region is an estimate (`mem_arviZone_iff`);
  every finite subset of it is an estimate. Its existence as a set is free; whether it is itself an
  estimate (one uniform set of constants) is not claimed.
-/
import Submissions.hailey_collet_1252270103.Record12518109Existence.UniformSource
import Submissions.hailey_collet_1252270103.Record1252270103Source.Core.Contract
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Energy.BandMonotonicity

set_option autoImplicit false

namespace QRH.ArviEnergyRegion
noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
open Filter OAI OAI.SevenEighths HeckeFamily
open CenteredMomentInductionEnergy CenteredMomentFiniteProfileExceptional QuadraticInitialBound
open CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorEnergyInitialState ConcretePrimeRowBridge CenteredMomentPrimeSlot
open QRH.Record12518109Source QRH.Record12518109Existence
local notation "O" => HeckeFamily.O

/-- A configuration `(m₁, m₂, s, M)`. -/
abbrev Config := ℝ × ℝ × ℝ × ℝ

/-- An energy region: a set of configurations. -/
abbrev EnergyRegion := Set Config

/-- The region of a source face. -/
def faceRegion (face : SourceFace) : EnergyRegion :=
  {x | face.Admissible x.1 x.2.1 x.2.2.1 x.2.2.2}

section
set_option linter.unusedSectionVars false
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rayModulus : Ideal O) [NeZero rayModulus]
local instance : Finite (O ⧸ rayModulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne rayModulus)
variable (H : Subgroup (O ⧸ rayModulus)ˣ)
variable (hH : RayOrthogonality.globalUnits rayModulus ≤ H)

/-- The literal initial-energy bound on every configuration of a region `R`: `InitialAffineAt` with the
face's admissibility replaced by membership in `R`. -/
def RegionAffineAt (R : EnergyRegion) (W : ℝ → ℂ)
    (bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ T : Finset α, ∀ (θ : T → RayQuotient.Characters rayModulus H)
      (w σ v : T → ℝ) (t height : ℝ),
    (∀ i, 0 ≤ w i) → (∀ i, w i ≤ mesh) →
    (∀ i, σlo ≤ σ i) → (∀ i, σ i ≤ σhi) →
    0 ≤ height → (∀ i, |v i| ≤ height) →
  ∀ M : ℝ, Mmin ≤ M → M ≤ Mmax →
  ∀ Φ : 𝓢(ℝ,ℂ), Function.support (Φ : ℝ → ℂ) ⊆ Set.Iic bΦ →
    (∀ x, 0 ≤ (Φ x).re) →
  ∀ p : Profiles a b, ∀ X₁ X₂ : ℝ, 0 < X₁ → 0 < X₂ →
    (length Z X₁, length Z X₂, ∑ i, w i, M) ∈ R →
    energy η (fixedBadMask*idealGenerator 1) 1 t (p.profile 0) (p.profile 1)
      (fun i => primePool rayModulus H bslot (Z^(w i)))
      (fun i I => idealCoeff (relativeCharacter rayModulus H hH η₀ (θ i)) I *
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i => Z^(w i)) X₁ X₂ (initialKeep η (internalQ Q η₀)) Φ (Z^M) ≤
      C*QuadraticInitialBound.diagonalControl Φ*(p.control S)^2*
        (1+|t|+height)^degree*Z^(M+ε)

theorem regionAffineAt_faceRegion_iff (face : SourceFace) (W : ℝ → ℂ)
    (bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z : ℝ)
    (η η₀ : Character) (Q : Ideal O) (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) :
    RegionAffineAt (α := α) rayModulus H hH (faceRegion face) W bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z
        η η₀ Q degree S C ↔
      InitialAffineAt (α := α) rayModulus H hH face W bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z
        η η₀ Q degree S C := Iff.rfl

/-- Smaller regions inherit the bound. -/
theorem RegionAffineAt.mono {R R' : EnergyRegion} (hRR : R' ⊆ R) {W : ℝ → ℂ}
    {bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z : ℝ}
    {η η₀ : Character} {Q : Ideal O} {degree : ℕ} {S : Finset (ℕ × ℕ)} {C : ℝ}
    (h : RegionAffineAt (α := α) rayModulus H hH R W bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z
      η η₀ Q degree S C) :
    RegionAffineAt (α := α) rayModulus H hH R' W bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z
      η η₀ Q degree S C := by
  intro T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hR
  exact h T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ (hRR hR)

/-- A smaller mesh keeps the bound. -/
theorem RegionAffineAt.mono_mesh {R : EnergyRegion} {W : ℝ → ℂ}
    {bslot a b bΦ mesh mesh' σlo σhi Mmin Mmax ε Z : ℝ}
    {η η₀ : Character} {Q : Ideal O} {degree : ℕ} {S : Finset (ℕ × ℕ)} {C : ℝ} (hle : mesh' ≤ mesh)
    (h : RegionAffineAt (α := α) rayModulus H hH R W bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z
      η η₀ Q degree S C) :
    RegionAffineAt (α := α) rayModulus H hH R W bslot a b bΦ mesh' σlo σhi Mmin Mmax ε Z
      η η₀ Q degree S C := by
  intro T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hR
  exact h T θ w σ v t height hw (fun i => (hwm i).trans hle) hσlo hσhi hh hv M hMlo hMhi Φ hΦ hΦpos
    p X₁ X₂ hX₁ hX₂ hR

/-- Larger constants (`C`, degree, controls) keep the bound, for `Z > 0`. -/
theorem RegionAffineAt.mono_const {R : EnergyRegion} {W : ℝ → ℂ}
    {bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z : ℝ}
    {η η₀ : Character} {Q : Ideal O} {d d' : ℕ} {S S' : Finset (ℕ × ℕ)} {C C' : ℝ}
    (hZ : 0 < Z) (hd : d ≤ d') (hS : S ⊆ S') (hC0 : 0 ≤ C) (hC : C ≤ C')
    (h : RegionAffineAt (α := α) rayModulus H hH R W bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z
      η η₀ Q d S C) :
    RegionAffineAt (α := α) rayModulus H hH R W bslot a b bΦ mesh σlo σhi Mmin Mmax ε Z
      η η₀ Q d' S' C' := by
  intro T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hR
  refine (h T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hR).trans ?_
  have hD : 0 ≤ QuadraticInitialBound.diagonalControl Φ := diagonalControl_nonneg Φ
  have hc0 : 0 ≤ p.control S := p.control_nonneg _
  have hcS : p.control S ≤ p.control S' :=
    CenteredMomentEnergyBandMonotonicity.profile_control_mono p hS
  have hb : 1 ≤ 1 + |t| + height := by have := abs_nonneg t; linarith
  have hpow : (1 + |t| + height)^d ≤ (1 + |t| + height)^d' := pow_le_pow_right₀ hb hd
  have hZp : 0 ≤ Z^(M+ε) := (Real.rpow_pos_of_pos hZ _).le
  have hc2 : (p.control S)^2 ≤ (p.control S')^2 := pow_le_pow_left₀ hc0 hcS 2
  have hpow0 : 0 ≤ (1 + |t| + height)^d := pow_nonneg (by linarith) d
  have hC'0 : 0 ≤ C' := le_trans hC0 hC
  have s1 : C*QuadraticInitialBound.diagonalControl Φ ≤ C'*QuadraticInitialBound.diagonalControl Φ :=
    mul_le_mul_of_nonneg_right hC hD
  have s2 : C*QuadraticInitialBound.diagonalControl Φ*(p.control S)^2 ≤
      C'*QuadraticInitialBound.diagonalControl Φ*(p.control S')^2 :=
    mul_le_mul s1 hc2 (sq_nonneg _) (mul_nonneg hC'0 hD)
  have s3 : C*QuadraticInitialBound.diagonalControl Φ*(p.control S)^2*(1+|t|+height)^d ≤
      C'*QuadraticInitialBound.diagonalControl Φ*(p.control S')^2*(1+|t|+height)^d' :=
    mul_le_mul s2 hpow hpow0 (mul_nonneg (mul_nonneg hC'0 hD) (sq_nonneg _))
  exact mul_le_mul_of_nonneg_right s3 hZp

end

/-- The same quantifiers as `UnitFaceSource`, for a region. -/
def UnitRegionSource (R : EnergyRegion) (mesh ε : ℝ) : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α],
  ∀ (rayM : Ideal O) [NeZero rayM] (H : Subgroup (O⧸rayM)ˣ)
    (hH : RayOrthogonality.globalUnits rayM≤H),
  ∀ (W : ℝ→ℂ), ContDiff ℝ ∞ W → Function.support W⊆Set.Icc (1:ℝ) 2 →
  ∀ bΦ : ℝ, 2≤bΦ → ∀ (η η₀ : Character) (Q : Ideal O),
    Q≤rayM → internalQ Q η₀≠0 → internalQ Q η₀≠⊤ →
    internalQ Q η₀≤Ideal.span {(72:O)} →
    ∃degree : ℕ, ∃controls : Finset (ℕ×ℕ), ∃C : ℝ, 0<C ∧
      ∀ᶠZ : ℝ in atTop,
        RegionAffineAt (α:=α) rayM H hH R W 2 (1/4) (9/4) bΦ mesh
          (33/50) (33/50) 1 1 ε Z η η₀ Q degree controls C

/-- An **energy region estimate**: the energy bound holds on the whole region with uniform constants. -/
def IsEstimate (R : EnergyRegion) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ mesh : ℝ, 0 < mesh ∧ UnitRegionSource R mesh ε

theorem isEstimate_faceRegion_iff (face : SourceFace) :
    IsEstimate (faceRegion face) ↔ UniformUnitFaceSource face := Iff.rfl

/-- A global source face is exactly an estimate of its half-space region. -/
theorem isEstimate_globalFace_iff (B lam cap : ℝ) :
    IsEstimate (faceRegion (QRH.Record1252270103Source.globalFace B lam cap)) ↔
      QRH.Record1252270103Source.GlobalSource B lam cap := Iff.rfl

theorem IsEstimate.mono {R R' : EnergyRegion} (hRR : R' ⊆ R) (h : IsEstimate R) : IsEstimate R' := by
  intro ε hε
  obtain ⟨mesh, hmesh, hs⟩ := h ε hε
  refine ⟨mesh, hmesh, ?_⟩
  intro α _ _ rayM _ H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨d, S, C, hC, hev⟩ := hs α rayM H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  exact ⟨d, S, C, hC, hev.mono fun Z hZ => RegionAffineAt.mono rayM H hH hRR hZ⟩

theorem isEstimate_empty : IsEstimate ∅ := by
  intro ε _
  refine ⟨1, one_pos, ?_⟩
  intro α _ _ rayM _ H hH W _ _ bΦ _ η η₀ Q _ _ _ _
  refine ⟨0, ∅, 1, one_pos, Filter.Eventually.of_forall fun Z => ?_⟩
  intro T θ w σ v t height _ _ _ _ _ _ M _ _ Φ _ _ p X₁ X₂ _ _ hR
  exact absurd hR (Set.notMem_empty _)

/-- **Join**: the union of two estimates is an estimate. -/
theorem IsEstimate.union {R₁ R₂ : EnergyRegion} (h₁ : IsEstimate R₁) (h₂ : IsEstimate R₂) :
    IsEstimate (R₁ ∪ R₂) := by
  intro ε hε
  obtain ⟨m₁, hm₁, hs₁⟩ := h₁ ε hε
  obtain ⟨m₂, hm₂, hs₂⟩ := h₂ ε hε
  refine ⟨min m₁ m₂, lt_min hm₁ hm₂, ?_⟩
  intro α _ _ rayM _ H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨d₁, S₁, C₁, hC₁, hev₁⟩ := hs₁ α rayM H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  obtain ⟨d₂, S₂, C₂, hC₂, hev₂⟩ := hs₂ α rayM H hH W hW hWs bΦ hbΦ η η₀ Q hQray hQ0 hQt hQ72
  refine ⟨max d₁ d₂, S₁ ∪ S₂, max C₁ C₂, lt_max_of_lt_left hC₁, ?_⟩
  filter_upwards [hev₁, hev₂, eventually_gt_atTop (0:ℝ)] with Z hZ₁ hZ₂ hZ
  have k₁ := RegionAffineAt.mono_const (S' := S₁ ∪ S₂) rayM H hH hZ (le_max_left d₁ d₂)
    Finset.subset_union_left hC₁.le (le_max_left C₁ C₂)
    (RegionAffineAt.mono_mesh rayM H hH (min_le_left m₁ m₂) hZ₁)
  have k₂ := RegionAffineAt.mono_const (S' := S₁ ∪ S₂) rayM H hH hZ (le_max_right d₁ d₂)
    Finset.subset_union_right hC₂.le (le_max_right C₁ C₂)
    (RegionAffineAt.mono_mesh rayM H hH (min_le_right m₁ m₂) hZ₂)
  intro T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hR
  rcases hR with hR | hR
  · exact k₁ T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hR
  · exact k₂ T θ w σ v t height hw hwm hσlo hσhi hh hv M hMlo hMhi Φ hΦ hΦpos p X₁ X₂ hX₁ hX₂ hR

/-- Finite unions of estimates are estimates (monotone shape iteration). -/
theorem isEstimate_biUnion {ι : Type*} (s : Finset ι) (R : ι → EnergyRegion)
    (h : ∀ i ∈ s, IsEstimate (R i)) : IsEstimate (⋃ i ∈ s, R i) := by
  induction s using Finset.induction_on with
  | empty => simpa using isEstimate_empty
  | @insert j s hj ih =>
    rw [Finset.set_biUnion_insert]
    exact (h j (Finset.mem_insert_self j s)).union (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Estimates form a lattice: join = union, meet = intersection, bottom = `∅`. -/
instance : Lattice {R : EnergyRegion // IsEstimate R} :=
  Subtype.lattice (fun _ _ h₁ h₂ => h₁.union h₂) (fun _ _ h₁ _ => h₁.mono Set.inter_subset_left)

instance : OrderBot {R : EnergyRegion // IsEstimate R} where
  bot := ⟨∅, isEstimate_empty⟩
  bot_le R := Set.empty_subset R.1

/-- The **Arvi Zone**: the union of all energy region estimates. -/
def arviZone : EnergyRegion := ⋃₀ {R | IsEstimate R}

theorem subset_arviZone {R : EnergyRegion} (h : IsEstimate R) : R ⊆ arviZone :=
  Set.subset_sUnion_of_mem h

/-- The Arvi Zone is the least upper bound of all estimates. -/
theorem arviZone_isLUB : IsLUB {R : EnergyRegion | IsEstimate R} arviZone :=
  ⟨fun _ h => subset_arviZone h, fun _ hU => Set.sUnion_subset fun _ h => hU h⟩

/-- Pointwise description: a configuration is in the Arvi Zone iff the one-point region is an estimate. -/
theorem mem_arviZone_iff (x : Config) : x ∈ arviZone ↔ IsEstimate {x} := by
  constructor
  · rintro ⟨R, hR, hx⟩
    exact hR.mono (Set.singleton_subset_iff.mpr hx)
  · intro h
    exact ⟨{x}, h, rfl⟩

/-- Every finite part of the Arvi Zone is an estimate. -/
theorem isEstimate_of_finite {s : Set Config} (hs : s.Finite) (h : s ⊆ arviZone) : IsEstimate s := by
  have : s = ⋃ x ∈ hs.toFinset, ({x} : Set Config) := by
    ext y; simp
  rw [this]
  exact isEstimate_biUnion _ _ fun x hx => (mem_arviZone_iff x).mp (h (hs.mem_toFinset.mp hx))

/-- Any family of estimates (e.g. a continuum of faces) lies in the Arvi Zone. -/
theorem iUnion_subset_arviZone {ι : Sort*} (R : ι → EnergyRegion) (h : ∀ i, IsEstimate (R i)) :
    (⋃ i, R i) ⊆ arviZone :=
  Set.iUnion_subset fun i => subset_arviZone (h i)

end
end QRH.ArviEnergyRegion

#print axioms QRH.ArviEnergyRegion.IsEstimate.union
#print axioms QRH.ArviEnergyRegion.arviZone_isLUB
#print axioms QRH.ArviEnergyRegion.mem_arviZone_iff
#print axioms QRH.ArviEnergyRegion.isEstimate_globalFace_iff
