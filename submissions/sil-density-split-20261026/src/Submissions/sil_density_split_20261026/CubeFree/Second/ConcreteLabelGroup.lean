/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M: the GROUPED bound of the second nonfixed label blocks (grouped OAI
`actual_block_from_squarefree_source`).

Children are pairs (label `ℓ`, squarefree second Möbius divisor `t₂`), for each pair of ray
characters `(χ, ξ)`; label weights `wt_ℓ` enter as `√wt_ℓ` in both coefficient vectors
(`childMatrix_smul`), and ONE `grouped_child_bound_dep` is applied per `(χ, ξ)`. The window
energies come from height-uniform bounds on the weighted sums (over label and `t₂`) of the
masked one-sided SOURCE energies (`summed_restricted_window_dep_from_height`,
`masked_height_energy`). -/
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteLabel
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell

set_option autoImplicit false
namespace QRH.SilDensitySplit.CubeFree.Second.Concrete
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI OAI.SevenEighths
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentSecondNonexceptional CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondMaskedWindow CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors CenteredMomentSecondWindowSource
open CenteredMomentSupportedCorrelation CenteredMomentFixedRay CenteredMomentHeckeWindowEnergy
open CenteredMomentSecondIdealBlockBound
local notation "O" => ActualEisensteinCubic.O

/-! ### Scalars -/

theorem childMatrix_smul {α β : Type*} (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (R : ℝ) (rows : Finset O)
    (S : Finset α) (T : Finset β) (a : α → O) (b : β → O) (c : α → ℂ) (d : β → ℂ)
    (u : α → ℝ) (v : β → ℝ) (ρ x : O → ℝ) (η : O → ℂ) (s : ℝ) :
    childMatrix W V R rows S T a b (fun i => (s:ℂ) * c i) (fun j => (s:ℂ) * d j) u v ρ x η =
      ((s^2 : ℝ) : ℂ) * childMatrix W V R rows S T a b c d u v ρ x η := by
  unfold childMatrix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro z _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

theorem moebius_ray_norm_le (P : Finset (Ideal O)) (pc : RayCharacter → RayCharacter → ℂ)
    (hpc : ∀ χ ξ, ‖pc χ ξ‖ ≤ 256) (F : Ideal O → RayCharacter → RayCharacter → ℂ) :
    ‖∑ L ∈ P, (UniqueFactorizationMonoid.moebius L : ℂ) *
        ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pc χ ξ * F L χ ξ‖ ≤
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, ∑ L ∈ P.filter Squarefree, 256 * ‖F L χ ξ‖ := by
  have hterm : ∀ L ∈ P, ‖(UniqueFactorizationMonoid.moebius L : ℂ) *
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pc χ ξ * F L χ ξ‖ ≤
      if Squarefree L then ∑ χ : RayCharacter, ∑ ξ : RayCharacter, 256 * ‖F L χ ξ‖ else 0 := by
    intro L _
    by_cases hs : Squarefree L
    · rw [if_pos hs, norm_mul]
      have hμ := QuadraticInitialBound.norm_ideal_moebius_le_one L
      have hin : ‖∑ χ : RayCharacter, ∑ ξ : RayCharacter, pc χ ξ * F L χ ξ‖ ≤
          ∑ χ : RayCharacter, ∑ ξ : RayCharacter, 256 * ‖F L χ ξ‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ξ _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hpc χ ξ) (norm_nonneg _)
      calc _ ≤ 1 * ∑ χ : RayCharacter, ∑ ξ : RayCharacter, 256 * ‖F L χ ξ‖ :=
            mul_le_mul hμ hin (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    · rw [if_neg hs]
      have h0 : (UniqueFactorizationMonoid.moebius L : ℂ) = 0 := by
        by_contra hne
        exact hs (CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero L hne)
      rw [h0, zero_mul, norm_zero]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans (le_of_eq ?_))
  rw [← Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro χ _
  rw [Finset.sum_comm]

theorem pairCoeff_le (D E : O) (χ ξ : RayCharacter) :
    ‖pairCoeff (phaseTable D E) χ ξ‖ ≤ 256 := by
  have h := phaseTable_mass D E
  have h1 : ‖pairCoeff (phaseTable D E) χ ξ‖ ≤ ∑ ξ' : RayCharacter, ‖pairCoeff (phaseTable D E) χ ξ'‖ :=
    Finset.single_le_sum (f := fun ξ' => ‖pairCoeff (phaseTable D E) χ ξ'‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ ξ)
  have h2 : (∑ ξ' : RayCharacter, ‖pairCoeff (phaseTable D E) χ ξ'‖) ≤
      ∑ χ' : RayCharacter, ∑ ξ' : RayCharacter, ‖pairCoeff (phaseTable D E) χ' ξ'‖ :=
    Finset.single_le_sum (f := fun χ' => ∑ ξ' : RayCharacter, ‖pairCoeff (phaseTable D E) χ' ξ'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ χ)
  linarith

/-- The weighted masked HEIGHT energy is the weighted masked source energy. -/
theorem masked_height_energy (η τ : Character) (χ : RayCharacter) (A : O)
    (C : Ideal O) (hC : Supported C)
    (hτ : ∀I:Ideal O,Supported I → IsCoprime C I → ∀t:ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (L : Ideal O) (v s : ℝ)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (H : ℝ) :
    restrictedEnergy keep Finset.univ (sectorElement C hC.1 S)
      (fun i => ((s:ℂ) * (if L ∣ (i:Ideal O) then β (C*i) else 0)) *
        heightCoeff τ v (Ideal.span {sectorElement C hC.1 S i})) Φ H =
    s^2 * sourceRestrictedEnergy keep (residualPool C hC.1 S)
      (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0) (heightCoeff τ v) Φ H := by
  have hf : (fun i : sectorPool C hC.1 S => ((s:ℂ) * (if L ∣ (i:Ideal O) then β (C*i) else 0)) *
      heightCoeff τ v (Ideal.span {sectorElement C hC.1 S i})) =
      (fun i => (s:ℂ) * divisorCoefficient L (sectorElement C hC.1 S)
        (movingCoefficient A (sectorElement C hC.1 S)
          (fun J:sectorPool C hC.1 S=>β (C*J)*heightCoeff η v J)) χ i) := by
    funext i
    rw [masked_divisor_coefficient η τ χ A C hC hτ S β L v i, sectorElement_span]
    ring
  rw [hf, restrictedEnergy_smul, masked_child_energy η τ χ A C hC hτ S β L v keep Φ H,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ### Labels of one dyadic class -/

/-- One nonfixed second label of a dyadic class. -/
structure BlockLabel (η : Character) (χ₀ : RayCharacter) (Q : Ideal O) (m : O)
    (S : Finset (Ideal O)) where
  C : Ideal O
  D : Ideal O
  hC : Supported C
  hD : Supported D
  hCD : CompletedGauss.primeSupport C = CompletedGauss.primeSupport D
  U : Finset (CommonIndex C D)
  R : ℝ
  rows : Finset O
  ρ : O → ℝ
  x : O → ℝ
  τ : RayCharacter → Character
  hτ : ∀χ:RayCharacter,∀I:Ideal O,Supported I → (IsCoprime C I ∨ IsCoprime D I) → ∀v:ℝ,
    heightCoeff (τ χ) v I=heightCoeff η v I*
      idealRowHom (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) I*
        rayCharacter χ (primaryGenerator I)
  hrows : ∀ z ∈ rows,
    nonexceptional η χ₀ Q m (commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U) z

namespace BlockLabel
variable {η : Character} {χ₀ : RayCharacter} {Q : Ideal O} {m : O} {S : Finset (Ideal O)}

def A (ℓ : BlockLabel η χ₀ Q m S) : O :=
  commonFrequencyGenerator ℓ.C ℓ.D * nonunitFrequencyGenerator ℓ.C ℓ.D ℓ.U

/-- The squarefree second Möbius divisors of the label. -/
def pool (ℓ : BlockLabel η χ₀ Q m S) : Finset (Ideal O) :=
  (divisorPool Finset.univ (fun j : sectorPool ℓ.D ℓ.hD.1 S =>
    Ideal.span {sectorElement ℓ.D ℓ.hD.1 S j})).filter Squarefree

end BlockLabel

/-- **The grouped label-block bound.** -/
theorem grouped_label_blocks (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ r : ℝ, 0 < r →
    ∀ (η : Character) (t : ℝ) (S : Finset (Ideal O)) (β : Ideal O → ℂ)
      (χ₀ : RayCharacter) (Q : Ideal O) (m : O),
      Q ≤ Ideal.span {(72:O)} → ConcretePrimeRowBridge.goodLambda ∣ m → (2:O) ∣ m →
    ∀ (X Y : ℝ), 0 < X → 0 < Y →
    ∀ (Φ : 𝓢(ℝ,ℂ)) (H : ℝ), 0 < H →
      (∀ z : O, 0 ≤ (Φ (‖eisEmbedding z‖^2/H)).re) →
    ∀ {Λ : Type*} (Ls : Finset Λ) (ℓ : Λ → BlockLabel η χ₀ Q m S) (wt : Λ → ℝ),
      (∀ l, 0 ≤ wt l) →
      (∀ l ∈ Ls, ∀ z ∈ (ℓ l).rows, 1 ≤ (Φ (‖eisEmbedding z‖^2/H)).re) →
    ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → 0 ≤ E₂ →
    (∀ (χ : RayCharacter) (v : ℝ),
      (∑ k ∈ Ls.sigma (fun l => (ℓ l).pool), wt k.1 *
        sourceRestrictedEnergy (nonexceptional η χ Q m (ℓ k.1).A)
          (residualPool (ℓ k.1).C (ℓ k.1).hC.1 S)
          (fun I => if IsCoprime (ℓ k.1).C I ∧ k.2 ∣ I then β ((ℓ k.1).C*I) else 0)
          (heightCoeff ((ℓ k.1).τ χ) v) Φ H) ≤ E₁ * (1+‖v‖)^(2*J₁)) →
    (∀ (χ : RayCharacter) (v : ℝ),
      (∑ k ∈ Ls.sigma (fun l => (ℓ l).pool), wt k.1 *
        sourceRestrictedEnergy (nonexceptional η χ Q m (ℓ k.1).A)
          (residualPool (ℓ k.1).D (ℓ k.1).hD.1 S)
          (fun I => if IsCoprime (ℓ k.1).D I ∧ k.2 ∣ I then β ((ℓ k.1).D*I) else 0)
          (heightCoeff ((ℓ k.1).τ χ) v) Φ H) ≤ E₂ * (1+‖v‖)^(2*J₂)) →
    (1+r)^decay * ∑ l ∈ Ls, wt l *
      ‖labelBlock η t S β (ℓ l).C (ℓ l).D (ℓ l).hC (ℓ l).hD (ℓ l).U (ℓ l).R (ℓ l).rows W r
        (ℓ l).ρ (ℓ l).x X Y‖ ≤
      Cg * (windowBudget J₁ t E₁ * windowBudget J₂ t E₂) := by
  obtain ⟨Ck, hCk, hk⟩ := grouped_child_bound_dep W (fun _ => logAnnulus) (fun _ => Real.log 4)
    (fun _ => Real.log_nonneg (by norm_num)) (fun _ x hx => logAnnulus_enclosure x hx) decay J₁ J₂
  let NR : ℝ := (Fintype.card RayCharacter : ℝ)
  refine ⟨256 * (NR * NR) * Ck, by positivity, ?_⟩
  intro r hr η t S β χ₀ Q m hQ hmLam hm2 X Y hX hY Φ H hH hΦ Λ Ls ℓ wt hwt hmajor E₁ E₂ hE₁ hE₂
    hleft hright
  let Ks := Ls.sigma (fun l => (ℓ l).pool)
  let sq : (Σ _ : Λ, Ideal O) → ℝ := fun k => Real.sqrt (wt k.1)
  have hsq (k : Σ _ : Λ, Ideal O) : (sq k)^2 = wt k.1 := Real.sq_sqrt (hwt k.1)
  -- the child of (label, t₂) at (χ, ξ), weighted
  let child : RayCharacter → RayCharacter → (Σ _ : Λ, Ideal O) → ℂ := fun χ ξ k =>
    labelChild η t S β (ℓ k.1).C (ℓ k.1).D (ℓ k.1).hC (ℓ k.1).hD (ℓ k.1).U (ℓ k.1).R
      (ℓ k.1).rows W r (ℓ k.1).ρ (ℓ k.1).x X Y k.2 χ ξ
  -- Step 1: one label
  have hstep1 : ∀ l ∈ Ls, wt l *
      ‖labelBlock η t S β (ℓ l).C (ℓ l).D (ℓ l).hC (ℓ l).hD (ℓ l).U (ℓ l).R (ℓ l).rows W r
        (ℓ l).ρ (ℓ l).x X Y‖ ≤
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, ∑ L ∈ (ℓ l).pool, 256 * (wt l * ‖child χ ξ ⟨l, L⟩‖) := by
    intro l _
    rw [labelBlock_eq η t S β (ℓ l).C (ℓ l).D (ℓ l).hC (ℓ l).hD (ℓ l).hCD]
    refine (mul_le_mul_of_nonneg_left (moebius_ray_norm_le _ _ (pairCoeff_le _ _) _)
      (hwt l)).trans (le_of_eq ?_)
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro χ _
    apply Finset.sum_congr rfl; intro ξ _
    apply Finset.sum_congr rfl; intro L _
    ring
  -- Step 2: one (χ, ξ), all children
  have hstep2 : ∀ χ ξ : RayCharacter,
      (1+r)^decay * ∑ k ∈ Ks, wt k.1 * ‖child χ ξ k‖ ≤
        Ck * (windowBudget J₁ t E₁ * windowBudget J₂ t E₂) := by
    intro χ ξ
    have hw : ∀ k ∈ Ks, wt k.1 * ‖child χ ξ k‖ =
        ‖childMatrix W (fun _ => logAnnulus) r (ℓ k.1).rows Finset.univ Finset.univ
          (sectorElement (ℓ k.1).C (ℓ k.1).hC.1 S) (sectorElement (ℓ k.1).D (ℓ k.1).hD.1 S)
          (fun i => (sq k : ℂ) * divisorCoefficient k.2 (sectorElement (ℓ k.1).C (ℓ k.1).hC.1 S)
            (movingCoefficient (ℓ k.1).A (sectorElement (ℓ k.1).C (ℓ k.1).hC.1 S)
              (fun I => β ((ℓ k.1).C*I) * heightCoeff η t I)) χ i)
          (fun j => (sq k : ℂ) * divisorCoefficient k.2 (sectorElement (ℓ k.1).D (ℓ k.1).hD.1 S)
            (movingCoefficient (ℓ k.1).A (sectorElement (ℓ k.1).D (ℓ k.1).hD.1 S)
              (fun J => β ((ℓ k.1).D*J) * heightCoeff η t J)) (ξ⁻¹) j)
          (fun I => Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X))
          (fun J => Real.log ((Ideal.absNorm (J:Ideal O):ℝ)/Y)) (ℓ k.1).ρ (ℓ k.1).x
          (fun z => retainedScalar (ℓ k.1).C (ℓ k.1).D (ℓ k.1).U (ℓ k.1).R z *
            actualCorrelation (primaryGenerator (ℓ k.1).C) (primaryGenerator (ℓ k.1).D)
              ((supported_span_primaryGenerator_iff _).mpr (ℓ k.1).hC)
              ((supported_span_primaryGenerator_iff _).mpr (ℓ k.1).hD) ((ℓ k.1).A * z))‖ := by
      intro k _
      rw [childMatrix_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _), hsq]
      rfl
    rw [Finset.sum_congr rfl hw]
    refine hk r hr Ks (fun k => (ℓ k.1).rows) (fun _ => Finset.univ) (fun _ => Finset.univ)
      (fun k => sectorElement (ℓ k.1).C (ℓ k.1).hC.1 S) (fun k => sectorElement (ℓ k.1).D (ℓ k.1).hD.1 S)
      (fun k => sectorElement_supported (ℓ k.1).C (ℓ k.1).hC.1 S)
      (fun k => sectorElement_supported (ℓ k.1).D (ℓ k.1).hD.1 S) _ _ _ _ _ _ _
      (fun k z => nonexceptional η χ Q m (ℓ k.1).A z)
      (fun k z => nonexceptional η (ξ⁻¹) Q m (ℓ k.1).A z)
      (fun k _ z hz => (nonexceptional_ray_independent η χ₀ χ Q hQ m (ℓ k.1).A z hmLam hm2).mp
        ((ℓ k.1).hrows z hz))
      (fun k _ z hz => (nonexceptional_reflection η χ₀ (ξ⁻¹) Q hQ m (ℓ k.1).A z hmLam hm2).mp
        ((ℓ k.1).hrows z hz))
      (fun k _ z _ => actual_retained_scalar_norm (ℓ k.1).C (ℓ k.1).D (ℓ k.1).hC (ℓ k.1).hD
        (ℓ k.1).hCD (ℓ k.1).U (ℓ k.1).R z)
      (fun k _ z _ => logAnnulus_norm _) (fun k _ z _ => logAnnulus_norm _)
      Φ H hH hΦ (fun k hk' z hz => hmajor k.1 (Finset.mem_sigma.mp hk').1 z hz)
      (windowBudget J₁ t E₁) (windowBudget J₂ t E₂) (windowBudget_nonneg _ _ _)
      (windowBudget_nonneg _ _ _) ?_ ?_
    · intro θ
      have hwin := summed_restricted_window_dep_from_height logAnnulus logAnnulus_compact
        logAnnulus_smooth J₁ Ks (fun k z => nonexceptional η χ Q m (ℓ k.1).A z)
        (fun _ => Finset.univ) (fun k => sectorElement (ℓ k.1).C (ℓ k.1).hC.1 S)
        (fun k => sectorElement_supported (ℓ k.1).C (ℓ k.1).hC.1 S)
        (fun k i => (sq k : ℂ) * (if k.2 ∣ (i:Ideal O) then β ((ℓ k.1).C*i) else 0))
        (fun k => (ℓ k.1).τ χ) t θ (fun _ => X) (fun _ => hX) Φ H hH hΦ E₁ hE₁ (by
          intro v
          refine le_trans (le_of_eq ?_) (hleft χ v)
          apply Finset.sum_congr rfl
          intro k _
          rw [masked_height_energy η ((ℓ k.1).τ χ) χ (ℓ k.1).A (ℓ k.1).C (ℓ k.1).hC
            (fun I hI hc v' => (ℓ k.1).hτ χ I hI (Or.inl hc) v') S β k.2 v (sq k), hsq])
      refine le_trans (le_of_eq ?_) (hwin.trans (shifted_window_budget J₁ t θ E₁ hE₁))
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      funext i
      rw [masked_divisor_coefficient η ((ℓ k.1).τ χ) χ (ℓ k.1).A (ℓ k.1).C (ℓ k.1).hC
        (fun I hI hc v' => (ℓ k.1).hτ χ I hI (Or.inl hc) v') S β k.2 t i, sectorElement_span]
      ring
    · intro θ
      have hwin := summed_restricted_window_dep_from_height logAnnulus logAnnulus_compact
        logAnnulus_smooth J₂ Ks (fun k z => nonexceptional η (ξ⁻¹) Q m (ℓ k.1).A z)
        (fun _ => Finset.univ) (fun k => sectorElement (ℓ k.1).D (ℓ k.1).hD.1 S)
        (fun k => sectorElement_supported (ℓ k.1).D (ℓ k.1).hD.1 S)
        (fun k i => (sq k : ℂ) * (if k.2 ∣ (i:Ideal O) then β ((ℓ k.1).D*i) else 0))
        (fun k => (ℓ k.1).τ (ξ⁻¹)) t (-θ) (fun _ => Y) (fun _ => hY) Φ H hH hΦ E₂ hE₂ (by
          intro v
          refine le_trans (le_of_eq ?_) (hright (ξ⁻¹) v)
          apply Finset.sum_congr rfl
          intro k _
          rw [masked_height_energy η ((ℓ k.1).τ (ξ⁻¹)) (ξ⁻¹) (ℓ k.1).A (ℓ k.1).D (ℓ k.1).hD
            (fun I hI hc v' => (ℓ k.1).hτ (ξ⁻¹) I hI (Or.inr hc) v') S β k.2 v (sq k), hsq])
      refine le_trans (le_of_eq ?_) (hwin.trans (conjugate_shifted_window_budget J₂ t θ E₂ hE₂))
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      funext j
      rw [star_logAnnulus_column, masked_divisor_coefficient η ((ℓ k.1).τ (ξ⁻¹)) (ξ⁻¹) (ℓ k.1).A
        (ℓ k.1).D (ℓ k.1).hD (fun I hI hc v' => (ℓ k.1).hτ (ξ⁻¹) I hI (Or.inr hc) v') S β k.2 t j,
        sectorElement_span]
      ring
  -- Step 3: assemble
  have hsum : ∑ l ∈ Ls, wt l *
      ‖labelBlock η t S β (ℓ l).C (ℓ l).D (ℓ l).hC (ℓ l).hD (ℓ l).U (ℓ l).R (ℓ l).rows W r
        (ℓ l).ρ (ℓ l).x X Y‖ ≤
      ∑ χ : RayCharacter, ∑ ξ : RayCharacter, 256 * ∑ k ∈ Ks, wt k.1 * ‖child χ ξ k‖ := by
    refine (Finset.sum_le_sum hstep1).trans (le_of_eq ?_)
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro χ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro ξ _
    rw [Finset.mul_sum, Finset.sum_sigma]
  have hr0 : 0 ≤ (1+r)^decay := by positivity
  calc (1+r)^decay * ∑ l ∈ Ls, wt l * _ ≤
        (1+r)^decay * ∑ χ : RayCharacter, ∑ ξ : RayCharacter, 256 * ∑ k ∈ Ks, wt k.1 * ‖child χ ξ k‖ :=
        mul_le_mul_of_nonneg_left hsum hr0
    _ = ∑ χ : RayCharacter, ∑ ξ : RayCharacter, 256 * ((1+r)^decay * ∑ k ∈ Ks, wt k.1 * ‖child χ ξ k‖) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro χ _
        apply Finset.sum_congr rfl; intro ξ _
        ring
    _ ≤ ∑ χ : RayCharacter, ∑ ξ : RayCharacter,
          256 * (Ck * (windowBudget J₁ t E₁ * windowBudget J₂ t E₂)) :=
        Finset.sum_le_sum fun χ _ => Finset.sum_le_sum fun ξ _ =>
          mul_le_mul_of_nonneg_left (hstep2 χ ξ) (by norm_num)
    _ = 256 * (NR * NR) * Ck * (windowBudget J₁ t E₁ * windowBudget J₂ t E₂) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, NR]
        ring

end
end QRH.SilDensitySplit.CubeFree.Second.Concrete
