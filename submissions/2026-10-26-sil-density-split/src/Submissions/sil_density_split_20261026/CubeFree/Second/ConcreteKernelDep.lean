/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M: the grouped second-step kernel estimate with CHILD-DEPENDENT columns.

The children of the second step are pairs (second label, Möbius divisor `t₂`); the columns of
a label are its own sector pool `sectorPool C hC S` (a type depending on `C`), with their own
log-variables `log(N I / X)` (window centre `X` depending on the dyadic block). This file is
the dependent form of `ConcreteKernel`:

* `summed_restricted_window_dep_from_height`: joint window energy from height energies, with
  per-child columns, elements, coefficients, characters, keep predicates and centres.
* `grouped_child_bound_dep`: ONE `whole_kernel_row_estimate` with column type
  `Σ k, α k` (the disjoint union of the children's columns, coefficients extended by zero)
  and row type `Σ k, O`. Only the kernel ratio `R` and the profiles `W, V` are common. -/
import Submissions.sil_density_split_20261026.CubeFree.Second.ConcreteKernel

set_option autoImplicit false
namespace QRH.SilDensitySplit.CubeFree.Second.Concrete
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open OAI OAI.SevenEighths
open CanonicalQuadraticSieve CanonicalRowCompletion CenteredMomentRowNorm
open CenteredMomentRestrictedEnergy CenteredMomentRestrictedWindow CenteredMomentPlainWindowEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy CenteredMomentPlainChildEnergy
open CenteredMomentCauchy CenteredMomentSmooth CenteredMomentSecondWindowBudget
open HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

/-! ### Joint window energy with dependent columns -/

theorem summed_restricted_window_dep_from_shifted {κ : Type*} {α : κ → Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (Ks : Finset κ) (keep : κ → O → Prop) (S : ∀ k, Finset (α k)) (a : ∀ k, α k → O)
    (ha : ∀ k i, Supported (Ideal.span {a k i}))
    (β : ∀ k, α k → ℂ) (τ : κ → Character) (t θ : ℝ) (X : κ → ℝ) (hX : ∀ k, 0 < X k)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K)
    (hU : ∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (E : ℝ) (hE : 0 ≤ E)
    (henergy : ∀ w : ℝ, (∑ k ∈ Ks, restrictedEnergy (keep k) (S k) (a k)
      (fun i => β k i*heightCoeff (τ k) (t+2*Real.pi*(w-θ)) (Ideal.span {a k i})) U K) ≤
        E*(1+‖w‖)^(2*J)) :
    (∑ k ∈ Ks, restrictedEnergy (keep k) (S k) (a k)
      (fun i => β k i*heightCoeff (τ k) t (Ideal.span {a k i})*
        columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a k i}):ℝ)/X k)) θ) U K) ≤
      E*(∫ w : ℝ, (1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  let u := fun (k : κ) (z : O) => if keep k z then (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0
  have hu (k : κ) (z : O) : 0 ≤ u k z := by
    dsimp only [u]; split_ifs
    · exact hU z
    · exact le_rfl
  let c := fun (k : κ) (i : α k) => β k i*heightCoeff (τ k) t (Ideal.span {a k i})*
    columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a k i}):ℝ)/X k)) θ
  have hnorm (k : κ) (z : O) (x : ℂ) : ‖(Real.sqrt (u k z):ℂ)*x‖^2 = u k z*‖x‖^2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (hu k z)]
  have hfin (rows : Finset O) :
      (∑ z ∈ rows, ∑ k ∈ Ks, ‖rowPolynomial (S k) (a k) (c k) z‖^2*u k z) ≤
        E*(∫ w : ℝ, (1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
    let φ := fun p : Ks × rows => fun w : ℝ => (Real.sqrt (u p.1 p.2):ℂ)*
      (logPhase (θ-w) (Real.log (X p.1))*rowPolynomial (S p.1) (a p.1)
        (fun i => β p.1 i*heightCoeff (τ p.1) (t+2*Real.pi*(w-θ)) (Ideal.span {a p.1 i})) p.2)
    have hi (p : Ks × rows) : Integrable (fun w => columnDensity V hVc hVs w*φ p w) := by
      have h := (plain_column_integrable (S p.1) (a p.1) (ha p.1) (β p.1) (τ p.1) t θ (X p.1)
        (hX p.1) V hVc hVs p.2).const_mul (Real.sqrt (u p.1 p.2):ℂ)
      convert h using 1
      funext w
      dsimp only [φ]
      ring
    have hb (w : ℝ) : (∑ p : Ks × rows, ‖φ p w‖^2) ≤ E*((1+‖w‖)^J)^2 := by
      let g := fun (k : κ) (z : O) => ‖rowPolynomial (S k) (a k)
        (fun i => β k i*heightCoeff (τ k) (t+2*Real.pi*(w-θ)) (Ideal.span {a k i})) z‖^2*
          (if keep k z then (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0)
      have hφ (p : Ks × rows) : ‖φ p w‖^2 = g p.1 p.2 := by
        dsimp only [φ, g]
        rw [hnorm, norm_mul, logPhase_norm]
        ring
      calc
        (∑ p : Ks × rows, ‖φ p w‖^2) = ∑ p : Ks × rows, g p.1 p.2 :=
          Finset.sum_congr rfl (fun p _ => hφ p)
        _ = ∑ k ∈ Ks, ∑ z ∈ rows, g k z := by
          rw [Fintype.sum_prod_type, ← Finset.sum_coe_sort Ks]
          exact Finset.sum_congr rfl (fun k _ => Finset.sum_coe_sort rows (g k))
        _ ≤ ∑ k ∈ Ks, restrictedEnergy (keep k) (S k) (a k)
            (fun i => β k i*heightCoeff (τ k) (t+2*Real.pi*(w-θ)) (Ideal.span {a k i})) U K :=
          Finset.sum_le_sum (fun k _ =>
            finite_weighted_le_restricted (keep k) (S k) (a k) (ha k) _ U K hK hU rows)
        _ ≤ E*(1+‖w‖)^(2*J) := henergy w
        _ = E*((1+‖w‖)^J)^2 := by rw [← pow_mul, Nat.mul_comm]
    have hh := finite_weighted_integral_energy (columnDensity V hVc hVs) φ
      (fun w => (1+‖w‖)^J) (by intro w; positivity) E hE (columnDensity_moments V hVc hVs J) hi hb
    have he (p : Ks × rows) : (∫ w : ℝ, columnDensity V hVc hVs w*φ p w) =
        (Real.sqrt (u p.1 p.2):ℂ)*rowPolynomial (S p.1) (a p.1) (c p.1) p.2 := by
      rw [show rowPolynomial (S p.1) (a p.1) (c p.1) p.2 = _ from
        plain_column_integral (S p.1) (a p.1) (ha p.1) (β p.1) (τ p.1) t θ (X p.1) (hX p.1)
          V hVc hVs p.2, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with w
      dsimp only [φ]
      ring
    calc
      (∑ z ∈ rows, ∑ k ∈ Ks, ‖rowPolynomial (S k) (a k) (c k) z‖^2*u k z) =
          ∑ k ∈ Ks, ∑ z ∈ rows, ‖rowPolynomial (S k) (a k) (c k) z‖^2*u k z := Finset.sum_comm
      _ = ∑ p : Ks × rows, ‖rowPolynomial (S p.1) (a p.1) (c p.1) p.2‖^2*u p.1 p.2 := by
          rw [Fintype.sum_prod_type, ← Finset.sum_coe_sort Ks]
          exact Finset.sum_congr rfl (fun k _ =>
            (Finset.sum_coe_sort rows (fun z => ‖rowPolynomial (S k) (a k) (c k) z‖^2*u k z)).symm)
      _ = ∑ p : Ks × rows, ‖∫ w : ℝ, columnDensity V hVc hVs w*φ p w‖^2 :=
        Finset.sum_congr rfl (fun p _ => by rw [he p, hnorm]; ring)
      _ ≤ _ := hh
  have hs : HasSum (fun z : O => ∑ k ∈ Ks, ‖rowPolynomial (S k) (a k) (c k) z‖^2*u k z)
      (∑ k ∈ Ks, restrictedEnergy (keep k) (S k) (a k) (c k) U K) :=
    hasSum_sum (fun k _ => restricted_hasSum_weighted (keep k) (S k) (a k) (ha k) (c k) U K hK)
  rw [← hs.tsum_eq]
  exact Real.tsum_le_of_sum_le
    (fun z => Finset.sum_nonneg (fun k _ => mul_nonneg (sq_nonneg _) (hu k z))) hfin

theorem summed_restricted_window_dep_from_height {κ : Type*} {α : κ → Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (Ks : Finset κ) (keep : κ → O → Prop) (S : ∀ k, Finset (α k)) (a : ∀ k, α k → O)
    (ha : ∀ k i, Supported (Ideal.span {a k i}))
    (β : ∀ k, α k → ℂ) (τ : κ → Character) (t θ : ℝ) (X : κ → ℝ) (hX : ∀ k, 0 < X k)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K)
    (hU : ∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (E : ℝ) (hE : 0 ≤ E)
    (henergy : ∀ v : ℝ, (∑ k ∈ Ks, restrictedEnergy (keep k) (S k) (a k)
      (fun i => β k i*heightCoeff (τ k) v (Ideal.span {a k i})) U K) ≤ E*(1+‖v‖)^(2*J)) :
    (∑ k ∈ Ks, restrictedEnergy (keep k) (S k) (a k)
      (fun i => β k i*heightCoeff (τ k) t (Ideal.span {a k i})*
        columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a k i}):ℝ)/X k)) θ) U K) ≤
      (E*heightCost t θ^(2*J))*(∫ w : ℝ, (1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  apply summed_restricted_window_dep_from_shifted V hVc hVs J Ks keep S a ha β τ t θ X hX U K hK hU
    (E*heightCost t θ^(2*J)) (mul_nonneg hE (pow_nonneg (heightCost_pos t θ).le _))
  intro w
  calc
    _ ≤ E*(1+‖t+2*Real.pi*(w-θ)‖)^(2*J) := henergy _
    _ ≤ E*(heightCost t θ*(1+‖w‖))^(2*J) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (norm_height_shift t θ w) _) hE
    _ = _ := by rw [mul_pow, mul_assoc]

/-! ### Indicator sums over a sigma finset -/

theorem sigma_indicator_sum {κ : Type*} {α : κ → Type*} (Ks : Finset κ) (S : ∀ k, Finset (α k))
    (f : ∀ k, α k → ℂ) (k : κ) (hk : k ∈ Ks) :
    (∑ i ∈ Ks.sigma S, if i.1 = k then f i.1 i.2 else 0) = ∑ i ∈ S k, f k i := by
  rw [Finset.sum_sigma]
  have h : ∀ k' ∈ Ks, (∑ i ∈ S k', if k' = k then f k' i else 0) =
      if k' = k then ∑ i ∈ S k', f k' i else 0 := by
    intro k' _
    by_cases hkk : k' = k
    · simp only [hkk, ite_true]
    · simp only [hkk, if_false, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq' Ks k (fun k' => ∑ i ∈ S k', f k' i), if_pos hk]

/-! ### The grouped child bound with dependent columns -/

theorem grouped_child_bound_dep (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {κ : Type*} {α β : κ → Type*} (Ks : Finset κ) (rows : κ → Finset O)
        (S : ∀ k, Finset (α k)) (T : ∀ k, Finset (β k))
        (a : ∀ k, α k → O) (b : ∀ k, β k → O)
        (_ha : ∀ k i, Supported (Ideal.span {a k i}))
        (_hb : ∀ k j, Supported (Ideal.span {b k j}))
        (c : ∀ k, α k → ℂ) (d : ∀ k, β k → ℂ) (u : ∀ k, α k → ℝ) (v : ∀ k, β k → ℝ)
        (ρ x : κ → O → ℝ) (η : κ → O → ℂ) (keep₁ keep₂ : κ → O → Prop),
      (∀ k ∈ Ks, ∀ z ∈ rows k, keep₁ k z) → (∀ k ∈ Ks, ∀ z ∈ rows k, keep₂ k (-z)) →
      (∀ k ∈ Ks, ∀ z ∈ rows k, ‖η k z‖ ≤ 1) →
      (∀ k ∈ Ks, ∀ z ∈ rows k, ‖V 0 (ρ k z)‖ ≤ 1) → (∀ k ∈ Ks, ∀ z ∈ rows k, ‖V 1 (x k z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      (∀ k ∈ Ks, ∀ z ∈ rows k, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → 0 ≤ E₂ →
      (∀ t : ℝ, (∑ k ∈ Ks, restrictedEnergy (keep₁ k) (S k) (a k)
        (fun i => c k i * columnPhase (V 2) (u k i) t) U K) ≤ (E₁ * (1 + ‖t‖) ^ J₁) ^ 2) →
      (∀ t : ℝ, (∑ k ∈ Ks, restrictedEnergy (keep₂ k) (T k) (b k)
        (fun j => d k j * star (columnPhase (V 3) (v k j) t)) U K) ≤ (E₂ * (1 + ‖t‖) ^ J₂) ^ 2) →
      (1 + R) ^ A * ∑ k ∈ Ks,
        ‖childMatrix W V R (rows k) (S k) (T k) (a k) (b k) (c k) (d k) (u k) (v k) (ρ k) (x k)
          (η k)‖ ≤ C * (E₁ * E₂) := by
  obtain ⟨C, hC, hbound⟩ := whole_kernel_row_estimate W V M hM hV A (J₁ + J₂)
  refine ⟨C, hC, ?_⟩
  intro R hR κ α β Ks rows S T a b ha hb c d u v ρ x η keep₁ keep₂ hkeep₁ hkeep₂ hη hV₀ hV₁
    U K hK hU hmajor E₁ E₂ hE₁ hE₂ hleft hright
  let P : Finset (Σ _ : κ, O) := Ks.sigma rows
  let SS : Finset (Σ k, α k) := Ks.sigma S
  let TT : Finset (Σ k, β k) := Ks.sigma T
  let uu : (Σ k, α k) → ℝ := fun i => u i.1 i.2
  let vv : (Σ k, β k) → ℝ := fun j => v j.1 j.2
  let cc : (Σ _ : κ, O) → (Σ k, α k) → ℂ := fun p i =>
    if i.1 = p.1 then c i.1 i.2 * idealRowHom p.2 (Ideal.span {a i.1 i.2}) else 0
  let dd : (Σ _ : κ, O) → (Σ k, β k) → ℂ := fun p j =>
    if j.1 = p.1 then d j.1 j.2 * idealRowHom (-p.2) (Ideal.span {b j.1 j.2}) else 0
  let phs : κ → ℂ := fun k =>
    unitPhase (childMatrix W V R (rows k) (S k) (T k) (a k) (b k) (c k) (d k) (u k) (v k) (ρ k)
      (x k) (η k))
  have hP (p : Σ _ : κ, O) (hp : p ∈ P) : p.1 ∈ Ks ∧ p.2 ∈ rows p.1 := Finset.mem_sigma.mp hp
  -- the joint bilinear form of one row is the child's bilinear form
  have hrow (p : Σ _ : κ, O) (hp : p.1 ∈ Ks) :
      (∑ i ∈ SS, ∑ j ∈ TT, (cc p i * star (dd p j)) *
        wholeKernel W V R (ρ p.1 p.2) (x p.1 p.2) (uu i) (vv j)) =
      ∑ i ∈ S p.1, ∑ j ∈ T p.1, ((c p.1 i * idealRowHom p.2 (Ideal.span {a p.1 i})) *
        star (d p.1 j * idealRowHom (-p.2) (Ideal.span {b p.1 j}))) *
          wholeKernel W V R (ρ p.1 p.2) (x p.1 p.2) (u p.1 i) (v p.1 j) := by
    have hin : ∀ i ∈ SS, (∑ j ∈ TT, (cc p i * star (dd p j)) *
        wholeKernel W V R (ρ p.1 p.2) (x p.1 p.2) (uu i) (vv j)) =
        if i.1 = p.1 then ∑ j ∈ T p.1, ((c i.1 i.2 * idealRowHom p.2 (Ideal.span {a i.1 i.2})) *
          star (d p.1 j * idealRowHom (-p.2) (Ideal.span {b p.1 j}))) *
            wholeKernel W V R (ρ p.1 p.2) (x p.1 p.2) (u i.1 i.2) (v p.1 j) else 0 := by
      intro i _
      by_cases hi : i.1 = p.1
      · rw [if_pos hi]
        have hj := sigma_indicator_sum Ks T (fun k' (j : β k') =>
          ((c i.1 i.2 * idealRowHom p.2 (Ideal.span {a i.1 i.2})) *
            star (d k' j * idealRowHom (-p.2) (Ideal.span {b k' j}))) *
              wholeKernel W V R (ρ p.1 p.2) (x p.1 p.2) (u i.1 i.2) (v k' j)) p.1 hp
        rw [← hj]
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj' : j.1 = p.1
        · simp only [cc, dd, uu, vv, hi, hj', ite_true]
        · simp only [cc, dd, hi, hj', ite_true, ite_false, star_zero, mul_zero, zero_mul]
      · rw [if_neg hi]
        apply Finset.sum_eq_zero
        intro j _
        simp only [cc, hi, if_false, zero_mul]
    rw [Finset.sum_congr rfl hin]
    exact sigma_indicator_sum Ks S (fun k' (i : α k') =>
      ∑ j ∈ T p.1, ((c k' i * idealRowHom p.2 (Ideal.span {a k' i})) *
        star (d p.1 j * idealRowHom (-p.2) (Ideal.span {b p.1 j}))) *
          wholeKernel W V R (ρ p.1 p.2) (x p.1 p.2) (u k' i) (v p.1 j)) p.1 hp
  have hsum : (∑ k ∈ Ks, ‖childMatrix W V R (rows k) (S k) (T k) (a k) (b k) (c k) (d k) (u k)
      (v k) (ρ k) (x k) (η k)‖) =
      ‖∑ p ∈ P, (phs p.1 * η p.1 p.2) *
        (∑ i ∈ SS, ∑ j ∈ TT, (cc p i * star (dd p j)) *
          wholeKernel W V R (ρ p.1 p.2) (x p.1 p.2) (uu i) (vv j))‖ := by
    rw [sum_norm_eq_norm_phase]
    congr 1
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_congr rfl (fun z _ => by rw [hrow ⟨k, z⟩ hk])]
    change phs k * childMatrix W V R (rows k) (S k) (T k) (a k) (b k) (c k) (d k) (u k) (v k)
      (ρ k) (x k) (η k) = _
    unfold childMatrix
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [hsum]
  apply hbound R hR P SS TT cc dd uu vv
    (fun p => ρ p.1 p.2) (fun p => x p.1 p.2) (fun p => phs p.1 * η p.1 p.2)
    (fun p hp => by
      rw [norm_mul, unitPhase_norm, one_mul]; exact hη _ (hP p hp).1 _ (hP p hp).2)
    (fun p hp => hV₀ _ (hP p hp).1 _ (hP p hp).2) (fun p hp => hV₁ _ (hP p hp).1 _ (hP p hp).2)
    (E₁ * E₂) (mul_nonneg hE₁ hE₂)
  intro t
  have hlc (p : Σ _ : κ, O) (hp : p.1 ∈ Ks) :
      leftColumn SS (cc p) (V 2) uu t =
        rowPolynomial (S p.1) (a p.1) (fun i => c p.1 i * columnPhase (V 2) (u p.1 i) t) p.2 := by
    rw [← leftColumn_eq_rowPolynomial]
    unfold leftColumn
    rw [← sigma_indicator_sum Ks S (fun k' (i : α k') =>
      c k' i * idealRowHom p.2 (Ideal.span {a k' i}) * columnPhase (V 2) (u k' i) t) p.1 hp]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.1 = p.1
    · simp only [cc, uu, hi, ite_true]
    · simp only [cc, hi, if_false, zero_mul]
  have hrc (p : Σ _ : κ, O) (hp : p.1 ∈ Ks) :
      rightColumn TT (dd p) (V 3) vv t =
        star (rowPolynomial (T p.1) (b p.1)
          (fun j => d p.1 j * star (columnPhase (V 3) (v p.1 j) t)) (-p.2)) := by
    rw [← rightColumn_eq_star_rowPolynomial]
    unfold rightColumn
    rw [← sigma_indicator_sum Ks T (fun k' (j : β k') =>
      star (d k' j * idealRowHom (-p.2) (Ideal.span {b k' j})) * columnPhase (V 3) (v k' j) t)
      p.1 hp]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.1 = p.1
    · simp only [dd, vv, hj, ite_true]
    · simp only [dd, hj, if_false, star_zero, zero_mul]
  have hL : (∑ p ∈ P, ‖leftColumn SS (cc p) (V 2) uu t‖ ^ 2) ≤ (E₁ * (1 + ‖t‖) ^ J₁) ^ 2 := by
    rw [Finset.sum_sigma]
    refine le_trans (Finset.sum_le_sum fun k hk => ?_) (hleft t)
    calc (∑ z ∈ rows k, ‖leftColumn SS (cc ⟨k, z⟩) (V 2) uu t‖ ^ 2)
        = ∑ z ∈ rows k, ‖rowPolynomial (S k) (a k)
            (fun i => c k i * columnPhase (V 2) (u k i) t) z‖ ^ 2 :=
          Finset.sum_congr rfl (fun z _ => by rw [hlc ⟨k, z⟩ hk])
      _ ≤ _ := finite_energy_le_restricted (keep₁ k) (S k) (a k) (ha k)
          (fun i => c k i * columnPhase (V 2) (u k i) t) U K hK (rows k) (hkeep₁ k hk) hU
          (hmajor k hk)
  have hR' : (∑ p ∈ P, ‖rightColumn TT (dd p) (V 3) vv t‖ ^ 2) ≤ (E₂ * (1 + ‖t‖) ^ J₂) ^ 2 := by
    rw [Finset.sum_sigma]
    refine le_trans (Finset.sum_le_sum fun k hk => ?_) (hright t)
    calc (∑ z ∈ rows k, ‖rightColumn TT (dd ⟨k, z⟩) (V 3) vv t‖ ^ 2)
        = ∑ z ∈ rows k, ‖rowPolynomial (T k) (b k)
            (fun j => d k j * star (columnPhase (V 3) (v k j) t)) (-z)‖ ^ 2 :=
          Finset.sum_congr rfl (fun z _ => by rw [hrc ⟨k, z⟩ hk, norm_star])
      _ ≤ _ := finite_negative_energy_le_restricted (keep₂ k) (T k) (b k) (hb k)
          (fun j => d k j * star (columnPhase (V 3) (v k j) t)) U K hK (rows k) (hkeep₂ k hk) hU
          (hmajor k hk)
  have hl := (Real.sqrt_le_iff).mpr ⟨by positivity, hL⟩
  have hr := (Real.sqrt_le_iff).mpr ⟨by positivity, hR'⟩
  calc
    _ ≤ (E₁ * (1 + ‖t‖) ^ J₁) * (E₂ * (1 + ‖t‖) ^ J₂) :=
      mul_le_mul hl hr (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

end
end QRH.SilDensitySplit.CubeFree.Second.Concrete
