/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M: the grouped (joint-row) second-step kernel estimate (generic, OAI only).

OAI bounds ONE second child (one label, one Möbius divisor `t₂`, one pair of ray characters)
by `whole_kernel_restricted_child_bound`, from height-uniform bounds on that child's two
restricted window energies. To feed Seam B, whose bound is for the WEIGHTED SUM over labels
at each height, the labels must be kept inside one Cauchy inequality, exactly as the first
artificial divisor is kept inside in `First.JointKernel`.

* `summed_restricted_window_from_height`: joint form (rows `children × O`) of OAI
  `restricted_window_energy_from_height`; every child has its own keep predicate, its own
  coefficients and its own character, the columns, their elements and the window centre `X`
  are common.
* `grouped_child_bound`: ONE `whole_kernel_row_estimate` on the joint rows `Σ k, rows k`:
  the sum over children of the NORMS of the child matrices is at most `C·E₁·E₂`, where
  `(E_i (1+|t|)^{J_i})²` bound the SUMS over children of the restricted window energies.
  The kernel ratio `R` and the column log-variables `u, v` are common (one dyadic class);
  the row variables `ρ, x`, the phases and the keep predicates may depend on the child.
  Weights are absorbed in the coefficients (`restrictedEnergy_smul`).
* `grouped_child_bound_from_height`: the two combined (window budgets from height-uniform
  bounds on the summed height energies). -/
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.RestrictedWindow
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.Moments.SecondWindowBudget

set_option autoImplicit false
namespace QRH.DensitySplitThird.CubeFree.Second.Concrete
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

/-! ### Scalar homogeneity of restricted energies -/

theorem restrictedEnergy_smul {α : Type*} (keep : O → Prop) (S : Finset α) (a : α → O)
    (c : α → ℂ) (s : ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    restrictedEnergy keep S a (fun i => s * c i) W K = ‖s‖^2 * restrictedEnergy keep S a c W K := by
  unfold restrictedEnergy
  rw [← tsum_mul_left]
  apply tsum_congr
  intro z
  have hp : rowPolynomial S a (fun i => s * c i) z = s * rowPolynomial S a c z := by
    unfold rowPolynomial
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  split_ifs
  · rw [hp, norm_mul, mul_pow]; ring
  · ring

theorem restrictedEnergy_nonneg {α : Type*} (keep : O → Prop) (S : Finset α) (a : α → O)
    (c : α → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ)
    (hW : ∀ z : O, 0 ≤ (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    0 ≤ restrictedEnergy keep S a c W K := by
  unfold restrictedEnergy
  apply tsum_nonneg
  intro z
  split_ifs
  · exact mul_nonneg (sq_nonneg _) (hW z)
  · exact le_rfl

/-! ### The summed restricted window energy -/

/-- Joint form of OAI `restricted_window_energy_from_shifted`. -/
theorem summed_restricted_window_from_shifted {κ α : Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (Ks : Finset κ) (keep : κ → O → Prop) (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (β : κ → α → ℂ) (τ : κ → Character) (t θ X : ℝ) (hX : 0 < X)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K)
    (hU : ∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (E : ℝ) (hE : 0 ≤ E)
    (henergy : ∀ w : ℝ, (∑ k ∈ Ks, restrictedEnergy (keep k) S a
      (fun i => β k i*heightCoeff (τ k) (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) U K) ≤
        E*(1+‖w‖)^(2*J)) :
    (∑ k ∈ Ks, restrictedEnergy (keep k) S a (fun i => β k i*heightCoeff (τ k) t (Ideal.span {a i})*
      columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) U K) ≤
      E*(∫ w : ℝ, (1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  let u := fun (k : κ) (z : O) => if keep k z then (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0
  have hu (k : κ) (z : O) : 0 ≤ u k z := by
    dsimp only [u]; split_ifs
    · exact hU z
    · exact le_rfl
  let c := fun (k : κ) i => β k i*heightCoeff (τ k) t (Ideal.span {a i})*
    columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ
  have hnorm (k : κ) (z : O) (x : ℂ) : ‖(Real.sqrt (u k z):ℂ)*x‖^2 = u k z*‖x‖^2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (hu k z)]
  have hfin (rows : Finset O) :
      (∑ z ∈ rows, ∑ k ∈ Ks, ‖rowPolynomial S a (c k) z‖^2*u k z) ≤
        E*(∫ w : ℝ, (1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
    let φ := fun p : Ks × rows => fun w : ℝ => (Real.sqrt (u p.1 p.2):ℂ)*
      (logPhase (θ-w) (Real.log X)*rowPolynomial S a
        (fun i => β p.1 i*heightCoeff (τ p.1) (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) p.2)
    have hi (p : Ks × rows) : Integrable (fun w => columnDensity V hVc hVs w*φ p w) := by
      have h := (plain_column_integrable S a ha (β p.1) (τ p.1) t θ X hX V hVc hVs p.2).const_mul
        (Real.sqrt (u p.1 p.2):ℂ)
      convert h using 1
      funext w
      dsimp only [φ]
      ring
    have hb (w : ℝ) : (∑ p : Ks × rows, ‖φ p w‖^2) ≤ E*((1+‖w‖)^J)^2 := by
      let g := fun (k : κ) (z : O) => ‖rowPolynomial S a
        (fun i => β k i*heightCoeff (τ k) (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z‖^2*
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
        _ ≤ ∑ k ∈ Ks, restrictedEnergy (keep k) S a
            (fun i => β k i*heightCoeff (τ k) (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) U K :=
          Finset.sum_le_sum (fun k _ =>
            finite_weighted_le_restricted (keep k) S a ha _ U K hK hU rows)
        _ ≤ E*(1+‖w‖)^(2*J) := henergy w
        _ = E*((1+‖w‖)^J)^2 := by rw [← pow_mul, Nat.mul_comm]
    have hh := finite_weighted_integral_energy (columnDensity V hVc hVs) φ
      (fun w => (1+‖w‖)^J) (by intro w; positivity) E hE (columnDensity_moments V hVc hVs J) hi hb
    have he (p : Ks × rows) : (∫ w : ℝ, columnDensity V hVc hVs w*φ p w) =
        (Real.sqrt (u p.1 p.2):ℂ)*rowPolynomial S a (c p.1) p.2 := by
      rw [show rowPolynomial S a (c p.1) p.2 = _ from
        plain_column_integral S a ha (β p.1) (τ p.1) t θ X hX V hVc hVs p.2, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with w
      dsimp only [φ]
      ring
    calc
      (∑ z ∈ rows, ∑ k ∈ Ks, ‖rowPolynomial S a (c k) z‖^2*u k z) =
          ∑ k ∈ Ks, ∑ z ∈ rows, ‖rowPolynomial S a (c k) z‖^2*u k z := Finset.sum_comm
      _ = ∑ p : Ks × rows, ‖rowPolynomial S a (c p.1) p.2‖^2*u p.1 p.2 := by
          rw [Fintype.sum_prod_type, ← Finset.sum_coe_sort Ks]
          exact Finset.sum_congr rfl (fun k _ =>
            (Finset.sum_coe_sort rows (fun z => ‖rowPolynomial S a (c k) z‖^2*u k z)).symm)
      _ = ∑ p : Ks × rows, ‖∫ w : ℝ, columnDensity V hVc hVs w*φ p w‖^2 :=
        Finset.sum_congr rfl (fun p _ => by rw [he p, hnorm]; ring)
      _ ≤ _ := hh
  have hs : HasSum (fun z : O => ∑ k ∈ Ks, ‖rowPolynomial S a (c k) z‖^2*u k z)
      (∑ k ∈ Ks, restrictedEnergy (keep k) S a (c k) U K) :=
    hasSum_sum (fun k _ => restricted_hasSum_weighted (keep k) S a ha (c k) U K hK)
  rw [← hs.tsum_eq]
  exact Real.tsum_le_of_sum_le
    (fun z => Finset.sum_nonneg (fun k _ => mul_nonneg (sq_nonneg _) (hu k z))) hfin

/-- Joint form of OAI `restricted_window_energy_from_height`. -/
theorem summed_restricted_window_from_height {κ α : Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (Ks : Finset κ) (keep : κ → O → Prop) (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (β : κ → α → ℂ) (τ : κ → Character) (t θ X : ℝ) (hX : 0 < X)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K)
    (hU : ∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (E : ℝ) (hE : 0 ≤ E)
    (henergy : ∀ v : ℝ, (∑ k ∈ Ks, restrictedEnergy (keep k) S a
      (fun i => β k i*heightCoeff (τ k) v (Ideal.span {a i})) U K) ≤ E*(1+‖v‖)^(2*J)) :
    (∑ k ∈ Ks, restrictedEnergy (keep k) S a (fun i => β k i*heightCoeff (τ k) t (Ideal.span {a i})*
      columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) U K) ≤
      (E*heightCost t θ^(2*J))*(∫ w : ℝ, (1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  apply summed_restricted_window_from_shifted V hVc hVs J Ks keep S a ha β τ t θ X hX U K hK hU
    (E*heightCost t θ^(2*J)) (mul_nonneg hE (pow_nonneg (heightCost_pos t θ).le _))
  intro w
  calc
    _ ≤ E*(1+‖t+2*Real.pi*(w-θ)‖)^(2*J) := henergy _
    _ ≤ E*(heightCost t θ*(1+‖w‖))^(2*J) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (norm_height_shift t θ w) _) hE
    _ = _ := by rw [mul_pow, mul_assoc]

/-! ### The grouped child kernel estimate -/

/-- The child matrix of OAI `whole_kernel_restricted_child_bound`. -/
def childMatrix {α β : Type*} (W : 𝓢(ℝ,ℂ)) (V : Fin 4 → ℝ → ℂ) (R : ℝ) (rows : Finset O)
    (S : Finset α) (T : Finset β) (a : α → O) (b : β → O) (c : α → ℂ) (d : β → ℂ)
    (u : α → ℝ) (v : β → ℝ) (ρ x : O → ℝ) (η : O → ℂ) : ℂ :=
  ∑ z ∈ rows, η z *
    (∑ i ∈ S, ∑ j ∈ T,
      ((c i * idealRowHom z (Ideal.span {a i})) * star (d j * idealRowHom (-z) (Ideal.span {b j}))) *
        wholeKernel W V R (ρ z) (x z) (u i) (v j))

/-- A unimodular phase turning a complex number into its norm. -/
def unitPhase (w : ℂ) : ℂ := if w = 0 then 1 else star w / (‖w‖:ℂ)

theorem unitPhase_norm (w : ℂ) : ‖unitPhase w‖ = 1 := by
  unfold unitPhase
  split_ifs with h
  · exact norm_one
  · have hn : (‖w‖:ℝ) ≠ 0 := norm_ne_zero_iff.mpr h
    rw [norm_div, norm_star, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), div_self hn]

theorem unitPhase_mul (w : ℂ) : unitPhase w * w = (‖w‖:ℂ) := by
  unfold unitPhase
  split_ifs with h
  · simp [h]
  · have hn : (‖w‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h)
    rw [div_mul_eq_mul_div, show star w * w = (‖w‖:ℂ)^2 from by
      rw [show star w = (starRingEnd ℂ) w from rfl, Complex.conj_mul'],
      pow_two, mul_div_assoc, div_self hn, mul_one]

/-- `∑_k ‖w_k‖ = ‖∑_k phase_k·w_k‖`. -/
theorem sum_norm_eq_norm_phase {κ : Type*} (Ks : Finset κ) (w : κ → ℂ) :
    (∑ k ∈ Ks, ‖w k‖) = ‖∑ k ∈ Ks, unitPhase (w k) * w k‖ := by
  simp_rw [unitPhase_mul]
  rw [← Complex.ofReal_sum, Complex.norm_real,
    Real.norm_of_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg _)]

/-- **The grouped child kernel estimate.** -/
theorem grouped_child_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {κ α β : Type*} (Ks : Finset κ) (rows : κ → Finset O) (S : Finset α) (T : Finset β)
        (a : α → O) (b : β → O)
        (_ha : ∀ i, Supported (Ideal.span {a i}))
        (_hb : ∀ j, Supported (Ideal.span {b j}))
        (c : κ → α → ℂ) (d : κ → β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : κ → O → ℝ) (η : κ → O → ℂ) (keep₁ keep₂ : κ → O → Prop),
      (∀ k ∈ Ks, ∀ z ∈ rows k, keep₁ k z) → (∀ k ∈ Ks, ∀ z ∈ rows k, keep₂ k (-z)) →
      (∀ k ∈ Ks, ∀ z ∈ rows k, ‖η k z‖ ≤ 1) →
      (∀ k ∈ Ks, ∀ z ∈ rows k, ‖V 0 (ρ k z)‖ ≤ 1) → (∀ k ∈ Ks, ∀ z ∈ rows k, ‖V 1 (x k z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      (∀ k ∈ Ks, ∀ z ∈ rows k, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖ ^ 2 / K)).re) →
      ∀ E₁ E₂ : ℝ, 0 ≤ E₁ → 0 ≤ E₂ →
      (∀ t : ℝ, (∑ k ∈ Ks, restrictedEnergy (keep₁ k) S a
        (fun i => c k i * columnPhase (V 2) (u i) t) U K) ≤ (E₁ * (1 + ‖t‖) ^ J₁) ^ 2) →
      (∀ t : ℝ, (∑ k ∈ Ks, restrictedEnergy (keep₂ k) T b
        (fun j => d k j * star (columnPhase (V 3) (v j) t)) U K) ≤ (E₂ * (1 + ‖t‖) ^ J₂) ^ 2) →
      (1 + R) ^ A * ∑ k ∈ Ks,
        ‖childMatrix W V R (rows k) S T a b (c k) (d k) u v (ρ k) (x k) (η k)‖ ≤ C * (E₁ * E₂) := by
  obtain ⟨C, hC, hbound⟩ := whole_kernel_row_estimate W V M hM hV A (J₁ + J₂)
  refine ⟨C, hC, ?_⟩
  intro R hR κ α β Ks rows S T a b ha hb c d u v ρ x η keep₁ keep₂ hkeep₁ hkeep₂ hη hV₀ hV₁
    U K hK hU hmajor E₁ E₂ hE₁ hE₂ hleft hright
  let P : Finset (Σ _ : κ, O) := Ks.sigma rows
  let phs : κ → ℂ := fun k =>
    unitPhase (childMatrix W V R (rows k) S T a b (c k) (d k) u v (ρ k) (x k) (η k))
  have hP (p : Σ _ : κ, O) (hp : p ∈ P) : p.1 ∈ Ks ∧ p.2 ∈ rows p.1 := Finset.mem_sigma.mp hp
  have hsum : (∑ k ∈ Ks, ‖childMatrix W V R (rows k) S T a b (c k) (d k) u v (ρ k) (x k) (η k)‖) =
      ‖∑ p ∈ P, (phs p.1 * η p.1 p.2) *
        (∑ i ∈ S, ∑ j ∈ T, ((c p.1 i * idealRowHom p.2 (Ideal.span {a i})) *
          star (d p.1 j * idealRowHom (-p.2) (Ideal.span {b j}))) *
            wholeKernel W V R (ρ p.1 p.2) (x p.1 p.2) (u i) (v j))‖ := by
    rw [sum_norm_eq_norm_phase]
    congr 1
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro k _
    simp only [childMatrix, Finset.mul_sum, phs]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  apply hbound R hR P S T
    (fun p i => c p.1 i * idealRowHom p.2 (Ideal.span {a i}))
    (fun p j => d p.1 j * idealRowHom (-p.2) (Ideal.span {b j})) u v
    (fun p => ρ p.1 p.2) (fun p => x p.1 p.2) (fun p => phs p.1 * η p.1 p.2)
    (fun p hp => by
      rw [norm_mul, unitPhase_norm, one_mul]; exact hη _ (hP p hp).1 _ (hP p hp).2)
    (fun p hp => hV₀ _ (hP p hp).1 _ (hP p hp).2) (fun p hp => hV₁ _ (hP p hp).1 _ (hP p hp).2)
    (E₁ * E₂) (mul_nonneg hE₁ hE₂)
  intro t
  have hL : (∑ p ∈ P, ‖leftColumn S (fun i => c p.1 i * idealRowHom p.2 (Ideal.span {a i}))
      (V 2) u t‖ ^ 2) ≤ (E₁ * (1 + ‖t‖) ^ J₁) ^ 2 := by
    simp only [leftColumn_eq_rowPolynomial]
    rw [Finset.sum_sigma]
    refine le_trans (Finset.sum_le_sum fun k hk => ?_) (hleft t)
    exact finite_energy_le_restricted (keep₁ k) S a ha
      (fun i => c k i * columnPhase (V 2) (u i) t) U K hK (rows k) (hkeep₁ k hk) hU (hmajor k hk)
  have hR' : (∑ p ∈ P, ‖rightColumn T (fun j => d p.1 j * idealRowHom (-p.2) (Ideal.span {b j}))
      (V 3) v t‖ ^ 2) ≤ (E₂ * (1 + ‖t‖) ^ J₂) ^ 2 := by
    simp only [rightColumn_eq_star_rowPolynomial, norm_star]
    rw [Finset.sum_sigma]
    refine le_trans (Finset.sum_le_sum fun k hk => ?_) (hright t)
    exact finite_negative_energy_le_restricted (keep₂ k) T b hb
      (fun j => d k j * star (columnPhase (V 3) (v j) t)) U K hK (rows k) (hkeep₂ k hk) hU
      (hmajor k hk)
  have hl := (Real.sqrt_le_iff).mpr ⟨by positivity, hL⟩
  have hr := (Real.sqrt_le_iff).mpr ⟨by positivity, hR'⟩
  calc
    _ ≤ (E₁ * (1 + ‖t‖) ^ J₁) * (E₂ * (1 + ‖t‖) ^ J₂) :=
      mul_le_mul hl hr (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring

end
end QRH.DensitySplitThird.CubeFree.Second.Concrete
