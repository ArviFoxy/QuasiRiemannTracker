/-
The switching flow is the maximal admissible envelope (research/chain-structure/README.md §5).

A continuum source chain is an envelope `E(s)` whose faces pass the HIGH gate of every amplitude
class `p ∈ [0, 1/2]` and the LOW limit. For class `p` this is the differential inequality

  `E′ ≤ −φ_p(s, E)`,  `φ_p = Q_p E/(1 − Q_p s)`,  `Q_p = 6q_p = 5A_p/D_p`,

with `A_p = (3 − p)E + 4ps − 2` and `D_p = (1 + p)E + 4p²s − 2p` (`ChainFamilyIntegrable.lean`).

* `Q_mono`: each class threshold increases with the plain length `E` (on the region where
  `A_p, D_p > 0` and `4ps < 2`): `D_p = pA_p + (1 − p)²E` and `A_p E′ − A′_p E = (4ps − 2)(E′ − E)`.
* `rate_mono`: `QE/(1 − Qs)` increases with `Q` and with `E` while `1 − Qs > 0`.
* `maximal_envelope`: if `bind s e` is a binding class (it maximizes `φ_p(s, e)` over the classes),
  every envelope admissible for all classes stays below the solution of `Ê′ = −φ_{bind}(s, Ê)` that
  starts at least as high. This is the comparison principle of `MaximalEnvelope.lean` with the
  monotonicity supplied by `Q_mono` and the maximality of the binding class.
* `closed_form_binding`: in the interior regime the binding class is
  `p* = (a² + ab − 1)/(b(a − 2b))` (`E = a²`, `s = b²`): its rate dominates every class rate,
  by the sum-of-squares bound of `ChainAMGM.lean` and `rate_mono`. So the maximal envelope is the
  closed-form flow `E′ = −Q*E/(1 − Q*s)`, `Q* = 5(√E − 2√s)²/(2 − E − 4√(Es))`.
Status: proved.
-/
import Mathlib

namespace ChainOptimal

open Set

/-! ## Comparison principle (local form) -/

theorem nonpos_of_deriv_nonpos_where_pos {h : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn h (Icc a b))
    (hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ h x)
    (hpos : ∀ x ∈ Ioo a b, 0 < h x → deriv h x ≤ 0)
    (ha : h a ≤ 0) : ∀ x ∈ Icc a b, h x ≤ 0 := by
  intro t₁ ht₁
  by_contra hcon
  push Not at hcon
  set S : Set ℝ := Icc a t₁ ∩ h ⁻¹' Iic 0 with hSdef
  have haS : a ∈ S := ⟨⟨le_refl a, ht₁.1⟩, ha⟩
  have hbdd : BddAbove S := ⟨t₁, fun t ht => ht.1.2⟩
  have hclosed : IsClosed S :=
    (hc.mono (Icc_subset_Icc_right ht₁.2)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  set t₀ := sSup S with ht₀def
  have ht₀S : t₀ ∈ S := hclosed.csSup_mem ⟨a, haS⟩ hbdd
  have hat₀ : a ≤ t₀ := ht₀S.1.1
  have ht₀t₁ : t₀ ≤ t₁ := ht₀S.1.2
  have ht₀nonpos : h t₀ ≤ 0 := ht₀S.2
  have ht₀lt : t₀ < t₁ := by
    rcases lt_or_eq_of_le ht₀t₁ with hlt | heq
    · exact hlt
    · exfalso
      rw [heq] at ht₀nonpos
      linarith
  have hposIoc : ∀ t ∈ Ioc t₀ t₁, 0 < h t := by
    intro t ht
    by_contra hneg
    push Not at hneg
    have htS : t ∈ S := ⟨⟨le_trans hat₀ (le_of_lt ht.1), ht.2⟩, hneg⟩
    have := le_csSup hbdd htS
    linarith [ht.1]
  have hanti : AntitoneOn h (Icc t₀ t₁) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc t₀ t₁)
    · exact hc.mono (Icc_subset_Icc hat₀ ht₁.2)
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x ⟨lt_of_le_of_lt hat₀ hx.1, lt_of_lt_of_le hx.2 ht₁.2⟩).differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact hpos x ⟨lt_of_le_of_lt hat₀ hx.1, lt_of_lt_of_le hx.2 ht₁.2⟩
        (hposIoc x ⟨hx.1, le_of_lt hx.2⟩)
  have hle := hanti ⟨le_refl t₀, ht₀t₁⟩ ⟨ht₀t₁, le_refl t₁⟩ ht₀t₁
  linarith

/-- Comparison with a slope that is only required to be monotone between the two envelopes. -/
theorem envelope_le {E Ê E' Ê' : ℝ → ℝ} {Λ : ℝ → ℝ → ℝ} {a b : ℝ}
    (hmono : ∀ s ∈ Icc a b, Ê s ≤ E s → Λ s (Ê s) ≤ Λ s (E s))
    (hE : ∀ s ∈ Icc a b, HasDerivAt E (E' s) s)
    (hÊ : ∀ s ∈ Icc a b, HasDerivAt Ê (Ê' s) s)
    (hineq : ∀ s ∈ Icc a b, E' s ≤ -Λ s (E s))
    (heq : ∀ s ∈ Icc a b, Ê' s = -Λ s (Ê s))
    (ha : E a ≤ Ê a) : ∀ s ∈ Icc a b, E s ≤ Ê s := by
  have key := nonpos_of_deriv_nonpos_where_pos (h := fun s => E s - Ê s) (a := a) (b := b)
    (fun s hs => ((hE s hs).sub (hÊ s hs)).continuousAt.continuousWithinAt)
    (fun s hs => ((hE s (Ioo_subset_Icc_self hs)).sub
      (hÊ s (Ioo_subset_Icc_self hs))).differentiableAt)
    (fun s hs hp => by
      have hs' := Ioo_subset_Icc_self hs
      show deriv (E - Ê) s ≤ 0
      rw [((hE s hs').sub (hÊ s hs')).deriv]
      have h1 := hineq s hs'
      have h2 := heq s hs'
      have hp' : 0 < E s - Ê s := hp
      have h3 : Λ s (Ê s) ≤ Λ s (E s) := hmono s hs' (by linarith)
      linarith)
    (show E a - Ê a ≤ 0 by linarith)
  intro s hs
  have := key s hs
  linarith

/-! ## Class thresholds and rates -/

def numA (p s E : ℝ) : ℝ := (3 - p) * E + 4 * p * s - 2
def denD (p s E : ℝ) : ℝ := (1 + p) * E + 4 * p ^ 2 * s - 2 * p

/-- The class threshold `6q_p`. -/
noncomputable def Q (p s E : ℝ) : ℝ := 5 * numA p s E / denD p s E

/-- The descent rate a face of class `p` imposes: `E′ ≤ −φ_p`. -/
noncomputable def φ (p s E : ℝ) : ℝ := Q p s E * E / (1 - Q p s E * s)

theorem denD_eq (p s E : ℝ) : denD p s E = p * numA p s E + (1 - p) ^ 2 * E := by
  unfold denD numA; ring

/-- The class threshold increases with the plain length. -/
theorem Q_mono {p s x y : ℝ} (hxy : x ≤ y) (hps : 4 * p * s < 2)
    (_hAx : 0 < numA p s x) (_hAy : 0 < numA p s y)
    (hDx : 0 < denD p s x) (hDy : 0 < denD p s y) : Q p s x ≤ Q p s y := by
  unfold Q
  rw [div_le_div_iff₀ hDx hDy]
  -- `A_x D_y − A_y D_x = (1 − p)² (A_x y − A_y x) = (1 − p)² (4ps − 2)(y − x) ≤ 0`
  have hkey : 5 * numA p s x * denD p s y - 5 * numA p s y * denD p s x
      = 5 * (1 - p) ^ 2 * (4 * p * s - 2) * (y - x) := by
    unfold numA denD; ring
  have hsq : 0 ≤ (1 - p) ^ 2 := sq_nonneg _
  have hneg : 5 * (1 - p) ^ 2 * (4 * p * s - 2) * (y - x) ≤ 0 := by
    have h1 : 4 * p * s - 2 ≤ 0 := by linarith
    have h2 : 0 ≤ y - x := by linarith
    have h3 : 0 ≤ 5 * (1 - p) ^ 2 := by positivity
    have := mul_nonpos_of_nonneg_of_nonpos h3 h1
    exact mul_nonpos_of_nonpos_of_nonneg this h2
  linarith

/-- `QE/(1 − Qs)` increases with `Q` and `E` while the LOW denominator stays positive. -/
theorem rate_mono {Q₁ Q₂ E₁ E₂ s : ℝ} (hQ : Q₁ ≤ Q₂) (hE : E₁ ≤ E₂) (hQ₁ : 0 ≤ Q₁)
    (hE₁ : 0 ≤ E₁) (hs : 0 ≤ s) (hden : 0 < 1 - Q₂ * s) :
    Q₁ * E₁ / (1 - Q₁ * s) ≤ Q₂ * E₂ / (1 - Q₂ * s) := by
  have hden1 : 0 < 1 - Q₁ * s := by nlinarith
  rw [div_le_div_iff₀ hden1 hden]
  have hQ₂ : 0 ≤ Q₂ := le_trans hQ₁ hQ
  have key : Q₂ * E₂ * (1 - Q₁ * s) - Q₁ * E₁ * (1 - Q₂ * s)
      = Q₂ * (E₂ - E₁) * (1 - Q₁ * s) + E₁ * (Q₂ - Q₁) := by ring
  have t1 : 0 ≤ Q₂ * (E₂ - E₁) * (1 - Q₁ * s) :=
    mul_nonneg (mul_nonneg hQ₂ (by linarith)) hden1.le
  have t2 : 0 ≤ E₁ * (Q₂ - Q₁) := mul_nonneg hE₁ (by linarith)
  linarith

/-- The region where class `p` is a genuine gate at height `e`. -/
def Good (p s e : ℝ) : Prop :=
  0 < numA p s e ∧ 0 < denD p s e ∧ 0 < 1 - Q p s e * s ∧ 0 ≤ e ∧ 0 ≤ s ∧ 4 * p * s < 2

theorem Q_nonneg {p s e : ℝ} (h : Good p s e) : 0 ≤ Q p s e := by
  unfold Q; exact div_nonneg (by linarith [h.1]) h.2.1.le

/-- The class rate increases with the height. -/
theorem φ_mono {p s x y : ℝ} (hxy : x ≤ y) (hx : Good p s x) (hy : Good p s y) :
    φ p s x ≤ φ p s y := by
  unfold φ
  exact rate_mono (Q_mono hxy hx.2.2.2.2.2 hx.1 hy.1 hx.2.1 hy.2.1) hxy (Q_nonneg hx) hx.2.2.2.1
    hx.2.2.2.2.1 hy.2.2.1

/-! ## Maximality of the binding-class flow -/

/-- **The binding-class flow is the maximal admissible envelope.** `bind s e` is a binding class:
it lies in `[0, 1/2]` and maximizes the class rate at `(s, e)`. Every envelope `E` whose faces pass
every class gate stays below the solution `Ê` of `Ê′ = −φ_{bind}(s, Ê)` that starts at least as
high. -/
theorem maximal_envelope {E Ê E' Ê' : ℝ → ℝ} {bind : ℝ → ℝ → ℝ} {a b : ℝ}
    (hbind : ∀ s e, bind s e ∈ Icc (0 : ℝ) (1 / 2))
    (hmax : ∀ s ∈ Icc a b, ∀ p ∈ Icc (0 : ℝ) (1 / 2), φ p s (E s) ≤ φ (bind s (E s)) s (E s))
    (hgood : ∀ s ∈ Icc a b, ∀ p ∈ Icc (0 : ℝ) (1 / 2), Good p s (E s) ∧ Good p s (Ê s))
    (hE : ∀ s ∈ Icc a b, HasDerivAt E (E' s) s)
    (hÊ : ∀ s ∈ Icc a b, HasDerivAt Ê (Ê' s) s)
    (hadm : ∀ s ∈ Icc a b, ∀ p ∈ Icc (0 : ℝ) (1 / 2), E' s ≤ -φ p s (E s))
    (hflow : ∀ s ∈ Icc a b, Ê' s = -φ (bind s (Ê s)) s (Ê s))
    (ha : E a ≤ Ê a) : ∀ s ∈ Icc a b, E s ≤ Ê s := by
  refine envelope_le (Λ := fun s e => φ (bind s e) s e) ?_ hE hÊ ?_ hflow ha
  · intro s hs hle
    have hp := hbind s (Ê s)
    have h1 : φ (bind s (Ê s)) s (Ê s) ≤ φ (bind s (Ê s)) s (E s) :=
      φ_mono hle (hgood s hs _ hp).2 (hgood s hs _ hp).1
    exact h1.trans (hmax s hs _ hp)
  · intro s hs
    exact hadm s hs _ (hbind s (E s))

/-! ## The binding class in closed form -/

/-- The sum-of-squares identity of `ChainAMGM.lean`. -/
theorem sos (p a b : ℝ) :
    (a + 2 * b) ^ 2 * ((a - 2 * b) ^ 2 * denD p (b ^ 2) (a ^ 2)
        - (2 - a ^ 2 - 4 * a * b) * numA p (b ^ 2) (a ^ 2))
      = 4 * (b * numA p (b ^ 2) (a ^ 2) - a * (1 - a ^ 2 - 2 * b ^ 2)) ^ 2 := by
  unfold denD numA; ring

/-- Every class threshold is at most the closed form `Q* = 5(a − 2b)²/(2 − a² − 4ab)`. -/
theorem Q_le_Qstar (p a b : ℝ) (hab : a + 2 * b ≠ 0) (hD : 0 < denD p (b ^ 2) (a ^ 2))
    (hW : 0 < 2 - a ^ 2 - 4 * a * b) :
    Q p (b ^ 2) (a ^ 2) ≤ 5 * (a - 2 * b) ^ 2 / (2 - a ^ 2 - 4 * a * b) := by
  unfold Q
  rw [div_le_div_iff₀ hD hW]
  have h := sos p a b
  have hpos : 0 < (a + 2 * b) ^ 2 := by positivity
  have hsq : 0 ≤ 4 * (b * numA p (b ^ 2) (a ^ 2) - a * (1 - a ^ 2 - 2 * b ^ 2)) ^ 2 := by
    positivity
  have : 0 ≤ (a - 2 * b) ^ 2 * denD p (b ^ 2) (a ^ 2)
      - (2 - a ^ 2 - 4 * a * b) * numA p (b ^ 2) (a ^ 2) := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg hpos hneg
    linarith
  nlinarith

/-- At `p* = (a² + ab − 1)/(b(a − 2b))` the class threshold equals the closed form. -/
theorem Q_pstar (a b : ℝ) (hb : b ≠ 0) (h2 : a - 2 * b ≠ 0) (hab : a + 2 * b ≠ 0)
    (hD : denD ((a ^ 2 + a * b - 1) / (b * (a - 2 * b))) (b ^ 2) (a ^ 2) ≠ 0)
    (hW : 2 - a ^ 2 - 4 * a * b ≠ 0) :
    Q ((a ^ 2 + a * b - 1) / (b * (a - 2 * b))) (b ^ 2) (a ^ 2)
      = 5 * (a - 2 * b) ^ 2 / (2 - a ^ 2 - 4 * a * b) := by
  set p := (a ^ 2 + a * b - 1) / (b * (a - 2 * b)) with hp
  have hA : b * numA p (b ^ 2) (a ^ 2) = a * (1 - a ^ 2 - 2 * b ^ 2) := by
    have h2' : a - b * 2 ≠ 0 := by intro h; apply h2; linarith
    rw [hp]; unfold numA; field_simp; ring
  have h := sos p a b
  have hzero : (a - 2 * b) ^ 2 * denD p (b ^ 2) (a ^ 2)
      - (2 - a ^ 2 - 4 * a * b) * numA p (b ^ 2) (a ^ 2) = 0 := by
    have hsq : 4 * (b * numA p (b ^ 2) (a ^ 2) - a * (1 - a ^ 2 - 2 * b ^ 2)) ^ 2 = 0 := by
      rw [hA]; ring
    rw [hsq] at h
    have hpos : (a + 2 * b) ^ 2 ≠ 0 := by positivity
    exact (mul_eq_zero.mp h).resolve_left hpos
  unfold Q
  rw [div_eq_div_iff hD hW]
  linarith

/-- **The binding class in the interior regime.** If `p*` is a class (`p* ∈ [0, 1/2]`) and the
class gates are genuine, the rate of `p*` dominates every class rate: `p*` is a binding class, and
its rate is `Q*E/(1 − Q*s)` with the closed form `Q*`. -/
theorem closed_form_binding (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h2 : a - 2 * b ≠ 0) (hW : 0 < 2 - a ^ 2 - 4 * a * b)
    (hgood : ∀ p ∈ Icc (0 : ℝ) (1 / 2), Good p (b ^ 2) (a ^ 2))
    (hp : (a ^ 2 + a * b - 1) / (b * (a - 2 * b)) ∈ Icc (0 : ℝ) (1 / 2)) :
    ∀ p ∈ Icc (0 : ℝ) (1 / 2),
      φ p (b ^ 2) (a ^ 2) ≤ φ ((a ^ 2 + a * b - 1) / (b * (a - 2 * b))) (b ^ 2) (a ^ 2) := by
  intro p hpI
  have hab : a + 2 * b ≠ 0 := by positivity
  set ps := (a ^ 2 + a * b - 1) / (b * (a - 2 * b)) with hps
  have gp := hgood p hpI
  have gs := hgood ps hp
  have hQs : Q ps (b ^ 2) (a ^ 2) = 5 * (a - 2 * b) ^ 2 / (2 - a ^ 2 - 4 * a * b) :=
    Q_pstar a b hb.ne' h2 hab gs.2.1.ne' hW.ne'
  have hle : Q p (b ^ 2) (a ^ 2) ≤ Q ps (b ^ 2) (a ^ 2) := by
    rw [hQs]; exact Q_le_Qstar p a b hab gp.2.1 hW
  unfold φ
  exact rate_mono hle le_rfl (Q_nonneg gp) gp.2.2.2.1 gp.2.2.2.2.1 gs.2.2.1

end ChainOptimal
