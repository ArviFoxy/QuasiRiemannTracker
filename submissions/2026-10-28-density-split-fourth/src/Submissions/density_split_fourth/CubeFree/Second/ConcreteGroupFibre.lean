/- Copyright (c) 2026 Sil. Apache-2.0.
WP-M2, item 3 (fibre): the weighted fibre of the concrete second-step labels at a row of
POLYNOMIALLY BOUNDED norm (CF §5, common-profile lemma §3(v)).

For a row `y ≠ 0` with `N(y) ≤ Z^{Cexp}`, the labels on `y` (`A₂ ∣ y`) are encoded injectively
by `k` divisors of `y` (genuine common factor, nonunit part, allocations, ...) together with
their second artificial divisor `t₂`; with `‖prefactor‖ ≤ 1` and `common ∣ A₂` the weight
`ρ(G)‖pref‖/N(t₂)` gives (`fibre_rows`)
  `∑_{x : A₂ ∣ y} ρ(G_x)‖pref_x‖/N(t₂,x) ≤ τ(y)^{k+1} · 256 (⌈log₂ Z^B⌉ + 1) ≤ Z^{ε/8}`
for all large `Z` (`ρ(G) ≤ τ(G) ≤ τ(y)`, `rho_le_card_divisors`; `∑ 1/N(t₂)` by OAI
`finite_inverse_norm_sum`; `τ(y)^{k+1} ≤ C Z^δ` by `Packet.Fibre.divisor_power_subpower`).

The norm restriction is necessary (for the product `y` of all twists of a group the fibre is
the whole group weight, a power of `Z`); `Second.AdmissibleGroup` therefore asks the fibre only
at rows with `N(y) ≤ Z^{Mmax+2}` (coordinator decision), which is `fibre_rows` with
`Cexp = Mmax + 2`. -/
import Submissions.density_split_fourth.CubeFree.Packet.GroupedFrame
import Submissions.density_split_fourth.CubeFree.Packet.Fibre
import Submissions.openai_baseline.OAI.NumberTheory.DirichletL.MeanSquare.TransformedColumns

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace QRH.DensitySplitThird.CubeFree.Second.ConcreteGroup
open QRH.DensitySplitThird.CubeFree.Packet.Grouped

noncomputable section
open scoped Classical BigOperators
open Filter OAI OAI.SevenEighths HeckeFamily
open OAI.IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
local notation "O" => HeckeFamily.O

/-- `ρ(G) = 2^{ω(G)} ≤ τ(G)`. -/
theorem rho_le_card_divisors (G : Ideal O) (hG : G ≠ ⊥) :
    rho G ≤ ((idealDivisors G).card : ℝ) := by
  unfold rho
  have himg := OAI.IdealMobiusDivisorSum.squarefree_divisors_eq_image G hG
  have hinj : Set.InjOn (fun S : Finset (Ideal O) => ∏ P ∈ S, P)
      (OAI.IdealMobiusDivisorSum.primeSupport G).powerset := by
    intro S hS T hT h
    exact OAI.IdealMobiusDivisorSum.support_product_injective
      (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) h
  have hcard : (2:ℕ)^(OAI.IdealMobiusDivisorSum.primeSupport G).card ≤ (idealDivisors G).card := by
    rw [← Finset.card_powerset, ← Finset.card_image_of_injOn hinj, ← himg]
    exact Finset.card_filter_le _ _
  exact_mod_cast hcard

theorem card_divisors_mono {I J : Ideal O} (hJ : J ≠ ⊥) (h : I ∣ J) (hI : I ≠ ⊥) :
    (idealDivisors I).card ≤ (idealDivisors J).card := by
  apply Finset.card_le_card
  intro K hK
  rw [mem_idealDivisors hI] at hK
  rw [mem_idealDivisors hJ]
  exact hK.trans h

/-- `256 (⌈log₂ Z^B⌉ + 1) ≤ C Z^δ` for `Z ≥ 1`. -/
theorem dyadic_length_subpower (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      256 * ((CanonicalQuadraticSieve.columnDyadicLength (Z^B) : ℝ) + 1) ≤ C * Z^δ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨256 * (B / (δ * Real.log 2) + 2), by positivity, ?_⟩
  intro Z hZ
  have hZ0 : 0 < Z := by linarith
  have hZδ : 1 ≤ Z^δ := Real.one_le_rpow hZ hδ.le
  have hlog : Real.log Z ≤ Z^δ / δ := Real.log_le_rpow_div hZ0.le hδ
  have hc : (CanonicalQuadraticSieve.columnDyadicLength (Z^B) : ℝ) ≤
      Real.log (Z^B) / Real.log 2 + 1 := by
    unfold CanonicalQuadraticSieve.columnDyadicLength
    have hnn : 0 ≤ Real.log (Z^B) / Real.log 2 :=
      div_nonneg (Real.log_nonneg (Real.one_le_rpow hZ hB)) hl2.le
    exact (Nat.ceil_lt_add_one hnn).le
  have hlZB : Real.log (Z^B) = B * Real.log Z := Real.log_rpow hZ0 B
  have h1 : Real.log (Z^B) / Real.log 2 ≤ B / (δ * Real.log 2) * Z^δ := by
    rw [hlZB, div_le_iff₀ hl2]
    have : B * Real.log Z ≤ B * (Z^δ / δ) := mul_le_mul_of_nonneg_left hlog hB
    calc B * Real.log Z ≤ B * (Z^δ / δ) := this
      _ = B / (δ * Real.log 2) * Z^δ * Real.log 2 := by field_simp
  have hBd : 0 ≤ B / (δ * Real.log 2) := by positivity
  nlinarith

/-- **The weighted fibre at a row of bounded norm.** -/
theorem fibre_rows (k : ℕ) (Cexp B ε : ℝ) (hCexp : 0 ≤ Cexp) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∀ᶠ Z : ℝ in atTop, ∀ (L : ℝ) (θ : GData L) (mesh : ℝ)
      (labels : Finset (GLabel θ mesh Z)) (code : GLabel θ mesh Z → Fin k → Ideal O),
      (∀ x ∈ labels, ‖x.prefactor‖ ≤ 1) →
      (∀ x ∈ labels, x.common ∣ Ideal.span {x.twist}) →
      (∀ x ∈ labels, x.D ≠ 0 ∧ (x.D.absNorm : ℝ) ≤ Z^B) →
      (∀ x ∈ labels, ∀ i, code x i ∣ Ideal.span {x.twist}) →
      Set.InjOn (fun x => (code x, x.D)) labels →
      ∀ y : O, y ≠ 0 → ((Ideal.span {y}).absNorm : ℝ) ≤ Z^Cexp →
        ∑ x ∈ labels.filter (fun x => x.twist ∣ y), gWeight x ≤ Z^(ε/8) := by
  obtain ⟨Cd, hCd, hdiv⟩ := Packet.Fibre.divisor_power_subpower (k+1) Cexp (ε/32) hCexp
    (by positivity)
  obtain ⟨Cl, hCl, hlen⟩ := dyadic_length_subpower B (ε/32) hB (by positivity)
  have hev : ∀ᶠ Z : ℝ in atTop, Cd * Cl ≤ Z^(ε/16) := by
    have h := (tendsto_rpow_atTop (show (0:ℝ) < ε/16 by positivity)).eventually_ge_atTop (Cd * Cl)
    exact h
  filter_upwards [hev, eventually_ge_atTop (1:ℝ)] with Z hZC hZ1
  intro L θ mesh labels code hpref hcom hD hcode hinj y hy hNy
  have hZ0 : 0 < Z := by linarith
  set Y : Ideal O := Ideal.span {y} with hYdef
  have hY : Y ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hy
  set F := labels.filter (fun x => x.twist ∣ y) with hF
  have hFsub : F ⊆ labels := Finset.filter_subset _ _
  have hdvdY : ∀ x ∈ F, Ideal.span {x.twist} ∣ Y := by
    intro x hx
    exact Ideal.span_singleton_dvd_span_singleton_iff_dvd.mpr (Finset.mem_filter.mp hx).2
  set τY : ℝ := ((idealDivisors Y).card : ℝ) with hτY
  have hτ0 : 0 ≤ τY := Nat.cast_nonneg _
  -- weights
  have hw : ∀ x ∈ F, gWeight x ≤ τY * (1 / (x.D.absNorm : ℝ)) := by
    intro x hx
    have hxl := hFsub hx
    have hc : x.common ∣ Y := (hcom x hxl).trans (hdvdY x hx)
    have hc0 : x.common ≠ ⊥ := by
      intro h0
      rw [h0] at hc
      exact hY (zero_dvd_iff.mp hc)
    have hrho : rho x.common ≤ τY :=
      (rho_le_card_divisors _ hc0).trans (by rw [hτY]; exact_mod_cast card_divisors_mono hY hc hc0)
    have hN : 0 < (x.D.absNorm : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hD x hxl).1)
    unfold gWeight
    rw [div_eq_mul_one_div (rho x.common * ‖x.prefactor‖)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc rho x.common * ‖x.prefactor‖ ≤ rho x.common * 1 :=
          mul_le_mul_of_nonneg_left (hpref x hxl) (by unfold rho; positivity)
      _ ≤ τY := by rw [mul_one]; exact hrho
  -- the code count
  have hsum : ∑ x ∈ F, 1 / (x.D.absNorm : ℝ) ≤
      ((Packet.Fibre.divisorTuples k Y).card : ℝ) *
        ∑ D ∈ F.image (fun x => x.D), 1 / (D.absNorm : ℝ) := by
    have hinjF : Set.InjOn (fun x => (code x, x.D)) F := hinj.mono (by exact_mod_cast hFsub)
    rw [← Finset.sum_image (f := fun p : (Fin k → Ideal O) × Ideal O => 1 / (p.2.absNorm : ℝ))
      hinjF]
    have himg : F.image (fun x => (code x, x.D)) ⊆
        Packet.Fibre.divisorTuples k Y ×ˢ F.image (fun x => x.D) := by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      refine Finset.mem_product.mpr ⟨?_, Finset.mem_image_of_mem _ hx⟩
      rw [Packet.Fibre.mem_divisorTuples hY]
      exact fun i => (hcode x (hFsub hx) i).trans (hdvdY x hx)
    calc ∑ p ∈ F.image (fun x => (code x, x.D)), 1 / (p.2.absNorm : ℝ)
        ≤ ∑ p ∈ Packet.Fibre.divisorTuples k Y ×ˢ F.image (fun x => x.D),
            1 / (p.2.absNorm : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)
      _ = _ := by
          rw [Finset.sum_product]
          simp only [Finset.sum_const, nsmul_eq_mul]
  have hinv : ∑ D ∈ F.image (fun x => x.D), 1 / (D.absNorm : ℝ) ≤
      256 * ((CanonicalQuadraticSieve.columnDyadicLength (Z^B) : ℝ) + 1) := by
    apply CanonicalQuadraticSieve.finite_inverse_norm_sum
    · intro D hD'
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hD'
      exact (hD x (hFsub hx)).1
    · intro D hD'
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hD'
      exact (hD x (hFsub hx)).2
  have htup : ((Packet.Fibre.divisorTuples k Y).card : ℝ) = τY^k := by
    rw [Packet.Fibre.card_divisorTuples]; push_cast; rfl
  have hτpow : τY^(k+1) ≤ Cd * Z^(ε/32) := hdiv Z hZ1 Y hY hNy
  calc ∑ x ∈ F, gWeight x ≤ ∑ x ∈ F, τY * (1 / (x.D.absNorm : ℝ)) := Finset.sum_le_sum hw
    _ = τY * ∑ x ∈ F, 1 / (x.D.absNorm : ℝ) := by rw [Finset.mul_sum]
    _ ≤ τY * (τY^k * (256 * ((CanonicalQuadraticSieve.columnDyadicLength (Z^B) : ℝ) + 1))) := by
        apply mul_le_mul_of_nonneg_left _ hτ0
        rw [← htup]
        exact hsum.trans (mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _))
    _ = τY^(k+1) * (256 * ((CanonicalQuadraticSieve.columnDyadicLength (Z^B) : ℝ) + 1)) := by
        ring
    _ ≤ (Cd * Z^(ε/32)) * (Cl * Z^(ε/32)) :=
        mul_le_mul hτpow (hlen Z hZ1) (by positivity) (by positivity)
    _ = (Cd * Cl) * Z^(ε/16) := by
        rw [show (Cd * Z^(ε/32)) * (Cl * Z^(ε/32)) = (Cd * Cl) * (Z^(ε/32) * Z^(ε/32)) by ring,
          ← Real.rpow_add hZ0]
        ring_nf
    _ ≤ Z^(ε/16) * Z^(ε/16) := mul_le_mul_of_nonneg_right hZC (by positivity)
    _ = Z^(ε/8) := by rw [← Real.rpow_add hZ0]; ring_nf

end
end QRH.DensitySplitThird.CubeFree.Second.ConcreteGroup
