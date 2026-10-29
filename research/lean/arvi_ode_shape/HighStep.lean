/-
The marked HIGH gate of one step from its scalar facts (`StepFacts`) and the facet bound.

All quantities are reals; nothing here depends on the curve. With `A = 19/50`, `D = 100`,
`N = (999/1000) L₀ A`, `F = (6B₀ - L₀) A` and `q(v) = N/(h(1 + D v) + F)`:
* `q` decreases in `v`, `q(vmax) > 1/2`, `q(0) ≤ Q₀ = N/F < 3/4`, `q(0) - q(v) ≤ q(0) h D v/E₀`;
* the slope margin `m₀ = (L₀ - 1)(s - σ(q(0))) > 0`;
* the no-dip bound `A·C₁₂(Q₀) ≤ q(vmax)·β`;
* `Γ₁₂` is nondecreasing in `ν` (`gamma_nu_mono`) and `Γ₁₂(v, q(v)) ≥ q(vmax)·m₀` (`gamma_lower`).
-/
import Submissions.arvi_ode_shape.High

set_option autoImplicit false

namespace QRH.ArviOdeShape
open QRH.ArviDensity QRH.ArviDensity.Hybrid QRH.ArviUniformChain Set

section
variable {L0 B0 s h : ℝ}

/-- The density threshold of the step at excess `v`. -/
noncomputable def qd (L0 B0 h v : ℝ) : ℝ := dens B0 L0 (L0 - h) (19/50) 100 v

theorem qd_eq (v : ℝ) : qd L0 B0 h v =
    (999/1000 * L0 * (19/50)) / (h * (1 + 100 * v) + (6 * B0 - L0) * (19/50)) := by
  unfold qd dens; congr 1; ring

theorem E_pos (S : StepFacts L0 B0 s h) {v : ℝ} (hv : 0 ≤ v) :
    0 < h * (1 + 100 * v) + (6 * B0 - L0) * (19/50) := by
  have := S.six; have := S.h_pos
  have : 0 ≤ h * (1 + 100 * v) := by positivity
  linarith

theorem N_pos (S : StepFacts L0 B0 s h) : 0 < 999/1000 * L0 * (19/50) := by
  have := S.L_lo; positivity

theorem qd_anti (S : StepFacts L0 B0 s h) {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) :
    qd L0 B0 h w ≤ qd L0 B0 h v := by
  rw [qd_eq, qd_eq]
  apply div_le_div_of_nonneg_left (N_pos S).le (E_pos S hv)
  have := S.h_pos
  nlinarith

theorem qd_lo (S : StepFacts L0 B0 s h) : 1/2 < qd L0 B0 h (1/10 - s) := by
  rw [qd_eq, lt_div_iff₀ (E_pos S (by linarith [S.s_hi]))]
  have := S.floor
  nlinarith

theorem qd_hi (S : StepFacts L0 B0 s h) : qd L0 B0 h 0 < 3/4 := by
  rw [qd_eq, div_lt_iff₀ (E_pos S le_rfl)]
  have := S.up; have := S.h_pos
  nlinarith

/-- The ideal density `Q₀ = N/F`. -/
noncomputable def Q0 (L0 B0 : ℝ) : ℝ := (999/1000 * L0 * (19/50)) / ((6 * B0 - L0) * (19/50))

theorem qd_le_Q0 (S : StepFacts L0 B0 s h) : qd L0 B0 h 0 ≤ Q0 L0 B0 := by
  rw [qd_eq, Q0]
  apply div_le_div_of_nonneg_left (N_pos S).le (by nlinarith [S.six])
  have := S.h_pos; nlinarith

theorem Q0_lt (S : StepFacts L0 B0 s h) : Q0 L0 B0 < 3/4 := by
  rw [Q0, div_lt_iff₀ (by nlinarith [S.six])]
  nlinarith [S.up]

theorem qd_drop (S : StepFacts L0 B0 s h) {v : ℝ} (hv : 0 ≤ v) :
    qd L0 B0 h 0 - qd L0 B0 h v ≤
      qd L0 B0 h 0 * h * 100 * v / (h + (6 * B0 - L0) * (19/50)) := by
  have hE0 := E_pos S (le_refl 0)
  have hEv := E_pos S hv
  rw [mul_zero, add_zero, mul_one] at hE0
  rw [qd_eq, qd_eq]
  simp only [mul_zero, add_zero, mul_one]
  set N := 999/1000 * L0 * (19/50)
  set E0 := h + (6 * B0 - L0) * (19/50)
  set Ev := h * (1 + 100 * v) + (6 * B0 - L0) * (19/50)
  have hN := N_pos S
  have hd : N / E0 - N / Ev = N * (Ev - E0) / (E0 * Ev) := by field_simp
  rw [hd]
  have hEE : Ev - E0 = h * 100 * v := by simp only [Ev, E0]; ring
  rw [hEE]
  rw [div_le_div_iff₀ (by positivity) hE0]
  have hle : E0 ≤ Ev := by have := S.h_pos; nlinarith
  have : 0 ≤ N * (h * 100 * v) := by have := S.h_pos; positivity
  have key : N * (h * 100 * v) * E0 ≤ N * (h * 100 * v) * Ev := mul_le_mul_of_nonneg_left hle this
  calc N * (h * 100 * v) * E0 ≤ N * (h * 100 * v) * Ev := key
    _ = N / E0 * h * 100 * v * (E0 * Ev) := by field_simp

theorem sigma_margin (S : StepFacts L0 B0 s h) : 0 < s - sigmaOf B0 L0 (qd L0 B0 h 0) := by
  have hE0 := E_pos S (le_refl 0)
  rw [mul_zero, add_zero, mul_one] at hE0
  have hN := N_pos S
  set N := 999/1000 * L0 * (19/50) with hNdef
  set E0 := h + (6 * B0 - L0) * (19/50) with hE0def
  have hq0 : qd L0 B0 h 0 = N / E0 := by
    rw [qd_eq]; simp only [mul_zero, add_zero, mul_one, hNdef, hE0def]
  have hlt : N < 3/4 * E0 := by
    have := qd_hi S; rw [hq0, div_lt_iff₀ hE0] at this; linarith
  have hG : 0 < 25 * E0 - 18 * N := by linarith
  have hH : 0 < 5 * E0 - 6 * N := by linarith
  have hy : yOf (qd L0 B0 h 0) = (5 * E0 - 6 * N) / (25 * E0 - 18 * N) := by
    rw [yOf, hq0]
    have h1 : (25:ℝ) - 18 * (N / E0) = (25 * E0 - 18 * N) / E0 := by field_simp
    have h2 : (5:ℝ) - 6 * (N / E0) = (5 * E0 - 6 * N) / E0 := by field_simp
    rw [h1, h2, div_div_div_cancel_right₀ hE0.ne']
  have hL1 : 1 < L0 := by linarith [S.L_lo]
  have hm := S.m0
  have hm' : 0 < s * ((L0 - 1) * (25 * E0 - 18 * N) + (5 * E0 - 6 * N)) -
      ((B0 - 1) * (25 * E0 - 18 * N) + (5 * E0 - 6 * N)) := by
    have e : s * ((L0 - 1) * (25 * E0 - 18 * N) + (5 * E0 - 6 * N)) -
        ((B0 - 1) * (25 * E0 - 18 * N) + (5 * E0 - 6 * N)) =
        s * ((L0 - 1) * (25 * (h + 19/50 * (6 * B0 - L0)) - 18 * (999/1000 * (19/50) * L0)) +
          (5 * (h + 19/50 * (6 * B0 - L0)) - 6 * (999/1000 * (19/50) * L0))) -
        ((B0 - 1) * (25 * (h + 19/50 * (6 * B0 - L0)) - 18 * (999/1000 * (19/50) * L0)) +
          (5 * (h + 19/50 * (6 * B0 - L0)) - 6 * (999/1000 * (19/50) * L0))) := by
      simp only [hNdef, hE0def]; ring
    rw [e]; exact hm
  rw [sigmaOf, hy]
  set G := 25 * E0 - 18 * N
  set Hh := 5 * E0 - 6 * N
  have hden : 0 < L0 - 1 + Hh / G := by have := div_pos hH hG; linarith
  rw [sub_pos, div_lt_iff₀ hden]
  have key : s * (L0 - 1 + Hh / G) - (B0 - 1 + Hh / G) =
      (s * ((L0 - 1) * G + Hh) - ((B0 - 1) * G + Hh)) / G := by field_simp
  have := div_pos hm' hG
  linarith

/-- The Lipschitz bound of `σ` in the density (`Ksig_upper`). -/
noncomputable def Lsig (L0 B0 : ℝ) : ℝ := 60 * (L0 - B0) / ((23/2)^2 * (L0 - 22/23)^2)

theorem Lsig_nonneg (S : StepFacts L0 B0 s h) : 0 ≤ Lsig L0 B0 := by
  unfold Lsig
  exact div_nonneg (by nlinarith [S.B_hi, S.L_lo]) (by positivity)

theorem Lsig_mul_lt (S : StepFacts L0 B0 s h) : (L0 - 1) * Lsig L0 B0 < 1 := by
  unfold Lsig
  have h0 : 0 < L0 - 22/23 := by linarith [S.L_lo]
  have h1 : 0 < (23/2:ℝ)^2 * (L0 - 22/23)^2 := by positivity
  rw [← mul_div_assoc, div_lt_one h1]
  have := S.lsig; nlinarith

/-- The width coefficient `β` of the dip bound is at least `L₀ - 101/100`. -/
theorem beta_ge (S : StepFacts L0 B0 s h) :
    L0 - 101/100 ≤ (L0 - 1 - h) - (L0 - 1) * Lsig L0 B0 * qd L0 B0 h 0 * h * 100 /
      (h + (6 * B0 - L0) * (19/50)) := by
  have hE0 := E_pos S (le_refl 0)
  rw [mul_zero, add_zero, mul_one] at hE0
  have hq0 := qd_hi S
  have hq00 : 0 ≤ qd L0 B0 h 0 := by
    rw [qd_eq]; exact div_nonneg (N_pos S).le (E_pos S le_rfl).le
  have hLs := Lsig_nonneg S
  have hLm := Lsig_mul_lt S
  have hh := S.h_pos; have hh' := S.h_le; have h6 := S.six
  have hL1 : 0 < L0 - 1 := by linarith [S.L_lo]
  have hterm : (L0 - 1) * Lsig L0 B0 * qd L0 B0 h 0 * h * 100 / (h + (6 * B0 - L0) * (19/50)) ≤ 1/100 - h := by
    rw [div_le_iff₀ hE0]
    have a : (L0 - 1) * Lsig L0 B0 * qd L0 B0 h 0 ≤ 3/4 := by
      have : 0 ≤ (L0 - 1) * Lsig L0 B0 := mul_nonneg hL1.le hLs
      nlinarith
    have b : 0 ≤ (L0 - 1) * Lsig L0 B0 * qd L0 B0 h 0 := by positivity
    nlinarith
  linarith

theorem nodip_real (S : StepFacts L0 B0 s h) :
    19/50 * C12 B0 L0 (Q0 L0 B0) ≤ qd L0 B0 h (1/10 - s) * ((L0 - 1 - h) - (L0 - 1) * Lsig L0 B0 *
      qd L0 B0 h 0 * h * 100 / (h + (6 * B0 - L0) * (19/50))) := by
  have hN := N_pos S
  set N := 999/1000 * L0 * (19/50) with hNdef
  set F := (6 * B0 - L0) * (19/50) with hFdef
  have hF : 0 < F := by have := S.six; simp only [hFdef]; nlinarith
  have hQ : Q0 L0 B0 = N / F := rfl
  have hQlt : N < 3/4 * F := by have := Q0_lt S; rw [hQ, div_lt_iff₀ hF] at this; linarith
  have hXd : 0 < 20 * F - 12 * N := by linarith
  have hXn : 0 < 5 * F - 6 * N := by linarith
  have hL1 : 0 < L0 - 1 := by linarith [S.L_lo]
  have hx : xOf (Q0 L0 B0) = (5 * F - 6 * N) / (20 * F - 12 * N) := by
    rw [xOf, hQ]
    have h1 : (20:ℝ) - 12 * (N / F) = (20 * F - 12 * N) / F := by field_simp
    have h2 : (5:ℝ) - 6 * (N / F) = (5 * F - 6 * N) / F := by field_simp
    rw [h1, h2, div_div_div_cancel_right₀ hF.ne']
  set Xn := 5 * F - 6 * N
  set Xd := 20 * F - 12 * N
  set Rn := (L0 - 1) * Xd + Xn * B0
  set Rd := (L0 - 1) * Xd + Xn * L0
  have hRd : 0 < Rd := by have := S.L_lo; positivity
  have hR : ROf B0 L0 (Q0 L0 B0) = Rn / Rd := by
    have e1 : L0 - 1 + Xn / Xd * B0 = Rn / Xd := by
      simp only [Rn]; field_simp
    have e2 : L0 - 1 + Xn / Xd * L0 = Rd / Xd := by
      simp only [Rd]; field_simp
    rw [ROf, hx, e1, e2, div_div_div_cancel_right₀ hXd.ne']
  have hC : C12 B0 L0 (Q0 L0 B0) = (6 * N * Rn - N * Rd - F * Rd) / (F * Rd) := by
    rw [C12, hR, hQ]; field_simp
  have hnod := S.nodip
  have hnod' : 19/50 * (6 * N * Rn - N * Rd - F * Rd) * (F + 11/10000) < N * (L0 - 101/100) * F * Rd := by
    have e1 : 19/50 * (6 * N * Rn - N * Rd - F * Rd) * (F + 11/10000) =
      19/50 * ((6 * (999/1000 * (19/50) * L0 * ((L0 - 1) * (20 * (19/50 * (6 * B0 - L0)) -
        12 * (999/1000 * (19/50) * L0)) + (5 * (19/50 * (6 * B0 - L0)) - 6 * (999/1000 * (19/50) * L0)) * B0)) -
      999/1000 * (19/50) * L0 * ((L0 - 1) * (20 * (19/50 * (6 * B0 - L0)) - 12 * (999/1000 * (19/50) * L0)) +
        (5 * (19/50 * (6 * B0 - L0)) - 6 * (999/1000 * (19/50) * L0)) * L0) -
      19/50 * (6 * B0 - L0) * ((L0 - 1) * (20 * (19/50 * (6 * B0 - L0)) - 12 * (999/1000 * (19/50) * L0)) +
        (5 * (19/50 * (6 * B0 - L0)) - 6 * (999/1000 * (19/50) * L0)) * L0)) *
      (19/50 * (6 * B0 - L0) + 11/10000)) := by
      simp only [hNdef, hFdef, Rn, Rd, Xn, Xd]; ring
    have e2 : N * (L0 - 101/100) * F * Rd =
      999/1000 * (19/50) * L0 * (L0 - 101/100) * (19/50 * (6 * B0 - L0)) *
      ((L0 - 1) * (20 * (19/50 * (6 * B0 - L0)) - 12 * (999/1000 * (19/50) * L0)) +
        (5 * (19/50 * (6 * B0 - L0)) - 6 * (999/1000 * (19/50) * L0)) * L0) := by
      simp only [hNdef, hFdef, Rd, Xn, Xd]; ring
    rw [e1, e2]; exact hnod
  -- A·C12(Q₀) < q_min·(L₀ - 101/100) with q_min = N/(F + 11/10000)
  have hstep1 : 19/50 * C12 B0 L0 (Q0 L0 B0) ≤ N / (F + 11/10000) * (L0 - 101/100) := by
    rw [hC]
    have key : 19/50 * ((6 * N * Rn - N * Rd - F * Rd) / (F * Rd)) =
        (19/50 * (6 * N * Rn - N * Rd - F * Rd)) / (F * Rd) := by ring
    rw [key, div_le_iff₀ (by positivity)]
    have e : N / (F + 11/10000) * (L0 - 101/100) * (F * Rd) =
        N * (L0 - 101/100) * F * Rd / (F + 11/10000) := by field_simp
    rw [e, le_div_iff₀ (by positivity)]
    linarith [hnod']
  -- q_min ≤ q(vmax) and (L₀ - 101/100) ≤ β
  have hqmin : N / (F + 11/10000) ≤ qd L0 B0 h (1/10 - s) := by
    rw [qd_eq]
    apply div_le_div_of_nonneg_left hN.le (E_pos S (by linarith [S.s_hi]))
    have := S.h_pos; have := S.h_le; have := S.s_lo
    nlinarith
  have hβ := beta_ge S
  have hL101 : 0 ≤ L0 - 101/100 := by linarith [S.L_lo]
  calc 19/50 * C12 B0 L0 (Q0 L0 B0) ≤ N / (F + 11/10000) * (L0 - 101/100) := hstep1
    _ ≤ qd L0 B0 h (1/10 - s) * (L0 - 101/100) := mul_le_mul_of_nonneg_right hqmin hL101
    _ ≤ _ := mul_le_mul_of_nonneg_left hβ (by have := qd_lo S; linarith)

/-- The facet input at one step: on the gate's range the gain is at least facet `(1,2)` at `p = 1/2`. -/
def FacetInput (L0 B0 s h : ℝ) : Prop :=
  ∀ v, 0 ≤ v → v ≤ 1/10 - s → ∀ ν, qd L0 B0 h v ≤ ν → ν ≤ 3/4 →
    QRH.RepeatedMarks.facetVal ν (1/2) 8 B0 L0 (1/10) (s + v - sel (19/50) 100 v)
        (1 - 6 * sel (19/50) 100 v) ((1 : Fin 2), (2 : Fin 3)) ≤
      QRH.RepeatedMarks.Source.gainC ν B0 L0 (1/10) (s + v - sel (19/50) 100 v) (1 - 6 * sel (19/50) 100 v)

set_option maxHeartbeats 1000000 in
/-- **The marked HIGH gate of one step** from its scalar facts and the facet input, with the reserve
`q(vmax)·(L₀ - 1)(s - σ(q(0)))`. -/
theorem high_of_stepFacts (S : StepFacts L0 B0 s h) (hfac : FacetInput L0 B0 s h) :
    ∃ r : ℝ, 0 < r ∧ ∀ v, 0 ≤ v → v ≤ 1/10 - s → ∀ ν, qd L0 B0 h v ≤ ν → ν ≤ 3/4 →
      r ≤ highJ (B0 - s * h) (L0 - h) (s + v) (sel (19/50) 100 v) ν +
        QRH.RepeatedMarks.Source.gainC ν B0 L0 (1/10) (s + v - sel (19/50) 100 v) (packed (19/50) 100 v) := by
  have hL1 : 1 < L0 := by linarith [S.L_lo]
  have hL3 : L0 ≤ 3 := by linarith [S.L_hi]
  have hB0 : 22/23 ≤ B0 := S.B_lo.le
  have hBL : B0 ≤ L0 := by linarith [S.B_hi, S.L_lo]
  have hh0 := S.h_pos
  have hqlo := qd_lo S
  have hq0 := qd_hi S
  have hE0 := E_pos S (le_refl 0)
  rw [mul_zero, add_zero, mul_one] at hE0
  have hm := sigma_margin S
  have hq0lo : qd L0 B0 h (1/10 - s) ≤ qd L0 B0 h 0 := qd_anti S le_rfl (by linarith [S.s_hi])
  set qlo := qd L0 B0 h (1/10 - s)
  set q0 := qd L0 B0 h 0
  set σ0 := sigmaOf B0 L0 q0
  have hq01 : 1/2 ≤ q0 := by linarith
  refine ⟨qlo * ((L0 - 1) * (s - σ0)), mul_pos (by linarith) (mul_pos (by linarith) hm), ?_⟩
  intro v hv0 hv1 ν hν0 hν1
  set u := sel (19/50) 100 v with hu_def
  have hden : 0 < 1 + 100 * v := by linarith
  have hu0 : 0 ≤ u := by simp only [hu_def, sel]; positivity
  have huA : u ≤ 19/50 * v := by
    simp only [hu_def, sel]; rw [div_le_iff₀ hden]; nlinarith
  have hu1 : u ≤ 19/5000 := by
    simp only [hu_def, sel]; rw [div_le_iff₀ hden]; nlinarith
  set qv := qd L0 B0 h v
  have hqv_lo : qlo ≤ qv := qd_anti S hv0 hv1
  have hqv_hi : qv ≤ q0 := qd_anti S le_rfl hv0
  have hqv1 : 1/2 ≤ qv := by linarith
  have hqv3 : qv ≤ 3/4 := by linarith
  have hν12 : 1/2 ≤ ν := by linarith
  -- the facet bound and the binding-pair identity
  have hg := hfac v hv0 hv1 ν hν0 hν1
  have heq := gamma12_eq (B0 := B0) (L0 := L0) (h := h) (s0 := s) (v := v) (u := u) (ν := ν) (h0 := 1/10)
    hν12 hν1 hL1
  -- σ at q(v): within Lσ (q₀ - q(v)) of σ₀
  have hLs := Lsig_nonneg S
  have hσv : sigmaOf B0 L0 qv ≤ σ0 + Lsig L0 B0 * (q0 - qv) := by
    have e := sigmaOf_sub (B0 := B0) hL1 hqv1 hqv3 hq01 hq0.le
    have k := Ksig_upper (B0 := B0) hL1 hBL hqv1 hqv3 hq01 hq0.le
    have hd : 0 ≤ q0 - qv := by linarith
    have : (q0 - qv) * Ksig B0 L0 qv q0 ≤ (q0 - qv) * Lsig L0 B0 := mul_le_mul_of_nonneg_left k hd
    simp only [σ0]; nlinarith
  have hdrop := qd_drop S hv0
  -- ν-monotonicity
  have hKlow := Ksig_lower (B0 := B0) hL1 hBL hqv1 hqv3 hν12 hν1
  have hKup := KR_upper (B0 := B0) hL1 hBL hqv1 hqv3 hν12 hν1
  have hKR0 := KR_nonneg (B0 := B0) hL1 hBL hqv1 hqv3 hν12 hν1
  have hLB : 0 ≤ 60 * (L0 - B0) / (256 * (L0 - 7/8)^2) := by
    apply div_nonneg <;> nlinarith
  have hKσ : (L0 - 1) * (1/2) * (60 * (L0 - B0) / (256 * (L0 - 7/8)^2)) ≤
      (L0 - 1) * qv * Ksig B0 L0 qv ν := by
    have a : (1/2) * (60 * (L0 - B0) / (256 * (L0 - 7/8)^2)) ≤ qv * Ksig B0 L0 qv ν :=
      mul_le_mul hqv1 hKlow hLB (by linarith)
    have := mul_le_mul_of_nonneg_left a (by linarith : (0:ℝ) ≤ L0 - 1)
    linarith
  have hKR : 6 * qv * KR B0 L0 qv ν ≤ 4 := by
    have hkr := S.kr
    have b : KR B0 L0 qv ν ≤ 60 * (L0 - B0) / (121 * (L0 - 1)) := hKup
    have c : 60 * (L0 - B0) / (121 * (L0 - 1)) ≤ 8/9 := by
      rw [div_le_iff₀ (by nlinarith)]; nlinarith
    nlinarith
  have hσν : sigmaOf B0 L0 ν ≤ sigmaOf B0 L0 qv := by
    have e := sigmaOf_sub (B0 := B0) hL1 hqv1 hqv3 hν12 hν1
    have : 0 ≤ (ν - qv) * Ksig B0 L0 qv ν := mul_nonneg (by linarith) (le_trans hLB hKlow)
    linarith
  have hLm := Lsig_mul_lt S
  have he : -(1/100) ≤ (L0 - 1) * (s - sigmaOf B0 L0 ν) := by
    have hhle := S.h_le
    have hv' : v ≤ 1/10 := by linarith [S.s_lo]
    have hq0n : 0 ≤ q0 := by linarith
    have hqd : q0 - qv ≤ 3/4 * (1/10000) * 100 * (1/10) / (3 * (19/50)) := by
      have k1 : q0 * h ≤ 3/4 * (1/10000) := mul_le_mul hq0.le hhle hh0.le (by norm_num)
      have k2 : q0 * h * 100 * v ≤ 3/4 * (1/10000) * 100 * (1/10) := by
        have : 0 ≤ q0 * h := mul_nonneg hq0n hh0.le
        have k3 : q0 * h * 100 * v ≤ 3/4 * (1/10000) * 100 * v := by nlinarith
        nlinarith
      have k4 : q0 * h * 100 * v / (h + (6 * B0 - L0) * (19/50)) ≤
          3/4 * (1/10000) * 100 * (1/10) / (3 * (19/50)) := by
        rw [div_le_div_iff₀ hE0 (by norm_num)]
        have := S.six
        have : 0 ≤ q0 * h * 100 * v := by positivity
        nlinarith
      linarith [hdrop]
    have hpos : 0 ≤ (L0 - 1) * Lsig L0 B0 := mul_nonneg (by linarith) hLs
    have hd : 0 ≤ q0 - qv := by linarith
    have hterm : (L0 - 1) * Lsig L0 B0 * (q0 - qv) ≤ 1/100 := by
      have : (L0 - 1) * Lsig L0 B0 * (q0 - qv) ≤ 1 * (q0 - qv) :=
        mul_le_mul_of_nonneg_right hLm.le hd
      linarith
    have a1 : (L0 - 1) * (s - sigmaOf B0 L0 qv) ≤ (L0 - 1) * (s - sigmaOf B0 L0 ν) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have a2 : (L0 - 1) * (sigmaOf B0 L0 qv - σ0) ≤ (L0 - 1) * Lsig L0 B0 * (q0 - qv) := by
      have := mul_le_mul_of_nonneg_left (show sigmaOf B0 L0 qv - σ0 ≤ Lsig L0 B0 * (q0 - qv) by linarith)
        (by linarith : (0:ℝ) ≤ L0 - 1)
      linarith [show (L0 - 1) * (Lsig L0 B0 * (q0 - qv)) = (L0 - 1) * Lsig L0 B0 * (q0 - qv) by ring]
    have a3 : 0 ≤ (L0 - 1) * (s - σ0) := mul_nonneg (by linarith) hm.le
    have id : (L0 - 1) * (s - sigmaOf B0 L0 qv) = (L0 - 1) * (s - σ0) - (L0 - 1) * (sigmaOf B0 L0 qv - σ0) := by
      ring
    linarith
  have hcond : 1/100 + 19/5000 * (5 + 4) ≤ (L0 - 1) * (1/2) * (60 * (L0 - B0) / (256 * (L0 - 7/8)^2)) := by
    have hn := S.nmono
    have hp : 0 < 256 * (L0 - 7/8)^2 := by
      have h78 : 0 < L0 - 7/8 := by linarith
      positivity
    rw [show (L0 - 1) * (1/2) * (60 * (L0 - B0) / (256 * (L0 - 7/8)^2)) =
      (30 * ((L0 - 1) * (L0 - B0))) / (256 * (L0 - 7/8)^2) by ring, le_div_iff₀ hp]
    nlinarith
  have hmono := gamma_nu_mono (L0 := L0) (h := h) (s0 := s) (v := v) (u := u) (q := qv) (ν := ν)
    (σq := sigmaOf B0 L0 qv) (σν := sigmaOf B0 L0 ν) (Rq := ROf B0 L0 qv) (Rν := ROf B0 L0 ν)
    (Kσ := Ksig B0 L0 qv ν) (KR := KR B0 L0 qv ν) (e := 1/100)
    (Klo := (L0 - 1) * (1/2) * (60 * (L0 - B0) / (256 * (L0 - 7/8)^2))) (KRhi := 4) (umax := 19/5000)
    hν0 (sigmaOf_sub hL1 hqv1 hqv3 hν12 hν1) (ROf_sub hL1 hqv1 hqv3 hν12 hν1)
    (ROf_le_one hL1 hBL hν12 hν1) hKσ hKR0 hKR hu0 hu1 hv0 (by linarith [S.h_le, S.L_lo]) he hcond (by norm_num)
  -- the dip bound
  have hlow := gamma_lower (L0 := L0) (h := h) (s0 := s) (v := v) (u := u) (qv := qv) (q_lo := qlo) (q0 := q0)
    (σv := sigmaOf B0 L0 qv) (σ0 := σ0) (Ls := Lsig L0 B0) (Cv := C12 B0 L0 qv)
    (C0 := C12 B0 L0 (Q0 L0 B0)) (A := 19/50) (D := 100) (E0 := h + (6 * B0 - L0) * (19/50))
    hL1 hh0.le hv0 hu0 huA hqv_lo (by linarith) hqv_hi hLs hσv hE0 (by linarith) (by norm_num) hdrop
    (C12_nonneg hL1 hL3 hB0 hqv1 hqv3) (C12_mono hL1 hL3 hB0 hBL hqv1 (hqv_hi.trans (qd_le_Q0 S)) (Q0_lt S).le)
    (mul_nonneg (by linarith) hm.le) (le_trans (by linarith [S.L_lo]) (beta_ge S)) (nodip_real S)
  -- combine
  have hpk : packed (19/50) 100 v = 1 - 6 * u := rfl
  rw [hpk]
  have hg12 : gamma12 B0 L0 h s v u ν = ν * (L0 - 1) * (s - sigmaOf B0 L0 ν) + ν * (L0 - 1 - h) * v -
      u * (6 * ν * ROf B0 L0 ν - ν - 1) := by unfold gamma12 C12; ring
  have hgq : qv * (L0 - 1) * (s - sigmaOf B0 L0 qv) + qv * (L0 - 1 - h) * v - u * C12 B0 L0 qv =
      qv * (L0 - 1) * (s - sigmaOf B0 L0 qv) + qv * (L0 - 1 - h) * v - u * (6 * qv * ROf B0 L0 qv - qv - 1) := by
    unfold C12; ring
  linarith [hg, heq, hmono, hlow, hg12, hgq]

end

end QRH.ArviOdeShape

#print axioms QRH.ArviOdeShape.high_of_stepFacts
