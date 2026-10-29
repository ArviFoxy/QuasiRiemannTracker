/-
The facet input along the curve (`FacetsAll`): from the kernel facts of `FacetFacts.lean` and the facet
reduction `facets_ge_facet12_of_N10` (`FacetForms.lean`).
-/
import Submissions.arvi_ode_shape.FacetFacts
import Submissions.arvi_ode_shape.Final
import Submissions.arvi_uniform_chain.FacetForms

set_option autoImplicit false

namespace QRH.ArviOdeShape
open QRH.ArviReturnTuning QRH.ArviDensity QRH.ArviDensity.Hybrid QRH.ArviUniformChain Set
open OAI OAI.SevenEighths

theorem posBox_ev01 {P : Q2} {k : ℕ} (hP : posBox P k (-1) 1 0 1 = true) {t z : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) : 0 < Q2.ev P t z :=
  posBox_sound P k _ _ _ _ hP (by push_cast; exact ht.1) (by push_cast; exact ht.2)
    (by push_cast; exact hz0) (by push_cast; exact hz1)

/-- N₁₀ from its cleared form, with `ν = νn/D`. -/
theorem n10_real {sl N D z ν : ℝ} (hD : 0 < D) (hz : N + z * (3/4 * D - N) = ν * D)
    (h : 0 < 5 * (sl * ((5 * D - 6 * (N + z * (3/4 * D - N))) * (5 * D - 6 * (N + z * (3/4 * D - N))) +
      5 * ((5 * D - 6 * (N + z * (3/4 * D - N))) * D) + 10 * (D * D))) -
      2 * ((5 * D - 6 * (N + z * (3/4 * D - N))) * (5 * D - 6 * (N + z * (3/4 * D - N))))) :
    2 * (5 - 6*ν)^2 < 5 * sl * ((5 - 6*ν)^2 + 5*(5 - 6*ν) + 10) := by
  rw [hz] at h
  have e : 5 * (sl * ((5 * D - 6 * (ν * D)) * (5 * D - 6 * (ν * D)) + 5 * ((5 * D - 6 * (ν * D)) * D) +
      10 * (D * D))) - 2 * ((5 * D - 6 * (ν * D)) * (5 * D - 6 * (ν * D))) =
      D^2 * (5 * sl * ((5 - 6*ν)^2 + 5*(5 - 6*ν) + 10) - 2 * (5 - 6*ν)^2) := by ring
  rw [e] at h
  have := pos_of_mul_pos_right h (by positivity)
  linarith

/-- P₁₂ from its cleared form. -/
theorem p12_real {sl N D z ν L0 B0 : ℝ} (hD : 0 < D) (hz : N + z * (3/4 * D - N) = ν * D)
    (h : 0 < sl * (((L0 - 1) * (25 * D - 18 * (N + z * (3/4 * D - N))) + (5 * D - 6 * (N + z * (3/4 * D - N)))) *
        ((L0 - 1) * (25 * D - 18 * (N + z * (3/4 * D - N))) + (5 * D - 6 * (N + z * (3/4 * D - N))))) +
      (5 * D - 6 * (N + z * (3/4 * D - N))) *
        ((5 * D - 6 * (N + z * (3/4 * D - N))) * (B0 * L0 - 4 * B0 - 4 * (L0 * L0) + 6 * L0) +
          10 * (L0 * (1 - B0)) * D)) :
    0 < sl * ((L0-1)*(25-18*ν) + (5-6*ν))^2 + (5-6*ν) * (B0*L0*(5-6*ν) - 10*B0*L0 -
        4*B0*(5-6*ν) - 4*L0^2*(5-6*ν) + 6*L0*(5-6*ν) + 10*L0) := by
  rw [hz] at h
  have e : sl * (((L0 - 1) * (25 * D - 18 * (ν * D)) + (5 * D - 6 * (ν * D))) *
        ((L0 - 1) * (25 * D - 18 * (ν * D)) + (5 * D - 6 * (ν * D)))) +
      (5 * D - 6 * (ν * D)) * ((5 * D - 6 * (ν * D)) * (B0 * L0 - 4 * B0 - 4 * (L0 * L0) + 6 * L0) +
          10 * (L0 * (1 - B0)) * D) =
      D^2 * (sl * ((L0-1)*(25-18*ν) + (5-6*ν))^2 + (5-6*ν) * (B0*L0*(5-6*ν) - 10*B0*L0 -
        4*B0*(5-6*ν) - 4*L0^2*(5-6*ν) + 6*L0*(5-6*ν) + 10*L0)) := by ring
  rw [e] at h
  exact pos_of_mul_pos_right h (by positivity)

theorem qmin_le {L0 B0 s h : ℝ} (S : StepFacts L0 B0 s h) :
    (999/1000 * L0 * (19/50)) / ((6 * B0 - L0) * (19/50) + 11/10000) ≤ qd L0 B0 h (1/10 - s) := by
  rw [qd_eq]
  apply div_le_div_of_nonneg_left (N_pos S).le (E_pos S (by linarith [S.s_hi]))
  have := S.h_pos; have := S.h_le; have := S.s_lo
  nlinarith

/-- The slope lower bound does not depend on the second variable. -/
theorem ev_slQ (t a b : ℝ) : Q2.ev slQ t a = Q2.ev slQ t b := by
  simp only [slQ, Q2.ev_sub, ev_ofQ1X, Q2.ev_C]

/-- The density drop over the excess is tiny: `q(0) - q(v) ≤ v/100`. -/
theorem qd_drop_small {L0 B0 s h v : ℝ} (S : StepFacts L0 B0 s h) (hv : 0 ≤ v) :
    qd L0 B0 h 0 - qd L0 B0 h v ≤ v / 100 := by
  have hdrop := qd_drop S hv
  have hE0 := E_pos S (le_refl 0)
  rw [mul_zero, add_zero, mul_one] at hE0
  have hq0 := qd_hi S
  have hq00 : 0 ≤ qd L0 B0 h 0 := by rw [qd_eq]; exact div_nonneg (N_pos S).le (E_pos S le_rfl).le
  have h6 := S.six
  have hh := S.h_pos
  have hhl := S.h_le
  have hE1 : 114/100 ≤ h + (6 * B0 - L0) * (19/50) := by linarith
  have b1 : qd L0 B0 h 0 * h ≤ 3/4 * (1/10000) := mul_le_mul hq0.le hhl hh.le (by norm_num)
  have b2 : qd L0 B0 h 0 * h * 100 * v ≤ 3/4 * (1/10000) * 100 * v := by
    have := mul_le_mul_of_nonneg_right b1 (by positivity : (0:ℝ) ≤ 100 * v)
    linarith [show qd L0 B0 h 0 * h * 100 * v = qd L0 B0 h 0 * h * (100 * v) by ring,
      show 3/4 * (1/10000) * 100 * v = 3/4 * (1/10000) * (100 * v) by ring]
  have b3 : qd L0 B0 h 0 * h * 100 * v / (h + (6 * B0 - L0) * (19/50)) ≤ v / 100 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    have : 0 ≤ qd L0 B0 h 0 * h * 100 * v := by positivity
    nlinarith
  linarith

/-- The facet order `Q σ(ν) ≤ S` at the point `S = s + v - u`, `Q = 1 - 6u` of the gate. -/
theorem facet_order {L0 B0 s h v ν : ℝ} (S : StepFacts L0 B0 s h) (hv0 : 0 ≤ v) (hv1 : v ≤ 1/10 - s)
    (hν0 : qd L0 B0 h v ≤ ν) (hν1 : ν ≤ 3/4) :
    (1 - 6 * sel (19/50) 100 v) * (B0 - 1 + yOf ν) ≤ (s + v - sel (19/50) 100 v) * (L0 - 1 + yOf ν) := by
  have hL1 : 1 < L0 := by linarith [S.L_lo]
  have hBL : B0 ≤ L0 := by linarith [S.B_hi, S.L_lo]
  have hqv_lo : qd L0 B0 h (1/10 - s) ≤ qd L0 B0 h v := qd_anti S hv0 hv1
  have hqv_hi : qd L0 B0 h v ≤ qd L0 B0 h 0 := qd_anti S le_rfl hv0
  have hqlo := qd_lo S
  have hq0 := qd_hi S
  have hν12 : 1/2 ≤ ν := by linarith
  have hqv1 : 1/2 ≤ qd L0 B0 h v := by linarith
  have hqv3 : qd L0 B0 h v ≤ 3/4 := by linarith
  have hq01 : 1/2 ≤ qd L0 B0 h 0 := by linarith
  -- σ(ν) ≤ σ(q(v))
  have e1 := sigmaOf_sub (B0 := B0) hL1 hqv1 hqv3 hν12 hν1
  have k1 := Ksig_lower (B0 := B0) hL1 hBL hqv1 hqv3 hν12 hν1
  have hLB : 0 ≤ 60 * (L0 - B0) / (256 * (L0 - 7/8)^2) :=
    div_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)
  have hσνq : sigmaOf B0 L0 ν ≤ sigmaOf B0 L0 (qd L0 B0 h v) := by
    have : 0 ≤ (ν - qd L0 B0 h v) * Ksig B0 L0 (qd L0 B0 h v) ν := mul_nonneg (by linarith) (le_trans hLB k1)
    linarith
  -- σ(q(v)) ≤ σ(q₀) + Lσ (q₀ - q(v)) ≤ σ(q₀) + v/50
  have e2 := sigmaOf_sub (B0 := B0) hL1 hqv1 hqv3 hq01 hq0.le
  have k2 := Ksig_upper (B0 := B0) hL1 hBL hqv1 hqv3 hq01 hq0.le
  have hd : 0 ≤ qd L0 B0 h 0 - qd L0 B0 h v := by linarith
  have hLm := Lsig_mul_lt S
  have hLs := Lsig_nonneg S
  have hLs2 : Lsig L0 B0 ≤ 2 := by
    by_contra hc
    have : 2 < Lsig L0 B0 := lt_of_not_ge hc
    have : (L0 - 1) * 2 < (L0 - 1) * Lsig L0 B0 := mul_lt_mul_of_pos_left this (by linarith [S.L_lo])
    linarith [S.L_lo]
  have hsmall := qd_drop_small S hv0
  have hσq : sigmaOf B0 L0 (qd L0 B0 h v) ≤ sigmaOf B0 L0 (qd L0 B0 h 0) + v / 50 := by
    have a : (qd L0 B0 h 0 - qd L0 B0 h v) * Ksig B0 L0 (qd L0 B0 h v) (qd L0 B0 h 0) ≤
        (qd L0 B0 h 0 - qd L0 B0 h v) * Lsig L0 B0 := by
      apply mul_le_mul_of_nonneg_left _ hd; simpa [Lsig] using k2
    have b : (qd L0 B0 h 0 - qd L0 B0 h v) * Lsig L0 B0 ≤ (v / 100) * 2 :=
      mul_le_mul hsmall hLs2 hLs (by positivity)
    linarith
  have hm := sigma_margin S
  -- S - σ(ν) ≥ (s - σ₀) + v (1 - 19/50 - 1/50) ≥ 0
  have hu : sel (19/50) 100 v ≤ 19/50 * v := by
    unfold sel; rw [div_le_iff₀ (by linarith)]; nlinarith
  have hu0 : 0 ≤ sel (19/50) 100 v := by unfold sel; apply div_nonneg <;> nlinarith
  have hSσ : sigmaOf B0 L0 ν ≤ s + v - sel (19/50) 100 v := by linarith
  have hσ0 : 0 ≤ sigmaOf B0 L0 ν := by
    obtain ⟨y1, y2⟩ := yOf_bounds ν hν12 hν1
    unfold sigmaOf; apply div_nonneg <;> linarith [S.B_lo]
  have hQ1 : 1 - 6 * sel (19/50) 100 v ≤ 1 := by linarith
  have hQ0 : 0 ≤ 1 - 6 * sel (19/50) 100 v := by
    have : sel (19/50) 100 v ≤ 19/5000 := by unfold sel; rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hQσ : (1 - 6 * sel (19/50) 100 v) * sigmaOf B0 L0 ν ≤ s + v - sel (19/50) 100 v := by
    have : (1 - 6 * sel (19/50) 100 v) * sigmaOf B0 L0 ν ≤ 1 * sigmaOf B0 L0 ν :=
      mul_le_mul_of_nonneg_right hQ1 hσ0
    linarith
  obtain ⟨y1, y2⟩ := yOf_bounds ν hν12 hν1
  have hpos : 0 < L0 - 1 + yOf ν := by linarith
  unfold sigmaOf at hQσ
  rw [mul_div_assoc', div_le_iff₀ hpos] at hQσ
  exact hQσ

set_option maxHeartbeats 2000000 in
/-- **The facet input of every step along the curve.** -/
theorem facetInput_curve {t h : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (hh : 0 < h) (hh' : h ≤ hmax) :
    FacetInput (Lr t) (Br t) (Sr t h) h := by
  have S := stepFacts ht hh hh'
  have hch := posBox_ev chordSlQ_pos ht hh.le hh'
  simp only [chordSlQ, Q2.ev_sub, ev_chordQ'] at hch
  set L0 := Lr t with hL0def
  set B0 := Br t with hB0def
  set s := Sr t h with hsdef
  set sl := Q2.ev slQ t h with hsldef
  have hL1 : 1 < L0 := by linarith [S.L_lo]
  have hL3 : L0 ≤ 3 := by linarith [S.L_hi]
  have hBL : B0 ≤ L0 := by linarith [S.B_hi, S.L_lo]
  intro v hv0 hv1 ν hν0 hν1
  set u := sel (19/50) 100 v with hu_def
  have hden : 0 < 1 + 100 * v := by linarith
  have hu0 : 0 ≤ u := by simp only [hu_def, sel]; positivity
  have huA : u ≤ 19/50 * v := by simp only [hu_def, sel]; rw [div_le_iff₀ hden]; nlinarith
  have hu1 : u ≤ 19/5000 := by simp only [hu_def, sel]; rw [div_le_iff₀ hden]; nlinarith
  -- densities: q_min ≤ q(vmax) ≤ q(v) ≤ ν ≤ 3/4
  have hqmin := qmin_le S
  have hqv_lo : qd L0 B0 h (1/10 - s) ≤ qd L0 B0 h v := qd_anti S hv0 hv1
  have hqv_hi : qd L0 B0 h v ≤ qd L0 B0 h 0 := qd_anti S le_rfl hv0
  have hqlo := qd_lo S
  have hq0 := qd_hi S
  have hν12 : 1/2 ≤ ν := by linarith
  -- the normalised variable z of the facts
  set N := 999/1000 * L0 * (19/50) with hNdef
  set Dv := (6 * B0 - L0) * (19/50) + 11/10000 with hDvdef
  have hDv : 0 < Dv := by have := S.six; simp only [hDvdef]; nlinarith
  have hNpos : 0 < N := N_pos S
  have hNle : N ≤ ν * Dv := by
    have : N / Dv ≤ ν := by linarith
    rwa [div_le_iff₀ hDv] at this
  have hgap : 0 < 3/4 * Dv - N := by
    have : N / Dv < 3/4 := by linarith
    rw [div_lt_iff₀ hDv] at this; linarith
  set z := (ν * Dv - N) / (3/4 * Dv - N) with hzdef
  have hz0 : 0 ≤ z := div_nonneg (by linarith) hgap.le
  have hz1 : z ≤ 1 := by rw [div_le_one hgap]; nlinarith
  have hz : N + z * (3/4 * Dv - N) = ν * Dv := by
    rw [hzdef, div_mul_cancel₀ _ hgap.ne']; ring
  -- the two facts at (t, z)
  have h10 := posBox_ev01 p10Q_pos ht hz0 hz1
  have h12 := posBox_ev01 p12Q_pos ht hz0 hz1
  have eN : Q2.ev NQ t z = N := by
    simp only [NQ, Q2.ev_smul, ev_LQ', hNdef, hL0def]; push_cast; ring
  have eD : Q2.ev DqQ t z = Dv := by
    simp only [DqQ, FQ, Q2.ev_add, Q2.ev_smul, Q2.ev_sub, Q2.ev_C, ev_LQ', ev_BQ', hDvdef, hL0def, hB0def]
    push_cast; ring
  have eνn : Q2.ev νnQ t z = N + z * (3/4 * Dv - N) := by
    simp only [νnQ, Q2.ev_add, Q2.ev_mul, Q2.ev_Y, Q2.ev_sub, Q2.ev_smul, eN, eD]; push_cast; ring
  have ew : Q2.ev wnQ t z = 5 * Dv - 6 * (N + z * (3/4 * Dv - N)) := by
    simp only [wnQ, Q2.ev_sub, Q2.ev_smul, eD, eνn]; push_cast; ring
  have esl : Q2.ev slQ t z = sl := ev_slQ t z h
  have h10' : 0 < 5 * (sl * ((5 * Dv - 6 * (N + z * (3/4 * Dv - N))) * (5 * Dv - 6 * (N + z * (3/4 * Dv - N))) +
      5 * ((5 * Dv - 6 * (N + z * (3/4 * Dv - N))) * Dv) + 10 * (Dv * Dv))) -
      2 * ((5 * Dv - 6 * (N + z * (3/4 * Dv - N))) * (5 * Dv - 6 * (N + z * (3/4 * Dv - N)))) := by
    have e : Q2.ev p10Q t z = 5 * (sl * ((5 * Dv - 6 * (N + z * (3/4 * Dv - N))) * (5 * Dv - 6 * (N + z * (3/4 * Dv - N))) +
      5 * ((5 * Dv - 6 * (N + z * (3/4 * Dv - N))) * Dv) + 10 * (Dv * Dv))) -
      2 * ((5 * Dv - 6 * (N + z * (3/4 * Dv - N))) * (5 * Dv - 6 * (N + z * (3/4 * Dv - N)))) := by
      simp only [p10Q, Q2.ev_add, Q2.ev_sub, Q2.ev_mul, Q2.ev_smul, ew, eD, esl]; push_cast; ring
    rw [← e]; exact h10
  have h12' : 0 < sl * (((L0 - 1) * (25 * Dv - 18 * (N + z * (3/4 * Dv - N))) + (5 * Dv - 6 * (N + z * (3/4 * Dv - N)))) *
        ((L0 - 1) * (25 * Dv - 18 * (N + z * (3/4 * Dv - N))) + (5 * Dv - 6 * (N + z * (3/4 * Dv - N))))) +
      (5 * Dv - 6 * (N + z * (3/4 * Dv - N))) *
        ((5 * Dv - 6 * (N + z * (3/4 * Dv - N))) * (B0 * L0 - 4 * B0 - 4 * (L0 * L0) + 6 * L0) +
          10 * (L0 * (1 - B0)) * Dv) := by
    have e : Q2.ev p12Q t z = sl * (((L0 - 1) * (25 * Dv - 18 * (N + z * (3/4 * Dv - N))) + (5 * Dv - 6 * (N + z * (3/4 * Dv - N)))) *
        ((L0 - 1) * (25 * Dv - 18 * (N + z * (3/4 * Dv - N))) + (5 * Dv - 6 * (N + z * (3/4 * Dv - N))))) +
      (5 * Dv - 6 * (N + z * (3/4 * Dv - N))) *
        ((5 * Dv - 6 * (N + z * (3/4 * Dv - N))) * (B0 * L0 - 4 * B0 - 4 * (L0 * L0) + 6 * L0) +
          10 * (L0 * (1 - B0)) * Dv) := by
      simp only [p12Q, DLnQ, EnQ, Q2.ev_add, Q2.ev_sub, Q2.ev_mul, Q2.ev_smul, Q2.ev_C, ew, eD, eνn, esl,
        ev_LQ', ev_BQ']
      push_cast; ring
    rw [← e]; exact h12
  have hn10 := n10_real hDv hz h10'
  have hp12 := p12_real hDv hz h12'
  -- the facet point S = s + v - u, Q = 1 - 6u
  set Sv := s + v - u with hSvdef
  set Qv := 1 - 6 * u with hQvdef
  have hSsl : sl ≤ Sv := by linarith [hch, huA, hv0]
  have hSv0 : 1/50 ≤ Sv := by linarith [S.s_lo, huA, hv0]
  have hSv1 : Sv ≤ 1/10 := by linarith
  have hQv0 : 9/10 ≤ Qv := by linarith
  have hQv1 : Qv ≤ 1 := by linarith
  have hSQ : Sv ≤ Qv / 10 := by linarith
  have hσν : Qv * (B0 - 1 + yOf ν) ≤ Sv * (L0 - 1 + yOf ν) := facet_order S hv0 hv1 hν0 hν1
  -- the facet conditions at (ν, Sv, Qv)
  have hw : 0 ≤ 5 - 6*ν := by linarith
  have hN10 : 2 * Qv * (5 - 6*ν)^2 ≤ 5 * Sv * ((5 - 6*ν)^2 + 5*(5 - 6*ν) + 10) := by
    have hb : 0 < (5 - 6*ν)^2 + 5*(5 - 6*ν) + 10 := by positivity
    have a : Qv * (5 - 6*ν)^2 ≤ 1 * (5 - 6*ν)^2 := mul_le_mul_of_nonneg_right hQv1 (sq_nonneg _)
    have c : sl * ((5 - 6*ν)^2 + 5*(5 - 6*ν) + 10) ≤ Sv * ((5 - 6*ν)^2 + 5*(5 - 6*ν) + 10) :=
      mul_le_mul_of_nonneg_right hSsl hb.le
    have e1 : 2 * Qv * (5 - 6*ν)^2 = 2 * (Qv * (5 - 6*ν)^2) := by ring
    have e2 : 5 * Sv * ((5 - 6*ν)^2 + 5*(5 - 6*ν) + 10) = 5 * (Sv * ((5 - 6*ν)^2 + 5*(5 - 6*ν) + 10)) := by ring
    have e3 : 5 * sl * ((5 - 6*ν)^2 + 5*(5 - 6*ν) + 10) = 5 * (sl * ((5 - 6*ν)^2 + 5*(5 - 6*ν) + 10)) := by ring
    rw [e1, e2]
    rw [e3] at hn10
    linarith only [a, c, hn10]
  have hP12 : 0 ≤ Sv * ((L0-1)*(25-18*ν) + (5-6*ν))^2 + (5-6*ν) * Qv * (B0*L0*(5-6*ν) - 10*B0*L0 -
      4*B0*(5-6*ν) - 4*L0^2*(5-6*ν) + 6*L0*(5-6*ν) + 10*L0) := by
    set E := B0*L0*(5-6*ν) - 10*B0*L0 - 4*B0*(5-6*ν) - 4*L0^2*(5-6*ν) + 6*L0*(5-6*ν) + 10*L0 with hEdef
    set DL2 := ((L0-1)*(25-18*ν) + (5-6*ν))^2 with hDLdef
    have hDL2 : 0 ≤ DL2 := sq_nonneg _
    have hSv0' : 0 ≤ Sv := by linarith only [hSv0]
    rcases le_total 0 E with hE | hE
    · have a : 0 ≤ (5 - 6*ν) * Qv * E := mul_nonneg (mul_nonneg hw (by linarith only [hQv0])) hE
      have b : 0 ≤ Sv * DL2 := mul_nonneg hSv0' hDL2
      linarith only [a, b]
    · have a : sl * DL2 ≤ Sv * DL2 := mul_le_mul_of_nonneg_right hSsl hDL2
      have hwE : (5 - 6*ν) * E ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw hE
      have b : 0 ≤ ((5 - 6*ν) * E) * (Qv - 1) := mul_nonneg_of_nonpos_of_nonpos hwE (by linarith only [hQv1])
      have e : (5 - 6*ν) * Qv * E = (5 - 6*ν) * E + ((5 - 6*ν) * E) * (Qv - 1) := by ring
      rw [e]
      linarith only [a, b, hp12]
  -- the gain is at least facet (1,2) at p = 1/2
  exact le_gainC_of_facets (by linarith) hν1 S.B_lo.le S.B_hi.le hL1 (by norm_num) (by norm_num)
    (by linarith) (by linarith)
    (fun p hp hp' k => facets_ge_facet12_of_N10 hν12 hν1 hp hp' (by linarith [S.L_lo]) (by linarith [S.L_hi])
      S.B_lo.le S.B_hi.le hSv0 hSv1 hQv0 hQv1 hSQ hσν hN10 hP12 k)

/-- **The facet input along the whole curve.** -/
theorem facetsAll : FacetsAll := by
  intro Λ₀ hΛ₀ Λ hΛ hlt hle
  have ht := tOf_mem hΛ₀
  have hh : 0 < Λ₀ - Λ := sub_pos.mpr hlt
  have hL : Lr (tOf Λ₀) = Λ₀ := Lr_tOf Λ₀
  have hB : Br (tOf Λ₀) = beta Λ₀ := by simp only [Br, hL]
  have := facetInput_curve ht hh hle
  rwa [hL, hB] at this

/-- **The merged bound from the continuous energy region estimate**, unconditionally. -/
theorem beta_le_theta_ode : HeckeZeroSupremum.beta ≤ (43693617/50000000 : ℝ) := beta_le_theta_of_curve facetsAll

/-- **Dirichlet nonvanishing for `Re s > 43693617/50000000` from the continuous energy region estimate**: no density
steps, no native steps, no face list. -/
theorem dirichlet_nonvanishing_ode {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (43693617 / 50000000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 :=
  dirichlet_of_curve facetsAll χ hs hpole

end QRH.ArviOdeShape

#print axioms QRH.ArviOdeShape.facetsAll
#print axioms QRH.ArviOdeShape.dirichlet_nonvanishing_ode
