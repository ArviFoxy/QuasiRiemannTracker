/- Numerical parameters of the marked HIGH branch.

`PivotParams sourceMesh` bundles the side conditions of PR 76's pivot
`actual_dictionary_regular_raw_max_uniform_tau_rm` (the dictionary count with the repeated-mark
gain): the analytic losses, the bin buffer `e`, the slot floor `wmin`, the live-width window.
`highParams` produces one instance from the master loss `θ`, the cardinality `N` of the slot
alphabet, the plain-factor loss `ε₁` and the plain length cap `Rplain`; the plain and slot
budgets of the buffered suppliers (`highBuffer`, `highKappa`) are inherited from Collet's
`HighParameters`. -/
import Submissions.hailey_collet_1252270103.Cycle61.Moment.HighParameters
import Submissions.hailey_collet_1252270103.Cycle61.Density.BufferedPartition
import Mathlib.Tactic

set_option autoImplicit false
namespace QRH.ArviDensity.Density
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.Cycle61Moment OAI.SevenEighths.LocalMoment

/-- The side conditions of the pivot, bundled. -/
structure PivotParams (sourceMesh : ℝ) where
  εm : ℝ
  binWidth : ℝ
  ζ : ℝ
  η : ℝ
  dmin : ℝ
  dmax : ℝ
  rmin : ℝ
  Rwidth : ℝ
  εp : ℝ
  e : ℝ
  κ : ℝ
  ηw : ℝ
  εslot : ℝ
  ηslot : ℝ
  δ : ℝ
  Bmask : ℝ
  Broot : ℝ
  wmin : ℝ
  qlo : ℝ
  Q : ℝ
  mesh : ℝ
  I : ℕ
  hδ : 0 < δ
  hBmask : 0 ≤ Bmask
  hBroot : 0 ≤ Broot
  hwmin : 0 < wmin
  hbin : 0 < binWidth
  hη : 0 < η
  hζ : 0 < ζ
  hεm : 0 < εm
  hdmin : 0 < dmin
  hdmax : dmin ≤ dmax
  hrmin : 0 < rmin
  hRw : 0 ≤ Rwidth
  hε : 0 < εp
  hεsmall : εp ≤ 1/1000
  he : 0 < e
  he' : e < 1/1000
  hκ : 0 < κ
  hκ' : κ ≤ 1
  hηw : 0 ≤ ηw
  hbudget : 288*e + 8*κ + 2*ηw ≤ εp/2
  hεslot : 0 < εslot
  hηslot : 0 ≤ ηslot
  hslotBudget : 8*e*Rwidth + κ ≤ εslot
  hgap : εslot < rmin*binWidth
  hqlo : 0 < qlo
  hQ : qlo ≤ Q
  hQroot : Q/12 ≤ Broot
  hdlo : dmin ≤ qlo/2 + δ
  hdsource : Q + Bmask + δ ≤ dmax
  hrlower : rmin ≤ wmin/dmax
  hmesh : 0 ≤ mesh
  hmeshmax : mesh ≤ sourceMesh
  hmeshR : mesh ≤ Rwidth
  hI : bufferCount e ≤ I

/-- The slot floor, which is also the bin width: `θ/(N+1)`. -/
def highWmin (θ : ℝ) (N : ℕ) : ℝ := θ/((N:ℝ)+1)

/-- The live-width floor `rmin`. -/
def highRmin (Mmax θ : ℝ) (N : ℕ) : ℝ := highWmin θ N/(2*(Mmax + 2*θ))

/-- The slot loss `εslot`. -/
def highEslot (Mmax θ ε₁ : ℝ) (N : ℕ) : ℝ :=
  min (min ε₁ (θ/64)) (highRmin Mmax θ N*highWmin θ N/2)

theorem highWmin_pos {θ : ℝ} (hθ : 0 < θ) (N : ℕ) : 0 < highWmin θ N := by
  unfold highWmin; positivity

theorem highWmin_mul {θ : ℝ} (hθ : 0 ≤ θ) (N : ℕ) : (N:ℝ)*highWmin θ N ≤ θ := by
  unfold highWmin
  rw [mul_div_assoc']
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem highRmin_pos {Mmax θ : ℝ} (hθ : 0 < θ) (hM : 0 ≤ Mmax) (N : ℕ) :
    0 < highRmin Mmax θ N := by
  unfold highRmin
  have := highWmin_pos hθ N
  positivity

theorem highEslot_pos {Mmax θ ε₁ : ℝ} (hθ : 0 < θ) (hM : 0 ≤ Mmax) (hε₁ : 0 < ε₁) (N : ℕ) :
    0 < highEslot Mmax θ ε₁ N := by
  unfold highEslot
  have h1 := highWmin_pos hθ N
  have h2 := highRmin_pos hθ hM N
  have : 0 < θ/64 := by positivity
  exact lt_min (lt_min hε₁ this) (by positivity)

theorem highEslot_le_eps {Mmax θ ε₁ : ℝ} (N : ℕ) : highEslot Mmax θ ε₁ N ≤ ε₁ :=
  (min_le_left _ _).trans (min_le_left _ _)

theorem highEslot_le_theta {Mmax θ ε₁ : ℝ} (N : ℕ) : highEslot Mmax θ ε₁ N ≤ θ/64 :=
  (min_le_left _ _).trans (min_le_right _ _)

theorem highEslot_lt_gap {Mmax θ ε₁ : ℝ} (hθ : 0 < θ) (hM : 0 ≤ Mmax) (hε₁ : 0 < ε₁) (N : ℕ) :
    highEslot Mmax θ ε₁ N < highRmin Mmax θ N*highWmin θ N := by
  have h0 := highEslot_pos hθ hM hε₁ N
  have h1 : highEslot Mmax θ ε₁ N ≤ highRmin Mmax θ N*highWmin θ N/2 := min_le_right _ _
  linarith

/-- The pivot parameters from the master loss `θ`, with `dmin = Mmin/2`, `qlo = Mmin`,
`Q = Mmax + θ`, `Bmask = 0` (the unit puncture), `binWidth = wmin = θ/(N+1)`, `Rwidth = 1`;
the buffer `e` and `κ` are Collet's `highBuffer`, `highKappa` at the slot loss and the
plain loss `ε₁`. The pivot mesh is the leaf mesh `meshL` divided by `dmin`. -/
def highParams (Mmin Mmax θ sourceMesh ε₁ Rplain meshL : ℝ) (N : ℕ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1/100000) (hMmin : 0 < Mmin) (hMmax : Mmin ≤ Mmax)
    (hε₁ : 0 < ε₁) (hRp : 0 ≤ Rplain) (hmesh0 : 0 ≤ meshL)
    (hmeshθ : meshL ≤ θ*(Mmin/2)) (hmeshS : meshL ≤ sourceMesh*(Mmin/2)) :
    PivotParams sourceMesh :=
  have hM0 : 0 ≤ Mmax := hMmin.le.trans hMmax
  have hes := highEslot_pos hθ hM0 hε₁ N
  have hw := highWmin_pos hθ N
  have hr := highRmin_pos hθ hM0 N
  have hbb := high_buffer_budgets (Rs := 1) (Rp := Rplain) (es := highEslot Mmax θ ε₁ N) (ep := ε₁)
    zero_le_one hRp hes hε₁
  have hepos := high_buffer_pos (Rs := 1) (Rp := Rplain) (es := highEslot Mmax θ ε₁ N) (ep := ε₁)
    zero_le_one hRp hes hε₁
  have hk := high_kappa_pos (es := highEslot Mmax θ ε₁ N) (ep := ε₁) hes hε₁
  have hesθ := highEslot_le_theta (Mmax := Mmax) (θ := θ) (ε₁ := ε₁) N
  have hebuf : highBuffer 1 Rplain (highEslot Mmax θ ε₁ N) ε₁ ≤ highEslot Mmax θ ε₁ N/64 := by
    have : highBuffer 1 Rplain (highEslot Mmax θ ε₁ N) ε₁ ≤
        highEslot Mmax θ ε₁ N/(32*(1+1)) :=
      (min_le_right (1/2000:ℝ) _).trans (min_le_left _ _)
    linarith
  have hkap : highKappa (highEslot Mmax θ ε₁ N) ε₁ ≤ highEslot Mmax θ ε₁ N/4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  { εm := θ
    binWidth := highWmin θ N
    ζ := θ
    η := θ
    dmin := Mmin/2
    dmax := Mmax + 2*θ
    rmin := highRmin Mmax θ N
    Rwidth := 1
    εp := θ
    e := highBuffer 1 Rplain (highEslot Mmax θ ε₁ N) ε₁
    κ := highKappa (highEslot Mmax θ ε₁ N) ε₁
    ηw := θ/16
    εslot := highEslot Mmax θ ε₁ N
    ηslot := 1
    δ := θ
    Bmask := 0
    Broot := (Mmax + θ)/12
    wmin := highWmin θ N
    qlo := Mmin
    Q := Mmax + θ
    mesh := meshL/(Mmin/2)
    I := bufferCount (highBuffer 1 Rplain (highEslot Mmax θ ε₁ N) ε₁)
    hδ := hθ
    hBmask := le_rfl
    hBroot := by positivity
    hwmin := hw
    hbin := hw
    hη := hθ
    hζ := hθ
    hεm := hθ
    hdmin := by positivity
    hdmax := by linarith
    hrmin := hr
    hRw := zero_le_one
    hε := hθ
    hεsmall := by linarith
    he := hepos
    he' := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    hκ := hk
    hκ' := min_le_left _ _
    hηw := by positivity
    hbudget := by nlinarith
    hεslot := hes
    hηslot := zero_le_one
    hslotBudget := by nlinarith
    hgap := highEslot_lt_gap hθ hM0 hε₁ N
    hqlo := hMmin
    hQ := by linarith
    hQroot := le_rfl
    hdlo := by linarith
    hdsource := by linarith
    hrlower := by
      unfold highRmin
      exact div_le_div_of_nonneg_left hw.le (by positivity) (by nlinarith)
    hmesh := by positivity
    hmeshmax := by
      rw [div_le_iff₀ (by positivity)]
      exact hmeshS
    hmeshR := by
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right (show θ ≤ 1 by linarith) (by positivity : (0:ℝ) ≤ Mmin/2)
      linarith
    hI := le_rfl }

/-- The facts about `highParams` used by the leaf: the unit slot width bound, small bin width,
the plain budget, the loss bound `Lfix`, and the pivot mesh `mesh·dmin = meshL`. -/
theorem highParams_facts (Mmin Mmax θ sourceMesh ε₁ Rplain meshL d : ℝ) (N : ℕ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1/100000) (hMmin : 0 < Mmin) (hMmax : Mmin ≤ Mmax)
    (hε₁ : 0 < ε₁) (hRp : 0 ≤ Rplain) (hmesh0 : 0 ≤ meshL)
    (hmeshθ : meshL ≤ θ*(Mmin/2)) (hmeshS : meshL ≤ sourceMesh*(Mmin/2)) (hd : 0 ≤ d) :
    let PP := highParams Mmin Mmax θ sourceMesh ε₁ Rplain meshL N hθ hθ1 hMmin hMmax hε₁ hRp hmesh0
      hmeshθ hmeshS
    PP.Rwidth = 1 ∧ PP.binWidth ≤ 1/4 ∧ PP.qlo ≤ Mmin ∧ Mmax + θ ≤ PP.Q ∧
    12*PP.e*(Rplain+2) + 8*PP.κ + 2*(ε₁/8) ≤ ε₁ ∧ PP.εslot ≤ ε₁ ∧ 0 < PP.ηw ∧ 0 < PP.ηslot ∧
    PP.mesh * PP.dmin = meshL ∧ PP.εp = θ ∧ PP.εm = θ ∧ PP.δ = θ ∧
    2*ε₁*d + 2*PP.εslot*d*(N:ℝ) + (PP.dmax*(155*PP.εp + PP.mesh + PP.εm + (3/4)*PP.ζ + PP.η) +
      PP.δ + 2*PP.binWidth*(N:ℝ)) + θ + (N:ℝ)*PP.wmin ≤
      2*ε₁*d*((N:ℝ)+1) + (159*(Mmax+1)+5)*θ := by
  intro PP
  have hM0 : 0 ≤ Mmax := hMmin.le.trans hMmax
  have hes := highEslot_pos hθ hM0 hε₁ N
  have hbb := high_buffer_budgets (Rs := 1) (Rp := Rplain) (es := highEslot Mmax θ ε₁ N) (ep := ε₁)
    zero_le_one hRp hes hε₁
  have hw := highWmin_pos hθ N
  have hwN := highWmin_mul hθ.le N
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hmeshle : meshL/(Mmin/2) ≤ θ := by
    rw [div_le_iff₀ (by positivity)]; exact hmeshθ
  have hwleθ : highWmin θ N ≤ θ := by
    unfold highWmin
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨rfl, ?_, le_rfl, le_rfl, ?_, highEslot_le_eps N, ?_, one_pos, ?_, rfl, rfl,
    rfl, ?_⟩
  · exact hwleθ.trans (by linarith)
  · exact hbb.2
  · show 0 < θ/16
    positivity
  · show meshL/(Mmin/2)*(Mmin/2) = meshL
    field_simp
  · have hdm : 0 ≤ Mmax + 2*θ := by linarith
    have h1 : (Mmax + 2*θ)*(155*θ + meshL/(Mmin/2) + θ + (3/4)*θ + θ) ≤ (159*(Mmax+1))*θ := by
      have : 155*θ + meshL/(Mmin/2) + θ + (3/4)*θ + θ ≤ 159*θ := by linarith
      calc (Mmax + 2*θ)*(155*θ + meshL/(Mmin/2) + θ + (3/4)*θ + θ)
          ≤ (Mmax + 2*θ)*(159*θ) := mul_le_mul_of_nonneg_left this hdm
        _ ≤ (Mmax + 1)*(159*θ) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = (159*(Mmax+1))*θ := by ring
    have h2 : 2*highWmin θ N*(N:ℝ) ≤ 2*θ := by nlinarith
    have h3 : 2*ε₁*d*highEslot Mmax θ ε₁ N ≥ 0 := by positivity
    have h4 : 2*highEslot Mmax θ ε₁ N*d*(N:ℝ) ≤ 2*ε₁*d*(N:ℝ) := by
      have := highEslot_le_eps (Mmax := Mmax) (θ := θ) (ε₁ := ε₁) N
      have : 0 ≤ d*(N:ℝ) := mul_nonneg hd hN0
      nlinarith
    show 2*ε₁*d + 2*highEslot Mmax θ ε₁ N*d*(N:ℝ) + ((Mmax + 2*θ)*(155*θ + meshL/(Mmin/2) + θ +
      (3/4)*θ + θ) + θ + 2*highWmin θ N*(N:ℝ)) + θ + (N:ℝ)*highWmin θ N ≤
      2*ε₁*d*((N:ℝ)+1) + (159*(Mmax+1)+5)*θ
    nlinarith

end
end QRH.ArviDensity.Density
