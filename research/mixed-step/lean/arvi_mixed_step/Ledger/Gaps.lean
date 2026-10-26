/- Mixed source step, ledger N4 (HIGH side): the actual HIGH gaps at every virtual node.

The certified mixed HIGH gate (`HighPos3R`, the repeated-mark gate with amplifier `A = r + d`,
total width `T`, marked width `S = b - 2e - d` and scale `F' - e`) and the three special sectors of
`SourceValidC3` (`densityGate3`) give a reserve uniform in the width and the density
(`high3_uniform_reserve`, `density3_uniform_margin`). At a node `vnode2 n low b δ θ`
(`0 ≤ θ ≤ δ ≤ d`, width `b - θ`) every gap is at least the certified one (proved, not assumed):
* the base `physicalBase ν (r + δ) (T - θ)` is at most `physicalBase ν (r + d) T`
  (the amplifier slope `5 - 6ρ` is `≥ 0` for `ν ≥ 1/2`, and `T` only drops);
* the repeated-mark gain is monotone in the marked width and in the scale (`gainK_mono_S`,
  `gainK_mono_Q`), and both are larger at the node;
* the three family gaps exceed the certified ones by `θ + (d - δ)(5 - 6ρ + 3ν)`, `θ + 4(d - δ)`,
  `θ + (d - δ)(5 - 6ρ + 3ν)`.
Hence `ActualGapsK (vnode2 n low b δ θ) low h (b - θ) ν reserve` (`mixed_uniform_reserve`). -/
import Submissions.arvi_mixed_step.Ledger.Nodes
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.PhysicalReserveK
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Source.PaymentWrappersK
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace QRH.MixedStep.Ledger
noncomputable section
open Record1252270103Finite QRH.MixedStep.Finite QRH.Record1252270103Graph
open QRH.RepeatedMarks QRH.RepeatedMarks.Finite
open QRH.Record1252270103Source.PhysicalScalar

/-! ## Monotonicity of the repeated-mark gain in the marked width -/

/-- Every facet has a nonnegative marked-width coefficient, so the gain is monotone in `S`. -/
theorem gainK_mono_S {ν K B lam h : ℝ} (P : ParentParams ν K B lam h) {S S' Q : ℝ}
    (hS : 0 ≤ S) (hSS : S ≤ S') (hQ : 0 ≤ Q) :
    gainK ν K B lam h S Q ≤ gainK ν K B lam h S' Q := by
  have hS' : 0 ≤ S' := hS.trans hSS
  have hne : ((fun p => gainP ν p K B lam h S' Q) '' classes).Nonempty :=
    ⟨_, ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩⟩
  show gainK ν K B lam h S Q ≤ sInf ((fun p => gainP ν p K B lam h S' Q) '' classes)
  apply le_csInf hne
  rintro _ ⟨p, hp, rfl⟩
  apply (gainK_le_gainP P hS hQ hp).trans
  show gainP ν p K B lam h S Q ≤ gainP ν p K B lam h S' Q
  rw [gainP_eq_inf ν p K B lam h S Q P.hν0.le, gainP_eq_inf ν p K B lam h S' Q P.hν0.le]
  apply Finset.le_inf'
  intro k _
  apply (Finset.inf'_le _ (Finset.mem_univ k)).trans
  rw [facetVal_linear ν p K B lam h S Q k, facetVal_linear ν p K B lam h S' Q k]
  have hc := facet_coeffs (P.at hp) k
  nlinarith [mul_le_mul_of_nonneg_right hSS hc.1]

theorem gainK_mono {ν K B lam h : ℝ} (P : ParentParams ν K B lam h) {S S' Q Q' : ℝ}
    (hS : 0 ≤ S) (hSS : S ≤ S') (hQ : 0 ≤ Q) (hQQ : Q ≤ Q') :
    gainK ν K B lam h S Q ≤ gainK ν K B lam h S' Q' :=
  (gainK_mono_S P hS hSS hQ).trans (gainK_mono_Q P (hS.trans hSS) hQ hQQ)

/-! ## The certified mixed HIGH gate gives a uniform reserve -/

theorem highGate3Real_continuous (n low h : Source) (copies : ℚ) (k : Branch) :
    Continuous (fun x : ℝ × ℝ × ℝ => highGate3Real n low h copies x.1 x.2.1 x.2.2 k) := by
  rcases k with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [highGate3Real, gateG, gateM, gateN, dI, eP, gP, bI, hP, sourceAmp3Real, sourceDReal,
      sourceTReal, sourceF3Real] <;> fun_prop

/-- Mirror of `high_uniform_reserve` (Finite/HighGate.lean) for the mixed gate. -/
theorem high3_uniform_reserve (n low h : Source) (copies : ℚ) (hcopies : 0 ≤ copies)
    (hq0 : 1/2 ≤ n.q) (hB0 : 22/23 ≤ (h.B:ℝ)) (hB1 : (h.B:ℝ) ≤ 1)
    (hL : 1 < (h.L:ℝ)) (hh0 : 0 ≤ (h.cap:ℝ)) (hh1 : (h.cap:ℝ) ≤ 1)
    (hv : ∀ b ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ), ∀ ν ∈ Set.Icc (n.q:ℝ) (3/4),
      ∀ p ∈ Set.Icc (0:ℝ) (1/2), ∀ k, 0 < highGate3Real n low h copies b ν p k) :
    ∃ reserve : ℝ, 0 < reserve ∧ ∀ b ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ),
      ∀ ν ∈ Set.Icc (n.q:ℝ) (3/4),
      0 ≤ b - 2*(n.allowance:ℝ) - sourceDReal n low b →
      0 ≤ sourceF3Real n low b - (n.allowance:ℝ) →
      reserve ≤ 1 - physicalBase ν (sourceAmp3Real n low b) (sourceTReal n b + b) +
        gainK ν copies h.B h.L h.cap (b - 2*(n.allowance:ℝ) - sourceDReal n low b)
          (sourceF3Real n low b - (n.allowance:ℝ)) - (n.highFee:ℝ) := by
  let D := Set.Icc (crossing n low:ℝ) (n.cap:ℝ) ×ˢ
    (Set.Icc (n.q:ℝ) (3/4) ×ˢ Set.Icc (0:ℝ) (1/2))
  have hD : IsCompact D := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  obtain ⟨δ, hδ, hall⟩ := QRH.Record1252270103StepScalar.compact_finite_margin D hD
    (fun k : Branch => fun x : ℝ × ℝ × ℝ => highGate3Real n low h copies x.1 x.2.1 x.2.2 k)
    (fun k => (highGate3Real_continuous n low h copies k).continuousOn)
    (fun k x hx => hv x.1 hx.1 x.2.1 hx.2.1 x.2.2 hx.2.2 k)
  have hLpos : 0 < (h.L:ℝ) := by linarith
  refine ⟨δ/(180*(h.L:ℝ)), by positivity, ?_⟩
  intro b hb ν hν hS hF
  have hq0' : (1/2:ℝ) ≤ (n.q:ℝ) := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr hq0
    norm_num at hh
    exact hh
  have hν0 : 1/2 ≤ ν := le_trans hq0' hν.1
  have hfacet : ∀ p ∈ classes, ∀ k : Branch,
      δ/(180*(h.L:ℝ)) ≤ 1 - physicalBase ν (sourceAmp3Real n low b) (sourceTReal n b + b) +
        facetVal ν p copies h.B h.L h.cap (b - 2*(n.allowance:ℝ) - sourceDReal n low b)
          (sourceF3Real n low b - (n.allowance:ℝ)) k - (n.highFee:ℝ) := by
    intro p hp k
    have hp1 : p < 1 := by linarith [hp.2]
    have hpL : 2*p < (h.L:ℝ) := by linarith [hp.2]
    have hg := hall k (b, ν, p) ⟨hb, hν, hp⟩
    simp only at hg
    rw [highGate3Real, gateG_eq _ _ _ _ _ _ _ _ _ ν p (by linarith) hν.2 hp1 hpL hLpos k] at hg
    have hM := gateM_pos (ν:=ν) (p:=p) (L:=(h.L:ℝ)) (by linarith) hν.2 hp1 hpL hLpos k
    have hMle := gateM_le (ν:=ν) (p:=p) (L:=(h.L:ℝ)) (by linarith) hν.2 hp.1 hp.2 hL k
    have ht0 : 0 < 15 - 6*ν := by linarith [hν.2]
    have ht1 : 15 - 6*ν ≤ 12 := by linarith
    set G := 1 - physicalBase ν (sourceAmp3Real n low b) (sourceTReal n b + b) +
      facetVal ν p copies h.B h.L h.cap (b - 2*(n.allowance:ℝ) - sourceDReal n low b)
        (sourceF3Real n low b - (n.allowance:ℝ)) k - (n.highFee:ℝ) with hGdef
    have hGpos : 0 < G := by
      by_contra hcon; push Not at hcon
      have : gateM ν p (h.L:ℝ) k*(15 - 6*ν)*G ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hcon
      linarith
    have hbound : gateM ν p (h.L:ℝ) k*(15 - 6*ν) ≤ 180*(h.L:ℝ) := by nlinarith
    have : δ ≤ 180*(h.L:ℝ)*G := le_trans hg (by nlinarith)
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hgain : δ/(180*(h.L:ℝ)) - (1 - physicalBase ν (sourceAmp3Real n low b) (sourceTReal n b + b) -
      (n.highFee:ℝ)) ≤ gainK ν copies h.B h.L h.cap (b - 2*(n.allowance:ℝ) - sourceDReal n low b)
        (sourceF3Real n low b - (n.allowance:ℝ)) := by
    have hne : ((fun p => gainP ν p (copies:ℝ) (h.B:ℝ) (h.L:ℝ) (h.cap:ℝ)
        (b - 2*(n.allowance:ℝ) - sourceDReal n low b)
        (sourceF3Real n low b - (n.allowance:ℝ))) '' classes).Nonempty :=
      ⟨_, ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩⟩
    show _ ≤ sInf _
    apply le_csInf hne
    rintro _ ⟨p, hp, rfl⟩
    dsimp only
    rw [gainP_eq_inf _ _ _ _ _ _ _ _ (by linarith)]
    apply Finset.le_inf'
    intro k _
    linarith [hfacet p hp k]
  linarith

/-! ## The three special sectors -/

/-- `densityGate3` at a real width and density. -/
def densityGate3Real (n low : Source) (b ν : ℝ) (j : Fin 3) : ℝ :=
  let a := sourceAmp3Real n low b
  let T := sourceTReal n b + b
  let F := sourceF3Real n low b - (n.allowance:ℝ)
  let fee : ℝ := n.highFee
  let t := 15 - 6*ν
  let H := (a - ν*T)*t + (10 - 60*a)*ν
  let fixed := H + (ν*F/2 - (1 - ν)*b - fee)*t
  let core := H + ((5/6)*F - (1 - ν)*b - fee)*t - 10*ν*F
  let tiny := H + (ν*(F - 1/50)/2 - (1 - ν)*b - fee)*t - 10*ν*(1/50)
  ![fixed, core, tiny] j

theorem densityGate3Real_cubic (n low : Source) (b : ℚ) (ν : ℝ) (j : Fin 3) :
    densityGate3Real n low (b:ℝ) ν j =
      cubicEval (fun i => (cubicCoeffs (fun z => densityGate3 n low b z j) i : ℝ)) ν := by
  have hA := sourceAmp3Real_rat n low b
  have hT := sourceTReal_rat n b
  have hF := sourceF3Real_rat n low b
  fin_cases j <;>
    simp [densityGate3Real, densityGate3, cubicEval, cubicCoeffs, hA, hT, hF] <;> ring

theorem densityGate3Real_affine (n low : Source) (ν : ℝ) (j : Fin 3) :
    WidthAffine (fun b => densityGate3Real n low b ν j) := by
  intro x y t
  fin_cases j <;>
    simp [densityGate3Real, sourceAmp3Real, sourceDReal, sourceTReal, sourceF3Real] <;> ring

theorem densityGate3Real_continuous (n low : Source) (j : Fin 3) :
    Continuous (fun x : ℝ × ℝ => densityGate3Real n low x.1 x.2 j) := by
  fin_cases j <;>
    simp [densityGate3Real, sourceAmp3Real, sourceDReal, sourceTReal, sourceF3Real] <;> fun_prop

theorem density3_full_width (n low h : Source) (hv : SourceValidC3 n low h) {b ν : ℝ}
    (hb : b ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ)) (hν : ν ∈ Set.Icc (n.q:ℝ) (3/4)) (j : Fin 3) :
    0 < densityGate3Real n low b ν j := by
  have hq : n.q < 3/4 := hv.2.2.2.2.2.2.1
  have hend : ∀ c : ℚ, c ∈ [crossing n low, n.cap] → 0 < densityGate3Real n low (c:ℝ) ν j := by
    intro c hc
    have hcert := (hv.2.2.2.2.2.2.2.2.2.2.2.2 c hc).2.2 j
    rw [densityGate3Real_cubic]
    exact cubic_cast_positive (fun z => densityGate3 n low c z j) hq (by simpa using hν) hcert
  exact width_affine_positive (densityGate3Real_affine n low ν j) hb
    (hend _ (by simp)) (hend _ (by simp))

/-- A positive margin for the three special sectors, uniform in the width and the density. -/
theorem density3_uniform_margin (n low h : Source) (hv : SourceValidC3 n low h) :
    ∃ m : ℝ, 0 < m ∧ ∀ b ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ), ∀ ν ∈ Set.Icc (n.q:ℝ) (3/4),
      ∀ j, m ≤ densityGate3Real n low b ν j := by
  let D := Set.Icc (crossing n low:ℝ) (n.cap:ℝ) ×ˢ Set.Icc (n.q:ℝ) (3/4:ℝ)
  have hD : IsCompact D := isCompact_Icc.prod isCompact_Icc
  obtain ⟨m, hm, hall⟩ := QRH.Record1252270103StepScalar.compact_finite_margin D hD
    (fun j : Fin 3 => fun x : ℝ × ℝ => densityGate3Real n low x.1 x.2 j)
    (fun j => (densityGate3Real_continuous n low j).continuousOn)
    (fun j x hx => density3_full_width n low h hv hx.1 hx.2 j)
  exact ⟨m, hm, fun b hb ν hν j => hall j (b, ν) ⟨hb, hν⟩⟩

/-! ## The gaps at a node dominate the certified gaps -/

theorem rho_le (ν : ℝ) (hν0 : 1/2 ≤ ν) (hν1 : ν ≤ 3/4) :
    0 ≤ 5 - 6*QRH.Record1252270103Source.High.rho ν := by
  simp only [QRH.Record1252270103Source.High.rho, QRH.Record1252270103Source.High.baseXi,
    QRH.Record1252270103Source.High.densityDenom]
  have hd : 0 < 15 - 6*ν := by linarith
  rw [show (5:ℝ) - 6*(1 - ν*(10/(15 - 6*ν))) = (66*ν - 15)/(15 - 6*ν) by field_simp; ring]
  exact div_nonneg (by linarith) hd.le

/-- The base at a node is at most the certified base. -/
theorem node_base_le (n low : Source) (b δ θ : ℚ) (hden : sourceDen n low ≠ 0) {ν : ℝ}
    (hν0 : 1/2 ≤ ν) (hν1 : ν ≤ 3/4) (hθ0 : 0 ≤ θ) (hδ : (δ:ℝ) ≤ sourceDReal n low (b:ℝ)) :
    sourceBase (vnode2 n low b δ θ) low ((b - θ : ℚ) : ℝ) ν ≤
      physicalBase ν (sourceAmp3Real n low (b:ℝ)) (sourceTReal n (b:ℝ) + (b:ℝ)) := by
  obtain ⟨hT, hA, _⟩ := vnode2_real n low b δ θ hden
  have hθ0' : (0:ℝ) ≤ θ := by exact_mod_cast hθ0
  have hr := rho_le ν hν0 hν1
  simp only [sourceBase, physicalBase, hT, hA, sourceAmp3Real]
  have hbθ : ((b - θ : ℚ) : ℝ) = (b:ℝ) - θ := by push_cast; ring
  rw [hbθ]
  nlinarith [mul_nonneg (sub_nonneg.mpr hδ) hr]

/-- The certified family gaps (the `densityGate3` sectors divided by `15 - 6ν`). -/
theorem densityGate3Real_eq (n low : Source) (b ν : ℝ) (hν : ν ≤ 3/4) (j : Fin 3) :
    densityGate3Real n low b ν j =
      (15 - 6*ν)*(![1 - physicalBase ν (sourceAmp3Real n low b) (sourceTReal n b + b) +
          ν*(sourceF3Real n low b - (n.allowance:ℝ))/2 - (1 - ν)*b - (n.highFee:ℝ),
        1 - physicalBase ν (sourceAmp3Real n low b) (sourceTReal n b + b) +
          (QRH.Record1252270103Source.High.rho ν - 1/6)*(sourceF3Real n low b - (n.allowance:ℝ)) -
          (1 - ν)*b - (n.highFee:ℝ),
        1 - physicalBase ν (sourceAmp3Real n low b) (sourceTReal n b + b) +
          ν*((sourceF3Real n low b - (n.allowance:ℝ)) - 1/50)/2 -
          (1 - QRH.Record1252270103Source.High.rho ν)/50 - (1 - ν)*b - (n.highFee:ℝ)] j) := by
  have hd : (15 - 6*ν) ≠ 0 := by linarith
  have hd' : (15 - ν*6) ≠ 0 := by linarith
  fin_cases j <;>
    simp [densityGate3Real, physicalBase, QRH.Record1252270103Source.High.rho,
      QRH.Record1252270103Source.High.baseXi, QRH.Record1252270103Source.High.densityDenom] <;>
    field_simp <;> ring

/-- The family gaps at a node exceed the certified ones. -/
theorem node_family_ge (n low : Source) (b δ θ : ℚ) (hden : sourceDen n low ≠ 0) {ν : ℝ}
    (hν0 : 1/2 ≤ ν) (hν1 : ν ≤ 3/4) (hθ0 : 0 ≤ θ) (hθ : θ ≤ δ)
    (hδ : (δ:ℝ) ≤ sourceDReal n low (b:ℝ)) (j : Fin 3) :
    densityGate3Real n low (b:ℝ) ν j/(15 - 6*ν) ≤
      familyGap (vnode2 n low b δ θ) low ((b - θ : ℚ) : ℝ) ν j := by
  obtain ⟨hT, hA, hF⟩ := vnode2_real n low b δ θ hden
  have hθ0' : (0:ℝ) ≤ θ := by exact_mod_cast hθ0
  have hθ' : (θ:ℝ) ≤ δ := by exact_mod_cast hθ
  have hr := rho_le ν hν0 hν1
  have hd : 0 < 15 - 6*ν := by linarith
  rw [densityGate3Real_eq n low (b:ℝ) ν hν1 j, mul_div_cancel_left₀ _ hd.ne']
  have hbθ : ((b - θ : ℚ) : ℝ) = (b:ℝ) - θ := by push_cast; ring
  have hdd : 0 ≤ sourceDReal n low (b:ℝ) - δ := sub_nonneg.mpr hδ
  have hT' : sourceTReal (vnode2 n low b δ θ) ((b:ℝ) - θ) = sourceTReal n (b:ℝ) := by
    rw [← hbθ]; exact hT
  have hA' : sourceAReal (vnode2 n low b δ θ) low ((b:ℝ) - θ) = (n.lowFee:ℝ) + δ := by
    rw [← hbθ]; exact hA
  have hF' : sourceFReal (vnode2 n low b δ θ) low ((b:ℝ) - θ) =
      sourceF3Real n low (b:ℝ) + 6*(sourceDReal n low (b:ℝ) - δ) := by
    rw [← hbθ]; exact hF
  fin_cases j <;>
    simp [familyGap, sourceBase, physicalBase, hT', hA', hF', hbθ, sourceAmp3Real] <;> nlinarith [mul_nonneg hdd hr, mul_nonneg hdd (show (0:ℝ) ≤ ν by linarith),
      mul_nonneg hθ0' (show (0:ℝ) ≤ ν by linarith), mul_nonneg hθ0' (show (0:ℝ) ≤ 1 - ν by linarith)]

/-! ## The actual gaps at every node -/

/-- **The actual HIGH gaps at every node** `0 ≤ θ ≤ δ ≤ d`, with one reserve for all widths, nodes
and densities. -/
theorem mixed_uniform_reserve (n low h : Source) (hv : SourceValid3 n low h) (hlow : ParentGood low)
    (hden : sourceDen n low ≠ 0) (he : 0 ≤ (n.allowance:ℝ)) :
    ∃ reserve : ℝ, 0 < reserve ∧ ∀ b : ℚ, (b:ℝ) ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ) →
      ∀ δ θ : ℚ, 0 ≤ θ → θ ≤ δ → δ ≤ sourceD n low b → ∀ ν ∈ Set.Icc (n.q:ℝ) (3/4),
        QRH.RepeatedMarks.Source.ActualGapsK (vnode2 n low b δ θ) low h ((b - θ : ℚ) : ℝ) ν reserve := by
  obtain ⟨hC, hH, hcell⟩ := hv
  have S := shape3_of n low h hC
  have hgood := hC.2.2.2.2.2.2.2.2.2.2.2.1
  have hB0 : (22/23:ℝ) ≤ h.B := by
    have hh := (Rat.cast_le (K:=ℝ)).mpr hgood.1
    norm_num at hh
    exact hh
  have hB1 : (h.B:ℝ) ≤ 1 := by exact_mod_cast hgood.2.1
  have hL : 1 < (h.L:ℝ) := by exact_mod_cast hgood.2.2.1
  have hc0 : 0 ≤ (h.cap:ℝ) := by exact_mod_cast hgood.2.2.2.1
  have hc1 : (h.cap:ℝ) ≤ 1 := by exact_mod_cast hgood.2.2.2.2.le
  obtain ⟨r1, hr1, hres⟩ := high3_uniform_reserve n low h 8 (by norm_num) hC.2.2.2.2.2.1
    hB0 hB1 hL hc0 hc1 hH
  obtain ⟨m, hm, hdens⟩ := density3_uniform_margin n low h hC
  refine ⟨min r1 (m/12), lt_min hr1 (by positivity), ?_⟩
  intro b hb δ θ hθ0 hθ hδ ν hν
  have hν0 : (1/2:ℝ) ≤ ν := le_trans S.q_half hν.1
  have hν1 : ν ≤ 3/4 := hν.2
  -- the certified quantities at the actual width
  have hg := (scalar3_full_width n low h hC hb).1
  have g16 := hg 16
  simp only [scalarGate3Real] at g16
  norm_num at g16
  have hcr : 2*((b:ℝ) - 2*(n.allowance:ℝ)) ≤ sourceF3Real n low (b:ℝ) - (n.allowance:ℝ) := by
    have hl := hcell (crossing n low) (by simp)
    have hr := hcell n.cap (by simp)
    have haff : WidthAffine (fun x : ℝ => sourceF3Real n low x - (n.allowance:ℝ) -
        2*(x - 2*(n.allowance:ℝ))) := by
      intro x y t
      simp only [sourceF3Real, sourceDReal, sourceTReal]; ring
    have hf (c : ℚ) (hc' : 2*(c - 2*n.allowance) ≤ sourceF3 n low c - n.allowance) :
        0 ≤ sourceF3Real n low (c:ℝ) - (n.allowance:ℝ) - 2*((c:ℝ) - 2*(n.allowance:ℝ)) := by
      rw [sourceF3Real_rat]
      have hh : ((2*(c - 2*n.allowance) : ℚ) : ℝ) ≤ ((sourceF3 n low c - n.allowance : ℚ) : ℝ) := by
        exact_mod_cast hc'
      push_cast at hh
      linarith
    have := width_affine_nonnegative haff hb (hf _ hl) (hf _ hr)
    linarith
  have hS : 0 ≤ (b:ℝ) - 2*(n.allowance:ℝ) - sourceDReal n low (b:ℝ) := by linarith
  have hd0 := sourceDReal_nonneg n low h hC hlow he hb
  have hF0 : 0 ≤ sourceF3Real n low (b:ℝ) - (n.allowance:ℝ) := by linarith
  have hδ' : (δ:ℝ) ≤ sourceDReal n low (b:ℝ) := by rw [sourceDReal_rat]; exact_mod_cast hδ
  have hθ0' : (0:ℝ) ≤ θ := by exact_mod_cast hθ0
  have hθ' : (θ:ℝ) ≤ δ := by exact_mod_cast hθ
  obtain ⟨hT, hA, hF⟩ := vnode2_real n low b δ θ hden
  have hbθ : ((b - θ : ℚ) : ℝ) = (b:ℝ) - θ := by push_cast; ring
  -- node marked width and scale dominate the certified ones
  have hSn : (b:ℝ) - 2*(n.allowance:ℝ) - sourceDReal n low (b:ℝ) ≤
      ((b - θ : ℚ) : ℝ) - 2*((vnode2 n low b δ θ).allowance:ℝ) := by
    rw [hbθ]; simp only [vnode2_allowance]; linarith
  have hFn : sourceF3Real n low (b:ℝ) - (n.allowance:ℝ) ≤
      sourceFReal (vnode2 n low b δ θ) low ((b - θ : ℚ) : ℝ) - ((vnode2 n low b δ θ).allowance:ℝ) := by
    rw [hF]; simp only [vnode2_allowance]; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- HIGH facet gap
    have hr := hres (b:ℝ) hb ν hν hS hF0
    have hPP : ParentParams ν ((8:ℚ):ℝ) h.B h.L h.cap :=
      ⟨by linarith, hν1, by norm_num, hB0, hB1, hL, hc0, hc1⟩
    have hgm := gainK_mono hPP hS hSn hF0 hFn
    have hbase := node_base_le n low b δ θ hden hν0 hν1 hθ0 hδ'
    simp only [QRH.RepeatedMarks.Source.selectedGainK, vnode2_highFee]
    have e8 : ((8:ℚ):ℝ) = 8 := by norm_num
    rw [e8] at hgm hr
    have := min_le_left r1 (m/12)
    linarith
  · -- family gaps
    intro j
    have hfam := node_family_ge n low b δ θ hden hν0 hν1 hθ0 hθ hδ' j
    have hdj := hdens (b:ℝ) hb ν hν j
    have hd : 0 < 15 - 6*ν := by linarith
    have hd12 : 15 - 6*ν ≤ 12 := by linarith
    have h1 : m/12 ≤ densityGate3Real n low (b:ℝ) ν j/(15 - 6*ν) := by
      rw [le_div_iff₀ hd]
      nlinarith
    have := min_le_right r1 (m/12)
    linarith
  · -- the marked width is nonnegative at the node
    have := hSn; linarith
  · -- the cell condition at the node
    rw [hF, hbθ]; simp only [vnode2_allowance]
    have hdd : 0 ≤ sourceDReal n low (b:ℝ) - δ := sub_nonneg.mpr hδ'
    linarith

/-- The same in Collet's `ActualGaps` form with the repeated-mark gain (`ActualGaps_rm`). -/
theorem mixed_uniform_reserve_rm (n low h : Source) (hv : SourceValid3 n low h)
    (hlow : ParentGood low) (hden : sourceDen n low ≠ 0) (he : 0 ≤ (n.allowance:ℝ)) :
    ∃ reserve : ℝ, 0 < reserve ∧ ∀ b : ℚ, (b:ℝ) ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ) →
      ∀ δ θ : ℚ, 0 ≤ θ → θ ≤ δ → δ ≤ sourceD n low b → ∀ ν ∈ Set.Icc (n.q:ℝ) (3/4),
        ActualGaps_rm (vnode2 n low b δ θ) low (some h) ((b - θ : ℚ) : ℝ) ν reserve := by
  obtain ⟨reserve, hr, hall⟩ := mixed_uniform_reserve n low h hv hlow hden he
  exact ⟨reserve, hr, fun b hb δ θ hθ0 hθ hδ ν hν =>
    actualGaps_rm_of_K (hall b hb δ θ hθ0 hθ hδ ν hν)⟩

end
end QRH.MixedStep.Ledger
#print axioms QRH.MixedStep.Ledger.mixed_uniform_reserve
#print axioms QRH.MixedStep.Ledger.mixed_uniform_reserve_rm
