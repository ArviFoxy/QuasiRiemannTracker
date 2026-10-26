/- Mixed source step: the repeated-mark HIGH gate with the mixed amplifier, over the reals, and its
certificate. The selected width `δ(b)`, the amplifier `r + δ(b)`, the scale `F'(b)` and the marked
width `b − 2e − δ(b)` are affine in the width `b`, so the gate is affine in `b` and a bicubic in
`(ν, p)`; positivity on the whole cell follows from bisection trees at the two width endpoints, as
for `SourceValid2` (`Finite/HighGate.lean`). -/
import Submissions.arvi_mixed_step.Finite.SourceValid3
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace QRH.MixedStep.Finite
noncomputable section
open Record1252270103Finite QRH.RepeatedMarks QRH.RepeatedMarks.Finite

def sourceDReal (n low : Source) (b : ℝ) : ℝ :=
  ((n.q:ℝ)*(b + (sourceTReal n b - (low.B:ℝ))/(low.L:ℝ)) +
    6*(n.q:ℝ)*((low.B:ℝ)/(low.L:ℝ))*(n.lowFee:ℝ))/(sourceDen3 n low:ℝ)
def sourceAmp3Real (n low : Source) (b : ℝ) : ℝ := (n.lowFee:ℝ) + sourceDReal n low b
def sourceF3Real (n low : Source) (b : ℝ) : ℝ := 1 - 6*(n.lowFee:ℝ) - 6*sourceDReal n low b

theorem sourceDReal_rat (n low : Source) (b : ℚ) :
    sourceDReal n low (b:ℝ) = (sourceD n low b:ℝ) := by
  simp [sourceDReal, sourceD, sourceX0, sourceTReal_rat]

theorem sourceAmp3Real_rat (n low : Source) (b : ℚ) :
    sourceAmp3Real n low (b:ℝ) = (sourceAmp3 n low b:ℝ) := by
  simp [sourceAmp3Real, sourceAmp3, sourceDReal_rat]

theorem sourceF3Real_rat (n low : Source) (b : ℚ) :
    sourceF3Real n low (b:ℝ) = (sourceF3 n low b:ℝ) := by
  simp [sourceF3Real, sourceF3, sourceDReal_rat]

def highGate3Real (n low h : Source) (copies : ℚ) (b ν p : ℝ) (k : Branch) : ℝ :=
  gateG (sourceAmp3Real n low b) (sourceTReal n b + b)
    (b - 2*(n.allowance:ℝ) - sourceDReal n low b)
    (sourceF3Real n low b - (n.allowance:ℝ)) (n.highFee:ℝ) (copies:ℝ) (h.B:ℝ) (h.L:ℝ) (h.cap:ℝ)
    ν p k

def highCoeffs3 (n low h : Source) (copies b : ℚ) (k : Branch) : Fin 4 → Fin 4 → ℚ :=
  bicubic (fun ν p => highGate3 n low h copies b ν p k)

theorem highGate3Real_rat (n low h : Source) (copies b : ℚ) (ν p : ℝ) (k : Branch) :
    highGate3Real n low h copies (b:ℝ) ν p k =
      ∑ i : Fin 4, ∑ j : Fin 4, ((highCoeffs3 n low h copies b k i j : ℚ) : ℝ) *
        ν^(i:ℕ) * p^(j:ℕ) := by
  have e := gateG_bicubic (sourceAmp3 n low b) (sourceT n b + b)
    (b - 2*n.allowance - sourceD n low b) (sourceF3 n low b - n.allowance) n.highFee copies
    h.B h.L h.cap k ν p
  rw [highGate3Real, sourceAmp3Real_rat, sourceTReal_rat, sourceDReal_rat, sourceF3Real_rat]
  push_cast at e ⊢
  simpa only [highCoeffs3, highGate3] using e

theorem highGate3Real_affine (n low h : Source) (copies : ℚ) (ν p : ℝ) (k : Branch) :
    WidthAffine (fun b => highGate3Real n low h copies b ν p k) := by
  intro x y t
  rcases k with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp only [highGate3Real, gateG, gateM, gateN, dI, eP, gP, bI, hP, sourceAmp3Real,
      sourceDReal, sourceF3Real, sourceTReal] <;> simp <;> ring

/-- The certificate of one node at one width: one bisection tree per branch. -/
def HighCertAt3 (n low h : Source) (copies b : ℚ) (T : Branch → Split) : Prop :=
  ∀ k : Branch, checkBox (highCoeffs3 n low h copies b k) (T k) n.q (3/4 - n.q) 0 (1/2) = true

instance (n low h : Source) (copies b : ℚ) (T : Branch → Split) :
    Decidable (HighCertAt3 n low h copies b T) := by
  unfold HighCertAt3; infer_instance

theorem high3_endpoint_pos (n low h : Source) (copies b : ℚ) (T : Branch → Split)
    (hq : n.q < 3/4) (hc : HighCertAt3 n low h copies b T)
    {ν p : ℝ} (hν : ν ∈ Set.Icc (n.q:ℝ) (3/4)) (hp : p ∈ Set.Icc (0:ℝ) (1/2)) (k : Branch) :
    0 < highGate3Real n low h copies (b:ℝ) ν p k := by
  rw [highGate3Real_rat]
  apply checkBox_sound (highCoeffs3 n low h copies b k) (T k) n.q (3/4 - n.q) 0 (1/2)
    (by linarith) (by norm_num) (hc k) ν p hν.1 (by push_cast; linarith [hν.2]) (by simpa using hp.1)
    (by push_cast; linarith [hp.2])

/-- The HIGH certificates of a mixed step at both width endpoints. -/
def HighValid3 (n low h : Source) (copies : ℚ) : Prop :=
  ∀ b ∈ [crossing n low, n.cap], ∃ T : Branch → Split, HighCertAt3 n low h copies b T

/-- The semantic form: the mixed HIGH gate is positive on the whole cell. -/
def HighPos3R (n low h : Source) (copies : ℚ) : Prop :=
  ∀ b ∈ Set.Icc (crossing n low:ℝ) (n.cap:ℝ), ∀ ν ∈ Set.Icc (n.q:ℝ) (3/4),
    ∀ p ∈ Set.Icc (0:ℝ) (1/2), ∀ k, 0 < highGate3Real n low h copies b ν p k

theorem highPos3R_of_valid (n low h : Source) (copies : ℚ) (hq : n.q < 3/4)
    (hv : HighValid3 n low h copies) : HighPos3R n low h copies := by
  intro b hb ν hν p hp k
  obtain ⟨Tl, hl⟩ := hv (crossing n low) (by simp)
  obtain ⟨Tr, hr⟩ := hv n.cap (by simp)
  exact width_affine_positive (highGate3Real_affine n low h copies ν p k) hb
    (high3_endpoint_pos n low h copies _ Tl hq hl hν hp k)
    (high3_endpoint_pos n low h copies _ Tr hq hr hν hp k)

/-- Validity of a mixed step with HIGH parent `h` (`copies = 8`). -/
def SourceValid3 (n low h : Source) : Prop :=
  SourceValidC3 n low h ∧ HighPos3R n low h 8 ∧ CellRatio3 n low

theorem sourceValid3_of_certs (n low h : Source) (hc : SourceValidC3 n low h)
    (hv : HighValid3 n low h 8) (hr : CellRatio3 n low) : SourceValid3 n low h :=
  ⟨hc, highPos3R_of_valid n low h 8 hc.2.2.2.2.2.2.1 hv, hr⟩

end
end QRH.MixedStep.Finite
#print axioms QRH.MixedStep.Finite.highPos3R_of_valid
