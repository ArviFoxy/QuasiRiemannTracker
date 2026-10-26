/- Mixed source step: the finite gates `SourceValid3` of a step with a pool of width `a = r` (the
low fee) and a selected fourth-power block of width `δ`.

With `t = B − L(b − e)`, `X₀ = b + (t − B₀)/L₀`, `β = B₀/L₀`:
  `den3 = 1 + q − 6qβ`,  `δ = (q X₀ + 6qβ r)/den3`,  `F' = 1 − 6r − 6δ`.
The payment `r(1 − 6qβ) + δ(1 + q − 6qβ) = qX₀ + r` holds by definition (`mixed_payment`).
Compared with Collet's gates (`Record1252270103Finite.scalarGate`, natural cost `9/2`):
  * `den → den3`, `F → F'`, every amplifier charge `k a → k (r + δ)`, `1/75 − a → 1/75 − r − δ`;
  * two new gates: the selected block is live width (`b − 2e − δ ≥ 0`) and `δ ≥ 0`;
  * the weak cap at `F'`; the three special sectors and the HIGH gate with `a → r + δ`,
    `F → F' − e`, and the marked width `S = b − 2e − δ`.
This mirrors `research/mixed-step/mixed_certs.py` exactly. -/
import Submissions.arvi_repeated_marks_on_sil_face_20261025.Finite.SourceValid2
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace QRH.MixedStep.Finite
open Record1252270103Finite QRH.RepeatedMarks QRH.RepeatedMarks.Finite

def sourceDen3 (n low : Source) : ℚ := 1 + n.q - 6*n.q*low.B/low.L
def sourceX0 (n low : Source) (b : ℚ) : ℚ := b + (sourceT n b - low.B)/low.L
/-- The selected (transferred) width. -/
def sourceD (n low : Source) (b : ℚ) : ℚ :=
  (n.q*sourceX0 n low b + 6*n.q*(low.B/low.L)*n.lowFee)/sourceDen3 n low
/-- The total amplifier width: the pool `r` plus the selected block. -/
def sourceAmp3 (n low : Source) (b : ℚ) : ℚ := n.lowFee + sourceD n low b
def sourceF3 (n low : Source) (b : ℚ) : ℚ := 1 - 6*n.lowFee - 6*sourceD n low b

/-- The mixed LOW payment holds with equality. -/
theorem mixed_payment (n low : Source) (b : ℚ) (hden : sourceDen3 n low ≠ 0) (hL : low.L ≠ 0) :
    n.lowFee*(1 - 6*n.q*(low.B/low.L)) + sourceD n low b*(1 + n.q - 6*n.q*(low.B/low.L)) =
      n.q*sourceX0 n low b + n.lowFee := by
  have h3 : 1 + n.q - 6*n.q*(low.B/low.L) = sourceDen3 n low := by unfold sourceDen3; ring
  rw [h3]; unfold sourceD; field_simp; ring

def scalarGate3 (n low : Source) (b : ℚ) (j : Fin 18) : ℚ :=
 let a := n.lowFee
 let d := sourceD n low b
 let A := a + d
 let t := sourceT n b
 let T := t+b
 let F := sourceF3 n low b
 let e := n.allowance
 let Lref := 49/100-(9/2)*b
 ![sourceDen3 n low,b-2*e,a,1/75-A,F-T/2-4*e,
 low.B*F-t-b-4*e,1-n.q*low.cap,
 n.lowFee-(n.q*low.B/low.L+n.q*low.cap+4)*e-10*e,
 a-20*e,Lref,1-Lref-1/2-(9/2)*b-10*e,
 5/6+(499/1000)*Lref-T-9*A-n.highFee,
 1-T-5*A-n.highFee,1-1/50-T-4*A-n.highFee,
 1-1/50-T-(9/2)*A-n.highFee,Lref-7*A-n.highFee,
 b-2*e-d, d+1/10^30] j

def weakCap3 (n low : Source) (b : ℚ) : ℚ :=
 low.cap*sourceF3 n low b-(low.B*sourceF3 n low b-sourceT n b)/low.L

/-- The special sectors (a HIGH parent is always present in the mixed chain). -/
def densityGate3 (n low : Source) (b ν : ℚ) (j : Fin 3) : ℚ :=
 let a := sourceAmp3 n low b
 let T := sourceT n b+b
 let F := sourceF3 n low b-n.allowance
 let fee := n.highFee
 let t := 15-6*ν
 let H := (a-ν*T)*t+(10-60*a)*ν
 let fixed := H+(ν*F/2-(1-ν)*b-fee)*t
 let core := H+((5/6)*F-(1-ν)*b-fee)*t-10*ν*F
 let tiny := H+(ν*(F-1/50)/2-(1-ν)*b-fee)*t-10*ν*(1/50)
 ![fixed,core,tiny] j

/-- The repeated-mark HIGH gate with the mixed amplifier. -/
def highGate3 (n low h : Source) (copies b ν p : ℚ) (k : Branch) : ℚ :=
  gateG (sourceAmp3 n low b) (sourceT n b + b) (b - 2*n.allowance - sourceD n low b)
    (sourceF3 n low b - n.allowance) n.highFee copies h.B h.L h.cap ν p k

def SourceValidC3 (n low h : Source) : Prop :=
 0<n.B ∧ n.B≤1 ∧ 1<n.L ∧ 0≤n.cap ∧ n.cap<1 ∧
 1/2≤n.q ∧ n.q<3/4 ∧ n.L<low.L ∧
 0≤crossing n low ∧ crossing n low≤n.cap ∧ crossing n low≤low.cap ∧
 (22/23≤h.B ∧ h.B≤1 ∧ 1<h.L ∧ 0≤h.cap ∧ h.cap<1) ∧
 (∀ b ∈ [crossing n low,n.cap],
  (∀ j : Fin 18, 0<scalarGate3 n low b j) ∧ 0≤weakCap3 n low b ∧
  ∀ j : Fin 3, ∀ i : Fin 4, 0<cubicBernstein (fun ν => densityGate3 n low b ν j) n.q (3/4) i)

instance (n low h : Source) : Decidable (SourceValidC3 n low h) := by
  unfold SourceValidC3; infer_instance

/-- The cell condition at both endpoints, at the mixed scale. -/
def CellRatio3 (n low : Source) : Prop :=
  ∀ b ∈ [crossing n low, n.cap], 2*(b - 2*n.allowance) ≤ sourceF3 n low b - n.allowance

instance (n low : Source) : Decidable (CellRatio3 n low) := by unfold CellRatio3; infer_instance

end QRH.MixedStep.Finite
