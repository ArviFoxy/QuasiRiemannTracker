/- Copyright (c) 2026 Sil. Apache-2.0.
Exponential deletion prices of the cube-free common-divisor step (CF §5, (5.2)).

A `Price` is the extra exponent paid by a leaf estimate (Seam A) at ordinary width `P`,
retained marked width `s` and envelope `M`, possibly depending on a live width `w₀`
(the density-split threshold `q(w₀)`). Every price is nonnegative, monotone in `P` and
`s`, and Lipschitz in `P`, `s`, `M`; the latter absorbs the `o(1)` changes coming from
profile separation and ordinary shortenings.

* `nativePrice κ`: the natural prime-slot cost `κ·s₊` (delete every slot).
* `parentPrice κ B₀ L₀ c₀`: delete just enough whole slots to enter the parent face
  `P + L₀ s' ≤ B₀ M`, `s' ≤ c₀ M`; if even `s' = 0` is not enough, delete everything
  (all-length zero-slot bound). The deleted width is `deletionNeed`. -/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.MinMax
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false
namespace QRH.SilDensitySplit.CubeFree
noncomputable section

/-- An exponential leaf price `f w P s M`; `P = m₁+m₂` is the ordinary width,
`s` the retained marked width, `M` the envelope (log of the packed scale), `w` a live
width on which a density threshold may depend. -/
structure Price where
  f : ℝ → ℝ → ℝ → ℝ → ℝ
  nonneg : ∀ w P s M, 0 ≤ f w P s M
  mono : ∀ w P P' s s' M, P' ≤ P → s' ≤ s → f w P' s' M ≤ f w P s M
  lip : ℝ
  lip_nonneg : 0 ≤ lip
  lipP : ∀ w P s M δ, 0 ≤ δ → f w (P+δ) s M ≤ f w P s M + lip*δ
  lipS : ∀ w P s M δ, 0 ≤ δ → f w P (s+δ) M ≤ f w P s M + lip*δ
  lipM : ∀ w P s M δ, f w P s (M+δ) ≤ f w P s M + lip*|δ|

/-- Width that must be deleted to enter the parent face `G(B₀,L₀,c₀)` at scale `M`,
clipped to `[0,s]`. -/
def deletionNeed (B₀ L₀ c₀ P s M : ℝ) : ℝ :=
  max 0 (min s (max (s - c₀*M) ((P + L₀*s - B₀*M)/L₀)))

/-! ### A clipped min–max helper -/

/-- `clip s X Y = max 0 (min s (max X Y))`. -/
def clip (s X Y : ℝ) : ℝ := max 0 (min s (max X Y))

theorem clip_nonneg (s X Y : ℝ) : 0 ≤ clip s X Y := le_max_left _ _

theorem clip_mono_add {s X Y s' X' Y' e : ℝ} (he : 0 ≤ e)
    (hs : s' ≤ s + e) (hX : X' ≤ X + e) (hY : Y' ≤ Y + e) :
    clip s' X' Y' ≤ clip s X Y + e := by
  unfold clip
  have h1 : min s' (max X' Y') ≤ min s (max X Y) + e := by
    have : max X' Y' ≤ max X Y + e := by
      rcases le_total X Y with h | h
      · rw [max_eq_right h]; exact max_le (by linarith) hY
      · rw [max_eq_left h]; exact max_le hX (by linarith)
    rcases le_total s (max X Y) with h | h
    · rw [min_eq_left h]; exact (min_le_left _ _).trans hs
    · rw [min_eq_right h]; exact (min_le_right _ _).trans this
  rcases le_total 0 (min s (max X Y)) with h | h
  · rw [max_eq_right h]; exact max_le (by linarith) h1
  · rw [max_eq_left h]; exact max_le (by linarith) (by linarith)

theorem clip_mono {s X Y s' X' Y' : ℝ} (hs : s' ≤ s) (hX : X' ≤ X) (hY : Y' ≤ Y) :
    clip s' X' Y' ≤ clip s X Y := by
  have := clip_mono_add (s:=s) (X:=X) (Y:=Y) (s':=s') (X':=X') (Y':=Y') le_rfl
    (by linarith) (by linarith) (by linarith)
  linarith

theorem deletionNeed_eq (B₀ L₀ c₀ P s M : ℝ) :
    deletionNeed B₀ L₀ c₀ P s M = clip s (s - c₀*M) ((P + L₀*s - B₀*M)/L₀) := rfl

theorem deletionNeed_nonneg (B₀ L₀ c₀ P s M : ℝ) : 0 ≤ deletionNeed B₀ L₀ c₀ P s M :=
  le_max_left _ _

theorem deletionNeed_le_self {B₀ L₀ c₀ P s M : ℝ} (hs : 0 ≤ s) :
    deletionNeed B₀ L₀ c₀ P s M ≤ s :=
  max_le hs (min_le_left _ _)

/-- With the parent cap satisfied (`s ≤ c₀ M`), the need is at most the positive part of
the face defect divided by `L₀` (CF (5.2)). -/
theorem deletionNeed_le_defect {B₀ L₀ c₀ P s M : ℝ} (hcap : s - c₀*M ≤ 0) :
    deletionNeed B₀ L₀ c₀ P s M ≤ max 0 ((P + L₀*s - B₀*M)/L₀) := by
  unfold deletionNeed
  apply max_le (le_max_left _ _)
  refine (min_le_right _ _).trans (max_le ?_ (le_max_right _ _))
  exact hcap.trans (le_max_left _ _)

/-- If nothing is retained, nothing is deleted. -/
theorem deletionNeed_of_nonpos {B₀ L₀ c₀ P s M : ℝ} (hs : s ≤ 0) :
    deletionNeed B₀ L₀ c₀ P s M = 0 :=
  le_antisymm (max_le le_rfl ((min_le_left _ _).trans hs)) (deletionNeed_nonneg _ _ _ _ _ _)

/-- The Lipschitz constant (per unit of `κ`) of the parent deletion need. -/
def needLip (B₀ L₀ c₀ : ℝ) : ℝ := max (max 1 (1/L₀)) (max |c₀| (|B₀|/L₀))

theorem one_le_needLip (B₀ L₀ c₀ : ℝ) : 1 ≤ needLip B₀ L₀ c₀ :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem deletionNeed_mono {B₀ L₀ c₀ P P' s s' M : ℝ} (hL : 0 < L₀)
    (hP : P' ≤ P) (hs : s' ≤ s) :
    deletionNeed B₀ L₀ c₀ P' s' M ≤ deletionNeed B₀ L₀ c₀ P s M := by
  rw [deletionNeed_eq, deletionNeed_eq]
  apply clip_mono hs (by linarith)
  apply div_le_div_of_nonneg_right _ hL.le
  nlinarith

theorem deletionNeed_lipP {B₀ L₀ c₀ P s M δ : ℝ} (hL : 0 < L₀) (hδ : 0 ≤ δ) :
    deletionNeed B₀ L₀ c₀ (P+δ) s M ≤
      deletionNeed B₀ L₀ c₀ P s M + needLip B₀ L₀ c₀ * δ := by
  rw [deletionNeed_eq, deletionNeed_eq]
  have hK := one_le_needLip B₀ L₀ c₀
  have hK1 : 1/L₀ ≤ needLip B₀ L₀ c₀ := (le_max_right _ _).trans (le_max_left _ _)
  have hKδ : δ ≤ needLip B₀ L₀ c₀ * δ := by nlinarith
  apply clip_mono_add (by nlinarith) (by linarith) (by linarith)
  have : (P + δ + L₀*s - B₀*M)/L₀ = (P + L₀*s - B₀*M)/L₀ + (1/L₀)*δ := by
    rw [show P + δ + L₀*s - B₀*M = (P + L₀*s - B₀*M) + δ by ring, add_div, one_div_mul_eq_div]
  rw [this]
  have : (1/L₀)*δ ≤ needLip B₀ L₀ c₀ * δ := mul_le_mul_of_nonneg_right hK1 hδ
  linarith

theorem deletionNeed_lipS {B₀ L₀ c₀ P s M δ : ℝ} (hL : 0 < L₀) (hδ : 0 ≤ δ) :
    deletionNeed B₀ L₀ c₀ P (s+δ) M ≤
      deletionNeed B₀ L₀ c₀ P s M + needLip B₀ L₀ c₀ * δ := by
  rw [deletionNeed_eq, deletionNeed_eq]
  have hK := one_le_needLip B₀ L₀ c₀
  have hKδ : δ ≤ needLip B₀ L₀ c₀ * δ := by nlinarith
  apply clip_mono_add (by nlinarith) (by linarith) (by linarith)
  have : (P + L₀*(s+δ) - B₀*M)/L₀ = (P + L₀*s - B₀*M)/L₀ + δ := by
    rw [show P + L₀*(s+δ) - B₀*M = (P + L₀*s - B₀*M) + L₀*δ by ring, add_div,
      mul_div_cancel_left₀ _ hL.ne']
  rw [this]; linarith

theorem deletionNeed_lipM {B₀ L₀ c₀ P s M δ : ℝ} (hL : 0 < L₀) :
    deletionNeed B₀ L₀ c₀ P s (M+δ) ≤
      deletionNeed B₀ L₀ c₀ P s M + needLip B₀ L₀ c₀ * |δ| := by
  rw [deletionNeed_eq, deletionNeed_eq]
  have hK := one_le_needLip B₀ L₀ c₀
  have hc : |c₀| ≤ needLip B₀ L₀ c₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hb : |B₀|/L₀ ≤ needLip B₀ L₀ c₀ := (le_max_right _ _).trans (le_max_right _ _)
  have hδ := abs_nonneg δ
  apply clip_mono_add (by nlinarith) (by nlinarith)
  · have h1 : -(c₀*δ) ≤ |c₀| * |δ| := by
      rw [← abs_mul]; exact neg_le_abs _
    have h2 : |c₀| * |δ| ≤ needLip B₀ L₀ c₀ * |δ| := mul_le_mul_of_nonneg_right hc hδ
    nlinarith
  · have : (P + L₀*s - B₀*(M+δ))/L₀ = (P + L₀*s - B₀*M)/L₀ + (-(B₀*δ))/L₀ := by
      rw [show P + L₀*s - B₀*(M+δ) = (P + L₀*s - B₀*M) + (-(B₀*δ)) by ring, add_div]
    rw [this]
    have h1 : -(B₀*δ) ≤ |B₀| * |δ| := by rw [← abs_mul]; exact neg_le_abs _
    have h2 : (-(B₀*δ))/L₀ ≤ (|B₀|/L₀) * |δ| := by
      rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right h1 hL.le
    have h3 : (|B₀|/L₀) * |δ| ≤ needLip B₀ L₀ c₀ * |δ| := mul_le_mul_of_nonneg_right hb hδ
    linarith

/-! ### The two native prices -/

/-- Native prime-slot cost `κ·max 0 s`: every retained slot is paid naturally. -/
def nativePrice (κ : ℝ) (hκ : 0 ≤ κ) : Price where
  f _ _ s _ := κ * max 0 s
  nonneg _ _ _ _ := mul_nonneg hκ (le_max_left _ _)
  mono _ _ _ _ _ _ _ hs := mul_le_mul_of_nonneg_left (max_le_max le_rfl hs) hκ
  lip := κ
  lip_nonneg := hκ
  lipP _ _ _ _ _ hδ := by nlinarith
  lipS _ _ s _ δ hδ := by
    have : max 0 (s+δ) ≤ max 0 s + δ :=
      max_le (by linarith [le_max_left 0 s]) (by linarith [le_max_right 0 s])
    nlinarith
  lipM _ _ _ _ δ := by nlinarith [abs_nonneg δ]

/-- Parent deletion price `κ·deletionNeed B₀ L₀ c₀ P s M` (CF (5.2)). -/
def parentPrice (κ B₀ L₀ c₀ : ℝ) (hκ : 0 ≤ κ) (hL : 0 < L₀) : Price where
  f _ P s M := κ * deletionNeed B₀ L₀ c₀ P s M
  nonneg _ _ _ _ := mul_nonneg hκ (deletionNeed_nonneg _ _ _ _ _ _)
  mono _ _ _ _ _ _ hP hs := mul_le_mul_of_nonneg_left (deletionNeed_mono hL hP hs) hκ
  lip := κ * needLip B₀ L₀ c₀
  lip_nonneg := mul_nonneg hκ (zero_le_one.trans (one_le_needLip _ _ _))
  lipP _ P s M δ hδ := by
    have := mul_le_mul_of_nonneg_left
      (deletionNeed_lipP (B₀:=B₀) (c₀:=c₀) (P:=P) (s:=s) (M:=M) hL hδ) hκ
    linarith
  lipS _ P s M δ hδ := by
    have := mul_le_mul_of_nonneg_left
      (deletionNeed_lipS (B₀:=B₀) (c₀:=c₀) (P:=P) (s:=s) (M:=M) hL hδ) hκ
    linarith
  lipM _ P s M δ := by
    have := mul_le_mul_of_nonneg_left
      (deletionNeed_lipM (B₀:=B₀) (c₀:=c₀) (P:=P) (s:=s) (M:=M) (δ:=δ) hL) hκ
    linarith

theorem nativePrice_f (κ : ℝ) (hκ : 0 ≤ κ) (w P s M : ℝ) :
    (nativePrice κ hκ).f w P s M = κ * max 0 s := rfl

theorem parentPrice_f (κ B₀ L₀ c₀ : ℝ) (hκ : 0 ≤ κ) (hL : 0 < L₀) (w P s M : ℝ) :
    (parentPrice κ B₀ L₀ c₀ hκ hL).f w P s M = κ * deletionNeed B₀ L₀ c₀ P s M := rfl

/-- The parent price never exceeds the native price: deleting more than everything is
never required. -/
theorem parentPrice_le_native (κ B₀ L₀ c₀ : ℝ) (hκ : 0 ≤ κ) (hL : 0 < L₀) (w P s M : ℝ) :
    (parentPrice κ B₀ L₀ c₀ hκ hL).f w P s M ≤ (nativePrice κ hκ).f w P s M := by
  rw [parentPrice_f, nativePrice_f]
  apply mul_le_mul_of_nonneg_left _ hκ
  exact max_le_max le_rfl (min_le_left _ _)

end
end QRH.SilDensitySplit.CubeFree
