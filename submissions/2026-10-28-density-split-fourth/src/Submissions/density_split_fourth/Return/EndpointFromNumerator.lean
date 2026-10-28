/- Repeated marks: fork of Collet's final-stage module EndpointFromNumerator (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): instances at theta = 174799/200000 -/
import Submissions.density_split_fourth.ReturnD.Transport.FinalCommonProbe
import Submissions.density_split_fourth.Return.TransportInstances
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace QRH.DensitySplitThird.Return
open QRH.Record1252270103Return
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
namespace Final
local instance : Geometry.Parameters := Geometry.finalParameters
local instance : Geometry.BoundsN := Geometry.finalBounds
abbrev LiteralNumeratorInput : Prop := GenericPhysical.FinalAssembly.ChosenFiniteNumeratorInput

theorem beta_of_literal_numerator (h : LiteralNumeratorInput) :
 HeckeZeroSupremum.beta≤QRH.DensitySplitThird.Return.theta :=
 GenericPhysical.FinalAssembly.beta_le_theta_of_finite_numerator h

theorem hecke_of_literal_numerator (h : LiteralNumeratorInput) (χ : Character) (s : ℂ)
 (hs : QRH.DensitySplitThird.Return.theta<s.re) (hpole : s≠1 ∨ χ.residue≠1) :
 LFunction χ s≠0 := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt χ
 ((beta_of_literal_numerator h).trans_lt hs) hpole

theorem dirichlet_of_literal_numerator (h : LiteralNumeratorInput) {q:ℕ} [NeZero q]
 (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : QRH.DensitySplitThird.Return.theta<s.re)
 (hpole : ¬(χ=1 ∧ s=1)) : χ.LFunction s≠0 :=
 Cycle25.dirichlet_of_hecke (by norm_num [QRH.DensitySplitThird.Return.theta,QRH.DensitySplitThird.Return.c])
 (hecke_of_literal_numerator h) χ s hs hpole

theorem zeta_of_literal_numerator (h : LiteralNumeratorInput) (s:ℂ)
 (hs : QRH.DensitySplitThird.Return.theta<s.re) : riemannZeta s≠0 :=
 Cycle25.zeta_of_hecke (by norm_num [QRH.DensitySplitThird.Return.theta,QRH.DensitySplitThird.Return.c])
 (hecke_of_literal_numerator h) s hs
end Final
end
end QRH.DensitySplitThird.Return
