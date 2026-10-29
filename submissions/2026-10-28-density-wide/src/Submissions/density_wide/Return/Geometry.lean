/- Repeated marks: fork of Collet's final-stage module Geometry (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): the PR69 `Parameters` at theta = 174799/200000, h = 8053/10000 -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.Geometry
import Submissions.density_wide.Return.Constants
set_option autoImplicit false
namespace QRH.DensityWide.Return.Geometry
open QRH.Record1252270103Return QRH.Record1252270103Return.Geometry
noncomputable def finalParameters : Parameters where
  theta := QRH.DensityWide.Return.theta
  ell := QRH.DensityWide.Return.ell
  x := QRH.DensityWide.Return.x
  y := QRH.DensityWide.Return.y
  ell_pos := by norm_num [QRH.DensityWide.Return.ell,QRH.DensityWide.Return.c]
  sixth_lt_ell := by norm_num [QRH.DensityWide.Return.ell,QRH.DensityWide.Return.c]
  ell_lt_fifth := by norm_num [QRH.DensityWide.Return.ell,QRH.DensityWide.Return.c]
  ell_lt_x := by norm_num [QRH.DensityWide.Return.x,QRH.DensityWide.Return.ell,QRH.DensityWide.Return.c,QRH.DensityWide.Return.h]
  x_lt_y := by norm_num [QRH.DensityWide.Return.x,QRH.DensityWide.Return.y,QRH.DensityWide.Return.ell,QRH.DensityWide.Return.c,QRH.DensityWide.Return.h]
  y_lt_half := by norm_num [QRH.DensityWide.Return.y,QRH.DensityWide.Return.ell,QRH.DensityWide.Return.c,QRH.DensityWide.Return.h]
  x_add_y := by dsimp [QRH.DensityWide.Return.x,QRH.DensityWide.Return.y];ring
  dilation_gap := by norm_num [QRH.DensityWide.Return.x,QRH.DensityWide.Return.y,QRH.DensityWide.Return.ell,QRH.DensityWide.Return.c,QRH.DensityWide.Return.h]
  tuple_margin_neg := by norm_num [QRH.DensityWide.Return.x,QRH.DensityWide.Return.y,QRH.DensityWide.Return.ell,QRH.DensityWide.Return.c,QRH.DensityWide.Return.h]
  signal_boundary := QRH.DensityWide.Return.geometry_mellin
end QRH.DensityWide.Return.Geometry
