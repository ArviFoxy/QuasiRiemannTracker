/- Repeated marks: fork of Collet's final-stage module Geometry (Record1252270103Return, Apache-2.0),
re-instantiated with the final constants of the repeated-mark graph. -/
/- Modified by Sil (2026-10-26): the PR69 `Parameters` at theta = 174799/200000, h = 8053/10000 -/
import Submissions.hailey_collet_1252270103.Record1252270103Return.Geometry
import Submissions.density_split_fine_chain.Return.Constants
set_option autoImplicit false
namespace QRH.SilDensitySplit.Return.Geometry
open QRH.Record1252270103Return QRH.Record1252270103Return.Geometry
noncomputable def finalParameters : Parameters where
  theta := QRH.SilDensitySplit.Return.theta
  ell := QRH.SilDensitySplit.Return.ell
  x := QRH.SilDensitySplit.Return.x
  y := QRH.SilDensitySplit.Return.y
  ell_pos := by norm_num [QRH.SilDensitySplit.Return.ell,QRH.SilDensitySplit.Return.c]
  sixth_lt_ell := by norm_num [QRH.SilDensitySplit.Return.ell,QRH.SilDensitySplit.Return.c]
  ell_lt_fifth := by norm_num [QRH.SilDensitySplit.Return.ell,QRH.SilDensitySplit.Return.c]
  ell_lt_x := by norm_num [QRH.SilDensitySplit.Return.x,QRH.SilDensitySplit.Return.ell,QRH.SilDensitySplit.Return.c,QRH.SilDensitySplit.Return.h]
  x_lt_y := by norm_num [QRH.SilDensitySplit.Return.x,QRH.SilDensitySplit.Return.y,QRH.SilDensitySplit.Return.ell,QRH.SilDensitySplit.Return.c,QRH.SilDensitySplit.Return.h]
  y_lt_half := by norm_num [QRH.SilDensitySplit.Return.y,QRH.SilDensitySplit.Return.ell,QRH.SilDensitySplit.Return.c,QRH.SilDensitySplit.Return.h]
  x_add_y := by dsimp [QRH.SilDensitySplit.Return.x,QRH.SilDensitySplit.Return.y];ring
  dilation_gap := by norm_num [QRH.SilDensitySplit.Return.x,QRH.SilDensitySplit.Return.y,QRH.SilDensitySplit.Return.ell,QRH.SilDensitySplit.Return.c,QRH.SilDensitySplit.Return.h]
  tuple_margin_neg := by norm_num [QRH.SilDensitySplit.Return.x,QRH.SilDensitySplit.Return.y,QRH.SilDensitySplit.Return.ell,QRH.SilDensitySplit.Return.c,QRH.SilDensitySplit.Return.h]
  signal_boundary := QRH.SilDensitySplit.Return.geometry_mellin
end QRH.SilDensitySplit.Return.Geometry
