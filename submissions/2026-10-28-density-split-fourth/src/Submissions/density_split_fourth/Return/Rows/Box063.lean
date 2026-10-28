/- Fourth density transition: exact return rectangle 063.
Generated from the audited rational receipt using the inherited Bernstein checker. -/
import Submissions.density_split_fourth.Return.Formulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.DensitySplitThird.Return
noncomputable section
def row063_oldSmall_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(139552752673627213041961/47793395491485468750:ℝ), (1442396835337061494783591/238966977457427343750:ℝ), (862654178756290768003367/238966977457427343750:ℝ), (12855689281155459825509/26551886384158593750:ℝ)],
![(629262941911363641241421/119483488728713671875:ℝ), (248497351693804492961099/23896697745742734375:ℝ), (672094088991647091552527/119483488728713671875:ℝ), (6251153474433476998717/13275943192079296875:ℝ)],
![(563027881426039417273037/238966977457427343750:ℝ), (1050497239969252455849799/238966977457427343750:ℝ), (245202743051405442725881/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row063_oldSmall_identity (δ p : ℝ) : rowMargin .oldSmall .old δ p =
 Record12518109.Bernstein.bsum 2 3 (888810990539170641257011/2062345986455961600000000:ℝ) row063_oldSmall_coefficients (3/8:ℝ) (27/64:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSmall,edgeC_oldSmall,row063_oldSmall_coefficients,Fin.sum_univ_succ] <;> ring
theorem row063_oldSmall_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSmall .old δ p := by
 rw [row063_oldSmall_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row063_oldSmall_coefficients]
def row063_oldSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(16086155895892351071961/47793395491485468750:ℝ), (141887009005364955313591/238966977457427343750:ℝ), (69483243569395218613367/238966977457427343750:ℝ), (1984853237175272886527/79655659152475781250:ℝ)],
![(81633224345396036671421/119483488728713671875:ℝ), (27611300835824965331099/23896697745742734375:ℝ), (61096563114814303962527/119483488728713671875:ℝ), (780590719207846326151/39827829576237890625:ℝ)],
![(85101430182778517983037/238966977457427343750:ℝ), (139762402279525179144799/238966977457427343750:ℝ), (28641961055320691518381/119483488728713671875:ℝ), (0:ℝ)] ]
theorem row063_oldSwitch_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (52228722963638072387011/2062345986455961600000000:ℝ) row063_oldSwitch_coefficients (3/8:ℝ) (27/64:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_oldSwitch,edgeC_oldSwitch,row063_oldSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row063_oldSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
 rw [row063_oldSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row063_oldSwitch_coefficients]
def row063_newSwitch_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(42027128430925081/127796319843750:ℝ), (371344291832168311/638981599218750:ℝ), (182161189147198007/638981599218750:ℝ), (1728892141072789/70997955468750:ℝ)],
![(213350898720959741/319490799609375:ℝ), (72289743697377179/63898159921875:ℝ), (160256716682854367/319490799609375:ℝ), (676924771325357/35498977734375:ℝ)],
![(222624647487294077/638981599218750:ℝ), (366338527604638879/638981599218750:ℝ), (75269387919609901/319490799609375:ℝ), (0:ℝ)] ]
theorem row063_newSwitch_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
 Record12518109.Bernstein.bsum 2 3 (144586930497728131/5514574233600000000:ℝ) row063_newSwitch_coefficients (3/8:ℝ) (27/64:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newSwitch,edgeC_newSwitch,row063_newSwitch_coefficients,Fin.sum_univ_succ] <;> ring
theorem row063_newSwitch_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
 rw [row063_newSwitch_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row063_newSwitch_coefficients]
def row063_newTop_coefficients : Fin 3 → Fin 4 → ℝ := ![ ![(5385406230428445146817927919/30373351337264062500000000:ℝ), (8065389778851616967863651853/30373351337264062500000000:ℝ), (591420105961526219455383041/6074670267452812500000000:ℝ), (843199763899076360895973/1124938938417187500000000:ℝ)],
![(6071568856197304352809326319/15186675668632031250000000:ℝ), (1819098890484283460660777761/3037335133726406250000000:ℝ), (1655035003726597595896218743/7593337834316015625000000:ℝ), (0:ℝ)],
![(7045715850200963558800724719/30373351337264062500000000:ℝ), (5405077452198977355403532503/15186675668632031250000000:ℝ), (33675262055364032951438768867/242986810698112500000000000:ℝ), (36461108175050502359524873/8999511507337500000000000:ℝ)] ]
theorem row063_newTop_identity (δ p : ℝ) : rowMargin .newTop .old δ p =
 Record12518109.Bernstein.bsum 2 3 (351467518884151141193950481/262129771619942400000000000000:ℝ) row063_newTop_coefficients (3/8:ℝ) (27/64:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
 norm_num [rowMargin,Ebase,V,D,A,C0,Z,U,oldD,oldC,countJ,countN,countT,RN,MN,DJ,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,dm,dp,d0,physicalB,physicalLambda,physicalCap,parentCapB,parentCapLambda,countCB,countCL,countCap,fourthCountB,fourthCountL,naturalK,sMinus,mMinus,reserve,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,edgeD_newTop,edgeC_newTop,row063_newTop_coefficients,Fin.sum_univ_succ] <;> ring
theorem row063_newTop_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
 (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newTop .old δ p := by
 rw [row063_newTop_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [row063_newTop_coefficients]
end
end QRH.DensitySplitThird.Return
