/- Repeated marks: generated final-return certificate (see research/repeated-marks/gen_return_lean.py).
Layout and definitions follow Collet's final stage (Record1252270103Finite, Apache-2.0). -/

import Submissions.arvi_single_stage_20261025.FinalReturn.ReturnFormulas
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace QRH.RepeatedMarks.Return
noncomputable section
def admission05_00_coefficients : Fin 1 → Fin 2 → ℝ := ![![(2115720527452166397407/889034918041606397407:ℝ), (0:ℝ)]]
theorem admission05_00_identity (δ p : ℝ) : admissionGuard .C δ p 0 =
 Record12518109.Bernstein.bsum 0 1 (3218488980797471987035/1778069836083212794814:ℝ) admission05_00_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_00_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_00_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 0 := by
 rw [admission05_00_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_00_coefficients]
def admission05_01_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1226685609410560000000/889034918041606397407:ℝ), (0:ℝ)]]
theorem admission05_01_identity (δ p : ℝ) : admissionGuard .C δ p 1 =
 Record12518109.Bernstein.bsum 0 1 (1164727031377932794814/889034918041606397407:ℝ) admission05_01_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_01_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_01_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 1 := by
 rw [admission05_01_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_01_coefficients]
def admission05_02_coefficients : Fin 1 → Fin 2 → ℝ := ![![(1466689488397397859949977091/2222587295104015993517500000:ℝ), (0:ℝ)]]
theorem admission05_02_identity (δ p : ℝ) : admissionGuard .C δ p 2 =
 Record12518109.Bernstein.bsum 0 1 (2978485101810634127085022909/4445174590208031987035000000:ℝ) admission05_02_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_02_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_02_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 2 := by
 rw [admission05_02_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_02_coefficients]
def admission05_03_coefficients : Fin 2 → Fin 3 → ℝ := ![![(468958538424696585830823296/8001314262374457576663:ℝ), (619528206304178853314893184/8001314262374457576663:ℝ), (16824417889644865062674432/889034918041606397407:ℝ)],
![(317160843991920460756566272/8001314262374457576663:ℝ), (18605865334947896919798016/470665544845556328039:ℝ), (0:ℝ)]]
theorem admission05_03_identity (δ p : ℝ) : admissionGuard .C δ p 3 =
 Record12518109.Bernstein.bsum 1 2 (1338962503464123815232829/1365557634111907426417152:ℝ) admission05_03_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_03_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_03_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 3 := by
 rw [admission05_03_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_03_coefficients]
def admission05_04_coefficients : Fin 2 → Fin 3 → ℝ := ![![(22018755471151781267324628236007/2222587295104015993517500000:ℝ), (9856:ℝ), (0:ℝ)],
![(17252294155714925048447536024181/1111293647552007996758750000:ℝ), (1455939422135975326511225864704/69455852972000499797421875:ℝ), (381246093031761168266882932352/69455852972000499797421875:ℝ)]]
theorem admission05_04_identity (δ p : ℝ) : admissionGuard .C δ p 4 =
 Record12518109.Bernstein.bsum 1 2 (688030058518256483356640291979/4551858780373024754723840000000:ℝ) admission05_04_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_04_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_04_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 4 := by
 rw [admission05_04_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_04_coefficients]
def admission05_05_coefficients : Fin 2 → Fin 3 → ℝ := ![![(4604624559097322302361690445671/444517459020803198703500000:ℝ), (34557331541788482495690411392543/1666940471328011995138125000:ℝ), (34499092201319501340923922088543/3333880942656023990276250000:ℝ)],
![(0:ℝ), (257317143234972350374455783647/1666940471328011995138125000:ℝ), (432697120961521092254764247647/3333880942656023990276250000:ℝ)]]
theorem admission05_05_identity (δ p : ℝ) : admissionGuard .C δ p 5 =
 Record12518109.Bernstein.bsum 1 2 (171286107615572893544539617152493/1864441356440790939534884864000000:ℝ) admission05_05_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_05_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_05_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 5 := by
 rw [admission05_05_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_05_coefficients]
def admission05_06_coefficients : Fin 2 → Fin 4 → ℝ := ![![(61836361147664582316674199812542438133810184084734900116/20562309958639285375300277634105000705919931015625:ℝ), (123014012655587242583056998404694869629513903312730442644/20562309958639285375300277634105000705919931015625:ℝ), (61179618682353604173748813177164207544036519227995542528/20562309958639285375300277634105000705919931015625:ℝ), (0:ℝ)],
![(80530894582153191641140076985316271882096421308922321784/20562309958639285375300277634105000705919931015625:ℝ), (178584507015689899577727878645918563770247447737788224376/20562309958639285375300277634105000705919931015625:ℝ), (116242804253015036911855787999672449873748453779490486272/20562309958639285375300277634105000705919931015625:ℝ), (404159979940611170655436020339822116340849496680546304/456940221303095230562228391869000015687109578125:ℝ)]]
theorem admission05_06_identity (δ p : ℝ) : admissionGuard .C δ p 6 =
 Record12518109.Bernstein.bsum 1 3 (19107906662926875512296819139854680539942196582160603/89838103029958947090378599668580355084211239936000000:ℝ) admission05_06_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_06_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_06_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 6 := by
 rw [admission05_06_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_06_coefficients]
def admission05_07_coefficients : Fin 2 → Fin 3 → ℝ := ![![(769288724607220907317261971309690319660803552538578943/17783619423688030594854294170036757367282102500000:ℝ), (11675559068373751296208352373747991368536668975358504/185246035663416985363065564271216222575855234375:ℝ), (245407269878962237883651492589668320041695385211264/12349735710894465690871037618081081505057015625:ℝ)],
![(708521730803262836055883853459229878706579553380509/30767507653439499299055872266499580220211250000:ℝ), (14696221369692961361835801008715304147481456282864/640989742779989568730330672218741254587734375:ℝ), (0:ℝ)]]
theorem admission05_07_identity (δ p : ℝ) : admissionGuard .C δ p 7 =
 Record12518109.Bernstein.bsum 1 2 (1917244295929392483466027285856783750325745196963/4200790378282939637631095093452742686066176000000:ℝ) admission05_07_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_07_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_07_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 7 := by
 rw [admission05_07_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_07_coefficients]
def admission05_08_coefficients : Fin 2 → Fin 4 → ℝ := ![![(0:ℝ), (481986093158919051696624326897673876631979380208448147549000923483075857/6817159384460069883390259359768771336849991776476332032000000000000:ℝ), (48379255073686065663089644607919269136334095292475825247749803666297906747/340857969223003494169512967988438566842499588823816601600000000000000:ℝ), (24273454571745580266866916712487616505858673727670272605637720356784113897/340857969223003494169512967988438566842499588823816601600000000000000:ℝ)],
![(19490489922711613662703340384779006827405358340994867144000055515570150171/37873107691444832685501440887604285204722176535979622400000000000000:ℝ), (31970974967607522773476205875018899851096175950712498111030668817379865461/20050468777823734951147821646378739226029387577871564800000000000000:ℝ), (112202046608461128664644630574706779896818809352015105273267004580147215551/68171593844600698833902593597687713368499917764763320320000000000000:ℝ), (192911487691777427719126055410019237665842822235204066272948712430369716457/340857969223003494169512967988438566842499588823816601600000000000000:ℝ)]]
theorem admission05_08_identity (δ p : ℝ) : admissionGuard .C δ p 8 =
 Record12518109.Bernstein.bsum 1 3 (687721196545854523198545093449045378141061001482592793952847742510067163741/40665939733160403843105135493284404185934603246992761382607257600000000000000:ℝ) admission05_08_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_08_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_08_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 8 := by
 rw [admission05_08_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_08_coefficients]
def admission05_09_coefficients : Fin 2 → Fin 4 → ℝ := ![![(388564233334974891409811595748757284943359645797785211/395191542748622902107873203778594608161824500000:ℝ), (1416929375352276317542198132268859452421736737561040349/555738106990250956089196692813648667727565703125:ℝ), (1195678494038840089617325253197228064554876102252054016/555738106990250956089196692813648667727565703125:ℝ), (7226117031562216295897183996651789522995335905800192/12349735710894465690871037618081081505057015625:ℝ)],
![(74507512781246156299741669042231732514961930029596209/197595771374311451053936601889297304080912250000:ℝ), (418116693002102805453982007205217202034645229802020526/555738106990250956089196692813648667727565703125:ℝ), (208556518768466866507380757996106496062236912827352064/555738106990250956089196692813648667727565703125:ℝ), (0:ℝ)]]
theorem admission05_09_identity (δ p : ℝ) : admissionGuard .C δ p 9 =
 Record12518109.Bernstein.bsum 1 3 (29283860573970936126031861584727135802243253957781/1618704559098359407033848642677123515030833152000000:ℝ) admission05_09_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_09_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_09_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 9 := by
 rw [admission05_09_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_09_coefficients]
def admission05_10_coefficients : Fin 3 → Fin 4 → ℝ := ![![(31281340664035654726793203210885876/625102676748004498176796875:ℝ), (80348692875854862930162659806208756/625102676748004498176796875:ℝ), (13382010526102658046234901444388864/125020535349600899635359375:ℝ), (1189536543994265132419643375108096/41673511783200299878453125:ℝ)],
![(44457212018245421158795268511333232/625102676748004498176796875:ℝ), (21381318282461403778338749825743024/125020535349600899635359375:ℝ), (80550729022870799372106537215352832/625102676748004498176796875:ℝ), (6034018047829489782438952199323648/208367558916001499392265625:ℝ)],
![(253094648109537915022359846513776/12256915230353029376015625:ℝ), (505154273355588968315583674993776/12256915230353029376015625:ℝ), (403284205660810204498598125568/19611064368564847001625:ℝ), (0:ℝ)]]
theorem admission05_10_identity (δ p : ℝ) : admissionGuard .C δ p 10 =
 Record12518109.Bernstein.bsum 2 3 (147051805271921418464558603667/34272819052220421682626560000000:ℝ) admission05_10_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_10_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_10_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 10 := by
 rw [admission05_10_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_10_coefficients]
def admission05_11_coefficients : Fin 2 → Fin 3 → ℝ := ![![(645375704947572601821103581193373528153968083378364289/17783619423688030594854294170036757367282102500000:ℝ), (5894414382603432610381603048840913831590237377898852/111147621398050191217839338562729733545513140625:ℝ), (1039826288388782114977726095099041577723551769211264/61748678554472328454355188090405407525285078125:ℝ)],
![(10008886411005305919396578692142256002434555602366227/523047630108471488083949828530492863743591250000:ℝ), (622411319831472173073846219696031598370693581703736/32690476881779468005246864283155803983974453125:ℝ), (0:ℝ)]]
theorem admission05_11_identity (δ p : ℝ) : admissionGuard .C δ p 11 =
 Record12518109.Bernstein.bsum 1 2 (44546421644180579492213373350061238551166318368817/119022394051349956399547694314494376105208320000000:ℝ) admission05_11_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_11_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_11_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 11 := by
 rw [admission05_11_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_11_coefficients]
def admission05_12_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission05_12_identity (δ p : ℝ) : admissionGuard .C δ p 12 =
 Record12518109.Bernstein.bsum 0 0 (164999/10000000:ℝ) admission05_12_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_12_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_12_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 12 := by
 rw [admission05_12_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_12_coefficients]
def admission05_13_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission05_13_identity (δ p : ℝ) : admissionGuard .C δ p 13 =
 Record12518109.Bernstein.bsum 0 0 (1343952974242639915807071/122668560941056000000000000:ℝ) admission05_13_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_13_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_13_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 13 := by
 rw [admission05_13_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_13_coefficients]
def admission05_14_coefficients : Fin 1 → Fin 1 → ℝ := ![![(0:ℝ)]]
theorem admission05_14_identity (δ p : ℝ) : admissionGuard .C δ p 14 =
 Record12518109.Bernstein.bsum 0 0 (1:ℝ) admission05_14_coefficients (231/512:ℝ) (117/256:ℝ) (63/128:ℝ) (1/2:ℝ) δ p := by
 norm_num [admissionGuard,lowerM,upperM,naturalM,derivativeD,derivativeA,derivativeC,derivativeU,derivativeJ,rowMargin,Ebase,countN,countJ,countT,RN,MN,DJ,V,D,A,C0,Z,U,oldD,oldC,branchB,branchL,branchCap,branchZ,isCap,c,h,theta,ell,x,y,kappa,ds,dk,dp,d0,physicalB,physicalLambda,countCB,countCL,naturalK,rowFee,numeratorCap,Record12518109.Bernstein.bsum,Record12518109.Bernstein.bterm,admission05_14_coefficients,Fin.sum_univ_succ] <;> ring
theorem admission05_14_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) : 0 < admissionGuard .C δ p 14 := by
 rw [admission05_14_identity]
 apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
 intro i j
 fin_cases i <;> fin_cases j <;> norm_num [admission05_14_coefficients]
theorem admission05_all {δ p : ℝ} (hδ : δ ∈ Set.Icc (231/512:ℝ) (117/256:ℝ))
 (hp : p ∈ Set.Icc (63/128:ℝ) (1/2:ℝ)) (j : Fin 15) : 0<admissionGuard .C δ p j := by
 fin_cases j
 · exact admission05_00_pos hδ hp
 · exact admission05_01_pos hδ hp
 · exact admission05_02_pos hδ hp
 · exact admission05_03_pos hδ hp
 · exact admission05_04_pos hδ hp
 · exact admission05_05_pos hδ hp
 · exact admission05_06_pos hδ hp
 · exact admission05_07_pos hδ hp
 · exact admission05_08_pos hδ hp
 · exact admission05_09_pos hδ hp
 · exact admission05_10_pos hδ hp
 · exact admission05_11_pos hδ hp
 · exact admission05_12_pos hδ hp
 · exact admission05_13_pos hδ hp
 · exact admission05_14_pos hδ hp
end
end QRH.RepeatedMarks.Return
