/- Copyright (c) 2026 Joseph Bebel. -/
/- Generated/adapted by docs/research/tools/fine_return_lean.py.
Finite return algebra adapted from Hailey Collet, Sil and Sussman's PR86
at a284f4da56f7d65b3b4bd4c3f6b00699f9dddde1, Apache-2.0.
Two full source providers remain explicit; no missing estimate is asserted. -/
import Candidate.Local.Qrh.JointDetector.FineReturn.PowerRows
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unnecessarySeqFocus false
namespace Qrh.JointDetector.FineReturn.FinalEdges
open QRH.Record1252270103Return
noncomputable section

def row160_coefficients : Fin 3 → Fin 3 → ℝ := ![![(170564384302205986829293/1893039811875000000:ℝ), (287116361749864359136/1971916470703125:ℝ), (1646737950025676335168/29578747060546875:ℝ)],
![(206338917330676614021457/1893039811875000000:ℝ), (4324954426774605745376/29578747060546875:ℝ), (1111405706345792948608/29578747060546875:ℝ)],
![(93599022375258347578967/2524053082500000000:ℝ), (1091421129137016915656/29578747060546875:ℝ), (0:ℝ)]]
theorem row160_identity (δ p : ℝ) : rowMargin .oldSwitch .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (1006140340778155991659/55138780938240000000000:ℝ) row160_coefficients
      (33/64:ℝ) (69/128:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [power_oldSwitch_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row160_coefficients, Fin.sum_univ_succ, power_oldSwitch_capP] <;> ring
theorem row160_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (33/64:ℝ) (69/128:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .capP δ p := by
  rw [row160_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row160_coefficients]

def row161_coefficients : Fin 3 → Fin 4 → ℝ := ![![(53845393781535328852316537291/2150159837606241234609375000:ℝ), (261008643179213851396632466571/6450479512818723703828125000:ℝ), (52586062198384457790622677349/3225239756409361851914062500:ℝ), (0:ℝ)],
![(72044902012775816358509562827/1075079918803120617304687500:ℝ), (353686119082231034647912471523/3225239756409361851914062500:ℝ), (150280998892766526263069160803/3225239756409361851914062500:ℝ), (533291171665188464520597529/358359972934373539101562500:ℝ)],
![(110631110926505109644702588363/2150159837606241234609375000:ℝ), (23831818618092243711199548827/258019180512748948153125000:ℝ), (318827481555531573380484046883/6450479512818723703828125000:ℝ), (4876928186371974854955899033/716719945868747078203125000:ℝ)]]
theorem row161_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (22308144833413917262909432373/916366814765148405760000000000:ℝ) row161_coefficients
      (69/128:ℝ) (3/4:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
  rw [power_oldSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row161_coefficients, Fin.sum_univ_succ, power_oldSwitch_old] <;> ring
theorem row161_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
  rw [row161_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row161_coefficients]

def row162_coefficients : Fin 3 → Fin 4 → ℝ := ![![(581318295755297648376924121013/1075079918803120617304687500:ℝ), (370974046961759817214433411617/358359972934373539101562500:ℝ), (266276894445170989194984931919/537539959401560308652343750:ℝ), (0:ℝ)],
![(754104635374818710881597720409/537539959401560308652343750:ℝ), (482340360859205835439571665369/179179986467186769550781250:ℝ), (699251241962436950656467114187/537539959401560308652343750:ℝ), (557014875073197903816648721/59726662155728923183593750:ℝ)],
![(432288605627963500276527081541/215015983760624123460937500:ℝ), (1787142187092840996789285861721/358359972934373539101562500:ℝ), (4328341601510879743690638848011/1075079918803120617304687500:ℝ), (125168803981993564673935185617/119453324311457846367187500:ℝ)]]
theorem row162_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (1827961346253405416017294575271/98967615994636027822080000000000:ℝ) row162_coefficients
      (69/128:ℝ) (3/4:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
  rw [power_oldSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row162_coefficients, Fin.sum_univ_succ, power_oldSwitch_old] <;> ring
theorem row162_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
  rw [row162_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row162_coefficients]

def row163_coefficients : Fin 3 → Fin 4 → ℝ := ![![(642736987665277914301552780142/268769979700780154326171875:ℝ), (1395657174105491764514688476588/268769979700780154326171875:ℝ), (2628179753385029729055996641/796355495409718975781250:ℝ), (3305012207089966408947277343/6636295795080991464843750:ℝ)],
![(261105302166638190628100982848/53753995940156030865234375:ℝ), (509631170365730328982935909056/53753995940156030865234375:ℝ), (9209556825462595398642034304/1990888738524297439453125:ℝ), (0:ℝ)],
![(2895775459341162078432386121248/268769979700780154326171875:ℝ), (7738542484026432737802769527392/268769979700780154326171875:ℝ), (16868911414604133617036532448/663629579508099146484375:ℝ), (24551634445627721140363114016/3318147897540495732421875:ℝ)]]
theorem row163_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (418498014561324016351810607/27491004442954452172800000000:ℝ) row163_coefficients
      (69/128:ℝ) (3/4:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
  rw [power_oldSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row163_coefficients, Fin.sum_univ_succ, power_oldSwitch_old] <;> ring
theorem row163_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
  rw [row163_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row163_coefficients]

def row164_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3496159204239293830372186838012/268769979700780154326171875:ℝ), (2848890292764605010546447279128/89589993233593384775390625:ℝ), (6651253791333803804340093042907/268769979700780154326171875:ℝ), (35566769585315390206489769023/5972666215572892318359375:ℝ)],
![(970134099656857885549307591552/53753995940156030865234375:ℝ), (638590053940204451198194356608/17917998646718676955078125:ℝ), (945768228252153405453775478272/53753995940156030865234375:ℝ), (0:ℝ)],
![(18334794369908908012828566861248/268769979700780154326171875:ℝ), (17180311766406057509106488280512/89589993233593384775390625:ℝ), (48159030305678862506376059000128/268769979700780154326171875:ℝ), (332276214849689776638336911552/5972666215572892318359375:ℝ)]]
theorem row164_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (67750469967469120712471943701/4948380799731801391104000000000:ℝ) row164_coefficients
      (69/128:ℝ) (3/4:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
  rw [power_oldSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row164_coefficients, Fin.sum_univ_succ, power_oldSwitch_old] <;> ring
theorem row164_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
  rw [row164_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row164_coefficients]

def row165_coefficients : Fin 3 → Fin 4 → ℝ := ![![(885635248874981466358406442584/10750799188031206173046875:ℝ), (59023684076358705471024586294592/268769979700780154326171875:ℝ), (17238692955460457055613079511578/89589993233593384775390625:ℝ), (20347103602135956530855850298/368683099726721748046875:ℝ)],
![(3734737668464398473849537686528/53753995940156030865234375:ℝ), (7421140092384581799733511146496/53753995940156030865234375:ℝ), (1228844863336193754430824486656/17917998646718676955078125:ℝ), (0:ℝ)],
![(25791256303409863154885026475008/53753995940156030865234375:ℝ), (373661879347264976682473093362688/268769979700780154326171875:ℝ), (120205080509506380254385483133952/89589993233593384775390625:ℝ), (158997508902839398918996554752/368683099726721748046875:ℝ)]]
theorem row165_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (1187097503946469566256541751/91636681476514840576000000000:ℝ) row165_coefficients
      (69/128:ℝ) (3/4:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
  rw [power_oldSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row165_coefficients, Fin.sum_univ_succ, power_oldSwitch_old] <;> ring
theorem row165_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
  rw [row165_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row165_coefficients]

def row166_coefficients : Fin 3 → Fin 4 → ℝ := ![![(155289629961126609598654482404816/268769979700780154326171875:ℝ), (16185223582568136735575313758608/9954443692621487197265625:ℝ), (408314467418234155065759203404084/268769979700780154326171875:ℝ), (14066980351564553640011035098776/29863331077864461591796875:ℝ)],
![(14650128701387884444281265386752/53753995940156030865234375:ℝ), (1081638805338123269617551937792/1990888738524297439453125:ℝ), (14554251208829841772801136933632/53753995940156030865234375:ℝ), (0:ℝ)],
![(963898793674829085606291070780544/268769979700780154326171875:ℝ), (105190578621942583537393676877952/9954443692621487197265625:ℝ), (2788912761081885175384396658670976/268769979700780154326171875:ℝ), (101407274695125660826433161527424/29863331077864461591796875:ℝ)]]
theorem row166_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (1994077421579702986880830452811/158348185591417644515328000000000:ℝ) row166_coefficients
      (69/128:ℝ) (3/4:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
  rw [power_oldSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row166_coefficients, Fin.sum_univ_succ, power_oldSwitch_old] <;> ring
theorem row166_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
  rw [row166_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row166_coefficients]

def row167_coefficients : Fin 3 → Fin 4 → ℝ := ![![(54249806095067490066814779030088/89589993233593384775390625:ℝ), (91948451385923240763174351106732/53753995940156030865234375:ℝ), (431416830388739327039723512137728/268769979700780154326171875:ℝ), (14935972695376167042279466139648/29863331077864461591796875:ℝ)],
![(4819546016149531658712669493504/17917998646718676955078125:ℝ), (28821662936515943155612888507904/53753995940156030865234375:ℝ), (14363157054155746116883380027392/53753995940156030865234375:ℝ), (0:ℝ)],
![(316270689125750811626081158316032/89589993233593384775390625:ℝ), (559103971563652994312805825482752/53753995940156030865234375:ℝ), (2744920030901844885547859149586432/268769979700780154326171875:ℝ), (99801308972522087868768166346752/29863331077864461591796875:ℝ)]]
theorem row167_identity (δ p : ℝ) : rowMargin .oldSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (236523238122918782074620527/19329612498952349184000000000:ℝ) row167_coefficients
      (69/128:ℝ) (3/4:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [power_oldSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row167_coefficients, Fin.sum_univ_succ, power_oldSwitch_old] <;> ring
theorem row167_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (69/128:ℝ) (3/4:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .oldSwitch .old δ p := by
  rw [row167_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row167_coefficients]

def row168_coefficients : Fin 3 → Fin 4 → ℝ := ![![(401700667531839365081/19167028095234375000:ℝ), (1067254891029984202123/19167028095234375000:ℝ), (929407779464450309003/19167028095234375000:ℝ), (361939034247332609/26292219609375000:ℝ)],
![(175057349490549113177/9583514047617187500:ℝ), (425530000175270969947/9583514047617187500:ℝ), (331841215866764429363/9583514047617187500:ℝ), (111616687492513817/13146109804687500:ℝ)],
![(130145853389258861273/19167028095234375000:ℝ), (227202473131163429971/19167028095234375000:ℝ), (49785676882983534349/9583514047617187500:ℝ), (0:ℝ)]]
theorem row168_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (181340066784431779879/4594898411520000000000:ℝ) row168_coefficients
      (0:ℝ) (9/32:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row168_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row168_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row168_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row168_coefficients]

def row169_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3356171831373637953403/1064834894179687500:ℝ), (9792821270989846073969/1064834894179687500:ℝ), (9517127047858778287729/1064834894179687500:ℝ), (1026825869414190055721/354944964726562500:ℝ)],
![(1166351941962483160987/532417447089843750:ℝ), (3323584785246176059793/532417447089843750:ℝ), (25200785327473540637/4259339576718750:ℝ), (330955107550166560273/177472482363281250:ℝ)],
![(189929159777972289871/1064834894179687500:ℝ), (370644771801982732217/1064834894179687500:ℝ), (90427659734895846173/532417447089843750:ℝ), (0:ℝ)]]
theorem row169_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (1986151641635209068677/55138780938240000000000:ℝ) row169_coefficients
      (0:ℝ) (9/32:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row169_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row169_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row169_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row169_coefficients]

def row170_coefficients : Fin 3 → Fin 4 → ℝ := ![![(12674756792770355330819/532417447089843750:ℝ), (37472881932048930419977/532417447089843750:ℝ), (36921493485786794847497/532417447089843750:ℝ), (449013642463267398457/19719164707031250:ℝ)],
![(4324307650402073385443/266208723544921875:ℝ), (12629918555240833081993/266208723544921875:ℝ), (12288898580604735950657/266208723544921875:ℝ), (272697177775448501/18224736328125:ℝ)],
![(352846359800074662167/532417447089843750:ℝ), (696828440460640601809/532417447089843750:ℝ), (172025967191728282321/266208723544921875:ℝ), (0:ℝ)]]
theorem row170_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (2530586735580253870847/73518374584320000000000:ℝ) row170_coefficients
      (0:ℝ) (9/32:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row170_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row170_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row170_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row170_coefficients]

def row171_coefficients : Fin 3 → Fin 4 → ℝ := ![![(9834577521993502000523/53241744708984375:ℝ), (29283177187475651772577/53241744708984375:ℝ), (5812524361794159508717/10648348941796875:ℝ), (3204674047829549257177/17747248236328125:ℝ)],
![(33225129853997071971374/266208723544921875:ℝ), (98319247348763987160778/266208723544921875:ℝ), (96967073978195338293434/266208723544921875:ℝ), (2124863765561894873602/17747248236328125:ℝ)],
![(679414223934630969259/266208723544921875:ℝ), (1350138803036979778493/266208723544921875:ℝ), (670759505963794121734/266208723544921875:ℝ), (0:ℝ)]]
theorem row171_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (5937525320605683096181/176444099002368000000000:ℝ) row171_coefficients
      (0:ℝ) (9/32:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row171_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row171_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row171_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row171_coefficients]

def row172_coefficients : Fin 3 → Fin 4 → ℝ := ![![(387226719108043749590626/266208723544921875:ℝ), (1157269049754034164192038/266208723544921875:ℝ), (1152857942183937079612198/266208723544921875:ℝ), (4726118660962304506306/3286527451171875:ℝ)],
![(260315318604423062291012/266208723544921875:ℝ), (155110627540325782189532/53241744708984375:ℝ), (770168257275305794794284/266208723544921875:ℝ), (3147289360223456125156/3286527451171875:ℝ)],
![(2665833368497838729386/266208723544921875:ℝ), (5314462081638339701222/266208723544921875:ℝ), (2648663640001946284336/266208723544921875:ℝ), (0:ℝ)]]
theorem row172_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (13046398858651638062103/392097997783040000000000:ℝ) row172_coefficients
      (0:ℝ) (9/32:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row172_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row172_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row172_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row172_coefficients]

def row173_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3073085312187173656271032/266208723544921875:ℝ), (9201611506281132630493736/266208723544921875:ℝ), (9183967076000744292174376/266208723544921875:ℝ), (1018480293968928439317224/88736241181640625:ℝ)],
![(2060564345192000241470576/266208723544921875:ℝ), (6160185264611976898886224/266208723544921875:ℝ), (1227738673803717478580944/53241744708984375:ℝ), (679690816532870245163024/88736241181640625:ℝ)],
![(10560419883600336184744/266208723544921875:ℝ), (21086605090793223416888/266208723544921875:ℝ), (10526220134054332544644/266208723544921875:ℝ), (0:ℝ)]]
theorem row173_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (233515126970279443094761/7057763960094720000000000:ℝ) row173_coefficients
      (0:ℝ) (9/32:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row173_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row173_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row173_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row173_coefficients]

def row174_coefficients : Fin 3 → Fin 4 → ℝ := ![![(3065932972145016537481216/266208723544921875:ℝ), (9180154486154661274124288/266208723544921875:ℝ), (9162510055874272935804928/266208723544921875:ℝ), (1016096180621542733053952/88736241181640625:ℝ)],
![(412011326015014634909632/53241744708984375:ℝ), (6158693870002464337206976/266208723544921875:ℝ), (6137233725150343470313472/266208723544921875:ℝ), (679532161740984102551552/88736241181640625:ℝ)],
![(10492090238231219529544/266208723544921875:ℝ), (20950050580639326043988/266208723544921875:ℝ), (10457995269269551826944/266208723544921875:ℝ), (0:ℝ)]]
theorem row174_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (28345167930969304279/861543452160000000000:ℝ) row174_coefficients
      (0:ℝ) (9/32:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row174_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row174_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (0:ℝ) (9/32:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row174_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row174_coefficients]

def row175_coefficients : Fin 3 → Fin 4 → ℝ := ![![(617839675399512172241/2129669788359375000:ℝ), (1200578678052083901331/2129669788359375000:ℝ), (690054200591298456239/2129669788359375000:ℝ), (1200694590647860829/26292219609375000:ℝ)],
![(117579735599730400861/212966978835937500:ℝ), (1068360326689345541347/1064834894179687500:ℝ), (535207625857433549129/1064834894179687500:ℝ), (530994465692777927/13146109804687500:ℝ)],
![(578150105257791836369/2129669788359375000:ℝ), (985408349083341147163/2129669788359375000:ℝ), (210474786756055905397/1064834894179687500:ℝ), (0:ℝ)]]
theorem row175_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (628104005295250392367/18379593646080000000000:ℝ) row175_coefficients
      (9/32:ℝ) (21/64:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row175_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row175_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row175_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row175_coefficients]

def row176_coefficients : Fin 3 → Fin 3 → ℝ := ![![(70122897392027/67500000000:ℝ), (19728344288401/11250000000:ℝ), (49327383191359/67500000000:ℝ)],
![(44161661680979/33750000000:ℝ), (1204828503389/625000000:ℝ), (22113427191437/33750000000:ℝ)],
![(23718359656031/67500000000:ℝ), (3725861581031/11250000000:ℝ), (0:ℝ)]]
theorem row176_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (292853407165237/7864320000000000:ℝ) row176_coefficients
      (9/32:ℝ) (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
  rw [power_newSwitch_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row176_coefficients, Fin.sum_univ_succ, power_newSwitch_capP] <;> ring
theorem row176_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
  rw [row176_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row176_coefficients]

def row177_coefficients : Fin 3 → Fin 3 → ℝ := ![![(240656681567963/67500000000:ℝ), (8837655288811/1350000000:ℝ), (22478477525063/7500000000:ℝ)],
![(1757344767577/450000000:ℝ), (110966972768143/16875000000:ℝ), (10149715295269/3750000000:ℝ)],
![(43347148802527/67500000000:ℝ), (20991979316341/33750000000:ℝ), (0:ℝ)]]
theorem row177_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (376022159952807/10485760000000000:ℝ) row177_coefficients
      (9/32:ℝ) (21/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
  rw [power_newSwitch_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row177_coefficients, Fin.sum_univ_succ, power_newSwitch_capP] <;> ring
theorem row177_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
  rw [row177_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row177_coefficients]

def row178_coefficients : Fin 3 → Fin 3 → ℝ := ![![(891829917997787/67500000000:ℝ), (284853249669457/11250000000:ℝ), (163673958974387/13500000000:ℝ)],
![(447994477725203/33750000000:ℝ), (136251802501253/5625000000:ℝ), (14829227478869/1350000000:ℝ)],
![(82604727095519/67500000000:ℝ), (1504472906031/1250000000:ℝ), (0:ℝ)]]
theorem row178_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (885932238467633/25165824000000000:ℝ) row178_coefficients
      (9/32:ℝ) (21/64:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
  rw [power_newSwitch_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row178_coefficients, Fin.sum_univ_succ, power_newSwitch_capP] <;> ring
theorem row178_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
  rw [row178_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row178_coefficients]

def row179_coefficients : Fin 3 → Fin 3 → ℝ := ![![(3434599063169243/67500000000:ℝ), (3362219154896371/33750000000:ℝ), (365657717941831/7500000000:ℝ)],
![(548014210522801/11250000000:ℝ), (313598638100867/3375000000:ℝ), (165906455458853/3750000000:ℝ)],
![(161119883681503/67500000000:ℝ), (79878346755829/33750000000:ℝ), (0:ℝ)]]
theorem row179_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (5852508295223719/167772160000000000:ℝ) row179_coefficients
      (9/32:ℝ) (21/64:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
  rw [power_newSwitch_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row179_coefficients, Fin.sum_univ_succ, power_newSwitch_capP] <;> ring
theorem row179_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
  rw [row179_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row179_coefficients]

def row180_coefficients : Fin 3 → Fin 3 → ℝ := ![![(13481828042759387/67500000000:ℝ), (4446409551973201/11250000000:ℝ), (13197709483932799/67500000000:ℝ)],
![(6290782593372179/33750000000:ℝ), (2047037470207621/5625000000:ℝ), (5992656577562957/33750000000:ℝ)],
![(318150196853471/67500000000:ℝ), (52797834447271/11250000000:ℝ), (0:ℝ)]]
theorem row180_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (69911949345831157/2013265920000000000:ℝ) row180_coefficients
      (9/32:ℝ) (21/64:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
  rw [power_newSwitch_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row180_coefficients, Fin.sum_univ_succ, power_newSwitch_capP] <;> ring
theorem row180_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
  rw [row180_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row180_coefficients]

def row181_coefficients : Fin 3 → Fin 3 → ℝ := ![![(675656665022329/3375000000:ℝ), (34821911792864/87890625:ℝ), (51684278012992/263671875:ℝ)],
![(350448910782041/1875000000:ℝ), (96244133765888/263671875:ℝ), (46971742794112/263671875:ℝ)],
![(315423816513781/67500000000:ℝ), (1226799321656/263671875:ℝ), (0:ℝ)]]
theorem row181_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (1415944936713/40960000000000:ℝ) row181_coefficients
      (9/32:ℝ) (21/64:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [power_newSwitch_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row181_coefficients, Fin.sum_univ_succ, power_newSwitch_capP] <;> ring
theorem row181_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (9/32:ℝ) (21/64:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
  rw [row181_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row181_coefficients]

def row182_coefficients : Fin 3 → Fin 4 → ℝ := ![![(81617006287471894696/266208723544921875:ℝ), (30244154605232277769/53241744708984375:ℝ), (645307408638061774391/2129669788359375000:ℝ), (307761090707750293/8764073203125000:ℝ)],
![(160796869389728747408/266208723544921875:ℝ), (281703551650821679144/266208723544921875:ℝ), (132762339073185009014/266208723544921875:ℝ), (98072201607618238/3286527451171875:ℝ)],
![(81703916184756852712/266208723544921875:ℝ), (136641075344252036024/266208723544921875:ℝ), (57172478291995183312/266208723544921875:ℝ), (0:ℝ)]]
theorem row182_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (8645594691457297987/287181150720000000000:ℝ) row182_coefficients
      (21/64:ℝ) (3/8:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row182_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row182_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row182_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row182_coefficients]

def row183_coefficients : Fin 3 → Fin 3 → ℝ := ![![(116379046723/125000000:ℝ), (25151955158741/16875000000:ℝ), (39126325574389/67500000000:ℝ)],
![(147227025019/117187500:ℝ), (1809445341817/1054687500:ℝ), (2126612297869/4218750000:ℝ)],
![(47701414699/117187500:ℝ), (201565922593/527343750:ℝ), (0:ℝ)]]
theorem row183_identity (δ p : ℝ) : rowMargin .newSwitch .capP δ p =
    Record12518109.Bernstein.bsum 2 2 (1321495216619/40960000000000:ℝ) row183_coefficients
      (21/64:ℝ) (3/8:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
  rw [power_newSwitch_capP_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row183_coefficients, Fin.sum_univ_succ, power_newSwitch_capP] <;> ring
theorem row183_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .capP δ p := by
  rw [row183_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row183_coefficients]

def row184_coefficients : Fin 3 → Fin 4 → ℝ := ![![(22245355858696767119/269718808593750:ℝ), (17704648822116437633/80915642578125:ℝ), (617939777980147666481/3236625703125000:ℝ), (19628614277452929621/359625078125000:ℝ)],
![(42072713673061728088/404578212890625:ℝ), (103171142502325517984/404578212890625:ℝ), (80805403810339507954/404578212890625:ℝ), (2188376048602857562/44953134765625:ℝ)],
![(11278999325854733272/404578212890625:ℝ), (22177987427640189544/404578212890625:ℝ), (3635203756528485424/134859404296875:ℝ), (0:ℝ)]]
theorem row184_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (15968542262477463337/754188451840000000000:ℝ) row184_coefficients
      (21/64:ℝ) (3/8:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row184_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row184_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row184_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row184_coefficients]

def row185_coefficients : Fin 3 → Fin 4 → ℝ := ![![(219553066966279637677/404578212890625:ℝ), (614675604654379629674/404578212890625:ℝ), (2285047016055272657393/1618312851562500:ℝ), (140907316370297037881/323662570312500:ℝ)],
![(48670830487562457328/80915642578125:ℝ), (25727418212847497792/16183128515625:ℝ), (111520285943357068436/80915642578125:ℝ), (31551707257952036804/80915642578125:ℝ)],
![(42895538469203271088/404578212890625:ℝ), (9451574481029776464/44953134765625:ℝ), (42175255027864717088/404578212890625:ℝ), (0:ℝ)]]
theorem row185_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (12238639579116929781/603350761472000000000:ℝ) row185_coefficients
      (21/64:ℝ) (3/8:ℝ) (15/32:ℝ) (31/64:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row185_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row185_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (15/32:ℝ) (31/64:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row185_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row185_coefficients]

def row186_coefficients : Fin 3 → Fin 4 → ℝ := ![![(175150387381683571018/44953134765625:ℝ), (4557623188804639328308/404578212890625:ℝ), (1754917993733814650077/161831285156250:ℝ), (937346807401468374031/269718808593750:ℝ)],
![(1596628935782444992864/404578212890625:ℝ), (4452583523957315818112/404578212890625:ℝ), (4117796650081091282632/404578212890625:ℝ), (420610157120856819128/134859404296875:ℝ)],
![(167280322732181760352/404578212890625:ℝ), (333139948085086412704/404578212890625:ℝ), (55288749506901550784/134859404296875:ℝ), (0:ℝ)]]
theorem row186_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (239545281496957915609/12067015229440000000000:ℝ) row186_coefficients
      (21/64:ℝ) (3/8:ℝ) (31/64:ℝ) (63/128:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row186_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row186_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (31/64:ℝ) (63/128:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row186_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row186_coefficients]

def row187_coefficients : Fin 3 → Fin 4 → ℝ := ![![(2381763680796176976356/80915642578125:ℝ), (35049517807830938877128/404578212890625:ℝ), (34374768110603570631041/404578212890625:ℝ), (11234063635890669760693/404578212890625:ℝ)],
![(11415957201227092445888/404578212890625:ℝ), (32918650659707757695744/404578212890625:ℝ), (31594392991499927303824/404578212890625:ℝ), (10091687942475612053968/404578212890625:ℝ)],
![(660656715163264393408/404578212890625:ℝ), (439501717135658190272/134859404296875:ℝ), (657855059411510177408/404578212890625:ℝ), (0:ℝ)]]
theorem row187_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (947858364813405656289/48268060917760000000000:ℝ) row187_coefficients
      (21/64:ℝ) (3/8:ℝ) (63/128:ℝ) (127/256:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row187_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row187_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (63/128:ℝ) (127/256:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row187_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row187_coefficients]

def row188_coefficients : Fin 3 → Fin 4 → ℝ := ![![(11889130285886025722101/404578212890625:ℝ), (34994813654726515817341/404578212890625:ℝ), (11441469648696920455168/134859404296875:ℝ), (1246524500709713821696/44953134765625:ℝ)],
![(11401821242466323976784/404578212890625:ℝ), (32886134563325880788432/404578212890625:ℝ), (31571733903387528896512/404578212890625:ℝ), (3362469663994774028288/134859404296875:ℝ)],
![(218355549998451987136/134859404296875:ℝ), (1307344890574557706816/404578212890625:ℝ), (652284863747001745408/404578212890625:ℝ), (0:ℝ)]]
theorem row188_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (57227963159620863/2946048640000000000:ℝ) row188_coefficients
      (21/64:ℝ) (3/8:ℝ) (127/256:ℝ) (1/2:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row188_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row188_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (21/64:ℝ) (3/8:ℝ))
    (hp : p ∈ Set.Icc (127/256:ℝ) (1/2:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row188_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row188_coefficients]

def row189_coefficients : Fin 3 → Fin 4 → ℝ := ![![(141189391543908947389/425933957671875000:ℝ), (1250075487478486033939/2129669788359375000:ℝ), (614326711060431212243/2129669788359375000:ℝ), (645871953598640929/26292219609375000:ℝ)],
![(716390809638684569009/1064834894179687500:ℝ), (243277976725843121111/212966978835937500:ℝ), (540657181103652642683/1064834894179687500:ℝ), (28175905240907553/1460678867187500:ℝ)],
![(747027086217824401073/2129669788359375000:ℝ), (1231970653536679142971/2129669788359375000:ℝ), (253788086767708620949/1064834894179687500:ℝ), (0:ℝ)]]
theorem row189_identity (δ p : ℝ) : rowMargin .newSwitch .old δ p =
    Record12518109.Bernstein.bsum 2 3 (501002432011777155919/18379593646080000000000:ℝ) row189_coefficients
      (3/8:ℝ) (27/64:ℝ) (0:ℝ) (3/8:ℝ) δ p := by
  rw [power_newSwitch_old_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row189_coefficients, Fin.sum_univ_succ, power_newSwitch_old] <;> ring
theorem row189_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (0:ℝ) (3/8:ℝ)) : 0 < rowMargin .newSwitch .old δ p := by
  rw [row189_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row189_coefficients]

def row190_coefficients : Fin 3 → Fin 4 → ℝ := ![![(83715879180478468451/6473251406250000:ℝ), (13200502201162062151/431550093750000:ℝ), (148278415682780675177/6473251406250000:ℝ), (33880791161028211363/6473251406250000:ℝ)],
![(13024898299232501287/647325140625000:ℝ), (140915514120787155689/3236625703125000:ℝ), (90276315784700599073/3236625703125000:ℝ), (14366076139675949819/3236625703125000:ℝ)],
![(52498555291824525719/6473251406250000:ℝ), (100856045821994415313/6473251406250000:ℝ), (24245804839059944797/3236625703125000:ℝ), (0:ℝ)]]
theorem row190_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (244173883690320668573/12067015229440000000000:ℝ) row190_coefficients
      (3/8:ℝ) (27/64:ℝ) (3/8:ℝ) (7/16:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row190_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row190_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (3/8:ℝ) (7/16:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row190_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row190_coefficients]

def row191_coefficients : Fin 3 → Fin 4 → ℝ := ![![(45740123421714597703/647325140625000:ℝ), (592829766926326883369/3236625703125000:ℝ), (167550252553963005731/1078875234375000:ℝ), (15385402500192791371/359625078125000:ℝ)],
![(16737973002573771371/179812539062500:ℝ), (71513819267629265557/323662570312500:ℝ), (266674032577214635553/1618312851562500:ℝ), (6631898305781361123/179812539062500:ℝ)],
![(93177452464460143063/3236625703125000:ℝ), (182549138037140650001/3236625703125000:ℝ), (44719372573327753469/1618312851562500:ℝ), (0:ℝ)]]
theorem row191_identity (δ p : ℝ) : rowMargin .newSwitch .Cphys δ p =
    Record12518109.Bernstein.bsum 2 3 (883518082296822531229/48268060917760000000000:ℝ) row191_coefficients
      (3/8:ℝ) (27/64:ℝ) (7/16:ℝ) (15/32:ℝ) δ p := by
  rw [power_newSwitch_Cphys_expanded]
  norm_num [Record12518109.Bernstein.bsum, Record12518109.Bernstein.bterm,
    row191_coefficients, Fin.sum_univ_succ, power_newSwitch_Cphys] <;> ring
theorem row191_pos {δ p : ℝ} (hδ : δ ∈ Set.Icc (3/8:ℝ) (27/64:ℝ))
    (hp : p ∈ Set.Icc (7/16:ℝ) (15/32:ℝ)) : 0 < rowMargin .newSwitch .Cphys δ p := by
  rw [row191_identity]
  apply Record12518109.Bernstein.bsum_pos (by norm_num) _ hδ hp
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [row191_coefficients]

end
end Qrh.JointDetector.FineReturn.FinalEdges
