(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg AProto ABase.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AKit AModelFacts F_aunwind F_aalloc_s F_acache.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Section CANSEC1. Context {rc : runConstT}.
Definition allocate_entry := 0x3122c%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma rz_ladder_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n : Z),
  0 <= n < 2^40 ->
  rng_aimg RNG ->
  evtF asegs RNG (fun ms' => exists a0',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (rz_log n)) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x31398) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 49) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x312c4) fc None m (seg_rom asegs)).
Proof.
  intros until n. intros N RIMG. unfold rz_log.
  step. Local Ltac2 Set LiaHints.tbl := fun () => "00F0>28866468740.3836000989678.4038917905716.5140675739649.4141855593050.444354982892.38 52673946479.3958887966598.4060091000683.4361929812114.3861929812241.3961929812368.4061929812503.4161929812630.4261929812757.4361937685140.5162248037993.416231347328.42 63935938706.446396461315.43 67570755847.399880917736.42 00000400800900=00A00E00I00M00Q00T00W00Z00]00`00c00f00j00n01201601:01>S2K0S2K2SS2K3S2K6S2K0S2K1S2K2S2K5S1NS1NS1NS1NS1NS1NS1NS2K3S2K4S2K6S2K5S2K1S2K4".
if_cases K0; zify_cond K0.
  2: { replace (n <=? 48) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 48) with false by (symmetry; apply Z.leb_gt; lia).
  step. step. if_cases K1; zify_cond K1.
  2: { replace (n <=? 96) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 96) with false by (symmetry; apply Z.leb_gt; lia).
  step. step. if_cases K2; zify_cond K2.
  2: { replace (n <=? 448) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 448) with false by (symmetry; apply Z.leb_gt; lia).
  step. zstep. step. if_cases K3; zify_cond K3.
  2: { replace (n <=? 3968) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 3968) with false by (symmetry; apply Z.leb_gt; lia).
  step. zstep. step. if_cases K4; zify_cond K4.
  2: { replace (n <=? 16128) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 16128) with false by (symmetry; apply Z.leb_gt; lia).
  step. zstep. step. if_cases K5; zify_cond K5.
  2: { replace (n <=? 32256) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 32256) with false by (symmetry; apply Z.leb_gt; lia).
  step. zstep. zstep. zstep.
  apply evtF_done. destruct (Z.leb_spec n 64512) as [K6|K6]; eexists.
  - replace (n <? 64513) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - replace (n <? 64513) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma rz_clamp_spec : forall RNG ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n rz : Z),
  0 <= n < 2^40 -> 0 <= rz <= 7 ->
  rng_aimg RNG ->
  evtF asegs RNG (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) (Z_to_bv 64 (Z.max n 8)) (Z_to_bv 64 8) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 rz) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x313e0) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) (Z_to_bv 64 7) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 rz) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x313c4) fc None m (seg_rom asegs)).
Proof.
  intros until rz. intros N RZ RIMG.
  step. Local Ltac2 Set LiaHints.tbl := fun () => "00:0>10635129997.3920419410667.3920419410667.4045782037665.3945782037794.3846702646762.3861479276013.3961479276013.4061929812368.3961929812368.4000000700;00?00C00G00N00R00V00Y00\S2RZ2K1S2K2S2K2S2RZS2RZS2RZ2K0S2K2S2K2S1NS1N".
if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1.
    + (* [comment removed for export] *) step. step. step. if_cases K2; zify_cond K2.
      * replace (Z.max n 8) with n by lia. apply evtF_done. reflexivity.
      * step. replace (Z.max n 8) with 8 by lia. apply evtF_done. reflexivity.
    + (* [comment removed for export] *) step. replace rz with 7 by lia. step. step. step. if_cases K2; zify_cond K2.
      * step. replace (Z.max n 8) with 8 by lia. apply evtF_done. reflexivity.
      * step. replace (Z.max n 8) with n by lia. apply evtF_done. reflexivity.
  - (* [comment removed for export] *) step. replace rz with 0 by lia. step. if_lit. step. step. step. if_cases K2; zify_cond K2.
    + replace (Z.max n 8) with n by lia. apply evtF_done. reflexivity.
    + step. replace (Z.max n 8) with 8 by lia. apply evtF_done. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition allocA_cells (m : amem) (ctx t : Z) : Prop :=
     rw_cells asegs m AINITED [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m ARSSLIM [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0x9e638 (* [comment removed for export] *) [C8 (Z_to_bv 64 (2^40)); C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
  /\ rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)]
  /\ rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)].

Definition allocA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n S t c cnt spacebeg lo : Z) (idxw maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x314cc) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 1) (Z_to_bv 64 n)
                  (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * bv_unsigned idxw)) a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x314cc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp); (acache_rec t c, acache_rec t c + 4); (acache_stats t, acache_stats t + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 128)
    /\ (exists j0, rw_cells asegs m' (bv_unsigned sp - 128)
         [CB 8 j0 (* [comment removed for export] *); C8 (Z_to_bv 64 1) (* [comment removed for export] *); C8 (Z_to_bv 64 16) (* [comment removed for export] *);
          C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ rw_cells asegs m' (acache_rec t c) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ (exists stj' : word, rw_cells asegs m' (acache_stats t) [C8 stj']).

#[using="Type"] Lemma allocA_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S ctx t c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 176 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= 448 -> 0 < S < 2^64 ->
  allocA_cells m ctx t ->
  rw_cells asegs m 0x9d838 [C8 (Z_to_bv 64 spacebeg)] ->
  Z.shiftr (needed_size n + 31) 5 = c ->
  rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (acache_stats t) [C8 stj] ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF asegs RNG (allocA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n S t c cnt spacebeg lo idxw maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom asegs)).
Proof.
  intros until idxw. intros ST CEIL LO MI TP -> -> -> -> -> -> N HS AC SB HC CR CH LCH CNT NTH IXS STS C0 C1 T0 T1 TAL CT2 SBR RIMG RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  destruct AC as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, AINITED, ATSDI, ATSDK, ATP88, ATSD, ARSSLIM, allocate_entry in *.
  pose proof (small_facts n N) as (PRIM & NS & RZR & RZE & RSR & RSM & NSR).
  Local Ltac2 Set LiaHints.tbl := fun () => "05a0?10002276566.98 10082350123.1051044680708.101 10629577799.98 11014877014.10011077664131.10011160400943.1001162083375.99  11658450183.12911775166127.10111801586693.10611801586693.11011801586693.116120833238.100  12279985372.99 12331942998.10512393425878.10012431607254.10412546622119.10112892874966.98 13081094916.98 13146370006.10113151127382.10013187052577.10013201050402.10513338178759.1001351984962.103 14453557927.10014763672662.10514871332950.10515140232534.10115174031830.1001533820803.100 15399217494.1001577073154.98  15813913888.10316520521031.10116600962308.10116870183111.10017002825942.10017139085270.10017683239510.10017776320431.99 17986879152.11018443305558.10018651764129.10018691909590.10018712044988.12919108682116.10019239446934.1051937063194.110 19491992743.10119812073942.10019913379627.10020294747862.1012046274134.101 2065397462.104 20805333024.10820805333024.95 20805333024.99 20854954799.10021153470338.10021651633935.1102165384406.98  22161629359.10022165204226.10122284289799.10622284289799.11022284289799.11622439364775.99 22542101334.10122568407585.10022609673092.10522675801219.10122700267513.10722700267513.11122700267513.11722709700310.10124266362535.10424271162582.10124346898045.10624346898045.11024346898045.11624557733334.10424559885231.99 2458073255.100 24633095682.10024794926247.10124972240369.10224982576641.10325029166211.10025101887574.10025119608324.10125348482085.10825348482085.95 25348482085.99 25475387094.10025787632170.10325787632170.94 25878270254.10025896385351.10126083973675.99 26278908583.10026291562981.12926492550416.10026492550416.10126492550416.10426492550416.10526492550416.98 26492550416.99 26507015092.12926507015092.13026507015092.13126868428163.99 27015870038.10027135919574.10027408782894.10027516840022.10027983680470.10028024393302.10028031021985.10128355653425.10428575982988.1302860990166.101 28737894315.10128986992043.98 29078730183.10029311285958.86 29782367974.10429965292900.10430198278530.10030403112534.10130439008982.10130518562691.10030863979691.10031145098372.10031146617686.10031239308591.10031689824982.98 32545997487.10132649392770.99 33529220054.10133532905180.95 33677903874.10133890036527.99 33891414.100   34434518102.10034775537831.10535270809255.10035289778563.10536115622446.10036367760551.10036635094629.10936986663037.10636986663037.11036986663037.11637156020484.10137319313223.10437363021782.10137410281889.98 37821760598.1003824569889.99  38333311882.93 38569341398.10038915808562.11638915808567.11938996969702.91 39005376854.10039039163289.10939091826902.10139351235818.10339829987030.10039836248662.10039932040893.10639932588075.10039938772488.11539938772488.11639938772490.11639940869632.11440091925676.98 40605904854.10040646919027.11040651652566.10440652982343.10041625904943.10041836534358.10542240553391.10442845057622.99 42858215713.10042932464815.98 42998092118.10043061431595.89 43104589767.10043181512580.10043188719081.11043468811196.12943530870230.98 43987951406.10044063045948.12944158664835.10144484923210.10644484923210.11044484923210.11644522897991.10144781669846.10144833359747.10044999795740.12945219141890.10445412913494.1004562448900.104 46048577110.99 46230876290.10046236641750.10146556098215.1014678377391.101 46814824022.1004696155388.129 47438431676.12948054906439.10148320830113.10448722578991.10548823048406.10049192305668.10049255182422.99 4930072150.99  49423094309.11049425192486.10849726415815.99 50077211645.10650077211645.11050077211645.11650489401671.10050584888647.95 50672158678.10150944119766.10151043783510.10051458250794.11251469190682.10351678667183.99 52031133206.11152076332701.11352076332702.11452200463318.10452237318794.93 52237461281.10052624921519.10052675322539.10152793185963.10453375849430.10153461090518.10053496988502.99 53679676758.10053767577775.99 53825897814.10054263952130.10154667680086.10055209202390.10155220021892.10055488946646.1015557113430.100 55753344342.10056170256219.11256172400559.10756172529599.98 56175235539.94 565324930.105  56714183894.10056759929558.1015684463747.104 5703093030.110 57187414.100   57293592682.10257522549927.98 57700073633.10057731802838.10157743577986.10058054922582.10458168296790.10058362767830.10158655119491.10158806867907.99 59109042223.99 59314873579.10659314873579.10759314873579.10859314873579.11059314873579.94 59576986246.1075972701590.126 59907387523.10159908778326.10560468873383.10060634079619.10060799616214.10560976774461.10660976774461.11060976774461.11660997568167.10061228736260.10061521325654.99 61616721185.10061795975254.10061889459015.99 61917199023.99 61929802144.10561929802406.10761939782290.11562069552982.1006222415318.101 63011388847.10163047610823.10563164784673.10563172006742.10063235321900.97 63314293035.10063610297916.1296386026005.104 63901105366.10063963017942.10164260757035.10064302930659.93 64803448158.13064862446845.10664862446845.11064862446845.11665456795478.10065492691926.10165807272962.10165983638659.10066028155702.10266028155702.11166028155702.11366028155702.98 66330498723.10466773347627.10067081432737.10167100501013.85 67215858474.10467256438148.99 67510389213.10667510389213.11067510389213.11667841563051.10068010417238.10568031924935.10068201501398.99 68693594283.10168712786390.1047055476356.100 747874518.98   773933615.100  7741215905.101 8170740566.100 8179223683.98  8278980118.101 8432272592.131 8477187286.101 8581623554.100 8595948976.116 8595948983.119 8610795133.106 8610795133.110 8610795133.116 9184795990.100 9272504225.101 9448144982.98  9581476779.101 9612232322.100 9954448086.101 00000900E00I00U00^00_01301701801L01g02B02]02f02g03003903B03C03L03P03Y03b04204704C04D04E04N04W04`04i04j05305805<05H05L05X05a05j06306706=06F06V06_07G07K07L07P07Q07Z07f07o08808A08B08C08D08X08]08f08o09C09H09I09J09K09L09U09e09i09j0:W0;D0<50<>0<?0<H0<U0<b0<o0=80=<0==0=B0=C0=D0=E0=F0=O0=S0=W0=[0=_0=h0=k0=n0>20>>0>J0>K0>L0>M0>N0>O0>P0>Q0>R0?G0?H0?\0?]0?f0?o0@30@<0@E0@N0@^0@_0A[0Ad0B00B<0BH0BI0BJ0BM0BR0B[0Bd0Be0C10C50C>0CR0C[0Co0D40D=0D>0DC0DG0DP0DY0DZ0D[0D\0D`0Da0E60EC0EP0E]0Ea0Em0F60FF0FO0F_0F`0Fi0Fj0Fk0Fl0G50G60G?0G@0GI0GR0GW0Gc0Gd0Gi0H00H50H90HB0HK0HT0H`0I40I=0IQ0IZ0Ij0J>0JG0JK0JW0J[0J`0KH0KQ0KU0L=0L>0L?0L@0LA0LM0LV0LW0M?0MD0MM0MQ0MZ0M_0Mh0Mi0N=0NF0Nn0OV0Ob0P20PF0PO0PS0P\0Pe0Pi0Pm0Q90QF0QS0Q`0Ql0Qm0R60R?0RH0RK0RN0RR0RS0RT0RU0R^0R_0Ro0SC0SO0S[0Sd0Sm0T60T?0TC0TL0TQ0TZ0Tc0Tg0U00U90UB0UG0UH0UI0UJ0UO0UX0Ua0Ub0Ug0V00V10V20VB0VK0VP0VY0Vb0Vk0Vl0Vm0WA0WK0WW0Wa0X20X=0X>0X?0X@0XI0XJ0XK0XT0Xa0Xn0Y;0Y<0Y@0YI0YY0Yb0Yc0Yg0Yj0Ym0Z00Z90ZB0ZV0Zb0[20[;0[?0[K0\30\60\?0\H0\T0\X0\l0]90]F0]S0]\0]e0]j0]k0^:0^I0^X0^g0^k0_70_G0_f0_g0_k0`80`E0`R0`^0`g0a30a<0aH0aQ0aU0a^0b20bB0bK0bL0bM0b]0bf0bk0bl0bm0c:0cG0cT0c]0cm0d60dB0dG0dPS4CEIL2LOS4CEIL2LO2T1S2HBS4CEIL2LO2C1S4CEIL2LOSS4CEIL2LO3LCH2T13C16S2LOFS4CEIL2LO3LCH2T13C16S3Hsp4CEIL2LO2T13C162C13LCHS3Hsp4CEIL2LO2T13C162C13LCHS3Hsp4CEIL2LO2T13C162C13LCHS4CEIL2LOSS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LO2T13C16S3NSRS4CEIL2LO2C1SSS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOS3SPRS2LOS4CEIL2LO2C1S2HBS4CEIL2LO2C1S4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS4CEILS4CEIL2LOS4CEIL2LO2T13C16S4CEIL2LOS4CEIL2LO2HC3LCH3TAL3RSR3RSM3C163RLR3HspS2HBSS2T1SS4CEIL2LOS4CEIL2LO2T1S4CEIL2LOS4CEIL2LOS4CEIL2LOFFFS4CEIL2LO3LCH2T13C16S3SPRS3LCH3IXSS4CEIL2LOS4CEIL2LO3LCH2T13C16S3SPRFFFSS4CEIL2LOS4CEIL2LO2T13C16S2HBSS4CEIL2LO2HS3LCH2C02C12T02T13CT23C162KS3Hsp1HS4CEIL2LO2HS3LCH2C02C12T02T13CT23C162KS3Hsp1HS4CEIL2LO2HS3LCH2C02C12T02T13CT23C162KS3RLR3Hsp1HS4CEIL2LOSS4CEIL2LOS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS2LOSS3SPRSSSSS4CEIL2LOS2HBS2LOS2LOS2LOS4CEIL2LOS1NS1NS2LOS4CEIL2LO2C1S4CEIL2LO2T1SFSSSSSSS4CEIL2LO2HS3LCH2C02C12T02T13CT23C162KS3RLR2KE3Hsp2HCFS4CEIL2LO2T13C163HspSS4CEIL2LOS4CEIL2LOS2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO2T13C16SS4CEIL2LO2HS3LCH2C02C12T02T13CT23RSR3RSM3C162KS3RLR2KE3Hsp1HS4CEIL2LOS4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LO2C1SSS1NS3SPRS4CEIL2LOS4CEIL2LOSS4CEIL2LO2T1S2HBS4CEIL2LOS4CEIL2LO3LCH2T13C16S4CEIL2LOS4CEIL2LO3LCH2T13C16S3SPRS4CEIL2LOSS3SPRS2LOS4CEIL2LOS4CEIL2LOSSSS2LOSS2HS3LCH2T02T12KS3RLRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS2HBS4CEIL2LO2C1S4CEIL2LOS4CEIL2LO2T13C16S4CEIL2LOS4CEIL2LO2T13C16SS4CEIL2LOSSSS4CEIL2LOFS4CEIL2LOFS4CEIL2LOS4CEIL2LOS3NSRS4CEIL2LO2T1FS3NSRS1N3RSRS3RZRS2LOS4CEIL2LOS3LCH3CNTS4CEIL2LOS4CEIL2LO2C1S4CEIL2LO3LCH2T13C16S4CEIL2LOS4CEIL2LO3LCH2T13C16S4CEIL2LOS4CEIL2LO2T13C16S4CEIL2LO3LCH2T13C16S4CEIL2LOS2LOS4CEIL2LO2C1S2HBS3NSRS4CEIL2LO2HC3LCH3TAL3RSR3RSM3C163RLR3HspS4CEIL2LOS2LOS4CEIL2LO2HC3LCH3TAL3RSR3RSM3C163RLR3HspSFFFS4CEIL2LO2C1S4CEIL2LOSS4CEIL2LO2HC3LCH3TAL3RSR3RSM3C163RLR3HspS3SPRS4CEIL2LOS2HBS4CEIL2LOS3SPRS4CEIL2LOSS4CEIL2LO3LCH2T13C16S4CEIL2LOS4CEIL2LO2HC3LCH3TAL3RSR3RSM3C163RLR3HspS4CEIL2LO2HC3LCH3TAL3RSR3RSM3C163RLR3HspS4CEIL2LO2C1S4CEIL2LO2T13C16S4CEIL2LO3LCH2T13C16S4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOS2LOS2C0S4CEIL2LO2C1S4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO2C1FS4CEIL2LOS4CEIL2LOS4CEIL2LOS1NS1NS2LOSFFS4CEIL2LOSS4CEIL2LO2T13C16S4CEIL2LO3LCH2T13C16S4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOS3HspSSSS3SPRS4CEIL2LOS4CEIL2LOSS3SBRS4CEIL2LOSSS4CEIL2LO2T13C16S4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LOS4CEIL2LOSFS4CEIL2LO3LCH2T13C16S1N3LCH2KBS3LCH3NSR2KCS1N3LCH2KDS2HS3LCH2T02KS2KES2HS3LCH2KSSSSS4CEIL2LOSSS4CEIL2LOS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspSS2HBS4CEIL2LOS4CEIL2LO2T13C16S4CEIL2LOFS2LOS1NS1NS1NS4CEIL2LOS4CEIL2LOS4CEIL2LO3LCH2T13C16S4CEIL2LO2C1S4CEIL2LO2T13C16S4CEIL2LOS2LOS4CEIL2LO2T1S4CEIL2LO2HC3LCH3TAL3RSR3RSM3C163RLR3HspS1HS4CEIL2LOS4CEIL2LOS4CEIL2LO2T1S2HSS4CEIL2LO2T13C163HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS4CEIL2LOS3SPRSS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS2LOS4CEIL2LO2T1S4CEIL2LO2T13C16S3LCH2C02NS3RZR3RZE3RSR3RSM3NSRSS2HBS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO2T1S4CEIL2LOS4CEIL2LO2C1S4CEIL2LOS4CEIL2LO2T1S4CEIL2LOS2HBS4CEIL2LOS4CEIL2LO3LCH2T13C16S4CEIL2LO2T13C16S4CEIL2LOSSS4CEIL2LO2T13HspS4CEIL2LOS3SPRSSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS4CEIL2LO2T13C16S4CEIL2LOS4CEIL2LO2T1S3SPRS4CEIL2LO".
assert (C16 : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp); (acache_rec t c, acache_rec t c + 4); (acache_stats t, acache_stats t + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 128%nat ST.
  do 14 step.                                       (* [comment removed for export] *)
  do 6 step.                                        (* [comment removed for export] *)
  step. callp asan_inited_spec; [exact INI|]. step. if_lit.     (* [comment removed for export] *)
  step. callp rss_spec; [exact RSS|]. step. if_lit.             (* [comment removed for export] *)
  step. if_cases KS; zify_cond KS. { exfalso. lia. }            (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. step. step. if_lit.                                      (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                    (* [comment removed for export] *)
  step. step. zstep. zstep. zstep. step. zstep. zstep. zstep.    (* [comment removed for export] *)
  lstep. zstep. zstep. zstep.                               (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. zstep. zstep. step. if_lit.                              (* [comment removed for export] *)
  step. zstep. step. step.                                       (* [comment removed for export] *)
  callp rz_ladder_spec; [lia|].                                  (* [comment removed for export] *)
  lstep. step. step. zstep. zstep.                        (* [comment removed for export] *)
  step. call_sp rz2log16_spec; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try lia; try reflexivity; try solve_rng.
  rename POST into ST.
  step. lstep. step. zstep.                                      (* [comment removed for export] *)
  step. call_sp rz2log2048_spec; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try lia; try reflexivity; try solve_rng.
  rename POST into ST.
  callp rz_clamp_spec; [lia| pose proof (rz_log_range_small n N); lia |].   (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.        (* [comment removed for export] *)
  change ((Z.b2z (8 <? 9) + -1) mod 18446744073709551616) with 0. rewrite Z.land_0_l, Z.add_0_r.
  rewrite land_align8 by lia.
  setreg 10 (Z_to_bv 64 (rounded_size n)) ltac:(f_equal; rewrite rounded_size_align; lia).
  zstep. step. if_cases KA; zify_cond KA. { exfalso. apply KA. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. change (2^3) with 8. exact RSM. }   (* [comment removed for export] *)
  step. zstep.                                                   (* [comment removed for export] *)
  replace (n <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  zstep. zstep.                                                  (* [comment removed for export] *)
  pose proof (rz_log_range_small n N) as RLR. rewrite (sllw_rz n N).   (* [comment removed for export] *)
  step. zstep.                                                   (* [comment removed for export] *)
  zstep. replace (8 <? 65537) with true by reflexivity. cbn [Z.b2z].   (* [comment removed for export] *)
  zstep.                                                         (* [comment removed for export] *)
  rewrite <- NS.
  zstep. zstep. zstep. zstep. step. zstep.                       (* [comment removed for export] *)
  replace (needed_size n <? 65537) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  change ((Z.land 1 1 + -1) mod 18446744073709551616) with 0. change (Z.land 1 1) with 1. rewrite Z.land_0_l, Z.add_0_l.
  step. if_cases KB; zify_cond KB. { exfalso. lia. }            (* [comment removed for export] *)
  step. if_cases KC; zify_cond KC. { exfalso. lia. }            (* [comment removed for export] *)
  step. step. if_cases KD; zify_cond KD. 2: { exfalso. lia. }   (* [comment removed for export] *)
  box RT.
  step. call_sp get_current_thread_spec; try OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.eassumption_fast; try lia; try reflexivity; try solve_rng.
  unbox RT. rename POST into ST.
  step. step. if_cases KE; zify_cond KE. { exfalso. lia. }      (* [comment removed for export] *)
  zstep. step. step. step.                                       (* [comment removed for export] *)
  box RCTX.
  step. call_sp (combined_alloc_hit_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t (needed_size n) c cnt spacebeg lo maxc csz stj chunks idxw).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- rng _ _ _ => solve_rng
       | |- stk _ _ _ _ => exact ST
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => reflexivity
       | |- Z.shiftr _ _ = _ => exact HC
       | |- nth_error _ _ = _ => exact NTH
       | |- length _ = _ => exact LCH
       | |- _ mod _ = _ => exact TAL
       | |- u32arr _ _ _ _ => exact CH
       | |- rw_cells _ _ (_ + 208 + _ * 80) _ => exact CR
       | |- rw_cells _ _ (_ + 2784) _ => exact STS
       | |- rw_cells _ _ _ _ => exact SB
       | |- _ => unfold AIMG_HI; lia
       end.
  apply evtF_done. unfold allocA_post. do 15 eexists. split; [reflexivity|].
  repeat lazymatch goal with |- _ /\ _ => split end.
  all: try assumption. all: eexists; eassumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
