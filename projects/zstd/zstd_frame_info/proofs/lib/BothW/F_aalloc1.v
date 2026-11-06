(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AProto ABase.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import AKit AModelFacts F_aunwind F_aalloc_s F_acache.
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
Definition allocate_entry := 0x31230%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma rz_ladder_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n : Z),
  0 <= n < 2^40 ->
  rng_aimg RNG ->
  evtF bsegs RNG (fun ms' => exists a0',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (rz_log n)) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x3139c) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 49) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x312c8) fc None m (seg_rom bsegs)).
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
  evtF bsegs RNG (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) (Z_to_bv 64 (Z.max n 8)) (Z_to_bv 64 8) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 rz) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x313e4) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) (Z_to_bv 64 7) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 rz) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x313c8) fc None m (seg_rom bsegs)).
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
     rw_cells bsegs m AINITED [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m ARSSLIM [C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m 0x9e7f8 (* [comment removed for export] *) [C8 (Z_to_bv 64 (2^40)); C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
  /\ rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)]
  /\ rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)].

Definition allocA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n S t c cnt spacebeg lo : Z) (idxw maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x314d0) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 1) (Z_to_bv 64 n)
                  (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * bv_unsigned idxw)) a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x314d0) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp); (acache_rec t c, acache_rec t c + 4); (acache_stats t, acache_stats t + 8)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp - 128)
    /\ (exists j0, rw_cells bsegs m' (bv_unsigned sp - 128)
         [CB 8 j0 (* [comment removed for export] *); C8 (Z_to_bv 64 1) (* [comment removed for export] *); C8 (Z_to_bv 64 16) (* [comment removed for export] *);
          C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ rw_cells bsegs m' (acache_rec t c) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ (exists stj' : word, rw_cells bsegs m' (acache_stats t) [C8 stj']).

#[using="Type"] Lemma allocA_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S ctx t c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 176 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= 448 -> 0 < S < 2^64 ->
  allocA_cells m ctx t ->
  rw_cells bsegs m 0x9d9f8 [C8 (Z_to_bv 64 spacebeg)] ->
  Z.shiftr (needed_size n + 31) 5 = c ->
  rw_cells bsegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr bsegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (acache_stats t) [C8 stj] ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF bsegs RNG (allocA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n S t c cnt spacebeg lo idxw maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until idxw. intros ST CEIL LO MI TP -> -> -> -> -> -> N HS AC SB HC CR CH LCH CNT NTH IXS STS C0 C1 T0 T1 TAL CT2 SBR RIMG RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  destruct AC as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, AINITED, ATSDI, ATSDK, ATP88, ATSD, ARSSLIM, allocate_entry in *.
  pose proof (small_facts n N) as (PRIM & NS & RZR & RZE & RSR & RSM & NSR).
  Local Ltac2 Set LiaHints.tbl := fun () => "05a0?10082350123.1051044680708.101 10602470230.10010629577799.98 11077664131.10011160400943.1001162083375.99  11658450183.12911775166127.10111801586693.10611801586693.11011801586693.11611863097430.98 120833238.100  12142939350.10112279985372.99 12331942998.10512431607254.10412546622119.10112742302166.10012892874966.98 13081094916.98 13187052577.10013201050402.10513338178759.1001351984962.103 14453557927.10014527015389.10614527015389.11014527015389.11614763672662.10514808378326.10014990919126.10015005990614.1011533820803.100 1577073154.98  15813913888.10316303260700.12916520521031.10116600962308.101168676054.101  16870183111.10017139085270.10017683239510.10017776320431.99 17986879152.11018274889302.10118651764129.10018712044988.1291896977110.99  19108682116.1001937063194.110 19417778390.10019491992743.10119913379627.10020294747862.10120540342678.11120605410518.10120805333024.10820805333024.95 20805333024.99 20854954799.10021153470338.10021250035837.10621250035837.11021250035837.11621313019222.10021651633935.11022161629359.10022165204226.10122284289799.10622284289799.11022284289799.11622291614806.10022439364775.99 22568407585.10022609673092.10522675801219.10122700267513.10722700267513.11122700267513.11722709700310.10124266362535.10424346898045.10624346898045.11024346898045.11624557733334.10424559885231.99 2458073255.100 24633095682.10024794926247.10124841123417.10924957053782.10124972240369.10224982576641.10324991151882.93 25029166211.10025101887574.10025119608324.10125236895702.10125348482085.10825348482085.95 25348482085.99 25632203990.98 25787632170.10325787632170.94 25878270254.10025896385351.10126083973675.99 26278908583.10026291562981.12926492550416.10026492550416.10126492550416.10426492550416.10526492550416.98 26492550416.99 26507015092.12926507015092.13026507015092.13126868428163.99 26963603670.1012726332502.105 27408782894.10027516840022.10027525343574.10027843469846.10527872253706.93 28024056534.10128031021985.10128355653425.10428575982988.13028714888022.10028737894315.10128986992043.98 29078730183.10029311285958.86 29430822486.10029782367974.1042995232086.101 29965292900.10430198278530.10030398632918.10030439345750.10030518562691.10030569431638.10030834812886.10030863979691.10031145098372.10031239308591.10032545997487.10132649392770.99 3317524822.105 33392657660.12933532905180.95 33677903874.10133890036527.99 34104777430.98 3441642428.129 34775537831.10534897542716.12935270809255.10035289778563.10536115622446.10036367760551.10036611092438.10136635094629.10937126959190.99 37156020484.10137319313223.10437410281889.98 38236700118.1043824569889.99  38915808562.11638915808567.11938996969702.91 39732881027.99 39932040893.10639932588075.10039938772488.11539938772488.11639938772490.11639940869632.11440057560022.10440091925676.98 40236713046.10040605904854.10040646919027.11040652982343.1004069431612.129 41332867286.10041420198230.10041625904943.10042240553391.10442524776790.10042858215713.10042932464815.98 42998092118.10043061431595.89 43104589767.10043181512580.10043188719081.11043987951406.10044158664835.10144251355734.10544484923210.10644484923210.11044484923210.11644522897991.10144543597654.10544833359747.10045219141890.10445238050109.10645238050109.11045238050109.11645260010070.99 45311941718.10045412913494.10045507666326.10145605676758.1014562448900.104 45655346134.10146230876290.10046236641750.10146556098215.1014678377391.101 47196622294.10147438431676.12948054906439.10148257206230.10148320830113.10448656712918.10548722578991.10548925429462.10049123722493.10649123722493.11049123722493.11649192305668.1004930072150.99  49423094309.11049425192486.10849726415815.99 49846535446.12650073722538.10350489401671.10050584888647.95 50944119766.10151043783510.10051082036054.99 51458250794.11251469190682.10351678667183.99 51818017494.10151962374742.10052076332701.11352076332702.11452237461281.10052624921519.10052675322539.10152793185963.10453074125270.10153328572246.10053375849430.10153767577775.99 54263952130.10155209202390.10155220021892.1005557113430.100 55659093462.98 55753344342.10056170256219.11256172400559.10756172529599.98 56175235539.94 56240850262.100565324930.105  56584563158.10456627242070.10056714183894.1005684463747.104 5703093030.110 57293592682.10257522549927.98 57700073633.10057743577986.10058168296790.10058176800342.99 58362767830.10158403784534.10058620750422.10158655119491.10158943047254.10059109042223.99 59314873579.10659314873579.10759314873579.10859314873579.11059314873579.94 59381022806.10059576986246.10759907387523.10160468873383.10060469743958.10460634079619.10060968048854.10060997568167.10061228736260.10061486152918.10061521325654.99 61616721185.10061889459015.99 61917199023.99 61929802144.10561929802406.10761939782290.11562017286614.10062798988758.10163011388847.10163047610823.10563077870550.10163164784673.10563172006742.10063235321900.97 63294709462.10063314293035.1006386026005.104 64260757035.10064302930659.93 64484505430.10064803448158.13065807272962.10165811741693.10665811741693.11065811741693.11665822580054.10065983638659.10066028155702.10266028155702.11166028155702.11366028155702.98 66330498723.10466773347627.10067081432737.10167100501013.85 67215858474.10467256438148.99 67606130518.10067841563051.10068031924935.10068369921750.10468693594283.1017055476356.100 747874518.98   7587324118.98  7669170646.100 773933615.100  7741215905.101 8179223683.98  8432272592.131 8581623554.100 8595948976.116 8595948983.119 8610795133.106 8610795133.110 8610795133.116 9272504225.101 9581476779.101 9612232322.100 9954448086.101 00000<00@00I00U00V00j00n00o01C01^02902T02]02f02o03003903B03C03L03U03Y03i03n04:04;04<04I04V04c04l05505>05G05H05M05Q06@06L06P06Y06e06n07707;07A07J07Z08B08K08O08S08\08]08i09209309<09=09>09?09S09X09e0:20:?0:H0:Q0:e0:j0:k0:l0:m0;60;70;G0;K0;L0<90<f0=W0=`0=a0=n0>;0>H0>Q0>U0>V0>[0>\0>]0>f0>g0>h0>i0>j0?30?70?@0?D0?H0?L0?U0?X0?[0?_0?k0@70@80@90@:0@;0@<0@=0@>0@?0A40A50AI0AJ0AS0A\0A`0Ai0B20B30B40B=0BM0BN0CJ0CS0C_0Ck0D70D80DA0DB0DK0DN0DS0D\0De0Df0Do0E80ED0EH0E\0F00F50F>0Ff0Fg0Fl0G00G90Ga0Gb0HJ0HK0HL0HP0HQ0HZ0Ho0I80I<0IH0IX0Ia0J10J20J30J40J50J:0JF0JG0JL0JS0JX0Ja0Je0Jn0K70K@0KL0L40L=0LF0LZ0Ln0M70MG0M[0Md0Mh0N40N80N=0NA0NB0NK0NL0NM0NN0NZ0Nc0Nd0Ni0O60OC0OP0OY0Ob0Ok0Ol0P50P90PB0PG0PP0PQ0Pe0Pn0QV0Qb0Qk0R;0RD0RX0Ra0Rn0S;0SH0SL0SU0SY0S]0Si0Sj0Sk0T70T80TA0TJ0TS0TV0TY0T]0Tf0To0U00U10UA0UU0Ua0Um0V60V?0VH0VL0VQ0VZ0V^0Vg0W00W90W>0W?0W@0WA0WJ0WO0WX0Wa0Wj0Wk0X00X10X20XB0XG0XP0XY0Xb0Xk0Y40Y50Y>0YR0Y\0Yh0Z20ZC0ZN0ZW0ZX0ZY0ZZ0Zc0Zd0Zm0Zn0[20[;0[D0[T0[U0[Y0[\0[_0[b0[k0\40\H0\T0\]0\m0]60]:0]C0]O0]R0]^0]b0]k0^?0^D0^Q0^^0^k0_40_50_D0_S0_b0`10`50`A0`Q0a00a10a50a>0aJ0aV0a_0ak0ao0b80bA0bJ0b^0bn0bo0c?0cD0cE0cF0cS0c`0cm0d=0dI0dN0dWS4CEIL2LO2T1S2HBS4CEIL2LOS4CEIL2LO2C1SS4CEIL2LO3LCH2T13C16S2LOFS4CEIL2LO3LCH2T13C16S3Hsp4CEIL2LO2T13C162C13LCHS3Hsp4CEIL2LO2T13C162C13LCHS3Hsp4CEIL2LO2T13C162C13LCHS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LOS2HBS4CEIL2LO2T13C16S3NSRS4CEIL2LO2C1SSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS3SPRS2LOS4CEIL2LO2HS2HC3LCH2C02T03TAL3C162KS3RLR2KE3HspS4CEIL2LO2C1S2HBS4CEIL2LOS4CEIL2LO2C1S4CEIL2LOS4CEIL2LOS2LOS4CEILS4CEIL2LOS4CEIL2LO2T13C16S4CEIL2LO2HC3LCH3TAL3RSR3RSM3C163RLR3HspS4CEIL2LOS2HBS2T1S4CEIL2LOSS4CEIL2LO2T1S4CEIL2LOSS4CEIL2LOFFFS4CEIL2LO3LCH2T13C16S3SPRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS3LCH3IXSS4CEIL2LO3LCH2T13C16S3SPRFFFS4CEIL2LOSS4CEIL2LO2T13C16S2HBSS4CEIL2LO2HS3LCH2C02C12T02T13CT23C162KS3Hsp1HS4CEIL2LO2HS3LCH2C02C12T02T13CT23C162KS3Hsp1HS4CEIL2LO2HS3LCH2C02C12T02T13CT23C162KS3RLR3Hsp1HS4CEIL2LOSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS2LOSS3SPRSFS4CEIL2LOSSSSS4CEIL2LOS2HBS4CEIL2LOS2LOS2LOS2LOS4CEIL2LOS1NS1NS2LOS4CEIL2LO2C1S4CEIL2LO2T1SFSSSSSSS4CEIL2LO2HS3LCH2C02C12T02T13CT23C162KS3RLR2KE3Hsp2HCFS4CEIL2LO2T13C163HspSS4CEIL2LOS4CEIL2LOS2LOS4CEIL2LOS4CEIL2LOSSS4CEIL2LOS4CEIL2LO2T13C16SS4CEIL2LO2HS3LCH2C02C12T02T13CT23RSR3RSM3C162KS3RLR2KE3Hsp1HS4CEIL2LOS4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LO2C1SS4CEIL2LOSS4CEIL2LOS1NS3SPRS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LOS4CEIL2LO2T1S2HBS4CEIL2LO3LCH2T13C16S4CEIL2LO3LCH2T13C16S3SPRS4CEIL2LOS4CEIL2LO2HC3LCH3TAL3RSR3RSM3C163RLR3HspSS3SPRS2LOS4CEIL2LOS4CEIL2LO2HC3LCH3TAL3RSR3RSM3C163RLR3HspSS4CEIL2LO2HC3LCH3TAL3RSR3RSM3C163RLR3HspSSS2LOSS4CEIL2LOS2HS3LCH2T02T12KS3RLRS4CEIL2LOS2HBS4CEIL2LO2C1S4CEIL2LO2T13C16S4CEIL2LOS4CEIL2LO2T13C16SSSFS3NSRS4CEIL2LO2T1FS3NSRS1N3RSRS3RZRS4CEIL2LOS2LOS4CEIL2LOS4CEIL2LOS3LCH3CNTS4CEIL2LO2C1S4CEIL2LO2HC3LCH3TAL3RSR3RSM3C163RLR3HspS4CEIL2LOS4CEIL2LOS4CEIL2LO3LCH2T13C16S4CEIL2LO3LCH2T13C16S4CEIL2LOS4CEIL2LO2T13C16S4CEIL2LO3LCH2T13C16S4CEIL2LOS2LOS4CEIL2LO2C1S2HBS3NSRS2LOSS4CEIL2LOFFFS4CEIL2LO2C1S4CEIL2LOSS3SPRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOS2HBS4CEIL2LOS3SPRS4CEIL2LOSS4CEIL2LO3LCH2T13C16S4CEIL2LOS4CEIL2LO2HC3LCH3TAL3RSR3RSM3C163RLR3HspS4CEIL2LO2C1S4CEIL2LOS4CEIL2LO2T13C16S4CEIL2LOS4CEIL2LO3LCH2T13C16S4CEIL2LOS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS2HBS4CEIL2LOS2LOS2C0S4CEIL2LO2C1SFS4CEIL2LO2C1FS4CEIL2LOS4CEIL2LOS4CEIL2LOS1NS1NS2LOS4CEIL2LOS4CEIL2LOFFS4CEIL2LO2T13C16S4CEIL2LO3LCH2T13C16S4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LOS4CEIL2LOS4CEIL2LOS2LOS3SPRS4CEIL2LOS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOS3HspSSSS4CEIL2LOS3SPRS4CEIL2LOS4CEIL2LOS4CEIL2LOSS3SBRSSS4CEIL2LO2T13C16S3SPRS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LOSS4CEIL2LOS4CEIL2LO3LCH2T13C16S1N3LCH2KBS3LCH3NSR2KCS1N3LCH2KDS2HS3LCH2T02KS2KES2HS3LCH2KSS4CEIL2LOSSSS4CEIL2LOSS4CEIL2LOSS2HBS4CEIL2LOS4CEIL2LOS4CEIL2LO2T13C16FS2LOS1NS1NS1NS4CEIL2LOS4CEIL2LOS4CEIL2LO3LCH2T13C16S4CEIL2LO2C1S4CEIL2LOS4CEIL2LO2T13C16S4CEIL2LOS2LOS4CEIL2LOS4CEIL2LO2T1S1HS4CEIL2LO2T1S2HSS4CEIL2LOS4CEIL2LO2T13C163HspS3SPRS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LOSS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS4CEIL2LO3SPR1HS2LOS4CEIL2LO2T1S4CEIL2LO2T13C16S3LCH2C02NS3RZR3RZE3RSR3RSM3NSRSS2HBS4CEIL2LOS4CEIL2LO2T1S4CEIL2LO2C1S4CEIL2LOS4CEIL2LO2T1S2HBS4CEIL2LOS4CEIL2LOS4CEIL2LOS4CEIL2LO3LCH2T13C16S4CEIL2LO2T13C16SS4CEIL2LO2T13HspS3SPRSSS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO3HspS4CEIL2LO2T13C16S4CEIL2LO2T1S3SPRS4CEIL2LO".
assert (C16 : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp); (acache_rec t c, acache_rec t c + 4); (acache_stats t, acache_stats t + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
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
