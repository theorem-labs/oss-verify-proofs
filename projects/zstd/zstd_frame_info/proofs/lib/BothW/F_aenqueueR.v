(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg ABase AQConst ABytes.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import AKit AKit2 AKitQ.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Notation acache24 t := (t + 2128) (only parsing).       (* [comment removed for export] *)
Notation acache_stats t := (t + 2784) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition enq_to_refill_post (ra sp gp tp s0 s1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x35634) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2
                  (Z_to_bv 64 (acache24 t)) (Z_to_bv 64 (t + 208))
                  (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (acache24 t)) (Z_to_bv 64 0x9d9d8) (Z_to_bv 64 K_BATCH_CLASS) a4 a5 a6 a7
                  (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) a2 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x35e14) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -64)
    /\ rw_cells bsegs m' (bv_unsigned sp + -64) [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="Type"] Lemma enqueue_to_refill_spec : forall (full : bool) (t lst : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst qb hm n nx bsz lo : Z) (maxc csz : word),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 64 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 (t + 80) -> a1 = Z_to_bv 64 (t + 208) -> a3 = Z_to_bv 64 hm -> a4 = Z_to_bv 64 n ->
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= lst < 2^64 ->
  (if full then 0 < nb /\ rw_cells bsegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 Q_BATCH)]
             /\ AIMG_HI <= lst /\ lst + Q_BATCH_BYTES <= ATOP /\ rng RNG lst Q_BATCH_BYTES
   else nb = 0) ->
  (* [comment removed for export] *)
  rw_cells bsegs m (acache24 t) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 ->
  (t + 4096 <= lst \/ lst + Q_BATCH_BYTES <= t \/ lst = 0) ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF bsegs RNG (enq_to_refill_post ra sp gp tp s0 s1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t hm n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x354e0) fc None m (seg_rom bsegs)).
Proof.
  intros until csz. intros ST CEIL LO MI -> -> -> -> QC NB LST FULL CR T0 T1 TAL DTL RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, Q_BATCH, Q_BATCH_BYTES, K_BATCH_CLASS in *.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  Local Ltac2 Set LiaHints.tbl := fun () => "0270>11805467289.7111805467289.7211805467289.7311805467289.7411805467289.7511805467289.7611805467289.7711805467289.7811912744615.7311912744615.7712367362435.7212367362435.7613021749692.7313021749692.771318492691.73 1318492691.77 13415235858.7413415235858.791527479463.71 1527479463.75 17073101331.7317073101331.7717646078182.6517776320431.7217776320431.7618321399886.7718727805075.7418727805075.7819049469500.7419049469500.7819360297235.7319360297235.7721617132179.7121617132179.7521638840877.8021918414723.7321918414723.7724630998586.7124630998586.7525314760359.7425314760359.7825663111059.7425663111059.7825878270254.7325878270254.7728548849043.7428548849043.7828749799758.7729387301326.7831081687356.7431081687356.7831288622798.7832651489978.7332651489978.7733039531175.7433039531175.7833680001082.7433680001082.7834484510867.7434484510867.7835764571985.7735764571985.813593105683.73 3593105683.77 36115622446.7336115622446.7736834464974.7536993589379.7436993589379.7837107179452.7237107179452.7637478275932.8038148493075.7238148493075.7638647909198.763945979267.73 3945979267.77 41809558659.7141809558659.7543060403331.7443060403331.7843061431595.6343987951406.7343987951406.7745221239098.7445221239098.7849998208403.7449998208403.7850295509469.7951481786499.7451481786499.7851747557201.7551747557201.8053767577775.7253767577775.7656228262055.7256228262055.76563227834.72  563227834.76  57167265742.7857745675194.7357745675194.775849940627.71 5849940627.75 58804816386.6658804816386.7059314873579.6759314873579.6859314873579.7159314873579.7259314873579.7359587366675.7259587366675.7660025031335.7460025031335.7861482382924.6761482382924.7261917199020.7161917199020.7563235321900.7063235321900.7463694018620.7463694018620.7865276466911.7665276466911.8067800801447.7367800801447.777010956092.71 7010956092.75 8583720762.74 8583720762.78 985337532.73  985337532.77  9908502419.74 9908502419.78 00000100200300400500600700800900:00;00<00@00D00P00\00]00^00_00`00l01801901=01A01M01Y01e01i01m02902E02Q02]02^02_02`02e02j02k02l03803D03H03L03X03d04004<04@04D04P04U04Z04[04\04a04f05205>05?05@05L05X05\05`05l05m05n06206606706C06O06[06\06]06^06_06`06a06e06i06m07207707C07O07P07Q07R07S07T07X07\07]07^07c07h08408908>08J08V08Z08^08i08n09609:09>09J09V09W09X09Y09Z09^09b09f09j09n0:20:30:40:50:60::0:>0:C0:H0:L0:P0:\0:hSSSSSSSSSSSSS2HBS2HBS4CEIL2LO2T1S4CEIL2LO2T1SSSSS4CEIL2LO2T1S4CEIL2LO2T1SS2LOS2LOS4CEIL2LO2L1S4CEIL2LO2T1S4CEIL2LO2T1S2HBS2HBS4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LO2T1SSSS3SPRS3SPRSSS4CEIL2LO2T1S4CEIL2LO2T1S2LOS2LOS4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LO2L1S4CEIL2LO2L1S2HBS2HBS4CEIL2LO2L1S3SPRS3SPRSSS3SPRS3SPRS4CEIL2LO2T1S4CEIL2LO2T1SSS4CEIL2LO2T1S4CEIL2LO2T1S2LOS2LOS4CEIL2LO2L1SSS2HBS2HBSS4CEIL2LO2T1S4CEIL2LO2T1S4CEIL2LO2L1SSSSSSS2LOS2LOS2LOS3SPRS3SPRS4CEIL2LO2T1S4CEIL2LO2T1SSSSSS2LOS2LOSSS3SPRS3SPRS4CEIL2LO2L1S3SPRS3SPRS4CEIL2LO2T1S4CEIL2LO2T1S2NBS2NBS2NB3NB02K0S3K2'S3NB12K0S2K1S2K2S4CEIL2LO2T1S4CEIL2LO2T1SSSSS2LOS2LOS2LOS2LOS2HBS2HBSSSSS2HBS2HBS3SPRS3SPRS2HBS2HBS4CEIL2LO2T1S4CEIL2LO2T1".
carve_frame 64%nat ST.
  destruct full.
  - (* [comment removed for export] *)
    destruct FULL as (NB1 & LB & L0 & L1 & RL).
    do 8 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. step. step. if_cases K1; zify_cond K1; [exfalso; lia|].   (* [comment removed for export] *)
    lstep.                                     (* [comment removed for export] *)
    step. if_cases K2; zify_cond K2; [|exfalso; lia].        (* [comment removed for export] *)
    zstep. step. step.                         (* [comment removed for export] *)
    step. step. step. step. step. step.        (* [comment removed for export] *)
    step. step. step.                          (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    unfold enq_to_refill_post. finish. exact FR.
  - (* [comment removed for export] *)
    pose proof FULL as NB0. clear FULL.
    do 8 step.                                 (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [|exfalso; lia].        (* [comment removed for export] *)
    lstep.                                     (* [comment removed for export] *)
    step. if_cases K2'; zify_cond K2'; [|exfalso; lia].      (* [comment removed for export] *)
    zstep. step. step.
    step. step. step. step. step. step.
    step. step. step.
    step.
    unfold enq_to_refill_post. finish. exact FR.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition enq_from_refill_post (full : bool) (vra sp gp tp v0 v1 v2 v3 v4 v5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t nb fst lst qb hm n nx bsz cnt b lo : Z) (maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR vra (Z_to_bv 64 (bv_unsigned sp + 64)) gp tp t0 t1 t2 v0 v1 a0 a1 a2 a3 a4 a5 a6 a7 v2 v3 v4 v5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc vra) fc None m' (seg_rom bsegs)
    /\ munch [(t + 80, t + 112); (acache24 t, acache24 t + 4); (acache_stats t, acache_stats t + 8);
              (lst, lst + 8); (b, b + 8192)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + 64)
    /\ rw_cells bsegs m' (t + 80) [C8 (Z_to_bv 64 (nb + 1)); C8 (Z_to_bv 64 (if full then fst else b)); C8 (Z_to_bv 64 b);
                                 C8 (Z_to_bv 64 (qb + (n + 8192)))]
    /\ rw_cells bsegs m' (acache24 t) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ (exists stj' : word, rw_cells bsegs m' (acache_stats t) [C8 stj'])
    /\ rw_cells bsegs m' b [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (n + 8192)); C8 (Z_to_bv 64 1)]
    /\ u64arr bsegs m' (b + 24) [Z_to_bv 64 hm]
    /\ (exists bs, rw_cells bsegs m' (b + 24 + 8 * 1) [CB (Z.to_nat (8192 - 24 - 8 * 1)) bs])
    /\ (if full then rw_cells bsegs m' lst [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 1021)] else True).

#[using="Type"] Lemma enqueue_from_refill_spec : forall (full : bool) (t lst b : Z) RNG
    (ra0 sp gp tp t0 t1 t2 vra v0 v1 v2 v3 v4 v5 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : amem) (nb fst qb hm n nx bsz cnt spacebeg lo : Z) (maxc csz stj idxw : word) (chunks : list word) (j0 : list byte),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 64 < 2^64 ->
  mem_inv bsegs m ->
  rw_cells bsegs m (bv_unsigned sp) [CB 8 j0; C8 v5; C8 v4; C8 v3; C8 v2; C8 v1; C8 v0; C8 vra] ->
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 <= nb < 2^62 -> 0 <= qb -> qb + n + Q_BATCH_BYTES < 2^63 -> 0 <= n -> 0 <= hm < 2^64 -> 0 <= fst < 2^64 -> 0 <= lst < 2^64 ->
  (if full then 0 < nb /\ rw_cells bsegs m lst [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 bsz); C8 (Z_to_bv 64 Q_BATCH)]
             /\ 0 <= nx < 2^64 /\ 0 <= bsz < 2^64 /\ AIMG_HI <= lst /\ lst + Q_BATCH_BYTES <= ATOP
   else nb = 0) ->
  (* [comment removed for export] *)
  rw_cells bsegs m 0x9d9f8 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells bsegs m (acache24 t) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr bsegs m (acache24 t + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (acache_stats t) [C8 stj] ->
  b = spacebeg + K_BATCH_CLASS * 2^32 + 16 * bv_unsigned idxw ->
  (exists bs, rw_cells bsegs m b [CB (Z.to_nat Q_BATCH_BYTES) bs]) ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> 0 < spacebeg -> AIMG_HI <= b -> b + Q_BATCH_BYTES <= ATOP ->
  (t + 4096 <= b \/ b + Q_BATCH_BYTES <= t) -> (t + 4096 <= lst \/ lst + Q_BATCH_BYTES <= t \/ lst = 0) -> (b + Q_BATCH_BYTES <= lst \/ lst + Q_BATCH_BYTES <= b) ->
  rng_aimg RNG -> rng RNG (bv_unsigned sp) 64 -> rng RNG t 4096 -> rng RNG b Q_BATCH_BYTES -> (if full then rng RNG lst Q_BATCH_BYTES else True) ->
  evtF bsegs RNG (enq_from_refill_post full vra sp gp tp v0 v1 v2 v3 v4 v5 s6 s7 s8 s9 s10 s11 F fc t nb fst lst qb hm n nx bsz cnt b lo maxc csz m)
    (MS (mkR ra0 sp gp tp t0 t1 t2 (Z_to_bv 64 (acache24 t)) (Z_to_bv 64 (t + 208))
             (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 hm) (Z_to_bv 64 (t + 80)) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x35634) fc None m (seg_rom bsegs)).
Proof.
  intros until j0. intros ST CEIL LO SP64 MI FR QC NB QB QBN N HM FST LST FULL SB CR CH LCH CNT NTH IXS STS HB BJ T0 T1 TAL SBP B0 B1 DTB DTL DBL RIMG RSTK RT RB RL. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, Q_BATCH, Q_BATCH_BYTES, K_BATCH_CLASS in *.
  pose proof (munch_refl [(t + 80, t + 112); (t + 2128, t + 2128 + 4); (t + 2784, t + 2784 + 8); (lst, lst + 8); (b, b + 8192)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR. word_range idxw IXR.
  destruct BJ as [junkb BJ]. Local Ltac2 Set LiaHints.tbl := fun () => "04g0?10082350123.11710082350123.12210422297078.11610422297078.12111213771118.10411213771118.10911775166127.11711775166127.12212282866549.11612282866549.12112431607254.11712505512393.10912505512393.11412506424771.10212506424771.10712525554635.10212525554635.10713415235858.10813415235858.11313415235868.11114081336602.10814081336602.11414081336602.12114191121987.11314191121987.11814763672662.11714763672662.12215219254896.11615219254896.12115721548975.10915721548975.11415867407727.11515867407727.12016553534906.11316553534906.11816654661902.11016654661902.11518718229056.12118781667829.11518781667829.12018867207222.10218867207222.10718930958230.10219118515698.11719118515698.12219515728436.10219515728436.10719728240786.11519728240786.12019967583878.11719967583878.1222120151001.115 2120151001.120 2132821131.122 21638840877.11721638840877.12121638840877.12221651633935.10221651633935.10721878215663.11621878215663.12125098853573.11325098853573.11825281518355.12225993202438.11725993202438.12226081728704.12127233233268.1222724243422.116 2724243422.121 27345537325.11727810735710.11627810735710.12128691991121.10628691991121.11129003366760.10229003366760.10729518211028.10329518211028.10830842648281.11530842648281.12031286525686.12232004012422.11732026549982.11532026549982.12032473033413.11332473033413.11833677903874.11733677903874.12233725004155.11733725004155.12234482413739.11734482413739.12235212070530.11335212070530.11835268010949.11335268010949.11835764571985.11435764571985.11635764571985.11935764571985.12137868945377.12137951031538.11738138682880.11438138682880.11938150590251.11738150590251.1223830991471.116 3830991471.121 3832027923.122 38566322049.11338566322049.11838650006390.12238860591861.11638860591861.12139460092674.11239460092674.11739855497601.11339855497601.11839888517249.11339888517249.11840753433856.11440753433856.11940818989526.10340818989526.10840854900190.11640854900190.12141956975378.11541956975378.12042240553391.11742333175588.11342333175588.11842828922350.10342828922350.10842828922350.10942828922350.11442828922350.11642828922350.12143151507489.10643151507489.11144021460374.10244021460374.1074409199500.117 4409199500.122 4474788558.122 4474952704.114 4474952704.119 45219141890.11747489664620.10747489664620.11247650684435.12248185458843.10348185458843.10848185458843.10948185458843.11448185458843.11648185458843.12148445925628.10648445925628.11148480135152.11648480135152.12148722578991.11748722578991.12248843461303.10348843461303.10848843461303.11648843461303.12148930319418.11248930319418.11749141338643.11449141338643.11949242818135.10249242818135.10749388040153.11549388040153.12049996111275.11750295509468.11650295509468.12150295509469.12050526502779.11750669429877.10250669429877.10750915327836.11650915327836.12151000560815.11651000560815.12151007082073.11651007082073.12151246144882.11651246144882.12151345202948.10951345202948.11451356649574.10251356649574.10751747557201.10951747557201.11251747557201.1145195591069.105 5195591069.110 5244888359.110 5244888359.115 52565067731.10352565067731.10852565067731.10952565067731.11352565067731.11452565067731.11552565067731.11652565067731.11752565067731.11852565067731.12052565067731.12152565067731.12252793185963.11753289372016.11553289372016.12055517901572.12255989853626.10155989853626.10656216855090.12256428783466.10356428783466.10856428783466.10956428783466.11456428783466.11656428783466.12156439567680.120565324930.117  565324930.122  56717501381.11356717501381.11857008552236.10258273841244.11658528603905.11358528603905.11858804815878.10658804815878.11158899268058.10958899268058.11458931693703.10858933790875.10359314873579.10259314873579.10459314873579.10759314873579.10959314873579.11259395809188.11859455635980.11759455635980.12259483211481.11659483211481.12159536183085.11759536183085.12259584255094.11659584255094.12160066839216.10360066839216.10860066839216.10960066839216.11460066839216.11660066839216.12160554839223.12261156831970.11361156831970.11861523295858.10361523295858.10861542199749.12263418925148.11163418925148.11664593875639.10364593875639.10864593875639.10964593875639.1146514018009.116 6514018009.121 65276466908.11365276466908.11865276466909.11565276466909.12066397384571.11766397384571.12266541015119.11366541015119.11866759593561.11666759593561.12167033309574.10267033309574.10767388853175.10967388853175.11467388853175.11667388853175.12167600552182.11567600552182.1208233180530.109 8233180530.114 835094361.116  835094361.121  8879850866.117 8879850866.122 9128841996.117 9311109081.116 9311109081.121 9552935473.122 9581476779.117 9581476779.122 9869190602.102 9869190602.107 9954448086.117 9954448086.122 998721837.112  998721837.117  00000500:00C00L00Q00V00[00`01F01n02702@02I02R02[02d02m03203703<03H03T03`03h04004904B04J04R04W04\04d04l05505>05G05P05\06B06j06o07407907B07K07P07U07Z07_07h08108:08C08H08M08R08W08`08i09109909>09C09O09X09a09m0:60:?0:H0:M0:]0:m0;50;=0;B0;G0;L0;Q0;Z0;c0;o0<80<H0<X0<a0<j0=30=<0=A0=F0=K0=P0=Q0=R0=[0=d0=i0=n0>30>80>=0>F0>G0>L0>Q0>V0>^0>f0?20?30?80?D0?j0@R0@S0@X0@Y0@^0@_0@d0@e0@j0@o0A40AD0AT0AY0A^0Ac0Ak0B30B<0BE0BN0BW0B`0Bi0Bn0C30C80C=0CM0C]0Ce0Cf0Ck0D40D90D>0DJ0DO0DT0DY0D^0Dc0Dh0Dm0E20E:0EB0EG0EL0EQ0EV0E[0E`0Ee0Ej0Eo0F40F90F>0FG0FP0FU0FZ0F_0Fd0Fi0Fn0G30G80G=0GB0GG0GP0GY0Gb0Gk0H00H50HF0HZ0H_0Hd0Hi0Hj0Ho0I40I90I>0IC0IH0IM0IR0IW0I\0Ia0If0Ik0J00J50J:0JB0JJ0JZ0K:0K]0Ki0L20L;0LD0LM0LV0L_0Lk0M40M=0MF0MO0MX0M]0NC0Nk0No0O30O80O=0OH0OS0O[0Og0P=0PH0PT0P`0Q00Q@0QI0QR0QW0Q\0Qe0Qn0R>0RN0R^0Rn0S>0SN0T<0TL0T\0Te0Tn0U30U80U=0UB0UG0UL0UQ0UZ0Uc0Uh0Um0V20V70V<0VA0VF0VK0VT0V]0Vb0Vg0Vl0W10W60W;0WD0WM0WV0W_0Wh0X10X:0XC0XS0X\0Xe0Xn0Y30Y80Y=0YB0YK0YT0YY0Y^S3LCHS3LCHS3LCH3HB0S3LCH3HB0S3LCHS3LCHS3LCHS3LCHS3LCH2HB2T03SBP2B03DTB3DTL3DBL3IXR3K3'S2L03LCH2HB2T03SBP2B03DTB3DTL3DBL3IXR2K3S3LCH3TALS3LCH3CNTS3LCH3CNTS3LCH3CNTS3LCH3CNTS3LCH3CNTS3LCH3CNTS3LCHS3LCHS3LCHS2L03LCH3DTLS2L03LCH3DTLS2L03LCH3DTLS3LCH2B0S3LCH2B0S3LCH3TALS3LCH3TALS3LCH2B0S3LCH2B0S3LCHS3LCHS3LCH2B0S3LCH2B0S3LCH3HB0S3LCH3HB0S3LCH3CNTS3LCH3CNTS2L03LCH3DBLS3LCH2HB2T03SBP2B03DTB3DTL3DBL3IXR3K3'S2L03LCH2HB2T03SBP2B03DTB3DTL3DBL3IXR2K3S3LCHS3LCHS3LCHS3LCH3DTBS3LCH3DTBS3LCHS3LCHS3LCHS3LCHS3LCH3HB0S3LCH3HB0S3LCH3DTBS3LCH3DTBS3LCHS3LCHS3LCHS3LCHS3LCH3IXSS3LCH3IXSS3LCH2B0S3LCH2B0S3LCHS3LCHS2L03LCH3DTLS3LCH3HB0S3LCH3HB0S2L03LCH3DBLS3LCH3HB0S3LCH3DTBS3LCH3DTBS3LCHS4CEIL2LO3LCH2B1S4CEIL2LO3LCH2B1S2LO3LCHS2LO3LCHS3LCHS3LCHS3LCHS3LCHS3LCH3DTBS3LCH3DTBS2L03LCH3DTLS3LCH3HB0S4CEIL2LO3LCH2B1S4CEIL2LO3LCH2B1S3LCH3DTBS3LCH3DTBS3LCH3HB0S3LCH3HB0S3LCHS3LCHS3LCHS3LCHFFS3LCH3DTBS3LCH3DTBS3LCHS3LCHS3LCHS3LCHS3LCHS3LCH3DTBSS3LCHS3LCHS3LCHS3LCH2B0S3LCH2B0S2L03LCH3DTLSS3LCHS2L03LCH3DTLS3LCH2HB2T03SBP2B03DTB3DTL3DBL3IXR3K3'S2L03LCH2HB2T03SBP2B03DTB3DTL3DBL3IXR2K3SS3LCHSS3LCHSS3LCHSS3LCHS3LCHS3LCHS4CEIL2LO3LCH2B1S4CEIL2LO3LCH2B1S3LCHS3LCHS3LCHS3LCH2B0S3LCH2B0S3LCH3HB0S3LCH3HB0S3LCH3HB0S3LCH3HB0S3LCH3HB0S3LCH3HB0S3LCHS3LCHS3LCHS3LCHS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S2L03LCHSS3LCHS3LCH3HB0S3LCHS3LCHS2L03LCH3DTLS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCH2B0S3LCH2B0S3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCH3DTBS3LCH3DTBS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCH3DTBS3LCH3DTBS3LCH3HB0S3LCH3HB0S3LCHS3LCHS3LCH2T02T13TAL1HS2L03LCH2T02T13TAL1HS3LCHS3LCHS3LCHSS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCH2B0S3LCH2B0S4CEIL2LO2L13LCHS3LCH2HB3TAL3SBP3DTB3DTL3DBL3IXRS2L03LCH2HB3TAL3SBP3DTB3DTL3DBL3IXRS2L03LCH3DBLS3LCH3TALS3LCH3TALS3LCH3TALS3LCH3TALS3LCH3TALS3LCH3TALS2L03LCH3DBLS3LCH3HB0S3LCH3HB0S3LCH3DTBS3LCH3DTBS3LCH3CNTS3LCHS3LCH2HB2T03SBP2B03DTB3DTL3DBL3IXR3K3'S2L03LCH2HB2T03SBP2B03DTB3DTL3DBL3IXR2K3S2NBS2NBS3LCHS3LCHS3LCH2B02B1S3LCH2B02B1S3LCH2KRS3LCH2B03K3'S2NB3LCH2B03NB03K3'2K4S3LCH2B02K3S3NB13LCH2K4S2L03LCH3DBLS4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S3LCH3DTBS3LCH3DTBS3LCHS3LCHS3LCH3HB0S3LCH3HB0S4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S4CEIL2LO3LCH2T1S2NB2L03LCH2HB2T03SBP2B03DTB3DTL3DBL3IXR2K32K4S4CEIL2LO3LCH2B1S4CEIL2LO3LCH2B1S3LCH3HB0S3LCH3HB0S3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCH3DTBS3LCH3DTBS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCH3DTBS3LCH3DTBS3LCHS3LCHS3LCHS3LCHS3LCHS3LCHS3LCH3HB0S3LCH3HB0S3LCH3HB0S3LCH3HB0S3LCH3DTBS3LCH3DTBS3LCH3DTBS3LCH3DTBS4CEIL2LO3LCH2T1S3LCH3DTBS3LCH3DTBS3LST3LCHS3LCHS3LCHS3LCHS3LCHS3LCH3TALS3LCH3TALS3LCHS3LCH".
pose proof (stk_of_cb _ _ _ _ BJ ltac:(lia)) as TB. clear BJ junkb.
  (* [comment removed for export] *)
  step.                                        (* [comment removed for export] *)
  step. if_cases KR; zify_cond KR; [exfalso; lia|].          (* [comment removed for export] *)
  step. step. step.                            (* [comment removed for export] *)
  lstep.                                       (* [comment removed for export] *)
  step. step.                                  (* [comment removed for export] *)
  destruct full.
  - (* [comment removed for export] *)
    destruct FULL as (NB1 & LB & NX & BSZ & L0 & L1).
    (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    step. zstep. zstep.                        (* [comment removed for export] *)
    pose proof (u32arr_read bsegs _ _ chunks (cnt + -1) idxw (wa (t + 2128 + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. clear RD. rewrite (zx32_small idxw) by lia.        (* [comment removed for export] *)
    assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]).
    amo_stepA AMO.                             (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. zstep. zstep. zstep.          (* [comment removed for export] *)
    setreg 11%Z (Z_to_bv 64 b) ltac:(rewrite HB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases K3; zify_cond K3; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. zstep.                         (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split bsegs mm b (b + 32) (b + 8192) TB ltac:(lia)) as [TB0 TB1];
      destruct (stk_cb mm _ _ TB0 ltac:(lia)) as [junk32 BH] end.
    clear TB TB0. replace (Z.to_nat (b + 32 - b)) with 32%nat in BH by lia.
    step. step. step. step.                    (* [comment removed for export] *)
    step. if_cases K4; zify_cond K4; [exfalso; lia|].        (* [comment removed for export] *)
    step. step. zstep. step.                   (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. step.                         (* [comment removed for export] *)
    do 9 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp + 64).
    rw_split BH 3%nat BH1 BH2.
    unfold enq_from_refill_post. finish.
    + eexists. exact STS.
    + apply u64arr_one. exact BH2.
    + lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TB1 ltac:(lia)) as [bs Hbs] end.
      exists bs. replace (b + 8192 - (b + 32)) with (8192 - 24 - 8 * 1) in Hbs by lia. replace (b + 32) with (b + 24 + 8 * 1) in Hbs by lia. exact Hbs.
  - (* [comment removed for export] *)
    pose proof FULL as NB0. clear FULL.
    zstep. zstep.                              (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    zstep. zstep.                              (* [comment removed for export] *)
    replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
      by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
    step. zstep. zstep.                        (* [comment removed for export] *)
    pose proof (u32arr_read bsegs _ _ chunks (cnt + -1) idxw (wa (t + 2128 + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
    step. clear RD. rewrite (zx32_small idxw) by lia.        (* [comment removed for export] *)
    assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]).
    amo_stepA AMO.                             (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. zstep. zstep. zstep.          (* [comment removed for export] *)
    setreg 11%Z (Z_to_bv 64 b) ltac:(rewrite HB; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    step. if_cases K3'; zify_cond K3'; [exfalso; lia|].      (* [comment removed for export] *)
    step. step. zstep.                         (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split bsegs mm b (b + 32) (b + 8192) TB ltac:(lia)) as [TB0 TB1];
      destruct (stk_cb mm _ _ TB0 ltac:(lia)) as [junk32 BH] end.
    clear TB TB0. replace (Z.to_nat (b + 32 - b)) with 32%nat in BH by lia.
    step. step. step. step.                    (* [comment removed for export] *)
    step. if_cases K4; zify_cond K4; [|exfalso; lia].        (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    step. step.                                (* [comment removed for export] *)
    step. zstep. step.                         (* [comment removed for export] *)
    do 9 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp + 64).
    rw_split BH 3%nat BH1 BH2.
    unfold enq_from_refill_post. finish.
    + subst nb. exact QC.
    + eexists. exact STS.
    + apply u64arr_one. exact BH2.
    + lazymatch goal with |- exists bs, rw_cells _ ?mm _ _ => destruct (stk_cb mm _ _ TB1 ltac:(lia)) as [bs Hbs] end.
      exists bs. replace (b + 8192 - (b + 32)) with (8192 - 24 - 8 * 1) in Hbs by lia. replace (b + 32) with (b + 24 + 8 * 1) in Hbs by lia. exact Hbs.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
