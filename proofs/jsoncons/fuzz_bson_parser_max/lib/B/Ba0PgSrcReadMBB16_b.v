(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PgSrcKitA_b PnASrcRead1_b PnASrcReadK_b PnASrcReadP_b Ba0PgSrcReadK16_b Ba0PgSrcReadC16_b Ba0PgSrcReadMB16_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmParStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcReadK_b PnASrcRead1_b PnASrcReadP_b Ba0_code_raf314_af318_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PnRunA_b PmAUarK_b PmAUar_b PnAReadCsK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].


Module PGSRDMBB16.
Abbreviation RSEGS := PGSRDK16.RSEGS.
Abbreviation mem := (word -> option byte).
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).

Definition vxC (V : nat -> Z) (R : bvmap 5 word) : nat -> Z := fun i =>
  match i with
  | 60%nat => bv_unsigned (getr R (reg 24)) | 61%nat => bv_unsigned (getr R (reg 1)) | 62%nat => bv_unsigned (getr R (reg 5))
  | 63%nat => bv_unsigned (getr R (reg 6)) | 64%nat => bv_unsigned (getr R (reg 7)) | 65%nat => bv_unsigned (getr R (reg 12))
  | 66%nat => bv_unsigned (getr R (reg 13)) | 67%nat => bv_unsigned (getr R (reg 14)) | 68%nat => bv_unsigned (getr R (reg 15))
  | 69%nat => bv_unsigned (getr R (reg 16)) | 70%nat => bv_unsigned (getr R (reg 17)) | 71%nat => bv_unsigned (getr R (reg 28))
  | 72%nat => bv_unsigned (getr R (reg 29)) | 73%nat => bv_unsigned (getr R (reg 30)) | 74%nat => bv_unsigned (getr R (reg 31))
  | _ => V i
  end.

Section Bne.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "SM" in destruct PP as (H & PP) end.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Lemma srd_bne_ok : PGSA.fill_buffer_specG RSEGS PMA.AD L ar HI PNRA.FCB -> PGSRDK16.srd_fill_ret_T L ar HI 16 -> PGSRDMB16.srd_bne_T L ar HI 16.
Proof.
  intros FB FR. unfold PGSRDMB16.srd_bne_T.
  intros O R M model K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst pb kb CTX R11 R12
         F fl LK2 M2 model2 G fxc Rc Mc modelc LKc Ac V BD XV2 XV36 XV37 XV38 XV50 XV51 XVS XR3 XR4
         len1 ST BX XV39 XV34 XV35 XV45 XOW XIS XBASE XL1 XLK XLK' XDEF.
  pose proof CTX as CTX0. pose proof G as G0. pose proof BD as BD0.
  destruct CTX as (OK & HH & AM & K0 & ENT & FRM & FRS & OFR & A10 & S32 & ARGS & WX & PA & IA & BASE & INCS & KONT).
  set (src := PM.SRC qc de rem) in *. set (sm := PM.STRM g eg sst) in *.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  destruct ARGS as (p & k & A11 & A12 & Hk & DST). destruct WX as (p' & k' & A11' & A12' & Hp' & Hk' & ->).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  rewrite L5SAR.r11 in A11, A11'. rewrite L5SAR.r12 in A12, A12'. unfold PM.CHUNK in Hk.
  change (PMSPA.pm_scr 4) with 20480 in *. pose proof RAok as (Hr1 & Hr2).
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (PGSA.oo_lay _ _ _ _ _ _ OK) as (LY1 & LY2 & LY3 & LY4 & LY5 & O8 & I8 & LY6 & LYD).
  pose proof (PGSA.oo_src _ _ _ _ _ _ OK M src OB PA) as (PSRC & PNI & SDEF0).
  set (os := PGS.ow_os O) in *. set (ois := PGS.ow_ois O) in *. set (lo := PGS.ow_lo O) in *. set (hi := PGS.ow_hi O) in *.
  set (LB := PM.src_own src ++ OB ++ LBX) in *.
  assert (AO : PMSPA.aobjA FF os 296) by (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| exact LY1| exact LY2]).
  assert (AOI : PMSPA.aobjA FF ois 272) by (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| exact LY3| exact LY4]).
  pose proof (PGSKA.src_visG L ar C HI LY HIok LB FF LK cr Aw M model os _ _ src sp 20480 HH AO O8 PSRC PNI ASTK)
    as ((O1 & _ & OBIG) & OZ & OW & OCE & OAV & _ & OFS1 & OFS2).
  pose proof (PGSKA.iss_visG L ar C HI LY HIok LB FF LK cr Aw M model ois str sm sp 20480 HH AOI I8 IA ASTK)
    as ((I1 & _ & IBIG) & IZ & IW & ICE & IAV & _).
  pose proof (PMASK.mach_vis L ar C HI LY HIok LB FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok LB FF LK cr Aw M model sp 20480 80 HH ASTK ltac:(lia)) as (SL80 & SH80 & V3).
  pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY LB FF LK cr Aw M model 0x132c30 1 HH ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT1.
  pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY LB FF LK cr Aw M model 0x132b98 1 HH ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as VT2.
  cbn in VT1, VT2.
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & _).
  pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  pose proof OFR as (ff & Hff & FLO & FHI). destruct (WF _ Hff) as (FB1 & FB2 & _).
  unfold src, sm in *. clear src sm.
  cbn [PM.sr_qc PM.sr_de PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st] in *.
  pose proof PSRC as PSRC0.
  destruct PSRC as (S240 & S248 & SD256 & S264 & S272 & S280 & S288 & G1 & G2 & G3 & G16 & DCH & ACH & ACC240).
  cbn [PM.sr_qc PM.sr_de PM.sr_rem] in *. unfold PM.CHUNK in *.
  pose proof IA as (H0i & _ & _ & H16i & _ & _ & _ & _ & _ & _ & _ & _ & IOSB & _ & _).
  destruct IOSB as (I0 & I32 & I36 & I40 & _ & _ & _ & _ & IST).
  cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_iss pa_vp_strbuf pa_vp_iss_ios PMA.AD ADDR_A] in *.
  replace (ois + 120 + 32) with (ois + 152) in I32 by lia. replace (ois + 120 + 36) with (ois + 156) in I36 by lia.
  replace (ois + 120 + 40) with (ois + 160) in I40 by lia.
  assert (SOWN : incl (PM.vs_own str) LB) by (unfold LB; intros x Hx; apply in_or_app; right; apply in_or_app; right; exact (INCS x Hx)).
  assert (QIN : In (qc, 16384) LB) by (unfold LB, PM.src_own; cbn; left; reflexivity).
  assert (OBIN : forall B m, In (B, m) OB -> In (B, m) LB) by (intros B m Hin; unfold LB, PM.src_own; cbn; right; apply in_or_app; left; exact Hin).
  assert (ND : NoDup (map fst LB)) by exact (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH).
  destruct (WB _ QIN) as ((Q0 & QI & Q16 & _ & Q4 & QAPP) & _). cbn [fst snd] in Q0, QI, Q16, Q4, QAPP.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in QI.
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in QAPP, FSAPP.
  set (MV := mrestrict (ahid Aw model) M) in *.
  assert (STb : forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> In (q1, c1) LB).
  { intros c1 n1 q1 E. apply SOWN. rewrite E. cbn. left. reflexivity. }
  assert (STbX : forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> In (q1, c1) LBX).
  { intros c1 n1 q1 E. apply INCS. rewrite E. cbn. left. reflexivity. }
  assert (DF : 0 <= p /\ p + k <= 2 ^ 47 /\ L5.defined M p k /\ aacc M p k /\ app_rng ar p k
     /\ (forall a, p <= a < p + k -> in_block LB a \/ in_fframe FF a)
     /\ (forall a, p <= a < p + k -> ~ (sp - 20480 <= a < sp) /\ ~ (ois <= a < ois + 272) /\ ~ (os <= a < os + 296)
           /\ ~ (qc <= a < qc + 16384) /\ (forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> ~ (q1 <= a < q1 + c1))
           /\ ~ (65536 <= a < 6897664))
     /\ (p + k <= BIGSHADOW_LO \/ BIGSHADOW_HI <= p)
     /\ (k = 16384 -> PGS.in_blk OB p k)
     /\ (PMSPA.aobjA FF p k \/ exists q m, In (q, m) LB /\ q <= p /\ p + k <= q + m)
     /\ (p + k <= qc \/ qc + 16384 <= p)
     /\ (((p + k <= lo \/ hi <= p) /\ (forall B m, In (B, m) OB -> p + k <= B \/ B + m <= p)) \/ PGS.ow_win O M (PM.SRC qc de rem) OB p k)).
  { destruct FSAPP as (FSA0 & FSAs & FSA47). destruct QAPP as (QA0 & QAs & QA47).
    assert (OBJ : forall (APo : p + k <= os \/ os + 296 <= p) (APi : p + k <= ois \/ ois + 272 <= p),
      PMSPA.aobjA FF p k -> L5.defined M p k -> aacc M p k -> k < 16384 ->
      (((p + k <= lo \/ hi <= p) /\ (forall B m, In (B, m) OB -> p + k <= B \/ B + m <= p)) \/ PGS.ow_win O M (PM.SRC qc de rem) OB p k) ->
      0 <= p /\ p + k <= 2 ^ 47 /\ L5.defined M p k /\ aacc M p k /\ app_rng ar p k
     /\ (forall a, p <= a < p + k -> in_block LB a \/ in_fframe FF a)
     /\ (forall a, p <= a < p + k -> ~ (sp - 20480 <= a < sp) /\ ~ (ois <= a < ois + 272) /\ ~ (os <= a < os + 296)
           /\ ~ (qc <= a < qc + 16384) /\ (forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> ~ (q1 <= a < q1 + c1))
           /\ ~ (65536 <= a < 6897664))
     /\ (p + k <= BIGSHADOW_LO \/ BIGSHADOW_HI <= p)
     /\ (k = 16384 -> PGS.in_blk OB p k)
     /\ (PMSPA.aobjA FF p k \/ exists q m, In (q, m) LB /\ q <= p /\ p + k <= q + m)
     /\ (p + k <= qc \/ qc + 16384 <= p)
     /\ (((p + k <= lo \/ hi <= p) /\ (forall B m, In (B, m) OB -> p + k <= B \/ B + m <= p)) \/ PGS.ow_win O M (PM.SRC qc de rem) OB p k)).
    { intros APo APi AOD DD AD Hk16 DWX.
      pose proof AOD as (f & Hf & X1 & X2). destruct (WF f Hf) as (Y1 & Y2 & _).
      pose proof (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qc 16384 p k HH QIN AOD) as APQ.
      split; [clear - X1 Y1 FSI; lia|]. split; [clear - X2 Y2 FSCEIL SLO SHI SPT; lia|]. split; [exact DD|]. split; [exact AD|].
      split; [apply (L5SAR.app_rng_fs L ar C HI HIok LB FF LK cr Aw M _ p k HH); clear - X1 X2 Y1 Y2; lia|].
      split; [intros a Ha; right; apply (PMASR1.in_fframe_of_aobjA FF p k a AOD Ha)|].
      split; [|split; [unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct FSAs as [Z|Z]; [left|right]; clear - Z X1 X2 Y1 Y2; lia|
               split; [intros E; exfalso; clear - E Hk16; lia| split; [left; exact AOD| split; [clear - APQ; Lia.lia| exact DWX]]]]].
      intros a Ha. split; [clear - Ha X2 Y2 FSCEIL SLO; lia|]. split; [clear - Ha APi; lia|]. split; [clear - Ha APo; lia|].
      split; [clear - Ha APQ; lia|]. split; [|clear - Ha X1 Y1 FSI; lia].
      intros c1 n1 q1 E; destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q1 c1 p k HH (STb c1 n1 q1 E) AOD) as [Z|Z]; clear - Ha Z; lia. }
    destruct DST as [(AOD & Hk8 & DD & AD & APF)|DW].
    -
      apply OBJ; [clear - APF LY1 LY2; lia| clear - APF LY3 LY4; lia| exact AOD| exact DD| exact AD| clear - Hk8; lia|].
      left. split; [exact APF|]. intros B m Hin.
      destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ B m p k HH (OBIN B m Hin) AOD) as [Z|Z]; clear - Z; lia.
    - destruct (PGSA.oo_win _ _ _ _ _ _ OK M (PM.SRC qc de rem) OB p k PA DW) as (W0 & WD & [(B & m & BIN & WB1 & WB2)|(W1 & W2 & WL1 & WL2 & WL3 & WL4 & WL5)] & WACC).
      +
        pose proof (OBIN B m BIN) as TIN.
        destruct (WB _ TIN) as ((T0 & TI & _ & _ & T4 & TAPP) & _). cbn [fst snd] in T0, TI, T4, TAPP.
        rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in TI. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in TAPP. destruct TAPP as (TA0 & TAs & TA47).
        assert (NQ : B <> qc).
        { intros E. apply (PMASK.fst_neq_appA [(qc, 16384)] (OB ++ LBX) qc 16384 B m); [exact ND| left; reflexivity| apply in_or_app; left; exact BIN| symmetry; exact E]. }
        pose proof (PMASK.blk_apart L ar C HI HIok LB FF LK cr Aw M _ B m qc 16384 HH TIN QIN NQ) as APQ.
        pose proof (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ B m os 296 HH TIN AO) as APP.
        pose proof (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ B m ois 272 HH TIN AOI) as API.
        split; [clear - WB1 T0; lia|]. split; [clear - WB2 T4 SLO SHI SPT; lia|]. split; [exact WD|]. split; [exact WACC|].
        split; [apply (L5SAR.app_rng_block L ar C HI HIok LB FF LK cr Aw M _ B m p k HH TIN); clear - WB1 WB2; lia|].
        split; [intros a Ha; left; apply (PMASR1.in_block_of LB B m a TIN); clear - Ha WB1 WB2; lia|].
        split; [|split; [unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct TAs as [Z|Z]; [left|right]; clear - Z WB1 WB2; lia
                        | split; [intros _; exists B, m; split; [exact BIN|]; split; [exact WB1| exact WB2]|
                          split; [right; exists B, m; split; [exact TIN|]; split; [exact WB1| exact WB2]| split; [clear - APQ WB1 WB2; Lia.lia| right; exact DW]]]]].
        intros a Ha. split; [clear - Ha WB1 WB2 T4 SLO; lia|]. split; [clear - Ha WB1 WB2 API; lia|]. split; [clear - Ha WB1 WB2 APP; lia|].
        split; [clear - Ha WB1 WB2 APQ; lia|]. split; [|clear - Ha WB1 WB2 TI T0; lia].
        intros c1 n1 q1 E.
        assert (NS : B <> q1) by (apply (PMASK.fst_neq_appA ((qc, 16384) :: OB) LBX B m q1 c1); [exact ND| right; exact BIN| exact (STbX c1 n1 q1 E)]).
        destruct (PMASK.blk_apart L ar C HI HIok LB FF LK cr Aw M _ B m q1 c1 HH TIN (STb c1 n1 q1 E) NS) as [Z|Z]; clear - Ha WB1 WB2 Z; lia.
      +
        unfold PM.CHUNK in WL3.
        apply OBJ; [exact WL4| exact WL5| apply (PGSKA.aobjA_sub FF lo hi p k OFR WL1 WL2)| exact WD| exact WACC| exact WL3| right; exact DW]. }
  destruct DF as (DP0 & DP1 & DDP & DAP & DAPP & DCL & DX & DSH & D16K & DLOC & DQA & DWX).
  assert (pk : p' = p /\ k' = k).
  { rewrite A11 in A11'. rewrite A12 in A12'. apply (f_equal bv_unsigned) in A11', A12'.
    rewrite !L5.unsigned_lit in A11', A12' by (clear - Hp' Hk' DP0 DP1 Hk; lia). split; congruence. }
  destruct pk as (-> & ->). clear A11' A12'.
  destruct FSAPP as (FSA0 & FSAs & FSA47). destruct QAPP as (QA0 & QAs & QA47).
  assert (APQO : forall o n, PMSPA.aobjA FF o n -> qc + 16384 <= o \/ o + n <= qc).
  { intros o n AOo. exact (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ qc 16384 o n HH QIN AOo). }
  set (WA := PGS.W_srcG os ois (PM.SRC qc de rem) ++ [(p, k)]).
  assert (OUTWA : forall i, ~ (os + 256 <= i < os + 296) -> ~ (ois + 40 <= i < ois + 48) -> ~ (ois + 152 <= i < ois + 156) ->
                  ~ (qc <= i < qc + 16384) -> ~ (p <= i < p + k) -> L5.outside WA i).
  { intros i N1 N2 N3 N4 N5 r0 Hr. unfold WA, PGS.W_srcG, PGS.W_srcfG in Hr. cbn [PM.sr_qc app] in Hr. unfold L5.in_rng.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; unfold PM.CHUNK; clear - N1 N2 N3 N4 N5; lia. }
  assert (WAPP : PMKA.wapp WA).
  { unfold WA, PGS.W_srcG, PGS.W_srcfG. cbn [PM.sr_qc app]. unfold BIGSHADOW_LO, BIGSHADOW_HI in OBIG, IBIG, DSH.
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - OBIG; Lia.lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - IBIG; Lia.lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - IBIG; Lia.lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI, PM.CHUNK; clear - QAs; Lia.lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - DSH; Lia.lia| apply PMKA.wapp_nil]. }
  assert (OUTIMG : forall a, 65536 <= a < 6897664 -> L5.outside WA a).
  { intros a Ha. apply OUTWA; [clear - Ha O1; lia| clear - Ha I1; lia| clear - Ha I1; lia| clear - Ha QI; lia|].
    intros Y. destruct (DX a Y) as (_ & _ & _ & _ & _ & X6). apply X6. exact Ha. }
  assert (OWA : Forall (fun b => fst b + snd b <= lo \/ hi <= fst b) (PM.src_own (PM.SRC qc de rem) ++ OB)).
  { apply Forall_forall. intros [B m] Hin. cbn [fst snd].
    assert (HB : In (B, m) LB) by (unfold LB; rewrite app_assoc; apply in_or_app; left; exact Hin).
    destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ B m lo (hi - lo) HH HB OFR) as [X|X]; [left; exact X| right; clear - X; lia]. }
  assert (OWB : forall b, In b OB -> fst b + snd b <= PM.sr_qc (PM.SRC qc de rem) \/ PM.sr_qc (PM.SRC qc de rem) + PM.CHUNK <= fst b).
  { intros [B m] Hin. cbn [fst snd PM.sr_qc]. unfold PM.CHUNK.
    assert (NE : B <> qc).
    { intros E. apply (PMASK.fst_neq_appA [(qc, 16384)] (OB ++ LBX) qc 16384 B m); [exact ND| left; reflexivity| apply in_or_app; left; exact Hin| symmetry; exact E]. }
    destruct (PMASK.blk_apart L ar C HI HIok LB FF LK cr Aw M _ B m qc 16384 HH (OBIN B m Hin) QIN NE) as [X|X]; clear - X; lia. }
  assert (OWC : Forall (fun r => ((fst r + snd r <= lo \/ hi <= fst r) /\ (forall B m, In (B, m) OB -> fst r + snd r <= B \/ B + m <= fst r) /\ app_mem (fst r) (snd r))
                              \/ PGS.ow_win O M (PM.SRC qc de rem) OB (fst r) (snd r)) [(p, k)]).
  { constructor; [| constructor]. cbn [fst snd]. destruct DWX as [(DW1 & DW2)|DW]; [left| right; exact DW].
    split; [exact DW1|]. split; [exact DW2|]. unfold app_mem. split; [exact DP0|]. split; [exact DSH| exact DP1]. }
  assert (OWU : forall (M3 : word -> option byte) (de' rem' : Z),
      L5CA.ahpres L ar LB FF sp 20480 WA M M3 ->
      L5.u64_at RSEGS M3 (os + 264) qc -> L5.u64_at RSEGS M3 (os + 272) 16384 ->
      L5.u64_at RSEGS M3 (os + 280) de' -> L5.u64_at RSEGS M3 (os + 288) rem' ->
      qc <= de' -> 0 <= rem' -> de' + rem' <= qc + 16384 ->
      PGS.ow_at O M3 (PM.SRC qc de' rem') OB).
  { intros M3 de' rem' AH C264 C272 C280 C288 Q1' Q2' Q3'. pose proof (proj1 AH) as EK. pose proof (proj2 (proj2 AH)) as DK.
    assert (OUTO : forall i, os <= i < os + 256 -> L5.outside WA i).
    { intros i Hi. apply OUTWA; [clear - Hi; lia| clear - Hi LYD; lia| clear - Hi LYD; lia| destruct (APQO os 296 AO) as [Z|Z]; clear - Hi Z; lia|].
      intros Y. destruct (DX i Y) as (_ & _ & X3 & _). apply X3. clear - Hi; lia. }
    apply (PGSA.oo_upd _ _ _ _ _ _ OK LBX sp 20480 [(p, k)] M M3 (PM.SRC qc de rem) (PM.SRC qc de' rem') OB FF LK Aw cr (vml_of model) OFR PA HH OWA OWB OWC).
    - exact AH.
    - apply (PGSKA.src_fields_updG M M3 os ois (ois + 16) qc de rem de' rem' PSRC0); unfold PM.CHUNK.
      + clear - O1; lia.
      + clear - O1; lia.
      + apply (PMKA.agA_obj L ar LB FF sp 20480 WA M M3 EK WAPP FRB os 256); [apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| clear - LY1; lia| clear - LY2; lia]| exact OUTO].
      + apply (PMKA.agsh_obj L ar LB FF sp 20480 WA M M3 EK WAPP FRB (os + 256) 40). apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| clear - LY1; lia| clear - LY2; lia].
      + apply (PMASK.defined_dk L ar LB FF sp 20480 M M3 (os + 256) 8 DK); [| clear - O1; lia| clear - O1; lia| exact SD256].
        intros i Hi. apply PMASR1.cl_of_bf. right. apply (PMASR1.in_fframe_of_aobjA FF os 296 i AO). clear - Hi; lia.
      + apply (PMASK.agsh_blk L ar LB FF sp 20480 WA M M3 qc 16384 EK WAPP QIN); [clear - Q0; lia| clear - Q4 SLO SHI SPT; lia].
      + apply (PMASK.defined_dk L ar LB FF sp 20480 M M3 qc 16384 DK); [| clear - Q0; lia| clear - Q4 SLO SHI SPT; lia| exact DCH].
        intros i Hi. apply PMASR1.cl_of_bf. left. apply (PMASR1.in_block_of LB qc 16384 i QIN Hi).
      + exact C264. + exact C272. + exact C280. + exact C288. + exact Q1'. + exact Q2'. + exact Q3'.
    - reflexivity. }
  assert (pbk : pb = p /\ kb = k).
  { pose proof ST as STp. unfold PGSRDMB16.srd_stM in STp. pdestr STp.
    rewrite A11 in R11. rewrite A12 in R12. apply (f_equal bv_unsigned) in R11, R12.
    rewrite !L5.unsigned_lit in R11, R12 by (first [clear - DP0 DP1 Hk; lia | rewrite <- XV37; assumption | rewrite <- XV38; assumption]).
    split; congruence. }
  destruct pbk as (pbp & kbk). rewrite pbp in *. rewrite kbk in *. clear pbp kbk.
  unfold PGSRDK16.srd_frame in G. unfold PGSRDK16.srd_body in BD.
  set (MVc := mrestrict (ahid Ac modelc) Mc) in *.
  pose proof ST as ST0. unfold PGSRDMB16.srd_stM in ST. pdestr ST.
  pose proof BX as BX0. unfold PGSRDMB16.srd_bneX in BX. destruct BX as (BX22 & BX288 & BX39 & BX38 & BX3839).
  LeanFeed.pfeed P (PMASRP.asrBne16_conc fxc Rc MVc V) ltac:(assumption).
  destruct P as (fx1 & R1 & M1v & MG1 & _ & AG1 & MS1 & KS1 & B1 & B10 & B11 & B12 & B13 & B21 & B22 & B24 & P280 & P288).
  apply (PGSRDC16.srd_piece L ar C HI LY HIok O R M model K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) [(p, k)] F fl LK2 M2 model2 Mc modelc LKc Ac
           fxc fx1 Rc R1 _ _ M1v (fun a => V 36%nat + 256 <= a < V 36%nat + 256 + 8 \/ V 36%nat + 280 <= a < V 36%nat + 280 + 16) CTX0 G0 BD0 MS1 MG1).
  { intros a Ha N. apply AG1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { intros a Wa. cbn beta in Wa. right; right; left. clear - Wa XV36. lia. }
  intros M1 model1 BI1 HID1 MRT1 MGM1 FR1 VIS1 EK1.
  assert (SV1 : forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> vxC V R1 i = bv_unsigned (getr R (reg i))).
  { intros i Hi. rewrite <- (XVS i Hi). cbn in Hi. repeat destruct Hi as [<-|Hi]; first [reflexivity | destruct Hi]. }
  assert (X3' : getr R1 (reg 3) = getr R (reg 3)) by (rewrite KS1 by inl; exact XR3).
  assert (X4' : getr R1 (reg 4) = getr R (reg 4)) by (rewrite KS1 by inl; exact XR4).
  match goal with
  | H2 : _ <= V 2%nat <= _, H36 : _ <= V 36%nat <= _, H50 : _ <= V 50%nat <= _, H51 : 4096 <= V 51%nat <= _ |- _ =>
      pose proof (conj H2 (conj H36 (conj H50 H51))) as KB
  end.
  assert (STC1 : PGSRDK16.srd_stC (vxC V R1) R1 M1v).
  { unfold PGSRDK16.srd_stC, vxC. cbn beta iota.
    PGSRDC16.sweep ltac:(first [assumption | exact (bv_unsigned_in_range _ _) | (symmetry; apply Z_to_bv_bv_unsigned)
                      | (rewrite KS1 by inl; assumption) | (eapply L5.writable_grows; [exact MG1| assumption])
                      | (eapply L5.defined_grows; [exact MG1| assumption]) | (clear - BX38; lia) | (clear - BX39; lia) | PGSRDC16.carry MVc AG1 KB]). }
  assert (STC1' : PGSRDK16.srd_stC (vxC V R1) R1 (mrestrict (ahid Ac model1) M1)) by (rewrite HID1, MRT1; exact STC1).
  assert (V61 : vxC V R1 61%nat = bv_unsigned (getr R1 (reg 1))) by reflexivity.
  rewrite B1, L5.unsigned_lit in V61 by lia.
  assert (V65 : vxC V R1 65%nat = bv_unsigned (getr R1 (reg 12))) by reflexivity.
  rewrite B12, L5.unsigned_lit in V65 by lia.
  assert (V39' : vxC V R1 39%nat = len1) by exact XV39.
  assert (V34' : vxC V R1 34%nat = qc) by exact XV34.
  assert (R10' : getr R1 (reg 10) = Z_to_bv 64 (PGS.ow_os O)) by (rewrite B10, XV36; reflexivity).
  assert (R11' : getr R1 (reg 11) = Z_to_bv 64 qc) by (rewrite B11, XV34; reflexivity).
  pose proof (PGSA.oo_src _ _ _ _ _ _ OK Mc _ OB XOW) as (PSRC1 & _ & _).
  pose proof PSRC1 as (_ & _ & _ & F264 & F272 & _). cbn [PM.sr_qc] in F264.
  assert (U264 : L5.u64_at RSEGS M1 (os + 264) qc).
  { apply (L5C.u64_at_agree RSEGS Mc M1); [| clear - O1; lia| clear - O1; lia| exact F264].
    intros i Hi. apply FR1; [clear - Hi O1; lia|]. cbn beta. clear - Hi XV36. lia. }
  assert (U272 : L5.u64_at RSEGS M1 (os + 272) PM.CHUNK).
  { apply (L5C.u64_at_agree RSEGS Mc M1); [| clear - O1; lia| clear - O1; lia| exact F272].
    intros i Hi. apply FR1; [clear - Hi O1; lia|]. cbn beta. clear - Hi XV36. lia. }
  assert (VO1 : forall i, V 36%nat + 280 <= i < V 36%nat + 296 -> M1 (Z_to_bv 64 i) = M1v (Z_to_bv 64 i)).
  { intros i Hi. apply VIS1.
    apply (PGSRDC16.srd_vis L ar C HI LY HIok O R M model K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) [(p, k)] F fl LK2 M2 model2 Mc modelc LKc Ac i CTX0 G0 BD0).
    right; right; right; left. clear - Hi XV36. lia. }
  assert (U280 : L5.u64_at RSEGS M1 (os + 280) qc).
  { rewrite <- XV34. replace (os + 280) with (V 36%nat + 280) by (clear - XV36; lia).
    apply (L5C.u64_at_agree RSEGS M1v M1); [| PGSRDC16.sd KB| PGSRDC16.sd KB| exact P280]. intros i Hi. apply VO1. clear - Hi. lia. }
  assert (U288 : L5.u64_at RSEGS M1 (os + 288) 0).
  { replace (os + 288) with (V 36%nat + 288) by (clear - XV36; lia).
    apply (L5C.u64_at_agree RSEGS M1v M1); [| PGSRDC16.sd KB| PGSRDC16.sd KB| exact P288]. intros i Hi. apply VO1. clear - Hi. lia. }
  pose proof BD as BD'. unfold PMAUK.binv in BD'. destruct BD' as (HHc & AMc & MRTc & INCAc & INCLc & ASTKc & EKc & DKc & OWNc & DSHc).
  assert (EKm : L5SAR.ek L ar LB FF sp (PMSPA.pm_scr 4) WA M M1).
  { apply (L5SAR.ek_trans L ar LB FF sp _ WA M Mc M1 EKc). apply (L5SAR.ek_W L ar LB FF sp _ WA [(PGS.ow_os O + 256, 40)] Mc M1 EK1).
    intros a OA r0 [<-|[]] Hr. apply (OA (os + 256, 40)); [unfold WA, PGS.W_srcG, PGS.W_srcfG; cbn [app]; left; reflexivity| exact Hr]. }
  assert (AH1 : L5CA.ahpres L ar LB FF sp (PMSPA.pm_scr 4) WA M M1).
  { apply (L5SAR.ahpres_of L ar LB FF sp _ WA M M1 EKm).
    - pose proof (L5SAR.astk_grows ar Mc M1 sp _ ASTKc MGM1) as (_ & _ & _ & _ & SD1 & _). exact SD1.
    - exact (L5SAR.dk_trans L ar LB FF sp _ M Mc M1 DKc (L5SAR.dk_grows L ar LB FF sp _ Mc M1 MGM1)). }
  assert (OW1 : PGS.ow_at O M1 (PM.SRC qc qc 0) OB).
  { apply (OWU M1 qc 0 AH1 U264 U272 U280 U288); unfold PM.CHUNK; lia. }
  assert (WOS : PMKA.wapp [(PGS.ow_os O + 256, 40)]).
  { apply PMKA.wapp_cons; [cbn [fst snd]; clear - OBIG; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia| apply PMKA.wapp_nil]. }
  assert (ISS1 : PM.iss_at RSEGS PMA.AD PMSPA.accA M1 ois str (PM.STRM g eg sst)).
  { apply (PMFA.iss_at_agreeA RSEGS PMA.AD Mc M1 ois str _); [clear - I1; lia| clear - I1; lia| split| | exact XIS].
    - intros i Hi. apply EK1. split; [clear - Hi I1; lia|].
      split; [apply PMASR1.cl_of_bf; right; exact (PMASR1.in_fframe_of_aobjA FF ois 272 i AOI Hi)|].
      intros r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Hi LYD. lia.
    - exact (PMKA.agsh_obj L ar LB FF sp (PMSPA.pm_scr 4) [(PGS.ow_os O + 256, 40)] Mc M1 EK1 WOS FRB ois 272 AOI).
    - intros c1 n1 q1 Es. pose proof (STb c1 n1 q1 Es) as TIN. destruct (WB _ TIN) as ((T0 & _ & _ & _ & T4 & _) & _).
      cbn [fst snd] in T0, T4. split.
      + intros i Hi. apply EK1. split; [clear - Hi T0 T4 SLO SHI SPT; lia|].
        split; [apply PMASR1.cl_of_bf; left; exact (PMASR1.in_block_of LB q1 c1 i TIN Hi)|].
        intros r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd].
        destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q1 c1 os 296 HH TIN AO) as [Z|Z]; clear - Hi Z; lia.
      + apply (PMASK.agsh_blk L ar LB FF sp (PMSPA.pm_scr 4) [(PGS.ow_os O + 256, 40)] Mc M1 q1 c1 EK1 WOS TIN); clear - T0 T4 SLO SHI SPT; lia. }
  assert (BASE1 : PMSTA.base_okA RSEGS PMA.AD M1).
  { apply (PMASK.base_keep L ar C LY LB FF sp _ [(PGS.ow_os O + 256, 40)] Mc M1 EK1); [| exact XBASE].
    intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Ha O1. lia. }
  assert (DEF1 : L5.defined M1 p len1) by (eapply L5.defined_grows; [exact MGM1| exact XDEF]).
  assert (KL1 : k - len1 <= 16383) by (rewrite <- XV38, <- XV39; clear - BX3839; lia).
  exact (PGSRDMB16.srd_fill_call L ar C HI LY HIok IL ICok ILY FB FR O R M model K OB LBX FF LK Aw cr sp r str [(p, k)] qc de rem g eg sst p k CTX0 R11 R12 F fl LK2 M2 model2 G0
           fx1 R1 M1 model1 LKc Ac (vxC V R1) BI1 XV2 XV36 XV37 XV38 XV50 XV51 SV1 X3' X4' len1 STC1' V39' V34' V61 V65 R10' R11'
           OW1 ISS1 BASE1 XL1 XLK KL1 DEF1).
Qed.
End Bne.
End PGSRDMBB16.
