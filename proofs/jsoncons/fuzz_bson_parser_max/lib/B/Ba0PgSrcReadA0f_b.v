(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PgSrcKitA_b PnASrcRead1_b PnASrcReadK_b PnASrcReadP_b Ba0PgSrcReadK_b Ba0PgSrcReadC_b Ba0PgSrcReadMB_b Ba0PgSrcReadCD_b.
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

Module PGSRDA0F.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := PGSRDK.RSEGS.
Abbreviation mem := (word -> option byte).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom PGSRDK.RSEGS)) (only parsing).
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "S" in destruct PP as (H & PP) end.

Definition vxA (V : nat -> Z) (R : bvmap 5 word) : nat -> Z := fun i =>
  match i with
  | 39%nat => 0 | 60%nat => bv_unsigned (getr R (reg 24))
  | 61%nat => bv_unsigned (getr R (reg 1)) | 62%nat => bv_unsigned (getr R (reg 5)) | 63%nat => bv_unsigned (getr R (reg 6))
  | 64%nat => bv_unsigned (getr R (reg 7)) | 65%nat => bv_unsigned (getr R (reg 12)) | 66%nat => bv_unsigned (getr R (reg 13))
  | 67%nat => bv_unsigned (getr R (reg 14)) | 68%nat => bv_unsigned (getr R (reg 15)) | 69%nat => bv_unsigned (getr R (reg 16))
  | 70%nat => bv_unsigned (getr R (reg 17)) | 71%nat => bv_unsigned (getr R (reg 28)) | 72%nat => bv_unsigned (getr R (reg 29))
  | 73%nat => bv_unsigned (getr R (reg 30)) | 74%nat => bv_unsigned (getr R (reg 31))
  | _ => V i
  end.

Section A0f.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Lemma srd_a0f_ok : PGSA.fill_buffer_specG RSEGS PMA.AD L ar HI PNRA.FCB -> PGSRDK.srd_a0_T L ar HI 0 PGSRDK.srd_pthF.
Proof using LY HIok ICok ILY.
  intros FB. unfold PGSRDK.srd_a0_T.
  intros O R M model K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst pb kb CTX R11 R12
         F fl LK2 M2 model2 G fxc Rc Mc modelc LKc Ac V BD XV2 XV36 XV37 XV38 XV50 XV51 XVS XR3 XR4
         XV34 XV35 XV45 XIA STA PTH.
  pose proof CTX as CTX0.
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
  { pose proof STA as ST'. unfold PGSRDK.srd_stA in ST'. pdestr ST'.
    rewrite A11 in R11. rewrite A12 in R12. apply (f_equal bv_unsigned) in R11, R12.
    rewrite !L5.unsigned_lit in R11, R12 by (first [clear - DP0 DP1 Hk; lia | rewrite <- XV37; assumption | rewrite <- XV38; assumption]).
    split; congruence. }
  destruct pbk as (pbp & kbk). rewrite pbp in *. rewrite kbk in *. clear pbp kbk.
  destruct PTH as (REM0 & PA0F). unfold PGSRDK.srd_pA0f in PA0F. destruct PA0F as (P288 & PK).
  pose proof G as G'. unfold PGSRDK.srd_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  set (MVc := mrestrict (ahid Ac modelc) Mc) in *.
  pose proof STA as STc. unfold PGSRDK.srd_stA in STc. pdestr STc.
  match goal with
  | H2 : _ <= V 2%nat <= _, H36 : _ <= V 36%nat <= _, H50 : _ <= V 50%nat <= _, H51 : 4096 <= V 51%nat <= _ |- _ =>
      pose proof (conj H2 (conj H36 (conj H50 H51))) as KB
  end.
  pose proof (PMASRP.asrA0f_conc fxc Rc MVc V) as P0.
  PGSRDCD.feed P0 ltac:(idtac; PGSRDCD.dsp ltac:(idtac; clear - KB PK; unfold PM.CHUNK in *; lia) ltac:(idtac; fail)).
  destruct P0 as (fx1 & R1 & M1v & MG1 & AG1w & AG1 & MS1 & KS1 & P1).
  assert (F4 : 4 * V 50%nat = F / 8) by (clear - XV50; lia).
  apply (PGSRDC.srd_piece L ar C HI LY HIok O R M model K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) _ F fl LK2 M2 model2 Mc modelc LKc Ac
           fxc fx1 Rc R1 _ _ M1v
           (fun a => (V 36%nat + 280 <= a < V 36%nat + 280 + 8) \/ (V 2%nat - 152 <= a < V 2%nat - 152 + 16) \/ (V 2%nat - 112 <= a < V 2%nat - 112 + 8)
                     \/ (32 * V 50%nat + 0 <= a < 32 * V 50%nat + 0 + 24) \/ (32 * V 50%nat + 32 <= a < 32 * V 50%nat + 32 + 8)
                     \/ (4 * V 50%nat + 2147450880 <= a < 4 * V 50%nat + 2147450880 + 12))
           CTX0 G BD MS1 MG1).
  { intros a Ha NW. apply AG1; [exact Ha| ..]; intros X; apply NW; clear - X; cbn beta; tauto. }
  { intros a Wa. cbn beta in Wa. rewrite XV36 in Wa. rewrite XV2 in Wa. rewrite F4 in Wa. rewrite XV50 in Wa.
    unfold SB. destruct Wa as [Y|[Y|[Y|[Y|[Y|Y]]]]];
      [right; right; left| right; right; right| right; right; right| left| left| right; left]; clear - Y; lia. }
  intros M1 model1 BI1 HID1 MRT1 MGM1 FR1 VIS1 EK1.
  pdestr P1.
  pose proof BI1 as BI1'. unfold PGSRDK.srd_body, PMAUK.binv in BI1'.
  destruct BI1' as (HH1 & AM1 & MRT1b & INCA1 & INCL1 & ASTK1 & EK1b & DK1 & OWN1 & DSH1).
  assert (VIS : forall i, (sp - 160 <= i < sp) \/ (F <= i < F + 128) \/ (F / 8 + SB <= i < F / 8 + SB + 16) \/ (os <= i < os + 296)
                  \/ ((os + 8) / 8 + SB <= i < (os + 8) / 8 + SB + 36) -> M1 (Z_to_bv 64 i) = M1v (Z_to_bv 64 i)).
  { intros i Hi. apply VIS1. rewrite <- HID1.
    exact (PGSRDC.srd_vis L ar C HI LY HIok O R M model K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) _ F fl LK2 M2 model2 M1 model1 LKc Ac i CTX0 G BI1 Hi). }
  assert (OWNV : PNACSK.own sp R M1v).
  { apply (PNACSK.own_agree sp R M1 M1v); [clear - SLO SPT; lia| clear - SHI SPT; lia| exact OWN1|].
    intros a Ha. unfold PNACSK.ocell in Ha. symmetry. apply VIS. left. clear - Ha; lia. }
  destruct OWNV as (W1 & W8 & W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27).
  assert (SV1 : L5.u64_at RSEGS M1v (V 2%nat - 8) (V 1%nat)) by (rewrite XV2, (XVS 1%nat) by inl; replace (sp - 0 - 8) with (sp - 8) by (clear; lia); exact W1).
  assert (SV8 : L5.u64_at RSEGS M1v (V 2%nat - 16) (V 8%nat)) by (rewrite XV2, (XVS 8%nat) by inl; replace (sp - 0 - 16) with (sp - 16) by (clear; lia); exact W8).
  assert (SV9 : L5.u64_at RSEGS M1v (V 2%nat - 24) (V 9%nat)) by (rewrite XV2, (XVS 9%nat) by inl; replace (sp - 0 - 24) with (sp - 24) by (clear; lia); exact W9).
  assert (SV18 : L5.u64_at RSEGS M1v (V 2%nat - 32) (V 18%nat)) by (rewrite XV2, (XVS 18%nat) by inl; replace (sp - 0 - 32) with (sp - 32) by (clear; lia); exact W18).
  assert (SV19 : L5.u64_at RSEGS M1v (V 2%nat - 40) (V 19%nat)) by (rewrite XV2, (XVS 19%nat) by inl; replace (sp - 0 - 40) with (sp - 40) by (clear; lia); exact W19).
  assert (SV20 : L5.u64_at RSEGS M1v (V 2%nat - 48) (V 20%nat)) by (rewrite XV2, (XVS 20%nat) by inl; replace (sp - 0 - 48) with (sp - 48) by (clear; lia); exact W20).
  assert (SV21 : L5.u64_at RSEGS M1v (V 2%nat - 56) (V 21%nat)) by (rewrite XV2, (XVS 21%nat) by inl; replace (sp - 0 - 56) with (sp - 56) by (clear; lia); exact W21).
  assert (SV22 : L5.u64_at RSEGS M1v (V 2%nat - 64) (V 22%nat)) by (rewrite XV2, (XVS 22%nat) by inl; replace (sp - 0 - 64) with (sp - 64) by (clear; lia); exact W22).
  assert (SV23 : L5.u64_at RSEGS M1v (V 2%nat - 72) (V 23%nat)) by (rewrite XV2, (XVS 23%nat) by inl; replace (sp - 0 - 72) with (sp - 72) by (clear; lia); exact W23).
  assert (SV24 : L5.u64_at RSEGS M1v (V 2%nat - 80) (V 24%nat)) by (rewrite XV2, (XVS 24%nat) by inl; replace (sp - 0 - 80) with (sp - 80) by (clear; lia); exact W24).
  assert (SV25 : L5.u64_at RSEGS M1v (V 2%nat - 88) (V 25%nat)) by (rewrite XV2, (XVS 25%nat) by inl; replace (sp - 0 - 88) with (sp - 88) by (clear; lia); exact W25).
  assert (SV26 : L5.u64_at RSEGS M1v (V 2%nat - 96) (V 26%nat)) by (rewrite XV2, (XVS 26%nat) by inl; replace (sp - 0 - 96) with (sp - 96) by (clear; lia); exact W26).
  assert (SV27 : L5.u64_at RSEGS M1v (V 2%nat - 104) (V 27%nat)) by (rewrite XV2, (XVS 27%nat) by inl; replace (sp - 0 - 104) with (sp - 104) by (clear; lia); exact W27).
  assert (VR18 : 0 <= V 18%nat < 2 ^ 64) by (rewrite (XVS 18%nat) by inl; apply bv_unsigned_in_range).
  assert (VR20 : 0 <= V 20%nat < 2 ^ 64) by (rewrite (XVS 20%nat) by inl; apply bv_unsigned_in_range).
  assert (VR21 : 0 <= V 21%nat < 2 ^ 64) by (rewrite (XVS 21%nat) by inl; apply bv_unsigned_in_range).
  assert (VR23 : 0 <= V 23%nat < 2 ^ 64) by (rewrite (XVS 23%nat) by inl; apply bv_unsigned_in_range).
  assert (VR24 : 0 <= V 24%nat < 2 ^ 64) by (rewrite (XVS 24%nat) by inl; apply bv_unsigned_in_range).
  assert (VR25 : 0 <= V 25%nat < 2 ^ 64) by (rewrite (XVS 25%nat) by inl; apply bv_unsigned_in_range).
  assert (VR26 : 0 <= V 26%nat < 2 ^ 64) by (rewrite (XVS 26%nat) by inl; apply bv_unsigned_in_range).
  assert (STC1 : PGSRDK.srd_stC (vxA V R1) R1 M1v).
  { unfold PGSRDK.srd_stC, vxA. cbn beta iota.
    PGSRDC.sweep ltac:(idtac; PGSRDCD.dsp ltac:(idtac; first [clear; lia | clear - KB PK; unfold PM.CHUNK in *; lia])
                      ltac:(idtac; first [ (rewrite KS1 by inl; PGSRDCD.sfind)
                                         | (eapply L5.writable_grows; [exact MG1| PGSRDCD.sfind])
                                         | (eapply L5.defined_grows; [exact MG1| PGSRDCD.sfind])
                                         | PGSRDCD.carry_with MVc AG1 KB ltac:(idtac; PGSRDCD.sfind) ])). }
  assert (STC1' : PGSRDK.srd_stC (vxA V R1) R1 (mrestrict (ahid Ac model1) M1)) by (rewrite HID1, MRT1; exact STC1).
  assert (CV : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha1 Ha2 X. apply (L5C.u64_at_agree RSEGS M1v M1 a v); [| clear - Ha1 O1; lia| clear - Ha2 O1; lia| exact X].
    intros i Hi. apply VIS. right; right; right; left. clear - Hi Ha1 Ha2; lia. }
  assert (C264 : L5.u64_at RSEGS M1 (os + 264) qc).
  { apply CV; [clear; lia| clear; lia|]. rewrite <- XV34, <- XV36. PGSRDCD.carry_with MVc AG1 KB ltac:(idtac; PGSRDCD.sfind). }
  assert (C272 : L5.u64_at RSEGS M1 (os + 272) PM.CHUNK).
  { apply CV; [clear; lia| clear; lia|]. rewrite <- XV36. unfold PM.CHUNK. PGSRDCD.carry_with MVc AG1 KB ltac:(idtac; PGSRDCD.sfind). }
  assert (C280 : L5.u64_at RSEGS M1 (os + 280) qc).
  { apply CV; [clear; lia| clear; lia|]. rewrite <- XV34, <- XV36. PGSRDCD.sfind. }
  assert (C288 : L5.u64_at RSEGS M1 (os + 288) 0).
  { apply CV; [clear; lia| clear; lia|]. rewrite <- XV36. PGSRDCD.carry_with MVc AG1 KB ltac:(idtac; PGSRDCD.sfind). }
  pose proof ASTK1 as (_ & _ & _ & _ & ADEF1 & _).
  assert (AH1 : L5CA.ahpres L ar LB FF sp 20480 WA M M1) by exact (conj EK1b (conj ADEF1 DK1)).
  assert (PA1 : PGS.ow_at O M1 (PM.SRC qc qc 0) OB).
  { apply (OWU M1 qc 0 AH1 C264); [exact C272| exact C280| exact C288| clear; lia| clear; lia| unfold PM.CHUNK; clear; lia]. }
  assert (WOS : PMKA.wapp [(os + 256, 40)]).
  { apply PMKA.wapp_cons; [cbn [fst snd]; clear - OBIG; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia| apply PMKA.wapp_nil]. }
  assert (ISS1 : PM.iss_at RSEGS PMA.AD PMSPA.accA M1 ois str (PM.STRM g eg sst)).
  { apply (PMFA.iss_at_agreeA RSEGS PMA.AD Mc M1 ois str (PM.STRM g eg sst)); [clear - I1; lia| clear - I1; lia| split| | exact XIA].
    - intros i Hi. apply EK1. split; [clear - Hi I1; lia|].
      split; [apply PMASR1.cl_of_bf; right; exact (PMASR1.in_fframe_of_aobjA FF ois 272 i AOI Hi)|].
      intros r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Hi LYD. lia.
    - exact (PMKA.agsh_obj L ar LB FF sp 20480 [(os + 256, 40)] Mc M1 EK1 WOS FRB ois 272 AOI).
    - intros c1 n1 q1 Es. pose proof (STb c1 n1 q1 Es) as TIN. destruct (WB _ TIN) as ((T0 & _ & _ & _ & T4 & _) & _).
      cbn [fst snd] in T0, T4. split.
      + intros i Hi. apply EK1. split; [clear - Hi T0 T4 SLO SHI SPT; lia|].
        split; [apply PMASR1.cl_of_bf; left; exact (PMASR1.in_block_of LB q1 c1 i TIN Hi)|].
        intros r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd].
        destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M _ q1 c1 os 296 HH TIN AO) as [Z|Z]; clear - Hi Z; lia.
      + apply (PMASK.agsh_blk L ar LB FF sp 20480 [(os + 256, 40)] Mc M1 q1 c1 EK1 WOS TIN); clear - T0 T4 SLO SHI SPT; lia. }
  assert (OUTIMG2 : forall a, 65536 <= a < 6905856 -> L5.outside WA a).
  { intros a Ha. apply OUTWA; [clear - Ha O1 OFS1 FSI; lia| clear - Ha I1; lia| clear - Ha I1; lia| clear - Ha QI; lia|].
    intros Y. destruct (DCL a Y) as [HB|HF].
    - destruct HB as ((B & m) & HBin & HBr). cbn [fst snd] in HBr. destruct (WB _ HBin) as ((T0 & TI & _) & _). cbn [fst snd] in T0, TI.
      rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in TI. clear - Ha HBr TI; lia.
    - destruct HF as (f & Hf & Hr & _). destruct (WF f Hf) as (Wf1 & _). clear - Ha Hr Wf1 FSI; lia. }
  assert (BASE1 : PMSTA.base_okA RSEGS PMA.AD M1) by exact (PMASK.base_keep L ar C LY LB FF sp 20480 WA M M1 EK1b OUTIMG2 BASE).
  assert (SVX : forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> vxA V R1 i = bv_unsigned (getr R (reg i))).
  { intros i Hi. rewrite <- (XVS i Hi). cbn in Hi. repeat destruct Hi as [<-|Hi]; first [reflexivity | destruct Hi]. }
  assert (X3' : getr R1 (reg 3) = getr R (reg 3)) by (rewrite KS1 by inl; exact XR3).
  assert (X4' : getr R1 (reg 4) = getr R (reg 4)) by (rewrite KS1 by inl; exact XR4).
  assert (V61e : vxA V R1 61%nat = 0xaef9c).
  { cbn. match goal with H : getr R1 (reg 1) = _ |- _ => rewrite H end. apply L5.unsigned_lit. clear; lia. }
  assert (V65e : vxA V R1 65%nat = PM.CHUNK).
  { cbn. match goal with H : getr R1 (reg 12) = _ |- _ => rewrite H end. unfold PM.CHUNK. apply L5.unsigned_lit. clear; lia. }
  assert (X10 : getr R1 (reg 10) = Z_to_bv 64 (PGS.ow_os O)).
  { match goal with H : getr R1 (reg 10) = _ |- _ => rewrite H end. rewrite XV36. reflexivity. }
  assert (X11 : getr R1 (reg 11) = Z_to_bv 64 qc).
  { match goal with H : getr R1 (reg 11) = _ |- _ => rewrite H end. rewrite XV34. reflexivity. }
  assert (DEF0 : L5.defined M1 p 0) by (intros i Hi; exfalso; clear - Hi; lia).
  apply (PGSRDMB.srd_fill_call L ar C HI LY HIok IL ICok ILY FB (PGSRDCD.srd_fill_ret_ok L ar C HI LY HIok IL ICok ILY (PGSRDK.srd_exit_ok L ar C HI LY HIok IL ICok ILY))
           O R M model K OB LBX FF LK Aw cr sp r str _ qc de rem g eg sst p k CTX0 R11 R12 F fl LK2 M2 model2 G
           fx1 R1 M1 model1 LKc Ac (vxA V R1) BI1 XV2 XV36 XV37 XV38 XV50 XV51 SVX X3' X4' 0 STC1' eq_refl XV34 V61e V65e X10 X11 PA1 ISS1 BASE1 (eq_sym REM0)).
  - rewrite <- XV38. clear - PK. lia.
  - rewrite <- XV38. clear - PK. unfold PM.CHUNK in *. lia.
  - exact DEF0.
Qed.

End A0f.
End PGSRDA0F.
