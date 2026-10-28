(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs PmTxtSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcRead1_b PnAReset1_b PnARdSpanP_b Ba0PgRdSpan1_b Ba0PgRdSpan2_b Ba0PgRdSpan2b_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PgTxtKitA_b PnRunA_b Ba0PgSrd1_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGSRSA3.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PMA.AD.
Abbreviation pot := PGSRSA1.pot.
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "Q" in destruct PP as (H & PP) end.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (S r len : Z) (T : PGS.towner) (OB : list (Z * Z)) (src0 : PM.srcst) (tx0 : PM.vstr) (tg0 : Z) (str : PM.vstr) (sm0 : PM.strm).
#[local] Abbreviation os := (PGSSRA1.os T).   (* [comment removed for export] *)
#[local] Abbreviation ois := (PGSSRA1.ois T).   (* [comment removed for export] *)
#[local] Abbreviation tb := (PGSSRA1.tb T).   (* [comment removed for export] *)
#[local] Abbreviation lo := (PGSSRA1.lo T).   (* [comment removed for export] *)
#[local] Abbreviation hi := (PGSSRA1.hi T).   (* [comment removed for export] *)
Hypothesis TOK : PGSA.towner_ok RSEGS AD L ar HI T.
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis K0 : K [].
Hypothesis FRM0 : PGSA.ffroomB PNRA.FCB 6 FF LK0.
Hypothesis FRS : PMSPA.ffrsA FF S.
Hypothesis OFR : PGSA.ofr FF lo hi.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UN0 : PM.unread src0 sm0 < 2 ^ 26.
Hypothesis STKSH0 : shadow_zero M0 (S - 24576) 3072.
Hypothesis FBS : PGSA.fill_buffer_specG RSEGS AD L ar HI PNRA.FCB.
Hypothesis SRDS : PGSA.srd_read_specG RSEGS AD L ar HI PNRA.FCB (pa_srd_read AD).
#[local] Abbreviation W0 := (PGSSRA1.W0 T).   (* [comment removed for export] *)
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
                         (src' : PM.srcst) (tx' : PM.vstr) (tg' : Z) (sm' : PM.strm) (cr' : credit) (ptr n : Z),
  regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
  ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PM.src_own src' ++ PM.vs_own tx' ++ OB) ptr n \/ (tb + 1 <= ptr /\ ptr + n <= tb + 24)) ->
  L5.defined M' ptr n -> PMSPA.accA M' ptr n ->
  PGS.tw_at T M' src' tx' tg' OB -> PM.iss_at RSEGS AD PMSPA.accA M' ois str sm' ->
  PMSP.src_step src0 src' sm0 sm' ->
  L5CA.ahpres L ar LBX FF S (PMSPA.pm_scr 6) W0 M0 M' ->
  PMSP.credit_keep cr0 cr' (pot L ar tx0 tg0) (pot L ar tx' tg') ->
  model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' ->
  ri_inv HI (PM.src_own src' ++ PM.vs_own tx' ++ OB ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

#[local] Abbreviation lay := (PGSSRA1.lay L ar HI T TOK).
#[local] Abbreviation tsrc := (PGSSRA1.tsrc L ar HI T OB TOK).
#[local] Abbreviation aobjs := (PGSSRA1.aobjs L ar HI FF T TOK OFR).
#[local] Abbreviation frame_app := (PGSSRA1.frame_app L ar C HI LY HIok FF T TOK OFR).
#[local] Abbreviation wapp_W0 := (PGSSRA1.wapp_W0 L ar C HI LY HIok FF T TOK OFR).
#[local] Abbreviation tw_xferA := (PGSSRA1.tw_xferA L ar C HI HIok LBX FF T OB TOK OFR).
#[local] Abbreviation stw_ok := (PGSSRA1.stw_ok L ar C HI LY HIok T TOK).
#[local] Abbreviation own2 := PGSSRA1.own2.
#[local] Abbreviation unread_nn := (PGSRSA1.unread_nn L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation centry := (PGSRSA1.centry L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation U := (PGSRSA1.U R0).
#[local] Abbreviation saves9 := (PGSRSA1.saves9 R0 S).
#[local] Abbreviation kept_rs := (PGSRSA1.kept_rs R0).
#[local] Abbreviation memrel := (PGSRSA1.memrel L ar M0 LBX FF S T).
#[local] Abbreviation fields_eq := (PGSRSA1.fields_eq).
#[local] Abbreviation st_ok := (PGSRSA1.st_ok L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S T OB tx0 tg0 str).
#[local] Abbreviation bregs := (PGSRSA1.bregs R0 S len T).
#[local] Abbreviation finish_rs := (PGSRSA1.finish_rs L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation call_srd := (PGSRSA1.call_srd L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation vpack := (PGSRSA1.vpack L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation outside_W0 := (PGSSRA1.outside_W0 L ar HI T TOK).

#[local] Abbreviation fast := (PGSRSA2.fast L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation slow := (PGSRSA2b.slow L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation call_fill := (PGSRSA1.call_fill L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation src_step_trans := PGSRSA2.src_step_trans.
#[local] Abbreviation at_srd := (PGSRSA2.at_srd L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
Ltac bvr1 x := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R0 (reg x))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 1%nat; bvr1 8%nat; bvr1 9%nat; bvr1 18%nat; bvr1 19%nat; bvr1 20%nat; bvr1 21%nat; bvr1 22%nat; bvr1 23%nat.
Ltac vis64 AV := lazymatch goal with |- L5.u64_at ?sg (mrestrict ?H ?M) ?a ?v =>
  apply (proj2 (L5A.u64_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac vis8 AV := lazymatch goal with |- L5.u8_at ?sg (mrestrict ?H ?M) ?a ?v =>
  apply (proj2 (L5A.u8_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.


(* [comment removed for export] *)
Lemma src_eta (src : PM.srcst) : PM.SRC (PM.sr_qc src) (PM.sr_de src) (PM.sr_rem src) = src.
Proof. destruct src; reflexivity. Qed.

(* [comment removed for export] *)
Lemma after_fill (fx : FPState) R M model src tx tg sm sm1 cr LK Aw (c : Z) :
  bregs R -> getr R (reg 20) = Z_to_bv 64 (os + 264) -> getr R (reg 23) = Z_to_bv 64 ((os + 264) / 8 + 2147450880) ->
  getr R (reg 10) = Z_to_bv 64 c -> 0 <= c <= PM.CHUNK -> 1 <= len ->
  st_ok M model src tx tg sm1 cr LK Aw -> fields_eq src tx tg -> PMSP.src_step src0 src sm0 sm ->
  PMSP.src_step src src sm sm1 -> PM.sr_rem src = 0 -> PM.sm_g sm1 = PM.sm_g sm + c ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb4e5c M model) K.
Proof using All.
  intros BR0 A20 A23 A10 Hc Hl SO FE STEP STEP1 RZ G1. pose proof BR0 as (A2 & A8 & A9 & A18 & A19 & A21 & A22 & KP).
  pose proof (vpack M model src tx tg sm1 cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
  pose proof lay as LAY. pose proof aobjs as (AO_ & AOI & AT_). destruct (frame_app _ _ _ _ _ _ HH) as (FA1 & FA2 & FA3 & FA4 & FA5).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & _).
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  pose proof (tsrc M src tx tg PA) as (SRC & PNI & PD & VS & _).
  pose proof SRC as (F240 & F248 & F256 & F264 & F272 & F280 & F288 & Q1 & Q2 & Q3 & Q4 & DC & CC & C240).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  set (qc := PM.sr_qc src) in *.
  unfold PM.CHUNK in *.
  assert (QIN : In (qc, 16384) (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  destruct (BRB _ QIN) as (QB0 & QB1). cbn [fst snd] in QB0, QB1.
  assert (BLKAP : forall q m, In (q, m) (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX) -> q + m <= os \/ os + 296 <= q).
  { intros q m Hq. destruct (PMASK.blk_obj_apart L ar C HI HIok _ FF LK cr Aw M _ q m os 296 HH Hq AO) as [X|X]; [left| right]; lia. }
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72).
  set (MV := mrestrict (ahid Aw model) M) in *.
  LeanFeed.pfeed PP (PMARSPP.arpB_conc fx R MV (fun j => match j with 2%nat => S | 34%nat => qc | 36%nat => os | 37%nat => tb | 38%nat => len | 43%nat => c | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
      | |- PMARSPP.aligned _ _ => unfold PMARSPP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & EX).
  assert (CCs : L5.u64_at RSEGS M1v (os + 280) qc /\ L5.u64_at RSEGS M1v (os + 288) c).
  { destruct EX as [(_ & _ & _ & _ & _ & _ & C1 & C2) | (_ & _ & _ & _ & _ & _ & C1 & C2)]; split; assumption. }
  destruct CCs as (C1 & C2).
  set (P := fun a => os + 280 <= a < os + 280 + 16).
  set (s2 := PM.SRC qc qc c).
  (* [comment removed for export] *)
  assert (POST : forall M1 model1, ri_inv HI (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX) FF LK cr Aw M1 (vml_of model1) -> L5CA.amodel_ok Aw model1 -> model_rt model model1 ->
                   mrestrict (ahid Aw model) M1 = M1v -> mem_grows M M1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
                   st_ok M1 model1 s2 tx tg sm1 cr LK Aw).
  { intros M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1.
    assert (BK1 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v Ha Hb X. apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))). rewrite VIS1. exact X. }
    assert (AGO : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= os + 280 \/ os + 296 <= a) -> L5C.agree_on M M1 a n).
    { intros a n Ha Hn X i Hi. apply FR1; [lia| unfold P; clear - X Hi; lia]. }
    assert (AGSH : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n).
    { intros a n Ha Hn x Hx. unfold HeapIfaceA.S, HeapIfaceA.SB.
      assert (X8 : 0 <= x / 8 <= 17592186044416) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
      apply FR1; [lia|]. unfold P. clear - X8 OBIG. destruct OBIG; lia. }
    assert (AGB : forall q m, In (q, m) (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX) -> PMFA.agA M M1 q m).
    { intros q m Hq. destruct (BRB _ Hq) as (X0 & X1). cbn [fst snd] in X0, X1. destruct (BLKAP q m Hq) as [BF|BF]; (split; [apply AGO; lia| apply AGSH; lia]). }
    assert (SF1 : PM.src_fields_at RSEGS PMSPA.accA M1 os ois (ois + 16) s2).
    { apply (PGSKA.src_fields_updG M M1 os ois (ois + 16) qc (PM.sr_de src) (PM.sr_rem src) qc c ltac:(rewrite <- (src_eta src) in SRC; exact SRC)); unfold PM.CHUNK; [lia| lia| | | | | | | | | | lia| lia| lia].
      - split; [apply AGO; lia| apply AGSH; lia].
      - apply AGSH; lia.
      - apply (L5.defined_grows M M1 _ _ MGM1). exact F256.
      - apply AGSH; lia.
      - apply (L5.defined_grows M M1 _ _ MGM1). exact DC.
      - apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| exact F264].
      - apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| exact F272].
      - apply BK1; [lia| lia| exact C1].
      - apply BK1; [lia| lia| exact C2]. }
    assert (VS1 : PM.vstr_at RSEGS PMSPA.accA M1 tb tx).
    { apply (PMFA.vstr_at_agreeA RSEGS M M1 tb tx); [lia| lia| split; [apply AGO; lia| apply AGSH; lia]| | exact VS].
      intros c0 n0 p0 E. apply AGB. apply in_or_app; right; apply in_or_app; left. rewrite E. left; reflexivity. }
    assert (EKo : L5SAR.ek L ar (OB ++ LBX) FF S 24576 W0 M M1).
    { apply (L5SAR.ek_piece L ar (OB ++ LBX) FF S 24576 W0 M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. apply (OWx (os + 256, 40)); [unfold PGSSRA1.W0, PGS.W_srcfG; left; reflexivity|].
      unfold L5.in_rng, P in *; cbn [fst snd] in *. lia. }
    assert (PA1 : PGS.tw_at T M1 s2 tx tg OB).
    { apply (tw_xferA M M1 src s2 tx tx tg tg LK cr Aw (vml_of model) S 24576 [] PA HH); [| constructor| exact SF1| reflexivity| exact VS1| exact TBOK].
      apply (L5SAR.ahpres_of L ar (OB ++ LBX) FF S 24576 _ M M1); [exact EKo| apply (L5.defined_grows M M1 _ _ MGM1); exact SDEF| apply L5SAR.dk_grows; exact MGM1]. }
    set (Wp := [(os + 280, 16)]).
    assert (EK1 : L5SAR.ek L ar (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX) FF S 24576 Wp M M1).
    { apply (L5SAR.ek_piece L ar _ FF S 24576 Wp M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. apply (OWx (os + 280, 16)); [left; reflexivity|]. unfold L5.in_rng, P in *; cbn [fst snd]. lia. }
    assert (WAPPp : PMKA.wapp Wp) by (apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct OBIG; [right| left]; lia| apply PMKA.wapp_nil]).
    assert (IA1 : PM.iss_at RSEGS AD PMSPA.accA M1 ois str sm1).
    { apply (PMKA.iss_keepA RSEGS AD L ar _ FF S 24576 Wp M M1 EK1 WAPPp FRB BRB _ _ _ AOI); [intros x Hx; rewrite !in_app_iff; right; right; right; apply INCS; exact Hx| | |exact IA].
      - intros i Hi r0 Hr. unfold Wp in Hr. unfold L5.in_rng. destruct Hr as [<-|[]]; cbn [fst snd]; lia.
      - intros c1 n1 p1 E i Hi r0 Hr. assert (Ip : In (p1, c1) (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX)) by (rewrite !in_app_iff; right; right; right; apply INCS; rewrite E; left; reflexivity).
        destruct (BLKAP _ _ Ip) as [X|X]; unfold Wp in Hr; unfold L5.in_rng; destruct Hr as [<-|[]]; cbn [fst snd]; lia. }
    assert (EKn : L5SAR.ek L ar LBX FF S 24576 W0 M M1).
    { apply (L5SAR.ek_piece L ar LBX FF S 24576 W0 M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. apply (OWx (os + 256, 40)); [unfold PGSSRA1.W0, PGS.W_srcfG; left; reflexivity|].
      unfold L5.in_rng, P in *; cbn [fst snd] in *. lia. }
    split; [split; [|split]|].
    - exact (L5SAR.ek_trans L ar LBX FF S 24576 W0 M0 M M1 EK EKn).
    - apply (L5SAR.dk_trans L ar LBX FF S 24576 M0 M M1 DK). apply L5SAR.dk_grows. exact MGM1.
    - exact (L5SAR.astk_grows ar M M1 S 24576 STK MGM1).
    - split; [repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| assumption])|].
      split; [exact PA1|]. split; [exact IA1|].
      split; [apply (PMASK.base_keep L ar C LY LBX FF S 24576 W0 M M1 EKn); [intros a Ha; apply outside_W0; clear - Ha FA1 FSI; lia| exact BASE]|].
      split; [exact TBOK|]. split; [exact HH1|]. split; [exact AM1|]. split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1]|].
      split; [exact ILK|]. split; [exact IAW|]. split; [exact CRL| exact CRK]. }
  assert (STEP2 : PMSP.src_step src0 s2 sm0 sm1).
  { apply (src_step_trans _ _ _ _ _ _ STEP). unfold s2. unfold PMSP.src_step, PM.unread in *. cbn [PM.sr_qc PM.sr_rem] in *.
    destruct STEP1 as (E1 & E2 & L1 & S1 & U1). split; [reflexivity|]. split; [exact E2|]. split; [exact L1|]. split; [exact S1| lia]. }
  assert (FE2 : fields_eq s2 tx tg) by exact I.
  assert (WOB : forall a, 0 <= a < 2 ^ 64 -> P a -> aclientw L ar (PM.src_own src ++ PM.vs_own tx ++ OB ++ LBX) FF 0 0 a /\ ~ (0x10000 <= a < 0x696000)).
  { intros a Ha Wa. unfold P in Wa. split.
    - unfold aclientw, aclient_g. right; right; right; left. destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. clear - Wa X1 X2. lia.
    - clear - Wa O1. lia. }
  assert (FZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) by (intros a Ha N; apply FRZ1; [exact Ha| exact N]).
  unfold PMSPA.cfg, PMSP.cfg.
  destruct EX as [(MS & KS1 & E10 & E11 & E12 & Hlt & _) | (MS & KS1 & E10 & E11 & E12 & Hge & _)].
  - (* [comment removed for export] *)
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb4e5c R1 0xb4e9c M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    pose proof (POST M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1) as SO1.
    apply (slow fx1 R1 M1 model1 s2 tx tg sm1 cr LK Aw); try assumption.
    unfold PGSRSA1.bregs.
    split; [rewrite (KS1 2%nat) by inl; exact A2|]. split; [rewrite (KS1 8%nat) by inl; exact A8|].
    split; [rewrite (KS1 9%nat) by inl; exact A9|]. split; [rewrite (KS1 18%nat) by inl; exact A18|].
    split; [rewrite (KS1 19%nat) by inl; exact A19|]. split; [rewrite (KS1 21%nat) by inl; exact A21|].
    split; [rewrite (KS1 22%nat) by inl; exact A22|].
    intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
  - (* [comment removed for export] *)
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb4e5c R1 0xb4ee0 M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    pose proof (POST M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1) as SO1.
    assert (BR1 : bregs R1).
    { unfold PGSRSA1.bregs.
      split; [rewrite (KS1 2%nat) by inl; exact A2|]. split; [rewrite (KS1 8%nat) by inl; exact A8|].
      split; [rewrite (KS1 9%nat) by inl; exact A9|]. split; [rewrite (KS1 18%nat) by inl; exact A18|].
      split; [rewrite (KS1 19%nat) by inl; exact A19|]. split; [rewrite (KS1 21%nat) by inl; exact A21|].
      split; [rewrite (KS1 22%nat) by inl; exact A22|].
      intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx. }
    apply (fast fx1 R1 M1 model1 s2 tx tg sm1 cr LK Aw); try assumption.
    all: unfold s2; cbn [PM.sr_rem]; first [exact E12 | lia].
Qed.

Lemma src_step_refl a sa : PMSP.src_step a a sa sa.
Proof. unfold PMSP.src_step. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros X; exact X| lia]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma entry (fx : FPState) :
  ri_inv HI (PM.src_own src0 ++ PM.vs_own tx0 ++ OB ++ LBX) FF LK0 cr0 Aw0 M0 (vml_of model0) -> L5CA.amodel_ok Aw0 model0 -> L5CA.astk ar M0 S 24576 ->
  getr R0 (reg 10) = Z_to_bv 64 os -> getr R0 (reg 11) = Z_to_bv 64 len -> getr R0 (reg 12) = Z_to_bv 64 tb ->
  PGS.tw_at T M0 src0 tx0 tg0 OB -> PM.iss_at RSEGS AD PMSPA.accA M0 ois str sm0 -> PMSTA.base_okA RSEGS AD M0 ->
  PM.tb_ok tx0 tg0 -> PMSPA.credit_le (pot L ar tx0 tg0) cr0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R0 0xb4dc0 M0 model0) K.
Proof using All.
  intros HH AM STK A10 A11 A12 PA IA BASE TBOK CRL.
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof lay as LAY. pose proof aobjs as (AO_ & AOI & AT_). destruct (frame_app _ _ _ _ _ _ HH) as (FA1 & FA2 & FA3 & FA4 & FA5).
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 HH BASE) as (V0 & V1 & V2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 S 24576 80 HH STK ltac:(lia)) as (SL80 & SH80 & V3).
  pose proof (tsrc M0 src0 tx0 tg0 PA) as (SRC & PNI & PD & VS & _).
  pose proof (PGSKA.src_visG L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 os _ _ src0 S 24576 HH AO_ ltac:(clear - LAY; lia) SRC PNI STK)
    as ((O1 & O8 & OBIG) & OZ & OW & OCE & OAV & AO & OFS1 & OFS2).
  pose proof SRC as (F240 & F248 & F256 & F264 & F272 & F280 & F288 & Q1 & Q2 & Q3 & Q4 & DC & CC & C240).
  set (qc := PM.sr_qc src0) in *. set (rem := PM.sr_rem src0) in *.
  unfold PM.CHUNK in *.
  assert (QIN : In (qc, 16384) (PM.src_own src0 ++ PM.vs_own tx0 ++ OB ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  destruct (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH _ QIN) as (QB0 & QB1). cbn [fst snd] in QB0, QB1.
  set (MV := mrestrict (ahid Aw0 model0) M0) in *.
  LeanFeed.pfeed PP (PMARSPP.arpA_conc fx R0 MV (fun j => match j with 2%nat => S | 33%nat => rem | 36%nat => os | 37%nat => tb | 38%nat => len | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
      | |- PMARSPP.aligned _ _ => unfold PMARSPP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & EX).
  set (P := fun a => S - 80 <= a < S - 80 + 80).
  assert (FZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) by (intros a Ha N; apply FRZ1; [exact Ha| exact N]).
  assert (WOB : forall a, 0 <= a < 2 ^ 64 -> P a -> aclientw L ar (PM.src_own src0 ++ PM.vs_own tx0 ++ OB ++ LBX) FF 0 0 a /\ ~ (0x10000 <= a < 0x696000)).
  { intros a Ha Wa. unfold P in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| lia]. }
  (* [comment removed for export] *)
  assert (POST : forall M1 model1, ri_inv HI (PM.src_own src0 ++ PM.vs_own tx0 ++ OB ++ LBX) FF LK0 cr0 Aw0 M1 (vml_of model1) -> L5CA.amodel_ok Aw0 model1 -> model_rt model0 model1 ->
                   mrestrict (ahid Aw0 model0) M1 = M1v -> mem_grows M0 M1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
                   saves9 M1v -> st_ok M1 model1 src0 tx0 tg0 sm0 cr0 LK0 Aw0).
  { intros M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1 SVv.
    pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 HH) as (_ & VIS & _).
    assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= S - 80 \/ S <= a) -> L5C.agree_on M0 M1 a n).
    { intros a n Ha Hn X i Hi. apply FR1; [lia| unfold P; clear - X Hi; lia]. }
    assert (AGSH : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M0 M1 a n).
    { intros a n Ha Hn x Hx. unfold HeapIfaceA.S, HeapIfaceA.SB.
      assert (X8 : 0 <= x / 8 <= 17592186044416) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
      apply FR1; [lia|]. unfold P. lia. }
    assert (EKo : L5SAR.ek L ar (OB ++ LBX) FF S 24576 W0 M0 M1).
    { apply (PGSSRA1.ek_drop L ar (PM.src_own src0 ++ PM.vs_own tx0)). rewrite <- PGSSRA1.own2.
      apply (L5SAR.ek_piece L ar _ FF S 24576 W0 M0 M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. unfold P in Pa.
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 _ S 24576 a HH SPT CA) as [X|X]; lia. }
    pose proof (PGSSRA1.ek_drop L ar OB LBX FF S 24576 W0 M0 M1 EKo) as EKn.
    pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
    assert (EKp : L5SAR.ek L ar (PM.src_own src0 ++ PM.vs_own tx0 ++ OB ++ LBX) FF S 24576 [] M0 M1).
    { apply (L5SAR.ek_piece L ar _ FF S 24576 [] M0 M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. unfold P in Pa.
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 _ S 24576 a HH SPT CA) as [X|X]; lia. }
    split; [split; [|split]|].
    - exact EKn.
    - apply L5SAR.dk_grows. exact MGM1.
    - exact (L5SAR.astk_grows ar M0 M1 S 24576 STK MGM1).
    - split.
      { destruct SVv as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72).
        assert (BK : forall k v, 8 <= k <= 80 -> L5.u64_at RSEGS M1v (S - k) v -> L5.u64_at RSEGS M1 (S - k) v).
        { intros k v Hk X. apply (proj1 (L5A.u64_at_vis (ahid Aw0 model0) M1 (S - k) v (VIS (S - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact X. }
        repeat split; (apply BK; [lia| assumption]). }
      split.
      { apply (tw_xferA M0 M1 src0 src0 tx0 tx0 tg0 tg0 LK0 cr0 Aw0 (vml_of model0) S 24576 [] PA HH); [| constructor| | reflexivity| | exact TBOK].
        - apply (L5SAR.ahpres_of L ar (OB ++ LBX) FF S 24576 _ M0 M1); [exact EKo| apply (L5.defined_grows M0 M1 _ _ MGM1); exact SDEF| apply L5SAR.dk_grows; exact MGM1].
        - apply (PGSKA.src_fields_keepG M0 M1 os ois (ois + 16) src0 SRC); [clear - O1; lia| clear - O1; lia| | |].
          + apply (PMKA.agA_obj L ar _ FF S 24576 [] M0 M1 EKp PMKA.wapp_nil FRB os 296 AO_). intros i _ r0 [].
          + apply (PMASK.agsh_blk L ar _ FF S 24576 [] M0 M1 _ _ EKp PMKA.wapp_nil QIN); [clear - QB0; lia| clear - QB1; lia].
          + apply (L5.defined_grows M0 M1 _ _ MGM1). exact DC.
        - apply (PMKA.vstr_keepA RSEGS L ar _ FF S 24576 [] M0 M1 EKp PMKA.wapp_nil FRB BRB tb tx0 AT_); [| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact VS].
          intros x Hx. apply in_or_app; right. apply in_or_app; left. exact Hx. }
      split; [apply (PMKA.iss_keepA RSEGS AD L ar _ FF S 24576 [] M0 M1 EKp PMKA.wapp_nil FRB BRB _ _ _ AOI); [intros x Hx; rewrite !in_app_iff; right; right; right; apply INCS; exact Hx| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA]|].
      split; [apply (PMASK.base_keep L ar C LY LBX FF S 24576 W0 M0 M1 EKn); [intros a Ha; apply outside_W0; pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH); clear - Ha FA1 H; lia| exact BASE]|].
      split; [exact TBOK|]. split; [exact HH1|]. split; [exact AM1|]. split; [exact MRT1|].
      split; [apply incl_refl|]. split; [apply incl_refl|]. split; [exact CRL|].
      unfold PMSPA.credit_keep. lia. }
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 1))) as BU1. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 8))) as BU8.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 9))) as BU9. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 18))) as BU18.
  change (bv_modulus 64) with (2 ^ 64) in *.
  assert (FE0 : fields_eq src0 tx0 tg0) by exact I.
  unfold PMSPA.cfg, PMSP.cfg.
  destruct EX as [(MS & KS1 & E10 & E11 & Z0 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)
                 | [(MS & KS1 & E2 & E8 & E9 & E10 & E12 & E18 & E19 & E21 & E22 & Hle & Hr1 & Hl1 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)
                 | [(MS & KS1 & E2 & E8 & E9 & E10 & E12 & E18 & E19 & E21 & E22 & Hlt & Hr1 & Hl1 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)
                 | (MS & KS1 & E2 & E8 & E9 & E10 & E18 & E19 & E21 & E22 & Hr0 & Hl1 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)]]].
  - (* [comment removed for export] *)
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xb4dc0 R1 0xb501c M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    pose proof (POST M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1 ltac:(repeat split; assumption)) as SO1.
    assert (L0 : len = 0) by (rewrite Z.sub_0_r, Z.mod_small in Z0 by lia; lia).
    apply (finish_rs fx1 R1 M1 model1 src0 tx0 tg0 sm0 cr0 LK0 Aw0 0 0); try assumption.
    all: first [ rewrite (KS1 1%nat) by inl; unfold PGSRSA1.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 2%nat) by inl; exact Rsp0
               | rewrite (KS1 8%nat) by inl; unfold PGSRSA1.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 9%nat) by inl; unfold PGSRSA1.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 18%nat) by inl; unfold PGSRSA1.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 19%nat) by inl; unfold PGSRSA1.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 20%nat) by inl; unfold PGSRSA1.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 21%nat) by inl; unfold PGSRSA1.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 22%nat) by inl; unfold PGSRSA1.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 23%nat) by inl; unfold PGSRSA1.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | (intros x Hx; rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx); reflexivity)
               | lia
               | (left; split; reflexivity)
               | (intros i Hi; lia)
               | apply src_step_refl ].
  - (* [comment removed for export] *)
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xb4dc0 R1 0xb4ee0 M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    pose proof (POST M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1 ltac:(repeat split; assumption)) as SO1.
    assert (BR1 : bregs R1).
    { unfold PGSRSA1.bregs. do 7 (split; [assumption|]).
      intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). reflexivity. }
    apply (fast fx1 R1 M1 model1 src0 tx0 tg0 sm0 cr0 LK0 Aw0 BR1 E12); [rewrite Z.sub_0_r, Z.mod_small in Hr1, Hl1 by lia; lia| exact SO1| exact FE0| apply src_step_refl].
  - (* [comment removed for export] *)
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xb4dc0 R1 0xb4e9c M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    pose proof (POST M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1 ltac:(repeat split; assumption)) as SO1.
    assert (BR1 : bregs R1).
    { unfold PGSRSA1.bregs. do 7 (split; [assumption|]).
      intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). reflexivity. }
    apply (slow fx1 R1 M1 model1 src0 tx0 tg0 sm0 cr0 LK0 Aw0 BR1); [rewrite Z.sub_0_r, Z.mod_small in Hl1 by lia; lia| exact SO1| exact FE0| apply src_step_refl].
  - (* [comment removed for export] *)
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xb4dc0 R1 0xb4e20 M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    pose proof (POST M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1 ltac:(repeat split; assumption)) as SO1.
    assert (RZ : rem = 0) by (rewrite Z.sub_0_r, Z.mod_small in Hr0 by lia; lia).
    assert (LP : 1 <= len) by (rewrite Z.sub_0_r, Z.mod_small in Hl1 by lia; lia).
    pose proof (vpack M1 model1 src0 tx0 tg0 sm0 cr0 LK0 Aw0 SO1) as (W0v & W1v & W2v & (SR1 & S16 & W3v) & SVV & (P1 & P8 & PBIG) & PZ & PW & PAV & _ & _ & _ & _ & OSS & _ & _ & _).
    pose proof SO1 as (_ & _ & PA1 & _).
    pose proof (tsrc M1 src0 tx0 tg0 PA1) as (SRC1 & _).
    destruct SRC1 as (_ & _ & _ & G264 & G272 & _ & G288 & _). fold qc rem in G264, G288. rewrite RZ in G288.
    set (MV1 := mrestrict (ahid Aw0 model1) M1) in *.
    LeanFeed.pfeed PP (PMARSPP.arpR0_conc fx1 R1 MV1 (fun j => match j with 2%nat => S | 34%nat => qc | 36%nat => os | 37%nat => tb | 38%nat => len | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
        | |- L5.u64_at _ _ (os + _) _ => unfold MV1; vis64 PAV
        | |- PMARSPP.aligned _ _ => unfold PMARSPP.aligned; lia
        | |- _ => lia end]).
    destruct PP as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & [(MS2 & KS2 & F10 & F11 & F12 & Hgt) | (MS2 & KS2 & F1 & F10 & F11 & F12 & F20 & F23 & Hle)]).
    + (* [comment removed for export] *)
      apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M1 model1 fx1 fx2 R1 0xb4e20 R2 0xb4e9c M2v K HH1 AM1 MS2 MG2 FRZ2).
      intros M2 model2 HH2 AM2 MRT2 HID2 VIS2 MGM2 FR2.
      assert (E2' : M2 = M1) by (apply L5SAR.mem_eq_of_agree; exact FR2). subst M2.
      assert (SO2 : st_ok M1 model2 src0 tx0 tg0 sm0 cr0 LK0 Aw0).
      { pose proof SO1 as (X1 & X2 & X3 & X4 & X5 & X6 & _ & _ & X9 & X10 & X11 & X12 & X13).
        exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj HH2 (conj AM2 (conj (L5LZ.model_rt_trans _ _ _ X9 MRT2) (conj X10 (conj X11 (conj X12 X13)))))))))))). }
      assert (BR2 : bregs R2).
      { unfold PGSRSA1.bregs.
        split; [rewrite (KS2 2%nat) by inl; exact E2|]. split; [rewrite (KS2 8%nat) by inl; exact E8|].
        split; [rewrite (KS2 9%nat) by inl; exact E9|]. split; [rewrite (KS2 18%nat) by inl; exact E18|].
        split; [rewrite (KS2 19%nat) by inl; exact E19|]. split; [rewrite (KS2 21%nat) by inl; exact E21|].
        split; [rewrite (KS2 22%nat) by inl; exact E22|].
        intros x Hx. rewrite (KS2 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). reflexivity. }
      apply (slow fx2 R2 M1 model2 src0 tx0 tg0 sm0 cr0 LK0 Aw0 BR2 LP SO2 FE0 (src_step_refl _ _)).
    + (* [comment removed for export] *)
      apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M1 model1 fx1 fx2 R1 0xb4e20 R2 0xb29f8 M2v K HH1 AM1 MS2 MG2 FRZ2).
      intros M2 model2 HH2 AM2 MRT2 HID2 VIS2 MGM2 FR2.
      assert (E2' : M2 = M1) by (apply L5SAR.mem_eq_of_agree; exact FR2). subst M2.
      assert (SO2 : st_ok M1 model2 src0 tx0 tg0 sm0 cr0 LK0 Aw0).
      { pose proof SO1 as (X1 & X2 & X3 & X4 & X5 & X6 & _ & _ & X9 & X10 & X11 & X12 & X13).
        exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj HH2 (conj AM2 (conj (L5LZ.model_rt_trans _ _ _ X9 MRT2) (conj X10 (conj X11 (conj X12 X13)))))))))))). }
      assert (KP2 : kept_rs R2).
      { intros x Hx. rewrite (KS2 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). reflexivity. }
      assert (R2sp : getr R2 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (KS2 2%nat) by inl; exact E2).
      apply (call_fill fx2 R2 M1 model2 src0 tx0 tg0 sm0 cr0 LK0 Aw0 740956 F1 ltac:(split; [lia| reflexivity]) R2sp KP2 F10 F11 F12 SO2).
      intros fx3 R3 M3 model3 LK3 Aw3 sm3 c RP3 Y10 Hc G1 ST0 ST2 STEP3 SO3.
      assert (BR3 : bregs R3).
      { unfold PGSRSA1.bregs.
        split; [rewrite (L5SAR.cs_of_preserved R2 R3 2%nat RP3) by inl; exact R2sp|].
        split; [rewrite (L5SAR.cs_of_preserved R2 R3 8%nat RP3) by inl; rewrite (KS2 8%nat) by inl; exact E8|].
        split; [rewrite (L5SAR.cs_of_preserved R2 R3 9%nat RP3) by inl; rewrite (KS2 9%nat) by inl; exact E9|].
        split; [rewrite (L5SAR.cs_of_preserved R2 R3 18%nat RP3) by inl; rewrite (KS2 18%nat) by inl; exact E18|].
        split; [rewrite (L5SAR.cs_of_preserved R2 R3 19%nat RP3) by inl; rewrite (KS2 19%nat) by inl; exact E19|].
        split; [rewrite (L5SAR.cs_of_preserved R2 R3 21%nat RP3) by inl; rewrite (KS2 21%nat) by inl; exact E21|].
        split; [rewrite (L5SAR.cs_of_preserved R2 R3 22%nat RP3) by inl; rewrite (KS2 22%nat) by inl; exact E22|].
        intros x Hx. rewrite (L5SAR.cs_of_preserved R2 R3 x RP3) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP2. exact Hx. }
      apply (after_fill fx3 R3 M3 model3 src0 tx0 tg0 sm0 sm3 cr0 LK3 Aw3 c BR3); try assumption.
      * rewrite (L5SAR.cs_of_preserved R2 R3 20%nat RP3) by inl. exact F20.
      * rewrite (L5SAR.cs_of_preserved R2 R3 23%nat RP3) by inl. exact F23.
      * apply src_step_refl.
Qed.


End Call.
(* [comment removed for export] *)
Theorem read_span_okG : PGSA.fill_buffer_specG RSEGS AD L ar HI PNRA.FCB -> PGSA.srd_read_specG RSEGS AD L ar HI PNRA.FCB (pa_srd_read AD) ->
  PGSA.read_span_specG RSEGS AD L ar HI PNRA.FCB (pa_read_span AD).
Proof.
  intros FBS SRDS T TOK. unfold PGSA.read_span_specG.
  intros fx R M model K OB LBX FF LK Aw cr sp r len src tx tg str sm HH AM K0 ENT FRM FRS OFR A10 A11 A12 HLEN PA IA BASE INCS UN CRL KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 6) with 24576 in *. change (24576 / 8) with 3072 in STKSH.
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  rewrite L5SAR.r11 in A11. rewrite L5SAR.r12 in A12.
  cbn [pa_read_span PMA.AD ADDR_A].
  pose proof (PGSA.to_src _ _ _ _ _ _ TOK M src tx tg OB PA) as (_ & _ & _ & _ & TB).
  exact (entry R M model K LBX FF LK Aw cr sp r len T OB src tx tg str sm TOK Rra RAok Rsp Rgp Rtp K0 FRM FRS OFR HLEN INCS UN STKSH FBS SRDS KONT fx
           HH AM ASTK A10 A11 A12 PA IA BASE TB CRL).
Qed.

End WithHeap.
End PGSRSA3.
