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
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcRead1_b PnAReset1_b PnARdSpanVP_b Ba0PgRdSpanV1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PgTxtKitA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgV8A_b PgV8KitA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b Ba0PgSrd1_b Ba0PgVw1_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGSRVA2.
Abbreviation v8_atA := (PGV8.v8_at AsanUbsan.M.loaded_segments PMSPA.accA PGV8A.annA).
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PMA.AD.
Abbreviation pot := PGSRVA1.pot.
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "Q" in destruct PP as (H & PP) end.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.

Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (S r len : Z) (T : PGV8.vowner) (OB : list (Z * Z)) (src0 : PM.srcst) (x0 : PGV8.v8) (g0 : Z) (str : PM.vstr) (sm0 : PM.strm).
#[local] Abbreviation os := (PGVWA1.os T).   (* [comment removed for export] *)
#[local] Abbreviation ois := (PGVWA1.ois T).   (* [comment removed for export] *)
#[local] Abbreviation tb := (PGVWA1.tb T).   (* [comment removed for export] *)
#[local] Abbreviation lo := (PGVWA1.lo T).   (* [comment removed for export] *)
#[local] Abbreviation hi := (PGVWA1.hi T).   (* [comment removed for export] *)
Hypothesis TOK : PGV8A.vowner_ok RSEGS AD L ar HI T.
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
Hypothesis SRDS : PGV8A.srd_read_v_specG RSEGS AD L ar HI PNRA.FCB (PNL.pn_srd_read_v PMA.AN).
#[local] Abbreviation W0 := (PGVWA1.W0 T).   (* [comment removed for export] *)
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
                         (src' : PM.srcst) (x' : PGV8.v8) (g' : Z) (sm' : PM.strm) (cr' : credit) (ptr n : Z),
  regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
  PMSP.consumed src0 src' sm0 sm' = n ->
  ((ptr = 0 /\ n = 0) \/ PGS.in_blk (PM.src_own src' ++ PGV8.v8_own x' ++ OB) ptr n) ->
  L5.defined M' ptr n -> PMSPA.accA M' ptr n ->
  (n = len -> PGV8.v8_room x' (PM.unread src' sm')) ->
  PGV8.vw_at T M' src' x' g' OB -> PM.iss_at RSEGS AD PMSPA.accA M' ois str sm' ->
  PMSP.src_step src0 src' sm0 sm' ->
  L5CA.ahpres L ar LBX FF S (PMSPA.pm_scr 6) W0 M0 M' ->
  PMSP.credit_keep cr0 cr' (pot L ar x0 g0) (pot L ar x' g') ->
  model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' ->
  ri_inv HI (PM.src_own src' ++ PGV8.v8_own x' ++ OB ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

#[local] Abbreviation lay := (PGVWA1.lay L ar HI T TOK).
#[local] Abbreviation tsrc := (PGVWA1.tsrc L ar HI T OB TOK).
#[local] Abbreviation aobjs := (PGVWA1.aobjs L ar HI FF T TOK OFR).
#[local] Abbreviation frame_app := (PGVWA1.frame_app L ar C HI LY HIok FF T TOK OFR).
#[local] Abbreviation wapp_W0 := (PGVWA1.wapp_W0 L ar C HI LY HIok FF T TOK OFR).
#[local] Abbreviation tw_xferA := (PGVWA1.tw_xferA L ar C HI HIok LBX FF T OB TOK OFR).
#[local] Abbreviation stw_ok := (PGVWA1.stw_ok L ar C HI LY HIok T TOK).
#[local] Abbreviation own2 := PGVWA1.own2.
#[local] Abbreviation unread_nn := (PGSRVA1.unread_nn L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation centry := (PGSRVA1.centry L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation U := (PGSRVA1.U R0).
#[local] Abbreviation saves9 := (PGSRVA1.saves9 R0 S).
#[local] Abbreviation kept_rs := (PGSRVA1.kept_rs R0).
#[local] Abbreviation memrel := (PGSRVA1.memrel L ar M0 LBX FF S T).
#[local] Abbreviation fields_eq := (PGSRVA1.fields_eq).
#[local] Abbreviation st_ok := (PGSRVA1.st_ok L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S T OB x0 g0 str).
#[local] Abbreviation bregs := (PGSRVA1.bregs R0 S len T).
#[local] Abbreviation finish_rs := (PGSRVA1.finish_rs L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation call_srd := (PGSRVA1.call_srd L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation vpack := (PGSRVA1.vpack L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 STKSH0 FBS SRDS KONT).
#[local] Abbreviation outside_W0 := (PGVWA1.outside_W0 L ar HI T TOK).

Lemma src_step_trans a b c sa sb sc : PMSP.src_step a b sa sb -> PMSP.src_step b c sb sc -> PMSP.src_step a c sa sc.
Proof.
  unfold PMSP.src_step. intros (E1 & E2 & L1 & S1 & U1) (E3 & E4 & L2 & S2 & U2).
  split; [congruence|]. split; [congruence|]. split; [lia|]. split; [intros X; apply S2; apply S1; exact X| lia].
Qed.
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
Lemma fast (fx : FPState) R M model src x g sm cr LK Aw :
  bregs R -> getr R (reg 12) = Z_to_bv 64 (PM.sr_rem src) -> 1 <= len <= PM.sr_rem src ->
  st_ok M model src x g sm cr LK Aw -> fields_eq src x g -> PMSP.src_step src0 src sm0 sm ->
  PM.unread src sm = PM.unread src0 sm0 -> PGV8.v8_room x (PM.unread src sm) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb3d24 M model) K.
Proof using All.
  intros (A2 & A8 & A9 & A18 & A19 & A21 & A22 & KP) A12 Hl SO FE STEP CONS0 RM0.
  pose proof (vpack M model src x g sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof lay as LAY. pose proof aobjs as (AO_ & AOI & AT_). destruct (frame_app _ _ _ _ _ _ HH) as (FA1 & FA2 & FA3 & FA4 & FA5).
  pose proof (tsrc M src x g PA) as (SRC & PNI & PD & VS & _).
  pose proof SRC as (F240 & F248 & F256 & F264 & F272 & F280 & F288 & G1 & G2 & G3 & G4 & DC & CC & C240).
  set (qc := PM.sr_qc src) in *. set (de := PM.sr_de src) in *. set (rem := PM.sr_rem src) in *.
  unfold PM.CHUNK in *.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  assert (QIN : In (qc, 16384) (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  destruct (WB _ QIN) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in Q0, Q1, Q2, Q3, Q4, Q5.
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72). bvr.
  set (MV := mrestrict (ahid Aw model) M) in *.
  LeanFeed.pfeed PP (PMARSVP.arvF_conc fx R MV (fun j => match j with 2%nat => S | 33%nat => rem | 35%nat => de | 36%nat => os | 37%nat => tb | 38%nat => len
       | 44%nat => U 1 | 45%nat => U 8 | 46%nat => U 9 | 47%nat => U 18 | 48%nat => U 19 | 49%nat => U 20 | 50%nat => U 21 | 51%nat => U 22 | 52%nat => U 23
       | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
      | |- L5.defined _ (os + 256) 8 => unfold MV; apply (proj2 (L5A.defined_vis (ahid Aw model) M (os + 256) 8 ltac:(apply OAV; lia))); exact F256
      | |- PMARSVP.aligned _ _ => unfold PMARSVP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & E1 & E2 & E8 & E9 & E10 & E11 & E13 & E14 & E18 & E19 & E20 & E21 & E22 & E23 & C288 & C280).
  unfold PMSPA.cfg, PMSP.cfg.
  set (P := fun a => os + 256 <= a < os + 256 + 8 \/ os + 280 <= a < os + 280 + 16).
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb3d24 R1 0xb3db4 M1v P K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { intros a Ha Wa. unfold P in Wa. split.
    - unfold aclientw, aclient_g. right; right; right; left. destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. clear - Wa X1 X2. lia.
    - clear - Wa O1. lia. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  (* [comment removed for export] *)
  set (src' := PM.SRC qc (de + len) (rem - len)).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M1 model1 HH1) as (_ & VIS1s & _).
  assert (BK1 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha Hb X. apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))). rewrite VIS1. exact X. }
  assert (AGO : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= os + 256 \/ os + 264 <= a) -> (a + n <= os + 280 \/ os + 296 <= a) -> L5C.agree_on M M1 a n).
  { intros a n Ha Hn X Y i Hi. apply FR1; [lia| unfold P; lia]. }
  assert (AGSH : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n).
  { intros a n Ha Hn xs Hx. unfold HeapIfaceA.S, HeapIfaceA.SB.
    assert (X8 : 0 <= xs / 8 <= 17592186044416) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    apply FR1; [lia|]. unfold P. destruct OBIG; lia. }
  assert (BLKAP : forall q m, In (q, m) (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) -> q + m <= os \/ os + 296 <= q).
  { intros q m Hq. destruct (PMASK.blk_obj_apart L ar C HI HIok _ FF LK cr Aw M _ q m os 296 HH Hq AO) as [X|X]; [left| right]; lia. }
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  assert (AGB : forall q m, In (q, m) (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) -> PMFA.agA M M1 q m).
  { intros q m Hq. destruct (BRB _ Hq) as (X0 & X1). cbn [fst snd] in X0, X1. destruct (BLKAP q m Hq) as [BF|BF]; (split; [apply AGO; lia| apply AGSH; lia]). }
  (* [comment removed for export] *)
  assert (SF1 : PM.src_fields_at RSEGS PMSPA.accA M1 os ois (ois + 16) src').
  { apply (PGSKA.src_fields_updG M M1 os ois (ois + 16) qc de rem (de + len) (rem - len) ltac:(rewrite <- (src_eta src) in SRC; exact SRC)); unfold PM.CHUNK; [lia| lia| | | | | | | | | | lia| lia| lia].
    - split; [apply AGO; lia| apply AGSH; lia].
    - apply AGSH; lia.
    - apply (L5.defined_grows M M1 _ _ MGM1). exact F256.
    - apply AGSH; lia.
    - apply (L5.defined_grows M M1 _ _ MGM1). exact DC.
    - apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| exact F264].
    - apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| exact F272].
    - apply BK1; [lia| lia| exact C280].
    - apply BK1; [lia| lia| exact C288]. }
  assert (VS1 : v8_atA M1 tb x).
  { apply (PGV8KA.v8_keepA M M1 tb x); [lia| lia| split; [apply AGO; lia| apply AGSH; lia]| | exact VS].
    intros b0 n0 c0 E. apply AGB. apply in_or_app; right; apply in_or_app; left. rewrite E. left; reflexivity. }
  assert (IA1 : PM.iss_at RSEGS AD PMSPA.accA M1 ois str sm).
  { apply (PMFA.iss_at_agreeA RSEGS AD M M1 ois str sm); [lia| lia| split; [apply AGO; lia| apply AGSH; lia]| | exact IA].
    intros c0 n0 p0 E. apply AGB. rewrite !in_app_iff. right; right; right. apply INCS. rewrite E. left; reflexivity. }
  assert (EKn : L5SAR.ek L ar LBX FF S 24576 W0 M M1).
  { apply (L5SAR.ek_piece L ar LBX FF S 24576 W0 M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
    intros a Ha CA OWx Pa. apply (OWx (os + 256, 40)); [unfold PGVWA1.W0, PGS.W_srcfG; left; reflexivity|].
    unfold L5.in_rng, P in *; cbn [fst snd] in *. lia. }
  assert (EKo : L5SAR.ek L ar (OB ++ LBX) FF S 24576 W0 M M1).
  { apply (L5SAR.ek_piece L ar (OB ++ LBX) FF S 24576 W0 M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
    intros a Ha CA OWx Pa. apply (OWx (os + 256, 40)); [unfold PGVWA1.W0, PGS.W_srcfG; left; reflexivity|].
    unfold L5.in_rng, P in *; cbn [fst snd] in *. lia. }
  assert (PA1 : PGV8.vw_at T M1 src' x g OB).
  { apply (tw_xferA M M1 src src' x x g g LK cr Aw (vml_of model) S 24576 [] PA HH); [| constructor| exact SF1| reflexivity| exact VS1| exact TBOK].
    apply (L5SAR.ahpres_of L ar (OB ++ LBX) FF S 24576 _ M M1).
    - exact EKo.
    - apply (L5.defined_grows M M1 _ _ MGM1). exact SDEF.
    - apply L5SAR.dk_grows. exact MGM1. }
  pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  assert (SO1 : st_ok M1 model1 src' x g sm cr LK Aw).
  { split; [split; [|split]|].
    - exact (L5SAR.ek_trans L ar LBX FF S 24576 W0 M0 M M1 EK EKn).
    - apply (L5SAR.dk_trans L ar LBX FF S 24576 M0 M M1 DK). apply L5SAR.dk_grows. exact MGM1.
    - exact (L5SAR.astk_grows ar M M1 S 24576 STK MGM1).
    - split; [repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| assumption])|].
      split; [exact PA1|]. split; [exact IA1|].
      split; [apply (PMASK.base_keep L ar C LY LBX FF S 24576 W0 M M1 EKn); [intros a Ha; apply outside_W0; clear - Ha FA1 FSI; lia| exact BASE]|].
      split; [exact TBOK|]. split; [exact HH1|]. split; [exact AM1|]. split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1]|].
      split; [exact ILK|]. split; [exact IAW|]. split; [exact CRL| exact CRK]. }
  apply (finish_rs fx1 R1 M1 model1 src' x g sm cr LK Aw de len); try assumption.
  - intros xr Hx. rewrite (KS1 xr) by (revert xr Hx; intros xr Hx; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
  - lia.
  - lia.
  - unfold PMSP.consumed. rewrite <- CONS0. unfold src', PM.unread. cbn [PM.sr_rem]. unfold rem. lia.
  - right. exists qc, 16384. split; [left; reflexivity| lia].
  - intros i Hi. apply MGM1. replace (de + i) with (qc + (de - qc + i)) by lia. apply DC. lia.
  - destruct SF1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CC1 & _).
    change (PM.sr_qc src') with qc in CC1. unfold PM.CHUNK in CC1. intros xr Hx. apply CC1. lia.
  - intros _. apply (PGV8.v8_room_mono x (PM.unread src sm)); [unfold src', PM.unread; cbn [PM.sr_rem]; unfold rem; lia| exact RM0].
  - apply (src_step_trans _ _ _ _ _ _ STEP). unfold src', PMSP.src_step, PM.unread. cbn [PM.sr_qc PM.sr_rem].
    split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros X; exact X| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma at_srd (fx : FPState) R M model src x g sm cr LK Aw :
  getr R (reg 1) = Z_to_bv 64 736496 ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 len -> getr R (reg 9) = Z_to_bv 64 os -> getr R (reg 18) = Z_to_bv 64 tb ->
  getr R (reg 19) = Z_to_bv 64 (os + 288) -> getr R (reg 21) = Z_to_bv 64 2147450880 ->
  getr R (reg 22) = Z_to_bv 64 ((os + 288) / 8 + 2147450880) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 tb -> getr R (reg 12) = Z_to_bv 64 len -> 1 <= len ->
  st_ok M model src x g sm cr LK Aw -> fields_eq src x g -> PMSP.src_step src0 src sm0 sm -> PM.unread src sm = PM.unread src0 sm0 -> PGV8.v8_size x = 0 ->
  PGV8.v8_room x (PM.unread src sm) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb5500 M model) K.
Proof using All.
  intros A1 A2 A8 A9 A18 A19 A21 A22 KP A10 A11 A12 Hl SO FE STEP CONS0 SZ0 ROOM.
  pose proof SO as (_ & _ & PA & IA & _).
  assert (UN : 0 <= PM.unread src sm < 2 ^ 26).
  { pose proof (tsrc M src x g PA) as (SRC & _). destruct SRC as (_ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
    pose proof (PMASK.iss_size_ltA M ois str sm IA). destruct STEP as (_ & _ & _ & _ & U1). unfold PM.unread in *. lia. }
  apply (call_srd fx R M model src x g sm cr LK Aw 736496 A1 ltac:(split; [lia| reflexivity]) A2 KP A10 A11 A12 SO ltac:(lia) SZ0 ROOM).
  intros fx2 R2 M2 model2 LK2 Aw2 src2 x2 g2 sm2 cr2 d RP2 Y10 Hd CONS2 SZ2 RM2 STEP2 SO2.
  pose proof (vpack M2 model2 src2 x2 g2 sm2 cr2 LK2 Aw2 SO2) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO2 as ((EK2 & DK2 & STK2) & SV2 & PA2 & IA2 & BASE2 & TBOK2 & HH2 & AM2 & MRT2 & ILK2 & IAW2 & CRL2 & CRK2).
  pose proof lay as LAY.
  assert (UN2 : 0 <= PM.unread src2 sm2).
  { pose proof (tsrc M2 src2 x2 g2 PA2) as (SRC & _). destruct SRC as (_ & _ & _ & _ & _ & _ & _ & _ & G2' & _).
    pose proof (PMASK.iss_size_ltA M2 ois str sm2 IA2). unfold PM.unread in *. lia. }
  assert (Hd2 : d < 2 ^ 26) by (unfold PMSP.consumed in CONS2; lia).
  assert (STEP02 : PMSP.src_step src0 src2 sm0 sm2) by exact (src_step_trans _ _ _ _ _ _ STEP STEP2).
  assert (CONS02 : PMSP.consumed src0 src2 sm0 sm2 = d) by (unfold PMSP.consumed in *; lia).
  pose proof SV2 as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72). bvr.
  pose proof (tsrc M2 src2 x2 g2 PA2) as (_ & _ & _ & VS & _).
  assert (B2 : getr R2 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (L5SAR.cs_of_preserved R R2 2%nat RP2) by inl; exact A2).
  assert (B8 : getr R2 (reg 8) = Z_to_bv 64 len) by (rewrite (L5SAR.cs_of_preserved R R2 8%nat RP2) by inl; exact A8).
  assert (B9 : getr R2 (reg 9) = Z_to_bv 64 os) by (rewrite (L5SAR.cs_of_preserved R R2 9%nat RP2) by inl; exact A9).
  assert (B18 : getr R2 (reg 18) = Z_to_bv 64 tb) by (rewrite (L5SAR.cs_of_preserved R R2 18%nat RP2) by inl; exact A18).
  assert (B19 : getr R2 (reg 19) = Z_to_bv 64 (os + 288)) by (rewrite (L5SAR.cs_of_preserved R R2 19%nat RP2) by inl; exact A19).
  assert (B21 : getr R2 (reg 21) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R R2 21%nat RP2) by inl; exact A21).
  assert (B22 : getr R2 (reg 22) = Z_to_bv 64 ((os + 288) / 8 + 2147450880)) by (rewrite (L5SAR.cs_of_preserved R R2 22%nat RP2) by inl; exact A22).
  assert (KP2 : forall xr, In xr [3; 4; 24; 25; 26; 27]%nat -> getr R2 (reg xr) = getr R0 (reg xr)).
  { intros xr Hx. rewrite (L5SAR.cs_of_preserved R R2 xr RP2) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx. }
  set (MV2 := mrestrict (ahid Aw2 model2) M2) in *.
  (* [comment removed for export] *)
  assert (HW : exists b, L5.u64_at RSEGS M2 tb b /\ L5.u64_at RSEGS M2 (tb + 8) (b + d) /\ 0 <= b <= 2 ^ 47 /\
               ((b = 0 /\ d = 0) \/ (exists c, x2 = PGV8.V8Blk b d c /\ d <= c /\ L5.defined M2 b c /\ PMSPA.accA M2 b d /\ b + c <= 2 ^ 47))).
  { destruct VS as (VD & VA & VR). destruct x2 as [|b n c]; cbn [PGV8.v8_size] in SZ2.
    - destruct VR as (W0' & W8 & W16). exists 0. split; [exact W0'|]. split; [replace (0 + d) with 0 by lia; exact W8|]. split; [lia|]. left. split; [reflexivity| lia].
    - destruct VR as (W0' & W8 & W16 & B1 & B2' & B3 & B4 & BD & BA & BN). subst n. exists b. split; [exact W0'|]. split; [exact W8|].
      pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH2 (b, c) ltac:(apply in_or_app; right; apply in_or_app; left; left; reflexivity)) as (X0 & X1). cbn [fst snd] in X0, X1.
      split; [lia|]. right. exists c. split; [reflexivity|]. split; [lia|]. split; [exact BD|]. split; [exact BA| lia]. }
  destruct HW as (b & W0' & W8 & Hb & CASES).
  assert (Hdb : 0 <= d <= 2 ^ 27) by (destruct CASES as [(-> & ->)|(c & _ & Hdc & _ & _ & Hbc)]; lia).
  LeanFeed.pfeed PP (PMARSVP.arvE_conc fx2 R2 MV2 (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => b | 40%nat => d
       | 44%nat => U 1 | 45%nat => U 8 | 46%nat => U 9 | 47%nat => U 18 | 48%nat => U 19 | 49%nat => U 20 | 50%nat => U 21 | 51%nat => U 22 | 52%nat => U 23
       | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.u64_at _ _ tb _ => unfold MV2; vis64 TAV
      | |- L5.u64_at _ _ (tb + _) _ => unfold MV2; vis64 TAV
      | |- PMARSVP.aligned _ _ => unfold PMARSVP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23).
  unfold PMSPA.cfg, PMSP.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK2 cr2 Aw2 M2 model2 fx2 fx3 R2 0xb3cf0 R3 0xb3db4 M3v K HH2 AM2 MS3 MG3 FRZ3).
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
  assert (E3 : M3 = M2) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
  assert (SO3 : st_ok M2 model3 src2 x2 g2 sm2 cr2 LK2 Aw2).
  { split; [exact (conj EK2 (conj DK2 STK2))|]. split; [exact SV2|]. split; [exact PA2|]. split; [exact IA2|]. split; [exact BASE2|].
    split; [exact TBOK2|]. split; [exact HH3|]. split; [exact AM3|]. split; [eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]|].
    split; [exact ILK2|]. split; [exact IAW2|]. split; [exact CRL2| exact CRK2]. }
  apply (finish_rs fx3 R3 M2 model3 src2 x2 g2 sm2 cr2 LK2 Aw2 b d); try assumption; try exact I; try lia.
  + intros xr Hx. rewrite (KS3 xr) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP2. exact Hx.
  + destruct CASES as [(-> & ->)|(c & -> & Hdc & BD & BA & _)]; [left; split; reflexivity| right].
    exists b, c. split; [apply in_or_app; right; apply in_or_app; left; left; reflexivity| lia].
  + destruct CASES as [(-> & ->)|(c & -> & Hdc & BD & BA & _)]; [intros i Hi; lia| apply (L5.defined_sub M2 b c b d BD); lia].
  + destruct CASES as [(-> & ->)|(c & -> & Hdc & BD & BA & _)]; [intros i Hi; lia| exact BA].
Qed.

End Call.
End WithHeap.
End PGSRVA2.
