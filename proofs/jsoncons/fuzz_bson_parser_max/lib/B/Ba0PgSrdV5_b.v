(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs PmTxtSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcRead1_b PnAReset1_b PnASrdVP_b Ba0_code_b3dd8_b3ddc_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PgTxtKitA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgV8A_b PgV8KitA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b Ba0PgVw1_b Ba0PgSrdV1_b Ba0PgSrdV2_b Ba0PgSrdV3_b Ba0PgSrdV4_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGSSVA5.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PMA.AD.
Abbreviation pot := PGVWA1.pot.
Abbreviation v8_atA := (PGV8.v8_at RSEGS PMSPA.accA PGV8A.annA).
Ltac bvr1 R x := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R (reg x))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac vis64 AV := lazymatch goal with |- L5.u64_at ?sg (mrestrict ?H ?M) ?a ?v =>
  apply (proj2 (L5A.u64_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac vis8 AV := lazymatch goal with |- L5.u8_at ?sg (mrestrict ?H ?M) ?a ?v =>
  apply (proj2 (L5A.u8_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.
Lemma subw (x k : Z) : 0 <= x <= k -> k < 2 ^ 64 -> ((((k + ((18446744073709551615 * x) mod 2 ^ 64)) mod 2 ^ 64) - 0) mod 2 ^ 64) = k - x.
Proof.
  intros H1 H2. rewrite Z.sub_0_r, Z.mod_mod by lia. rewrite Zplus_mod_idemp_r.
  replace (k + 18446744073709551615 * x) with ((k - x) + x * 2 ^ 64) by lia. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma modneg (x : Z) : - 2 ^ 64 < x < 0 -> x mod 2 ^ 64 = x + 2 ^ 64.
Proof. intros H. symmetry. apply (Z.mod_unique x (2 ^ 64) (-1)); lia. Qed.
Lemma mod_lt1 (x : Z) : - 2 ^ 64 < x <= 0 -> x mod 2 ^ 64 < 1 -> x = 0.
Proof. intros H1 H2. destruct (Z.eq_dec x 0) as [E|NE]; [exact E|]. rewrite modneg in H2 by lia. lia. Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.
#[local] Abbreviation perm_v8 := (PGVWA1.perm_v8 L ar C HI HIok).
#[local] Abbreviation perm_v8_back := (PGVWA1.perm_v8_back L ar C HI HIok).
#[local] Abbreviation ek_drop := (PGVWA1.ek_drop L ar).
#[local] Abbreviation dk_drop := (PGVWA1.dk_drop L ar).

Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (S r len : Z) (T : PGV8.vowner) (OB : list (Z * Z)) (src0 : PM.srcst) (x0 : PGV8.v8) (g0 : Z) (str : PM.vstr) (sm0 : PM.strm).
(* [comment removed for export] *)
#[local] Abbreviation os := (PGVWA1.os T).
#[local] Abbreviation ois := (PGVWA1.ois T).
#[local] Abbreviation tb := (PGVWA1.tb T).
#[local] Abbreviation lo := (PGVWA1.lo T).
#[local] Abbreviation hi := (PGVWA1.hi T).
Hypothesis TOK : PGV8A.vowner_ok RSEGS AD L ar HI T.
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis K0 : K [].
Hypothesis FRM0 : PGSA.ffroomB PNRA.FCB 5 FF LK0.
Hypothesis FRS : PMSPA.ffrsA FF S.
Hypothesis OFR : PGSA.ofr FF lo hi.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UN0 : PM.unread src0 sm0 < 2 ^ 26.
Hypothesis SZ0 : PGV8.v8_size x0 = 0.
Hypothesis ROOM0 : PGV8.v8_room x0 (PM.unread src0 sm0).
Hypothesis STKSH0 : shadow_zero M0 (S - 22528) 2816.
Hypothesis RSZ : PGV8A.vu8_resize_spec RSEGS AD L ar HI PNRA.FCB (PNL.pn_vu8_resize PMA.AN).
Hypothesis SRD : PGSA.src_read_specG RSEGS AD L ar HI PNRA.FCB.
Hypothesis FBT : PGSA.fill_buffer_tb_specG RSEGS AD L ar HI PNRA.FCB.
(* [comment removed for export] *)
#[local] Abbreviation W0 := (PGVWA1.W0 T).
#[local] Abbreviation lay := (PGVWA1.lay L ar HI T TOK).
#[local] Abbreviation tsrc := (PGVWA1.tsrc L ar HI T OB TOK).
#[local] Abbreviation aobjs := (PGVWA1.aobjs L ar HI FF T TOK OFR).
#[local] Abbreviation inW_W0 := (PGVWA1.inW_W0 T).
#[local] Abbreviation outside_W0 := (PGVWA1.outside_W0 L ar HI T TOK).
#[local] Abbreviation frame_app := (PGVWA1.frame_app L ar C HI LY HIok FF T TOK OFR).
#[local] Abbreviation wapp_W0 := (PGVWA1.wapp_W0 L ar C HI LY HIok FF T TOK OFR).
#[local] Abbreviation tw_xferA := (PGVWA1.tw_xferA L ar C HI HIok LBX FF T OB TOK OFR).
#[local] Abbreviation stw_ok := (PGVWA1.stw_ok L ar C HI LY HIok T TOK).
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
                         (src' : PM.srcst) (x' : PGV8.v8) (g' : Z) (sm' : PM.strm) (cr' : credit) (d : Z),
  regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
  PMSP.consumed src0 src' sm0 sm' = d -> PGV8.v8_size x' = d ->
  (d = len -> PGV8.v8_room x' (PM.unread src' sm')) ->
  PGV8.vw_at T M' src' x' g' OB -> PM.iss_at RSEGS AD PMSPA.accA M' ois str sm' ->
  PMSP.src_step src0 src' sm0 sm' ->
  L5CA.ahpres L ar LBX FF S (PMSPA.pm_scr 5) W0 M0 M' ->
  PMSP.credit_keep cr0 cr' (pot L ar x0 g0) (pot L ar x' g') ->
  model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' ->
  ri_inv HI (PM.src_own src' ++ PGV8.v8_own x' ++ OB ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

#[local] Abbreviation fields_eq := PGSSVA1.fields_eq.
#[local] Abbreviation vdst := PGSSVA1.vdst.
#[local] Abbreviation U := (PGSSVA1.U R0).
#[local] Abbreviation saves13 := (PGSSVA1.saves13 R0 S).
#[local] Abbreviation locals := (PGSSVA1.locals S len T).
#[local] Abbreviation kept_rs := (PGSSVA1.kept_rs R0).
#[local] Abbreviation memrel := (PGSSVA1.memrel L ar M0 LBX FF S T OB).
#[local] Abbreviation vroom := (PGSSVA1.vroom len src0 sm0).
#[local] Abbreviation acct := (PGSSVA1.acct len src0 sm0).
#[local] Abbreviation st_ok := (PGSSVA1.st_ok L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S len T OB x0 g0 str).
#[local] Abbreviation lregs := (PGSSVA1.lregs R0 S T).
#[local] Abbreviation lstate := (PGSSVA1.lstate L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S len T OB src0 x0 g0 str sm0).
#[local] Abbreviation IHt := (PGSSVA1.IHt L ar HI R0 M0 model0 K LBX FF LK0 Aw0 cr0 S len T OB src0 x0 g0 str sm0).
#[local] Abbreviation lregs_keep := (PGSSVA1.lregs_keep R0 S len T Hlen).
#[local] Abbreviation lregs_set := (PGSSVA1.lregs_set R0 S len T Hlen).
#[local] Abbreviation lregs_pres := (PGSSVA1.lregs_pres R0 S len T Hlen).
#[local] Abbreviation grow_ok_now := (PGSSVA1.grow_ok_now L ar HI len T OB src0 sm0 TOK Hlen UN0).
#[local] Abbreviation vroom_after := (PGSSVA1.vroom_after L ar HI len T OB src0 sm0 TOK Hlen).
#[local] Abbreviation finish := (PGSSVA1.finish L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 SZ0 ROOM0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation callee_mem := (PGSSVA1.callee_mem L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 SZ0 ROOM0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation centry := (PGSSVA1.centry L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 SZ0 ROOM0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation call_resize := (PGSSVA1.call_resize L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 SZ0 ROOM0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation call_srcread := (PGSSVA1.call_srcread L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 SZ0 ROOM0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation call_fillv := (PGSSVA1.call_fillv L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 SZ0 ROOM0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation unread_nn := (PGSSVA1.unread_nn L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 SZ0 ROOM0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation vpack := (PGSSVA1.vpack L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 SZ0 ROOM0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation ro_step := (PGSSVA1.ro_step L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 SZ0 ROOM0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation fr_step := (PGSSVA1.fr_step L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 SZ0 ROOM0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation after_shrink := (PGSSVA2.after_shrink L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 SZ0 ROOM0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation after_read := (PGSSVA2.after_read L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 SZ0 ROOM0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation rpath := (PGSSVA3.rpath L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 SZ0 ROOM0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation dpath := (PGSSVA4.dpath L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 SZ0 ROOM0 STKSH0 RSZ SRD FBT KONT).
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat; bvr1 R0 23%nat; bvr1 R0 24%nat; bvr1 R0 25%nat; bvr1 R0 26%nat; bvr1 R0 27%nat.

Ltac ks_tac KS := intros xr Hx; apply KS; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx.
Ltac kp_tac KS KP := intros xr Hx; rewrite (KS xr) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx); apply KP; exact Hx.

Lemma src_step_refl a sa : PMSP.src_step a a sa sa.
Proof. unfold PMSP.src_step. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros X; exact X| lia]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma head mu0 (IH : IHt mu0) (fx : FPState) R M model src x g sm cr LK Aw (w : Z) :
  lstate R M model src x g sm cr LK Aw w -> PM.mu_src src sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb55a0 M model) K.
Proof using All.
  intros LS MU. pose proof LS as (LR & SO & AC & Hw & A10).
  pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A26 & A27 & A25 & KP).
  pose proof (unread_nn M model src x g sm cr LK Aw SO) as (UN & ST & RM & GE).
  pose proof (vpack M model src x g sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & _).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
  pose proof LC as (L136 & L128 & L120 & L112).
  pose proof lay as LAY.
  assert (D1 : S - 160 + 160 <= os \/ os + 296 <= S - 160) by (right; lia).
  assert (D2 : S - 160 + 160 <= tb \/ tb + 24 <= S - 160) by (right; lia).
  assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (clear - LAY; lia).
  bvr.
  pose proof (tsrc M src x g PA) as (SRC & _).
  destruct SRC as (F240 & _ & _ & _ & F272 & _ & F288 & _).
  change PM.CHUNK with 16384 in F272, RM.
  pose proof aobjs as (_ & AOI0 & _). destruct (frame_app _ _ _ _ _ _ HH) as (FA1 & FA2 & FA3 & FA4 & FA5).
  pose proof (PGSKA.iss_visG L ar C HI LY HIok _ FF LK cr Aw M model ois str sm S 22528 HH AOI0 ltac:(clear - LAY; lia) IA STK) as ((I1 & I8 & INSH) & Zis & IWR & ICE & IVIS & AOI).
  pose proof (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ FF LK cr Aw M model 0x135118 1 HH ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as ZOT.
  assert (D4 : S - 160 + 160 <= ois \/ ois + 272 <= S - 160) by (right; clear - LAY FA5 SLO; lia).
  assert (D5 : os + 296 <= ois \/ ois + 272 <= os) by (clear - LAY; lia).
  assert (D6 : tb + 24 <= ois \/ ois + 272 <= tb) by (clear - LAY; lia).
  set (MV := mrestrict (ahid Aw model) M) in *.
  destruct (Z.eq_dec (PM.sr_rem src) 0) as [RZ|RNZ].
  - (* [comment removed for export] *)
    rewrite RZ in F288.
    pose proof IA as (I0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IOS & _).
    cbn [pa_vp_iss PMA.AD ADDR_A] in I0.
    destruct IOS as (_ & U32 & _).
    pose proof (PMTK2.u8_of_u32 RSEGS M (ois + 120 + 32) (PM.sm_st sm) ltac:(lia) U32) as B152.
    rewrite Z.mod_small in B152 by lia.
    replace (ois + 120 + 32) with (ois + 152) in B152 by lia.
    assert (STR : 0 <= PM.sm_st sm <= 2) by lia.
    LeanFeed.pfeed PP (PMASRVP.asvH0_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
       | 45%nat => ois | 62%nat => PM.sm_st sm
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
      | |- L5.u64_at _ _ ois _ => unfold MV; vis64 IVIS
      | |- L5.u8_at _ _ (ois + _) _ => unfold MV; vis8 IVIS
      | |- PMASRVP.aligned _ _ => unfold PMASRVP.aligned; lia
      | |- _ => lia end]).
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & [(MS1 & KS1 & E1 & E10 & E11 & E12 & E13 & E23 & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19)
                 | [(MS1 & KS1 & E1 & E10 & E11 & E12 & E13 & E23 & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19)
                 | (MS1 & KS1 & E1 & E2 & E8 & E9 & E10 & E11 & E12 & E13 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18)]]).
    + (* [comment removed for export] *)
      apply (fr_step fx fx1 R 0xb55a0 R1 0xb55e0 M model src x g sm cr LK Aw M1v SO MS1 MG1 FRZ1 ltac:(repeat split; assumption) ltac:(repeat split; assumption)). intros M1 model1 SO1.
      assert (ST0 : PM.sm_st sm = 0) by (destruct ST as [E|E]; [exact E| rewrite E in C1; vm_compute in C1; discriminate]).
      apply (rpath mu0 IH fx1 R1 M1 model1 src x g sm cr LK Aw w w); try assumption.
      * apply (lregs_keep R R1 w LR). ks_tac KS1.
      * lia.
      * unfold PM.CHUNK. Lia.lia.
      * lia.
      * right. exact ST0.
    + (* [comment removed for export] *)
      apply (fr_step fx fx1 R 0xb55a0 R1 0xb5644 M model src x g sm cr LK Aw M1v SO MS1 MG1 FRZ1 ltac:(repeat split; assumption) ltac:(repeat split; assumption)). intros M1 model1 SO1.
      assert (ST0 : PM.sm_st sm = 0) by (destruct ST as [E|E]; [exact E| rewrite E in C1; vm_compute in C1; discriminate]).
      apply (dpath mu0 IH fx1 R1 M1 model1 src x g sm cr LK Aw w); try assumption.
      * apply (lregs_keep R R1 w LR). ks_tac KS1.
      * lia.
    + (* [comment removed for export] *)
      apply (fr_step fx fx1 R 0xb55a0 R1 0xb570c M model src x g sm cr LK Aw M1v SO MS1 MG1 FRZ1 ltac:(repeat split; assumption) ltac:(repeat split; assumption)). intros M1 model1 SO1.
      apply (finish fx1 R1 M1 model1 src x g sm cr LK Aw w); try assumption.
      all: first [ solve [intros xr Hx; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [assumption|]); destruct Hx] | solve [kp_tac KS1 KP]
                 | solve [rewrite E10; f_equal; lia] | lia ].
  - (* [comment removed for export] *)
    assert (F256 : True) by exact I.
    LeanFeed.pfeed PP (PMASRVP.asvH1_conc fx R MV (fun j => match j with 2%nat => S | 33%nat => PM.sr_rem src | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
      | |- L5.u64_at _ _ ois _ => unfold MV; vis64 IVIS
      | |- L5.u8_at _ _ (ois + _) _ => unfold MV; vis8 IVIS
      | |- PMASRVP.aligned _ _ => unfold PMASRVP.aligned; lia
      | |- _ => lia end]).
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & [(MS1 & KS1 & E1 & E10 & E11 & E12 & E13 & E23 & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18)
                 | (MS1 & KS1 & E1 & E10 & E11 & E12 & E13 & E23 & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18)]);
      apply (fr_step fx fx1 R 0xb55a0 R1 0xb55e0 M model src x g sm cr LK Aw M1v SO MS1 MG1 FRZ1 ltac:(repeat split; assumption) ltac:(repeat split; assumption)); intros M1 model1 SO1.
    + apply (rpath mu0 IH fx1 R1 M1 model1 src x g sm cr LK Aw w w); try assumption.
      * apply (lregs_keep R R1 w LR). ks_tac KS1.
      * lia.
      * unfold PM.CHUNK. Lia.lia.
      * lia.
      * left. lia.
    + apply (rpath mu0 IH fx1 R1 M1 model1 src x g sm cr LK Aw w 16384); try assumption.
      * apply (lregs_keep R R1 w LR). ks_tac KS1.
      * lia.
      * unfold PM.CHUNK. Lia.lia.
      * lia.
      * left. lia.
Qed.

(* [comment removed for export] *)
Lemma loop (n : nat) : forall (fx : FPState) R M model src x g sm cr LK Aw w,
  (Z.to_nat (PM.mu_src src sm) < n)%nat -> lstate R M model src x g sm cr LK Aw w ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb55a0 M model) K.
Proof using All.
  induction n as [|n IHn]; intros fx R M model src x g sm cr LK Aw w Hn LS; [lia|].
  assert (IHm : IHt (PM.mu_src src sm)).
  { intros fx' R' M' model' src' x' g' sm' cr' LK' Aw' w' Hlt LS'. apply (IHn fx' R' M' model' src' x' g' sm' cr' LK' Aw' w'); [|exact LS'].
    pose proof LS' as (_ & SO' & _). pose proof (unread_nn _ _ _ _ _ _ _ _ _ SO') as (UN' & _).
    assert (0 <= PM.mu_src src' sm') by (unfold PM.mu_src; destruct (Z.eqb _ _); lia). lia. }
  exact (head _ IHm fx R M model src x g sm cr LK Aw w LS ltac:(lia)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma entry_ok (fx : FPState) :
  ri_inv HI (PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX) FF LK0 cr0 Aw0 M0 (vml_of model0) -> L5CA.amodel_ok Aw0 model0 -> L5CA.astk ar M0 S 22528 ->
  getr R0 (reg 10) = Z_to_bv 64 os -> getr R0 (reg 11) = Z_to_bv 64 tb -> getr R0 (reg 12) = Z_to_bv 64 len ->
  PGV8.vw_at T M0 src0 x0 g0 OB -> PM.iss_at RSEGS AD PMSPA.accA M0 ois str sm0 -> PMSTA.base_okA RSEGS AD M0 ->
  PGV8.v8_ok x0 g0 -> PMSPA.credit_le (pot L ar x0 g0) cr0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R0 0xb5500 M0 model0) K.
Proof using All.
  intros HH AM STK A10 A11 A12 PA IA BASE TBOK CRL.
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof lay as LAY. pose proof aobjs as (AO0 & AOI0 & AT0). destruct (frame_app _ _ _ _ _ _ HH) as (FA1 & FA2 & FA3 & FA4 & FA5).
  pose proof (tsrc M0 src0 x0 g0 PA) as (PSF & PNI & PD & VS & _).
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 HH BASE) as (V0 & V1 & V2).
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 S 22528 160 HH STK ltac:(lia)) as (SL80 & SH80 & V3).
  pose proof (PGSKA.src_visG L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 os _ _ src0 S 22528 HH AO0 ltac:(clear - LAY; lia) PSF PNI STK)
    as ((O1 & O8 & OBIG) & OZ & OW & OCE & OAV & _ & OFS1 & OFS2).
  pose proof (PGV8KA.v8_visG L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 tb x0 HH AT0 ltac:(clear - LAY; lia) VS)
    as ((T1 & T8 & TBIG) & TZ & TW & TCE & TAV & _ & TFS1 & TFS2).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  unfold app_mem, FS_BYTES in FSAPP, FSCEIL, OFS1, OFS2, TFS1, TFS2.
  assert (D1 : S - 160 + 160 <= os \/ os + 296 <= S - 160) by (right; clear - LAY FA5 SLO; lia).
  assert (D2 : S - 160 + 160 <= tb \/ tb + 24 <= S - 160) by (right; clear - LAY FA5 SLO; lia).
  assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (clear - LAY; lia).
  set (MV := mrestrict (ahid Aw0 model0) M0) in *.
  LeanFeed.pfeed PP (PMASRVP.asvA_conc fx R0 MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- PMASRVP.aligned _ _ => unfold PMASRVP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & EX).
  set (P := fun a => S - 160 <= a < S - 160 + 160).
  assert (FZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) by (intros a Ha N; apply FRZ1; [exact Ha| exact N]).
  assert (WOB : forall a, 0 <= a < 2 ^ 64 -> P a -> aclientw L ar (PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX) FF 0 0 a /\ ~ (0x10000 <= a < 0x696000)).
  { intros a Ha Wa. unfold P in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| lia]. }
  (* [comment removed for export] *)
  assert (POST0 : forall M1 model1, ri_inv HI (PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX) FF LK0 cr0 Aw0 M1 (vml_of model1) ->
                   mrestrict (ahid Aw0 model0) M1 = M1v -> mem_grows M0 M1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
                   memrel M1 /\ PGV8.vw_at T M1 src0 x0 g0 OB /\ PM.iss_at RSEGS AD PMSPA.accA M1 ois str sm0 /\ PMSTA.base_okA RSEGS AD M1).
  { intros M1 model1 HH1 VIS1 MGM1 FR1.
    assert (EKn : L5SAR.ek L ar (OB ++ LBX) FF S 22528 W0 M0 M1).
    { apply (PGVWA1.ek_drop L ar (PM.src_own src0 ++ PGV8.v8_own x0)). rewrite <- PGVWA1.own2.
      apply (L5SAR.ek_piece L ar _ FF S 22528 W0 M0 M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. unfold P in Pa.
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 _ S 22528 a HH SPT CA) as [X|X]; lia. }
    pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
    assert (EKp : L5SAR.ek L ar (PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX) FF S 22528 [] M0 M1).
    { apply (L5SAR.ek_piece L ar _ FF S 22528 [] M0 M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. unfold P in Pa.
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 _ S 22528 a HH SPT CA) as [X|X]; lia. }
    assert (QIN : In (PM.sr_qc src0, PM.CHUNK) (PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX)) by (left; reflexivity).
    destruct (BRB _ QIN) as (QB0 & QB1). cbn [fst snd] in QB0, QB1. unfold PM.CHUNK in QB1.
    split; [split; [|split]|].
    - exact EKn.
    - apply L5SAR.dk_grows. exact MGM1.
    - exact (L5SAR.astk_grows ar M0 M1 S 22528 STK MGM1).
    - split.
      { apply (tw_xferA M0 M1 src0 src0 x0 x0 g0 g0 LK0 cr0 Aw0 (vml_of model0) S 22528 [] PA HH); [| constructor| | reflexivity| | exact TBOK].
        - apply (L5SAR.ahpres_of L ar (OB ++ LBX) FF S 22528 _ M0 M1); [exact EKn| apply (L5.defined_grows M0 M1 _ _ MGM1); exact SDEF| apply L5SAR.dk_grows; exact MGM1].
        - apply (PGSKA.src_fields_keepG M0 M1 os ois (ois + 16) src0 PSF); [clear - O1; lia| clear - O1; lia| | |].
          + apply (PMKA.agA_obj L ar _ FF S 22528 [] M0 M1 EKp PMKA.wapp_nil FRB os 296 AO0). intros i _ r0 [].
          + apply (PMASK.agsh_blk L ar _ FF S 22528 [] M0 M1 _ _ EKp PMKA.wapp_nil QIN); [clear - QB0; lia| unfold PM.CHUNK; clear - QB1; lia].
          + apply (L5.defined_grows M0 M1 _ _ MGM1). destruct PSF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DCH & _). exact DCH.
        - apply (PGV8KA.v8_keepA M0 M1 tb x0); [clear - LAY; lia| clear - LAY; lia| apply (PMKA.agA_obj L ar _ FF S 22528 [] M0 M1 EKp PMKA.wapp_nil FRB tb 24 AT0); intros i _ r0 []| | exact VS].
          intros b0 n0 c0 E. apply (PMKA.agA_blk L ar _ FF S 22528 [] M0 M1 EKp PMKA.wapp_nil BRB b0 c0); [apply in_or_app; right; apply in_or_app; left; rewrite E; left; reflexivity| intros i _ r0 []]. }
      split.
      { apply (PMKA.iss_keepA RSEGS AD L ar _ FF S 22528 [] M0 M1 EKp PMKA.wapp_nil FRB BRB _ _ _ AOI0); [| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA].
        intros xr Hx. rewrite !in_app_iff. right; right; right. apply INCS. exact Hx. }
      apply (PMASK.base_keep L ar C LY (OB ++ LBX) FF S 22528 W0 M0 M1 EKn); [| exact BASE].
      intros a Ha. apply outside_W0. pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH). clear - Ha FA1 LAY. lia. }
  assert (POST : forall M1 model1, ri_inv HI (PM.src_own src0 ++ PGV8.v8_own x0 ++ OB ++ LBX) FF LK0 cr0 Aw0 M1 (vml_of model1) -> L5CA.amodel_ok Aw0 model1 -> model_rt model0 model1 ->
                   mrestrict (ahid Aw0 model0) M1 = M1v -> mem_grows M0 M1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
                   saves13 M1v -> locals M1v -> st_ok M1 model1 src0 x0 g0 sm0 cr0 LK0 Aw0).
  { intros M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1 SVv LCv.
    destruct (POST0 M1 model1 HH1 VIS1 MGM1 FR1) as (MR1 & PA1 & IA1 & BASE1).
    pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 HH) as (_ & VIS & _).
    assert (BK : forall k v, 8 <= k <= 160 -> L5.u64_at RSEGS M1v (S - k) v -> L5.u64_at RSEGS M1 (S - k) v).
    { intros k v Hk X. apply (proj1 (L5A.u64_at_vis (ahid Aw0 model0) M1 (S - k) v (VIS (S - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact X. }
    split; [exact MR1|].
    split.
    { destruct SVv as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
      repeat split; (apply BK; [lia| assumption]). }
    split.
    { destruct LCv as (L136 & L128 & L120 & L112).
      repeat split; (apply BK; [lia| assumption]). }
    split; [exact PA1|]. split; [exact IA1|]. split; [exact BASE1|].
    split; [exact TBOK|]. split; [exact HH1|]. split; [exact AM1|]. split; [exact MRT1|].
    split; [apply incl_refl|]. split; [apply incl_refl|]. split; [exact CRL|].
    unfold PMSPA.credit_keep. lia. }
  bvr.
  assert (FE0 : fields_eq src0 x0 g0) by (unfold PGSSVA1.fields_eq; exact I).
  assert (VR0 : vroom x0).
  { pose proof ROOM0 as RM0. unfold PGSSVA1.vroom. clear - RM0. destruct x0 as [|b0 n0 c0]; [exact I|]. cbn in RM0.
    destruct RM0 as (a0 & j & Hj & Hc & Ha0 & Hu). exists a0, j. split; [exact Hj|]. split; [exact Hc|]. split; [exact Ha0|]. left. exact Hu. }
  assert (AC0 : forall w, w = len -> acct src0 x0 g0 sm0 w).
  { intros w ->. unfold PGSSVA1.acct, PMSP.consumed, PMSP.src_step. split; [lia|]. split; [rewrite SZ0; lia|].
    split; [split; [reflexivity|]; split; [reflexivity|]; split; [lia|]; split; [intros X; exact X| lia]|]. split; [exact VR0| left; reflexivity]. }
  unfold PMSPA.cfg, PMSP.cfg.
  destruct EX as [(MS & KS1 & E2 & E8 & E9 & E11 & E13 & E18 & E19 & E20 & E21 & E25 & E26 & E27 & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17)
                 | (MS & KS1 & E10 & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14)].
  - (* [comment removed for export] *)
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xb5500 R1 0xb55a0 M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    pose proof (POST M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1 ltac:(repeat split; assumption) ltac:(repeat split; assumption)) as SO1.
    rewrite Z.sub_0_r, Z.mod_small in C3 by lia.
    pose proof (unread_nn M1 model1 src0 x0 g0 sm0 cr0 LK0 Aw0 SO1) as (UN & _).
    apply (loop (Nat.succ (Z.to_nat (PM.mu_src src0 sm0))) fx1 R1 M1 model1 src0 x0 g0 sm0 cr0 LK0 Aw0 len); [apply Nat.lt_succ_diag_r|].
    split; [|split; [exact SO1| split; [exact (AC0 len eq_refl)| split; [lia| rewrite (KS1 10%nat) by inl; exact A10]]]].
    unfold PGSSVA1.lregs. do 10 (split; [assumption|]).
    intros xr Hx. rewrite (KS1 xr) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). reflexivity.
  - (* [comment removed for export] *)
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xb5500 R1 0xb570c M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    assert (L0 : len = 0) by (rewrite Z.sub_0_r, Z.mod_small in C0 by lia; lia).
    (* [comment removed for export] *)
    destruct (POST0 M1 model1 HH1 VIS1 MGM1 FR1) as ((EK1 & DK1 & STK1) & PA1 & IA1 & BASE1).
    pose proof RAok as (Hr1 & Hr2).
    assert (RA : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra0).
    apply (PMASK.ret_exit L ar C HI LY HIok fx1 R1 M1 model1 K _ FF LK0 cr0 Aw0 0xb570c r W_b3dd8 HH1 AM1 F_b3dd8 eq_refl D_b3dd8 RA ltac:(lia) Hr2).
    intros model2 MRT2 AM2 HH2.
    apply (KONT fx1 R1 M1 model2 LK0 Aw0 src0 x0 g0 sm0 cr0 0).
    + apply L5SAR.preserved_by_index. intros xr Hx. unfold L5SAR.cs_all in Hx.
      rewrite (KS1 xr) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). reflexivity.
    + rewrite L5K.rl10, E10. f_equal. lia.
    + lia.
    + unfold PMSP.consumed. lia.
    + exact SZ0.
    + intros _. exact ROOM0.
    + exact PA1.
    + exact IA1.
    + apply src_step_refl.
    + change (PMSPA.pm_scr 5) with 22528. apply (L5SAR.ahpres_of L ar LBX FF S 22528 _ M0 M1 (PGVWA1.ek_drop L ar OB LBX FF S 22528 W0 M0 M1 EK1)); [destruct STK1 as (_ & _ & _ & _ & D & _); exact D| exact (PGVWA1.dk_drop L ar OB LBX FF S 22528 M0 M1 DK1)].
    + unfold PMSP.credit_keep. lia.
    + eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT2].
    + apply incl_refl.
    + apply incl_refl.
    + exact AM2.
    + exact HH2.
Qed.

End Call.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem srd_read_v_okG : PGV8A.vu8_resize_spec RSEGS AD L ar HI PNRA.FCB (PNL.pn_vu8_resize PMA.AN) -> PGSA.src_read_specG RSEGS AD L ar HI PNRA.FCB ->
  PGSA.fill_buffer_tb_specG RSEGS AD L ar HI PNRA.FCB ->
  PGV8A.srd_read_v_specG RSEGS AD L ar HI PNRA.FCB (PNL.pn_srd_read_v PMA.AN).
Proof.
  intros RSZ SRD FBT T TOK. unfold PGV8A.srd_read_v_specG.
  intros fx R M model K OB LBX FF LK Aw cr sp r len src x g str sm HH AM K0 ENT FRM FRS OFR A10 A11 A12 Hlen PA IA BASE INCS UN SZ ROOM CRL KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 5) with 22528 in *. change (22528 / 8) with 2816 in STKSH.
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5SAR.r11 in A11. rewrite L5SAR.r12 in A12.
  cbn [PNL.pn_srd_read_v PMA.AN NADDR_A].
  pose proof (PGV8A.vo_src _ _ _ _ _ _ TOK M src x g OB PA) as (_ & _ & _ & _ & TB).
  exact (entry_ok R M model K LBX FF LK Aw cr sp r len T OB src x g str sm TOK Rra RAok Rsp Rgp Rtp K0 FRM FRS OFR Hlen INCS UN SZ ROOM STKSH RSZ SRD FBT KONT fx HH AM ASTK A10 A11 A12 PA IA BASE TB CRL).
Qed.

End WithHeap.
End PGSSVA5.
