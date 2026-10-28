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
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcRead1_b PnAReset1_b PnASrdVP_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PgTxtKitA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgV8A_b PgV8KitA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b Ba0PgVw1_b Ba0PgSrdV1_b Ba0PgSrdV2_b Ba0PgSrdV3_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGSSVA4.
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
#[local] Abbreviation after_shrink := (PGSSVA2.after_shrink L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 SZ0 ROOM0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation after_read := (PGSSVA2.after_read L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 x0 g0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UN0 SZ0 ROOM0 STKSH0 RSZ SRD FBT KONT).
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat; bvr1 R0 23%nat; bvr1 R0 24%nat; bvr1 R0 25%nat; bvr1 R0 26%nat; bvr1 R0 27%nat.

Ltac ks_tac KS := intros xr Hx; apply KS; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx.
Ltac kp_tac KS KP := intros xr Hx; rewrite (KS xr) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx); apply KP; exact Hx.

Lemma src_eta (src : PM.srcst) : PM.SRC (PM.sr_qc src) (PM.sr_de src) (PM.sr_rem src) = src.
Proof. destruct src; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pos_step (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) M model src x g sm cr LK Aw (M1v : word -> option byte) :
  st_ok M model src x g sm cr LK Aw ->
  msteps RSEGS (L5SAR.st fx R pc (mrestrict (ahid Aw model) M)) (L5SAR.st fx1 R1 pc1 M1v) ->
  mem_grows (mrestrict (ahid Aw model) M) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (os + 256 <= a < os + 256 + 8) -> M1v (Z_to_bv 64 a) = mrestrict (ahid Aw model) M (Z_to_bv 64 a)) ->
  (forall M1 model1, st_ok M1 model1 src x g sm cr LK Aw -> srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 pc1 M1 model1) K) ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R pc M model) K.
Proof using All.
  intros SO MS MG FRZ NEXT.
  pose proof (vpack M model src x g sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as ((EK & DK & STK) & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof lay as LAY. pose proof aobjs as (_ & AOI & _).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  pose proof (tsrc M src x g PA) as (PSF & PNI & PD & VS & _).
  pose proof PSF as (F240 & F248 & F256 & F264 & F272 & F280 & F288 & G1 & G2 & G3 & G4 & DC & CC & C240).
  set (P := fun a => os + 256 <= a < os + 256 + 8).
  unfold PMSPA.cfg, PMSP.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R pc R1 pc1 M1v P K HH AM MS MG).
  { intros a Ha N. apply FRZ; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold P in Wa. split.
    - unfold aclientw, aclient_g. right; right; right; left. destruct AO as (f & Hf & X1 & X2). exists f. split; [exact Hf|]. clear - Wa X1 X2. lia.
    - clear - Wa O1. lia. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  apply NEXT.
  assert (AGO : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= os + 256 \/ os + 264 <= a) -> L5C.agree_on M M1 a n).
  { intros a n Ha Hn X i Hi. apply FR1; [lia| unfold P; lia]. }
  assert (AGSH : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n).
  { intros a n Ha Hn xs Hx. unfold HeapIfaceA.S, HeapIfaceA.SB.
    assert (X8 : 0 <= xs / 8 <= 17592186044416) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    apply FR1; [lia|]. unfold P. destruct OBIG; lia. }
  assert (BLKAP : forall q m, In (q, m) (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) -> q + m <= os \/ os + 296 <= q).
  { intros q m Hq. destruct (PMASK.blk_obj_apart L ar C HI HIok _ FF LK cr Aw M _ q m os 296 HH Hq AO) as [X|X]; [left| right]; lia. }
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  assert (AGB : forall q m, In (q, m) (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX) -> PMFA.agA M M1 q m).
  { intros q m Hq. destruct (BRB _ Hq) as (X0 & X1). cbn [fst snd] in X0, X1. destruct (BLKAP q m Hq) as [BF|BF]; (split; [apply AGO; lia| apply AGSH; lia]). }
  assert (QIN : In (PM.sr_qc src, PM.CHUNK) (PM.src_own src ++ PGV8.v8_own x ++ OB ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  destruct (BRB _ QIN) as (QB0 & QB1). cbn [fst snd] in QB0, QB1. unfold PM.CHUNK in QB1.
  (* [comment removed for export] *)
  assert (SF1 : PM.src_fields_at RSEGS PMSPA.accA M1 os ois (ois + 16) src).
  { pose proof PSF as PSF0. rewrite <- (src_eta src) in PSF0. rewrite <- (src_eta src).
    apply (PGSKA.src_fields_updG M M1 os ois (ois + 16) _ _ _ (PM.sr_de src) (PM.sr_rem src) PSF0);
      [lia| lia| | | | | | | | | | exact G1| exact G2| exact G3].
    - split; [apply AGO; lia| apply AGSH; lia].
    - apply AGSH; lia.
    - apply (L5.defined_grows M M1 _ _ MGM1). exact F256.
    - unfold PM.CHUNK. apply AGSH; lia.
    - apply (L5.defined_grows M M1 _ _ MGM1). exact DC.
    - apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| exact F264].
    - apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| exact F272].
    - apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| exact F280].
    - apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| exact F288]. }
  (* [comment removed for export] *)
  assert (VS1 : v8_atA M1 tb x).
  { apply (PGV8KA.v8_keepA M M1 tb x); [lia| lia| split; [apply AGO; lia| apply AGSH; lia]| | exact VS].
    intros b0 n0 c0 E. apply AGB. apply in_or_app; right; apply in_or_app; left. rewrite E. left; reflexivity. }
  (* [comment removed for export] *)
  assert (IA1 : PM.iss_at RSEGS AD PMSPA.accA M1 ois str sm).
  { apply (PMFA.iss_at_agreeA RSEGS AD M M1 ois str sm); [lia| lia| split; [apply AGO; lia| apply AGSH; lia]| | exact IA].
    intros c0 n0 p0 E. apply AGB. rewrite !in_app_iff. right; right; right. apply INCS. rewrite E. left; reflexivity. }
  assert (EKn : L5SAR.ek L ar (OB ++ LBX) FF S 22528 W0 M M1).
  { apply (L5SAR.ek_piece L ar (OB ++ LBX) FF S 22528 W0 M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
    intros a Ha CA OWx Pa. apply (OWx (os + 256, 40)); [unfold PGVWA1.W0, PGS.W_srcfG; left; reflexivity|].
    unfold L5.in_rng, P in *; cbn [fst snd] in *. lia. }
  assert (PA1 : PGV8.vw_at T M1 src x g OB).
  { apply (tw_xferA M M1 src src x x g g LK cr Aw (vml_of model) S 22528 [] PA HH); [| constructor| exact SF1| reflexivity| exact VS1| exact TBOK].
    apply (L5SAR.ahpres_of L ar (OB ++ LBX) FF S 22528 _ M M1).
    - exact EKn.
    - apply (L5.defined_grows M M1 _ _ MGM1). exact SDEF.
    - apply L5SAR.dk_grows. exact MGM1. }
  pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  split; [split; [|split]|].
  - exact (L5SAR.ek_trans L ar (OB ++ LBX) FF S 22528 W0 M0 M M1 EK EKn).
  - apply (L5SAR.dk_trans L ar (OB ++ LBX) FF S 22528 M0 M M1 DK). apply L5SAR.dk_grows. exact MGM1.
  - exact (L5SAR.astk_grows ar M M1 S 22528 STK MGM1).
  - split.
    { destruct SV as (S8 & S16' & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104).
      repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| assumption]). }
    split.
    { destruct LC as (L136 & L128 & L120 & L112).
      repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| assumption]). }
    split; [exact PA1|]. split; [exact IA1|].
    split; [apply (PMASK.base_keep L ar C LY (OB ++ LBX) FF S 22528 W0 M M1 EKn); [| exact BASE]|].
    { intros a Ha. apply outside_W0. destruct (frame_app _ _ _ _ _ _ HH). lia. }
    split; [exact TBOK|]. split; [exact HH1|]. split; [exact AM1|]. split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1]|].
    split; [exact ILK|]. split; [exact IAW|]. split; [exact CRL| exact CRK].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma d_after_fill mu0 (IH : IHt mu0) (fx : FPState) R M model src x g sm cr LK Aw (w n c : Z) :
  lregs R w -> getr R (reg 10) = Z_to_bv 64 c -> getr R (reg 23) = Z_to_bv 64 16384 -> getr R (reg 22) = Z_to_bv 64 n ->
  0 <= c <= 16384 -> 16384 <= w <= len ->
  st_ok M model src x g sm cr LK Aw -> PGV8.v8_size x = n + 16384 -> vroom x -> n = len - w ->
  PMSP.consumed src0 src sm0 sm = len - w + c ->
  PMSP.src_step src0 src sm0 sm -> PM.mu_src src sm < mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb5694 M model) K.
Proof using All.
  intros LR A10 A23 A22 Hc Hw SO SZ VR En CONS STEP MU.
  pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A26 & A27 & A25 & KP).
  pose proof (unread_nn M model src x g sm cr LK Aw SO) as (UN & ST & RM & GE).
  assert (CAP : n + 16384 <= PGV8.v8_cap x /\ 0 <= n).
  { pose proof SO as (_ & _ & _ & PA' & _). destruct (tsrc M src x g PA') as (_ & _ & _ & VS' & _).
    destruct x as [|b' n' c']; cbn in SZ |- *; [lia| destruct VS' as (_ & _ & _ & _ & _ & H1 & H2 & _); lia]. }
  assert (Hn : 0 <= n < 67108864) by (unfold PMSP.consumed in CONS; lia).
  pose proof (vpack M model src x g sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & _).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
  pose proof LC as (L136 & L128 & L120 & L112).
  pose proof lay as LAY.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  assert (D1 : S - 160 + 160 <= os \/ os + 296 <= S - 160) by (right; lia).
  assert (D2 : S - 160 + 160 <= tb \/ tb + 24 <= S - 160) by (right; lia).
  assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (clear - LAY; lia).
  bvr.
  pose proof (tsrc M src x g PA) as (SRC & _).
  destruct SRC as (_ & _ & F256 & _).
  set (MV := mrestrict (ahid Aw model) M) in *.
  LeanFeed.pfeed PP (PMASRVP.asvD3_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
       | 44%nat => c | 46%nat => n
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.defined _ (os + 256) 8 => unfold MV; apply (proj2 (L5A.defined_vis (ahid Aw model) M (os + 256) 8 ltac:(apply OAV; lia))); exact F256
      | |- PMASRVP.aligned _ _ => unfold PMASRVP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & EX).
  destruct EX as [(MS1 & KS1 & E1 & E10 & E11 & E24 & C0) | [(MS1 & KS1 & E10 & E11 & E24 & E25 & C0 & C1)
                 | (MS1 & KS1 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & C0 & C1)]];
    apply (pos_step fx fx1 R 0xb5694 R1 _ M model src x g sm cr LK Aw M1v SO MS1 MG1 FRZ1); intros M1 model1 SO1.
  - (* [comment removed for export] *)
    assert (DK' : c < 16384).
    { destruct (Z.eq_dec c 16384) as [->|NE]; [rewrite Z.sub_diag, Zmod_0_l in C0; lia| lia]. }
    apply (call_resize fx1 R1 M1 model1 src x g sm cr LK Aw (c + n) 743108 w E1 ltac:(split; [lia| reflexivity])); try assumption.
    + rewrite (KS1 2%nat) by inl. exact A2.
    + kp_tac KS1 KP.
    + lia.
    + left. lia.
    + right. unfold PM.CHUNK. lia.
    + lia.
    + unfold PMSP.consumed in CONS. lia.
    + lia.
    + intros fx2 R2 M2 model2 LK2 Aw2 x2 g2 cr2 RP2 SZ2 CAP2 VR2 _ SO2.
      refine (after_shrink mu0 IH fx2 R2 M2 model2 src x2 g2 sm cr2 LK2 Aw2 w c _ _ ltac:(lia) ltac:(unfold PM.CHUNK; lia) ltac:(lia) SO2 _ MU).
      * apply (lregs_pres R1 R2 w RP2). apply (lregs_keep R R1 w LR). ks_tac KS1.
      * rewrite (L5SAR.cs_of_preserved R1 R2 24%nat RP2) by inl. exact E24.
      * unfold PGSSVA1.acct. split; [lia|]. split; [lia|]. split; [exact STEP|]. split; [exact VR2|]. right. unfold PM.CHUNK. lia.
  - (* [comment removed for export] *)
    replace (18446744073709535232) with ((18446744073709551615 * 16384) mod 2 ^ 64) in C0 by reflexivity.
    rewrite subw in C0 by lia.
    assert (DK' : c = 16384) by (apply (mod_lt1 (c - 16384)) in C1; lia). subst c.
    apply (IH fx1 R1 M1 model1 src x g sm cr LK Aw (w - 16384) MU).
    split; [|split; [exact SO1| split; [|split; [lia| exact E10]]]].
    + apply (lregs_set R R1 w (w - 16384) LR); [ks_tac KS1| exact E25].
    + unfold PGSSVA1.acct. split; [lia|]. split; [lia|]. split; [exact STEP|]. split; [exact VR|]. right. unfold PM.CHUNK. lia.
  - (* [comment removed for export] *)
    replace (18446744073709535232) with ((18446744073709551615 * 16384) mod 2 ^ 64) in C0 by reflexivity.
    rewrite subw in C0 by lia.
    assert (DK' : c = 16384) by (apply (mod_lt1 (c - 16384)) in C1; lia). subst c.
    apply (finish fx1 R1 M1 model1 src x g sm cr LK Aw 0); try assumption.
    + intros xr Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [assumption|]). destruct Hx.
    + kp_tac KS1 KP.
    + rewrite E10. f_equal. lia.
    + lia.
    + unfold PGSSVA1.acct. split; [lia|]. split; [lia|]. split; [exact STEP|]. split; [exact VR|]. right. unfold PM.CHUNK. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma d_after_resize mu0 (IH : IHt mu0) (fx : FPState) R M model src x g sm cr LK Aw (w n : Z) :
  lregs R w -> getr R (reg 23) = Z_to_bv 64 16384 -> getr R (reg 22) = Z_to_bv 64 n -> 16384 <= w <= len ->
  st_ok M model src x g sm cr LK Aw -> PGV8.v8_size x = n + 16384 -> vroom x -> n = len - w ->
  PMSP.consumed src0 src sm0 sm = len - w ->
  PMSP.src_step src0 src sm0 sm -> PM.sm_st sm = 0 -> PM.mu_src src sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb566c M model) K.
Proof using All.
  intros LR A23 A22 Hw SO SZ VR En CONS STEP ST0 MU.
  pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A26 & A27 & A25 & KP).
  pose proof (unread_nn M model src x g sm cr LK Aw SO) as (UN & ST & RM & GE).
  assert (Hn : 0 <= n < 67108864) by (unfold PMSP.consumed in CONS; lia).
  pose proof (vpack M model src x g sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & _).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
  pose proof LC as (L136 & L128 & L120 & L112).
  pose proof lay as LAY.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  assert (D1 : S - 160 + 160 <= os \/ os + 296 <= S - 160) by (right; lia).
  assert (D2 : S - 160 + 160 <= tb \/ tb + 24 <= S - 160) by (right; lia).
  assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (clear - LAY; lia).
  bvr.
  pose proof (tsrc M src x g PA) as (_ & _ & _ & VS & _).
  set (MV := mrestrict (ahid Aw model) M) in *.
  destruct x as [|b1 n1 c1]; cbn [PGV8.v8_size] in SZ; [lia|]. subst n1.
  destruct VS as (VD & VC & U0 & U8 & U16 & Hnc & Hc & Hb0 & Hb16 & Db & _ & _).
  assert (IN : In (b1, c1) (PM.src_own src ++ PGV8.v8_own (PGV8.V8Blk b1 (n + 16384) c1) ++ OB ++ LBX)) by (apply in_or_app; right; apply in_or_app; left; left; reflexivity).
  destruct (BRB _ IN) as (Q0 & Q4). cbn [fst snd] in Q0, Q4.
  LeanFeed.pfeed PP (PMASRVP.asvD2_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
       | 42%nat => b1 | 46%nat => n
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.u64_at _ _ tb _ => unfold MV; vis64 TAV
      | |- PMASRVP.aligned _ _ => unfold PMASRVP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS1 & KS1 & E1 & E10 & E11 & E12)).
  apply (ro_step fx fx1 R 0xb566c R1 0xb29f8 M model src (PGV8.V8Blk b1 (n + 16384) c1) g sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
  apply (call_fillv fx1 R1 M model1 src (PGV8.V8Blk b1 (n + 16384) c1) g sm cr LK Aw (b1 + n) 743060 b1 (n + 16384) c1 E1 ltac:(split; [lia| reflexivity])); try assumption; try reflexivity.
  + rewrite (KS1 2%nat) by inl. exact A2.
  + kp_tac KS1 KP.
  + lia.
  + unfold PM.CHUNK. lia.
  + intros fx2 R2 M2 model2 LK2 Aw2 sm2 c RP2 Y10 Hc' G2 STF ST2F STEP2 SO2.
    destruct (STF ST0) as (Ec & ST2).
    pose proof (unread_nn M2 model2 src (PGV8.V8Blk b1 (n + 16384) c1) g sm2 cr LK2 Aw2 SO2) as (UN2 & ST2' & RM2 & GE2).
    assert (CONS2 : PMSP.consumed src src sm sm2 = c).
    { unfold PMSP.consumed, PM.unread. destruct STEP2 as (_ & E2 & _). lia. }
    refine (d_after_fill mu0 IH fx2 R2 M2 model2 src (PGV8.V8Blk b1 (n + 16384) c1) g sm2 cr LK2 Aw2 w n c _ Y10 _ _ ltac:(unfold PM.CHUNK in Hc'; lia) Hw SO2 _ VR En _ _ _).
    * apply (lregs_pres R1 R2 w RP2). apply (lregs_keep R R1 w LR). ks_tac KS1.
    * rewrite (L5SAR.cs_of_preserved R1 R2 23%nat RP2) by inl. rewrite (KS1 23%nat) by inl. exact A23.
    * rewrite (L5SAR.cs_of_preserved R1 R2 22%nat RP2) by inl. rewrite (KS1 22%nat) by inl. exact A22.
    * reflexivity.
    * unfold PMSP.consumed in *. lia.
    * exact (PGSSVA3.src_step_trans _ _ _ _ _ _ STEP STEP2).
    * enough (PM.mu_src src sm2 < PM.mu_src src sm) by lia.
      apply (PGSSVA3.mu_dec _ _ _ _ STEP2 ST ST2').
      destruct (Z.ltb_spec c PM.CHUNK) as [LT|GE']; [right; split; [exact ST0| exact ST2]| left].
      unfold PMSP.consumed in CONS2. unfold PM.CHUNK in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dpath mu0 (IH : IHt mu0) (fx : FPState) R M model src x g sm cr LK Aw (w : Z) :
  lregs R w -> getr R (reg 23) = Z_to_bv 64 16384 -> 16384 <= w <= len ->
  st_ok M model src x g sm cr LK Aw -> acct src x g sm w -> PM.sm_st sm = 0 -> PM.mu_src src sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb5644 M model) K.
Proof using All.
  intros LR A23 Hw SO AC ST0 MU. pose proof AC as (CONS & SZ & STEP & VR & MIN).
  pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A26 & A27 & A25 & KP).
  pose proof (unread_nn M model src x g sm cr LK Aw SO) as (UN & ST & RM & GE).
  pose proof (vpack M model src x g sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & _).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
  pose proof LC as (L136 & L128 & L120 & L112).
  pose proof lay as LAY.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  assert (D1 : S - 160 + 160 <= os \/ os + 296 <= S - 160) by (right; lia).
  assert (D2 : S - 160 + 160 <= tb \/ tb + 24 <= S - 160) by (right; lia).
  assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (clear - LAY; lia).
  bvr.
  pose proof (tsrc M src x g PA) as (_ & _ & _ & VS & _).
  assert (Hn : 0 <= len - w < 67108864) by (unfold PMSP.consumed in CONS; lia).
  set (MV := mrestrict (ahid Aw model) M) in *.
  assert (HDR : exists b, L5.u64_at RSEGS M tb b /\ L5.u64_at RSEGS M (tb + 8) (b + (len - w)) /\ 0 <= b <= 2 ^ 47).
  { destruct x as [|b1 n1 c1]; cbn [PGV8.v8_size] in SZ.
    - destruct VS as (_ & _ & U0 & U8 & _). exists 0. rewrite <- SZ, Z.add_0_l. split; [exact U0|]. split; [exact U8| lia].
    - destruct VS as (_ & _ & U0 & U8 & U16 & Hnc & Hc & Hb0 & _). subst n1. exists b1. split; [exact U0|]. split; [exact U8|].
      assert (IN : In (b1, c1) (PM.src_own src ++ PGV8.v8_own (PGV8.V8Blk b1 (len - w) c1) ++ OB ++ LBX)) by (apply in_or_app; right; apply in_or_app; left; left; reflexivity).
      destruct (BRB _ IN) as (Q0 & Q4). cbn [fst snd] in Q0, Q4. lia. }
  destruct HDR as (b & U0 & U8 & Hb).
  LeanFeed.pfeed PP (PMASRVP.asvD_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
       | 40%nat => b | 41%nat => len - w
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.u64_at _ _ tb _ => unfold MV; vis64 TAV
      | |- L5.u64_at _ _ (tb + _) _ => unfold MV; vis64 TAV
      | |- PMASRVP.aligned _ _ => unfold PMASRVP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS1 & KS1 & E1 & E10 & E11 & E22)).
  apply (ro_step fx fx1 R 0xb5644 R1 0xb5764 M model src x g sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
  apply (call_resize fx1 R1 M model1 src x g sm cr LK Aw ((len - w) + 16384) 743020 w E1 ltac:(split; [lia| reflexivity])); try assumption.
  + rewrite (KS1 2%nat) by inl. exact A2.
  + kp_tac KS1 KP.
  + lia.
  + right. unfold PM.CHUNK. lia.
  + lia.
  + unfold PMSP.consumed in CONS. lia.
  + lia.
  + intros fx2 R2 M2 model2 LK2 Aw2 x2 g2 cr2 RP2 SZ2 CAP2 VR2 _ SO2.
    refine (d_after_resize mu0 IH fx2 R2 M2 model2 src x2 g2 sm cr2 LK2 Aw2 w (len - w) _ _ _ Hw SO2 SZ2 VR2 eq_refl CONS STEP ST0 MU).
    * apply (lregs_pres R1 R2 w RP2). apply (lregs_keep R R1 w LR). ks_tac KS1.
    * rewrite (L5SAR.cs_of_preserved R1 R2 23%nat RP2) by inl. rewrite (KS1 23%nat) by inl. exact A23.
    * rewrite (L5SAR.cs_of_preserved R1 R2 22%nat RP2) by inl. exact E22.
Qed.

End Call.
End WithHeap.
End PGSSVA4.
