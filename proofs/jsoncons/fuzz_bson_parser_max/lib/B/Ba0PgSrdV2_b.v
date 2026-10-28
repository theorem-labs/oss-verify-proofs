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
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcRead1_b PnAReset1_b PnASrdVP_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PgTxtKitA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgV8. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgV8A_b PgV8KitA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnRunA_b Ba0PgVw1_b Ba0PgSrdV1_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGSSVA2.
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
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat; bvr1 R0 23%nat; bvr1 R0 24%nat; bvr1 R0 25%nat; bvr1 R0 26%nat; bvr1 R0 27%nat.

Ltac ks_tac KS := intros xr Hx; apply KS; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx.
Ltac kp_tac KS KP := intros xr Hx; rewrite (KS xr) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx); apply KP; exact Hx.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_shrink mu0 (IH : IHt mu0) (fx : FPState) R M model src x g sm cr LK Aw (w d : Z) :
  lregs R w -> getr R (reg 24) = Z_to_bv 64 d -> 0 <= d <= w -> d <= PM.CHUNK -> 1 <= w <= len ->
  st_ok M model src x g sm cr LK Aw -> acct src x g sm (w - d) -> PM.mu_src src sm < mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb56c4 M model) K.
Proof using All.
  intros LR A24 Hd HdC Hw SO AC MU. unfold PM.CHUNK in HdC.
  pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A26 & A27 & A25 & KP).
  pose proof (vpack M model src x g sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as (MR & SV & LC & _).
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
  pose proof LC as (L136 & L128 & L120 & L112).
  pose proof lay as LAY.
  assert (D1 : S - 160 + 160 <= os \/ os + 296 <= S - 160) by (right; lia).
  assert (D2 : S - 160 + 160 <= tb \/ tb + 24 <= S - 160) by (right; lia).
  assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (clear - LAY; lia).
  bvr.
  set (MV := mrestrict (ahid Aw model) M) in *.
  LeanFeed.pfeed PP (PMASRVP.asvF_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w | 44%nat => d
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- PMASRVP.aligned _ _ => unfold PMASRVP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & [(MS1 & KS1 & E10 & E25 & C0) | (MS1 & KS1 & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & C0)]).
  - apply (ro_step fx fx1 R 0xb56c4 R1 0xb55a0 M model src x g sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    rewrite subw in C0 by lia.
    apply (IH fx1 R1 M model1 src x g sm cr LK Aw (w - d) MU).
    split; [|split; [exact SO1| split; [exact AC| split; [lia| exact E10]]]].
    apply (lregs_set R R1 w (w - d) LR); [ks_tac KS1| exact E25].
  - apply (ro_step fx fx1 R 0xb56c4 R1 0xb570c M model src x g sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    rewrite subw in C0 by lia.
    apply (finish fx1 R1 M model1 src x g sm cr LK Aw 0); try assumption.
    + intros xr Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [assumption|]). destruct Hx.
    + intros xr Hx. rewrite (KS1 xr) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
    + rewrite E10. f_equal. lia.
    + lia.
    + replace 0 with (w - d) by lia. exact AC.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_read mu0 (IH : IHt mu0) (fx : FPState) R M model src x g sm cr LK Aw (w k d n : Z) :
  lregs R w -> getr R (reg 10) = Z_to_bv 64 d -> getr R (reg 23) = Z_to_bv 64 k -> getr R (reg 22) = Z_to_bv 64 n ->
  0 <= d <= k -> 1 <= k <= w -> k = Z.min w PM.CHUNK -> w <= len ->
  st_ok M model src x g sm cr LK Aw -> PGV8.v8_size x = n + k -> vroom x -> n = len - w ->
  PMSP.consumed src0 src sm0 sm = len - w + d ->
  PMSP.src_step src0 src sm0 sm -> PM.mu_src src sm < mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb5630 M model) K.
Proof using All.
  intros LR A10 A23 A22 Hd Hk HkC Hw SO SZ VR En CONS STEP MU.
  assert (HkC' : k <= 16384) by (unfold PM.CHUNK in HkC; lia).
  pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A26 & A27 & A25 & KP).
  pose proof (unread_nn M model src x g sm cr LK Aw SO) as (UN & _).
  assert (CAP : n + k <= PGV8.v8_cap x /\ 0 <= n).
  { pose proof SO as (_ & _ & _ & PA & _). destruct (tsrc M src x g PA) as (_ & _ & _ & VS & _).
    destruct x as [|b' n' c']; cbn in SZ |- *; [lia| destruct VS as (_ & _ & _ & _ & _ & H1 & H2 & _); lia]. }
  assert (Hn : 0 <= n <= 134217728) by (unfold PMSP.consumed in CONS; lia).
  pose proof (vpack M model src x g sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as (MR & SV & LC & _).
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
  pose proof LC as (L136 & L128 & L120 & L112).
  pose proof lay as LAY.
  assert (D1 : S - 160 + 160 <= os \/ os + 296 <= S - 160) by (right; lia).
  assert (D2 : S - 160 + 160 <= tb \/ tb + 24 <= S - 160) by (right; lia).
  assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (clear - LAY; lia).
  bvr.
  set (MV := mrestrict (ahid Aw model) M) in *.
  LeanFeed.pfeed PP (PMASRVP.asvE_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w | 43%nat => k
       | 44%nat => d | 46%nat => n
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- PMASRVP.aligned _ _ => unfold PMASRVP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & [(MS1 & KS1 & E1 & E10 & E11 & E24 & C0) | [(MS1 & KS1 & E10 & E24 & E25 & C0 & C1)
                 | (MS1 & KS1 & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & C0 & C1)]]).
  - (* [comment removed for export] *)
    apply (ro_step fx fx1 R 0xb5630 R1 0xb5764 M model src x g sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    assert (DK' : d < k).
    { destruct (Z.eq_dec d k) as [->|NE]; [rewrite Z.sub_diag, Zmod_0_l in C0; lia| lia]. }
    apply (call_resize fx1 R1 M model1 src x g sm cr LK Aw (d + n) 743108 w); try assumption.
    + split; [lia| reflexivity].
    + rewrite (KS1 2%nat) by inl. exact A2.
    + intros xr Hx. rewrite (KS1 xr) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
    + lia.
    + left. lia.
    + right. lia.
    + lia.
    + unfold PMSP.consumed in CONS. lia.
    + lia.
    + intros fx2 R2 M2 model2 LK2 Aw2 x2 g2 cr2 RP2 SZ2 CAP2 VR2 _ SO2.
      apply (after_shrink mu0 IH fx2 R2 M2 model2 src x2 g2 sm cr2 LK2 Aw2 w d); try assumption.
      * apply (lregs_pres R1 R2 w RP2). apply (lregs_keep R R1 w LR). ks_tac KS1.
      * rewrite (L5SAR.cs_of_preserved R1 R2 24%nat RP2) by inl. exact E24.
      * lia.
      * unfold PM.CHUNK. lia.
      * lia.
      * unfold PGSSVA1.acct. split; [lia|]. split; [lia|]. split; [exact STEP|]. split; [exact VR2|]. right. lia.
  - (* [comment removed for export] *)
    apply (ro_step fx fx1 R 0xb5630 R1 0xb55a0 M model src x g sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    rewrite subw in C0 by lia.
    assert (DK' : d = k) by (apply (mod_lt1 (d - k)) in C1; lia). subst d.
    apply (IH fx1 R1 M model1 src x g sm cr LK Aw (w - k) MU).
    split; [|split; [exact SO1| split; [|split; [lia| exact E10]]]].
    + apply (lregs_set R R1 w (w - k) LR); [ks_tac KS1| exact E25].
    + unfold PGSSVA1.acct. split; [lia|]. split; [lia|]. split; [exact STEP|]. split; [exact VR|]. right. lia.
  - (* [comment removed for export] *)
    apply (ro_step fx fx1 R 0xb5630 R1 0xb570c M model src x g sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    rewrite subw in C0 by lia.
    assert (DK' : d = k) by (apply (mod_lt1 (d - k)) in C1; lia). subst d.
    apply (finish fx1 R1 M model1 src x g sm cr LK Aw 0); try assumption.
    + intros xr Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [assumption|]). destruct Hx.
    + intros xr Hx. rewrite (KS1 xr) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
    + rewrite E10. f_equal. lia.
    + lia.
    + unfold PGSSVA1.acct. split; [lia|]. split; [lia|]. split; [exact STEP|]. split; [exact VR|]. right. lia.
Qed.

End Call.
End WithHeap.
End PGSSVA2.
