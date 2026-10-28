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
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmTxtKit2. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcRead1_b PnAReset1_b PnASrdP_b Ba0PgSrd1_b Ba0PgSrd2_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PgTxtKitA_b PnRunA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PGSSRA3.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PMA.AD.
Abbreviation pot := PGSSRA1.pot.
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
Hypothesis FRM0 : PGSA.ffroomB PNRA.FCB 5 FF LK0.
Hypothesis FRS : PMSPA.ffrsA FF S.
Hypothesis OFR : PGSA.ofr FF lo hi.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UNS0 : PM.vs_size tx0 + PM.unread src0 sm0 < 2 ^ 26.
Hypothesis STKSH0 : shadow_zero M0 (S - 22528) 2816.
Hypothesis RSZ : PMA.str_resize_spec L ar HI.
Hypothesis SRD : PGSA.src_read_specG RSEGS AD L ar HI PNRA.FCB.
Hypothesis FBT : PGSA.fill_buffer_tb_specG RSEGS AD L ar HI PNRA.FCB.
#[local] Abbreviation W0 := (PGSSRA1.W0 T).   (* [comment removed for export] *)
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
                         (src' : PM.srcst) (tx' : PM.vstr) (tg' : Z) (sm' : PM.strm) (cr' : credit) (d : Z),
  regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
  PMSP.consumed src0 src' sm0 sm' = d -> PM.vs_size tx' = PM.vs_size tx0 + d ->
  PGS.tw_at T M' src' tx' tg' OB -> PM.iss_at RSEGS AD PMSPA.accA M' ois str sm' ->
  PMSP.src_step src0 src' sm0 sm' ->
  L5CA.ahpres L ar LBX FF S (PMSPA.pm_scr 5) W0 M0 M' ->
  PMSP.credit_keep cr0 cr' (pot L ar tx0 tg0) (pot L ar tx' tg') ->
  model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' ->
  ri_inv HI (PM.src_own src' ++ PM.vs_own tx' ++ OB ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx' R' r M' model') K.

#[local] Abbreviation lay := (PGSSRA1.lay L ar HI T TOK).
#[local] Abbreviation tsrc := (PGSSRA1.tsrc L ar HI T OB TOK).
#[local] Abbreviation aobjs := (PGSSRA1.aobjs L ar HI FF T TOK OFR).
#[local] Abbreviation frame_app := (PGSSRA1.frame_app L ar C HI LY HIok FF T TOK OFR).
#[local] Abbreviation tw_xferA := (PGSSRA1.tw_xferA L ar C HI HIok LBX FF T OB TOK OFR).
#[local] Abbreviation stw_ok := (PGSSRA1.stw_ok L ar C HI LY HIok T TOK).
#[local] Abbreviation U := (PGSSRA1.U R0).
#[local] Abbreviation saves13 := (PGSSRA1.saves13 R0 S).
#[local] Abbreviation locals := (PGSSRA1.locals S len T).
#[local] Abbreviation kept_rs := (PGSSRA1.kept_rs R0).
#[local] Abbreviation memrel := (PGSSRA1.memrel L ar M0 LBX FF S T OB).
#[local] Abbreviation fields_eq := (PGSSRA1.fields_eq).
#[local] Abbreviation acct := (PGSSRA1.acct len src0 tx0 sm0).
#[local] Abbreviation st_ok := (PGSSRA1.st_ok L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S len T OB tx0 tg0 str).
#[local] Abbreviation lregs := (PGSSRA1.lregs R0 S T).
#[local] Abbreviation tbdst := (PGSSRA1.tbdst T).
#[local] Abbreviation lstate := (PGSSRA1.lstate L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S len T OB src0 tx0 tg0 str sm0).
#[local] Abbreviation IHt := (PGSSRA1.IHt L ar HI R0 M0 model0 K LBX FF LK0 Aw0 cr0 S len T OB src0 tx0 tg0 str sm0).
#[local] Abbreviation lregs_keep := (PGSSRA1.lregs_keep R0 S len T Hlen).
#[local] Abbreviation lregs_set := (PGSSRA1.lregs_set R0 S len T Hlen).
#[local] Abbreviation lregs_pres := (PGSSRA1.lregs_pres R0 S len T Hlen).
#[local] Abbreviation finish := (PGSSRA1.finish L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation callee_mem := (PGSSRA1.callee_mem L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation centry := (PGSSRA1.centry L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation call_resize := (PGSSRA1.call_resize L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation call_srcread := (PGSSRA1.call_srcread L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation call_filltb := (PGSSRA1.call_filltb L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation unread_nn := (PGSSRA1.unread_nn L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation vpack := (PGSSRA1.vpack L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation ro_step := (PGSSRA1.ro_step L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
#[local] Abbreviation outside_W0 := (PGSSRA1.outside_W0 L ar HI T TOK).
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat; bvr1 R0 23%nat; bvr1 R0 24%nat; bvr1 R0 25%nat; bvr1 R0 26%nat; bvr1 R0 27%nat.

#[local] Abbreviation after_read := (PGSSRA2.after_read L ar C HI LY HIok R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r len T OB src0 tx0 tg0 str sm0 TOK Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS OFR Hlen INCS UNS0 STKSH0 RSZ SRD FBT KONT).
Ltac ks_tac KS := intros x Hx; apply KS; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx.

Lemma src_step_trans a b c sa sb sc : PMSP.src_step a b sa sb -> PMSP.src_step b c sb sc -> PMSP.src_step a c sa sc.
Proof.
  unfold PMSP.src_step. intros (E1 & E2 & L1 & S1 & U1) (E3 & E4 & L2 & S2 & U2).
  split; [congruence|]. split; [congruence|]. split; [lia|]. split; [intros X; apply S2; apply S1; exact X| lia].
Qed.
Lemma mu_dec src src' sm sm' : PMSP.src_step src src' sm sm' -> (PM.sm_st sm = 0 \/ PM.sm_st sm = 2) -> (PM.sm_st sm' = 0 \/ PM.sm_st sm' = 2) ->
  (PM.unread src' sm' < PM.unread src sm \/ (PM.sm_st sm = 0 /\ PM.sm_st sm' = 2)) -> PM.mu_src src' sm' < PM.mu_src src sm.
Proof.
  unfold PM.mu_src. intros (_ & _ & _ & S2 & U) ST ST' H.
  destruct ST as [E|E]; destruct ST' as [E'|E']; rewrite ?E, ?E' in *; cbn [Z.eqb]; [lia|lia| specialize (S2 eq_refl); lia| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma at_srcread mu0 (IH : IHt mu0) (fx : FPState) R M model src tx tg sm cr LK Aw (w k n p : Z) :
  lregs R w -> getr R (reg 1) = Z_to_bv 64 0xb526c -> getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 p -> getr R (reg 12) = Z_to_bv 64 k ->
  getr R (reg 24) = Z_to_bv 64 k -> getr R (reg 22) = Z_to_bv 64 n ->
  1 <= k <= w -> k <= PM.CHUNK -> w <= len -> tbdst tx p k ->
  st_ok M model src tx tg sm cr LK Aw -> PM.vs_size tx = n + k -> 0 <= n -> n = PM.vs_size tx0 + (len - w) ->
  PMSP.consumed src0 src sm0 sm = len - w ->
  PMSP.src_step src0 src sm0 sm -> fields_eq src tx tg ->
  (1 <= PM.sr_rem src \/ PM.sm_st sm = 0) -> PM.mu_src src sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xaed4c M model) K.
Proof using All.
  intros LR A1 A10 A11 A12 A24 AN Hk HkC Hw DST SO SZ Hn0 En CONS STEP FE PRG MU.
  pose proof LR as (A2 & A9 & A18 & A19 & A20 & A21 & A23 & A26 & A27 & A8 & KP).
  pose proof (unread_nn M model src tx tg sm cr LK Aw SO) as (UN & ST & RM & GE).
  apply (call_srcread fx R M model src tx tg sm cr LK Aw p k 0xb526c A1 ltac:(split; [lia| reflexivity]) A2 KP A10 A11 A12 ltac:(lia) DST SO).
  intros fx2 R2 M2 model2 LK2 Aw2 src2 sm2 d RP2 Y10 Hd CONS2 POS ZERO STEP2 SO2.
  pose proof (unread_nn M2 model2 _ _ _ sm2 cr LK2 Aw2 SO2) as (UN2 & ST2 & RM2 & GE2).
  refine (after_read mu0 IH fx2 R2 M2 model2 src2 tx tg sm2 cr LK2 Aw2 w k d n (lregs_pres R R2 w RP2 LR) Y10 _ _ Hd Hk HkC Hw SO2 SZ Hn0 En _ _ FE _).
  - rewrite (L5SAR.cs_of_preserved R R2 24%nat RP2) by inl. exact A24.
  - rewrite (L5SAR.cs_of_preserved R R2 22%nat RP2) by inl. exact AN.
  - unfold PMSP.consumed in *. lia.
  - exact (src_step_trans _ _ _ _ _ _ STEP STEP2).
  - enough (PM.mu_src src2 sm2 < PM.mu_src src sm) by lia.
    apply (mu_dec _ _ _ _ STEP2 ST ST2).
    unfold PMSP.consumed in CONS2. destruct (Z.eq_dec d 0) as [D0|D0]; [right| left; lia].
    destruct (ZERO D0) as (_ & E2). split; [|exact E2].
    destruct PRG as [P1|P1]; [specialize (POS P1); lia| exact P1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_resize1 mu0 (IH : IHt mu0) (fx : FPState) R M model src tx tg sm cr LK Aw (w k n : Z) :
  lregs R w -> getr R (reg 24) = Z_to_bv 64 k -> getr R (reg 22) = Z_to_bv 64 n ->
  1 <= k <= w -> k <= PM.CHUNK -> w <= len ->
  st_ok M model src tx tg sm cr LK Aw -> PM.vs_size tx = n + k -> 0 <= n -> n = PM.vs_size tx0 + (len - w) ->
  PMSP.consumed src0 src sm0 sm = len - w ->
  PMSP.src_step src0 src sm0 sm -> fields_eq src tx tg ->
  (1 <= PM.sr_rem src \/ PM.sm_st sm = 0) -> PM.mu_src src sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb5224 M model) K.
Proof using All.
  intros LR A24 AN Hk HkC Hw SO SZ Hn0 En CONS STEP FE PRG MU.
  pose proof LR as (A2 & A9 & A18 & A19 & A20 & A21 & A23 & A26 & A27 & A8 & KP).
  pose proof (unread_nn M model src tx tg sm cr LK Aw SO) as (UN & ST & RM & GE).
  assert (Hn : n < 67108864) by (unfold PMSP.consumed in CONS; lia).
  pose proof (vpack M model src tx tg sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & _).
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
  pose proof LC as (L168 & L160 & L152 & L144 & L136 & L128 & L120 & L112).
  pose proof lay as LAY.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  assert (D1 : S - 192 + 192 <= os \/ os + 296 <= S - 192) by (right; lia).
  assert (D2 : S - 192 + 192 <= tb \/ tb + 24 <= S - 192) by (right; lia).
  assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (clear - LAY; lia).
  bvr.
  pose proof (tsrc M src tx tg PA) as (_ & _ & _ & VS & _).
  assert (HkC' : k <= 16384) by (unfold PM.CHUNK in HkC; exact HkC).
  set (MV := mrestrict (ahid Aw model) M) in *.
  destruct VS as (VD & VC & VS). destruct tx as [n1|c1 n1 q1]; cbn [PM.vs_size] in SZ.
  - (* [comment removed for export] *)
    destruct VS as (Hn1 & B0). pose proof (PMF.even_byte n1) as EV.
    LeanFeed.pfeed PP (PMASRDP.srdQS_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
       | 40%nat => 2 * n1 | 43%nat => k | 46%nat => n
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
      | |- PMASRDP.aligned _ _ => unfold PMASRDP.aligned; lia
      | |- _ => lia end]).
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS1 & KS1 & E1 & E10 & E11 & E12)).
    apply (ro_step fx fx1 R 0xb5224 R1 0xaed4c M model src (PM.VShort n1) tg sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    refine (at_srcread mu0 IH fx1 R1 M model1 src (PM.VShort n1) tg sm cr LK Aw w k n (tb + n + 1) _ E1 E10 E11 E12 _ _ Hk HkC Hw _ SO1 _ Hn0 En CONS STEP FE PRG MU).
    + apply (lregs_keep R R1 w LR). ks_tac KS1.
    + rewrite (KS1 24%nat) by inl. exact A24.
    + rewrite (KS1 22%nat) by inl. exact AN.
    + unfold PGSSRA1.tbdst. left. split; [exists n1; reflexivity|]. lia.
    + exact SZ.
  - (* [comment removed for export] *)
    destruct VS as (W0' & W8 & W16 & Hn1 & Hc1 & Hce & DQ & CQ).
    pose proof (PMF.u8_of_u64 RSEGS M tb (c1 + 1) ltac:(lia) W0') as B0. pose proof (PMF.odd_byte c1 Hce ltac:(lia)) as ODB.
    assert (H39 : 0 <= (c1 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)); lia).
    assert (IN : In (q1, c1) (PM.src_own src ++ PM.vs_own (PM.VLong c1 n1 q1) ++ OB ++ LBX)) by (apply in_or_app; right; apply in_or_app; left; left; reflexivity).
    destruct (WB _ IN) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in Q0, Q1, Q2, Q3, Q4, Q5.
    LeanFeed.pfeed PP (PMASRDP.srdQL_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
       | 40%nat => (c1 + 1) mod 256 | 42%nat => q1 | 43%nat => k | 46%nat => n
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.u64_at _ _ (tb + _) _ => unfold MV; vis64 TAV
      | |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
      | |- PMASRDP.aligned _ _ => unfold PMASRDP.aligned; lia
      | |- _ => lia end]).
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS1 & KS1 & E1 & E10 & E11 & E12)).
    apply (ro_step fx fx1 R 0xb5224 R1 0xaed4c M model src (PM.VLong c1 n1 q1) tg sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    refine (at_srcread mu0 IH fx1 R1 M model1 src (PM.VLong c1 n1 q1) tg sm cr LK Aw w k n (q1 + n) _ E1 E10 E11 E12 _ _ Hk HkC Hw _ SO1 _ Hn0 En CONS STEP FE PRG MU).
    + apply (lregs_keep R R1 w LR). ks_tac KS1.
    + rewrite (KS1 24%nat) by inl. exact A24.
    + rewrite (KS1 22%nat) by inl. exact AN.
    + unfold PGSSRA1.tbdst. right. exists c1, n1, q1. split; [reflexivity|]. lia.
    + exact SZ.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rpath mu0 (IH : IHt mu0) (fx : FPState) R M model src tx tg sm cr LK Aw (w k : Z) :
  lregs R w -> getr R (reg 24) = Z_to_bv 64 k -> 1 <= k <= w -> k <= PM.CHUNK -> w <= len ->
  st_ok M model src tx tg sm cr LK Aw -> acct src tx tg sm w ->
  (1 <= PM.sr_rem src \/ PM.sm_st sm = 0) -> PM.mu_src src sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0xb51e4 M model) K.
Proof using All.
  intros LR A24 Hk HkC Hw SO (CONS & SZ & STEP & FE) PRG MU.
  pose proof LR as (A2 & A9 & A18 & A19 & A20 & A21 & A23 & A26 & A27 & A8 & KP).
  pose proof (unread_nn M model src tx tg sm cr LK Aw SO) as (UN & ST & RM & GE).
  pose proof (vpack M model src tx tg sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & _).
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
  pose proof LC as (L168 & L160 & L152 & L144 & L136 & L128 & L120 & L112).
  pose proof lay as LAY.
  assert (D1 : S - 192 + 192 <= os \/ os + 296 <= S - 192) by (right; lia).
  assert (D2 : S - 192 + 192 <= tb \/ tb + 24 <= S - 192) by (right; lia).
  assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (clear - LAY; lia).
  bvr.
  pose proof (tsrc M src tx tg PA) as (_ & _ & _ & VS & _).
  assert (HkC' : k <= 16384) by (unfold PM.CHUNK in HkC; exact HkC).
  assert (HSZ : PM.vs_size tx < 67108864) by (unfold PMSP.consumed in CONS; lia).
  set (MV := mrestrict (ahid Aw model) M) in *.
  destruct VS as (VD & VC & VS). destruct tx as [n1|c1 n1 q1]; cbn [PM.vs_size] in SZ, HSZ.
  - (* [comment removed for export] *)
    destruct VS as (Hn1 & B0). pose proof (PMF.even_byte n1) as EV.
    LeanFeed.pfeed PP (PMASRDP.srdRS_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
       | 40%nat => 2 * n1 | 43%nat => k
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
      | |- PMASRDP.aligned _ _ => unfold PMASRDP.aligned; lia
      | |- _ => lia end]).
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS1 & KS1 & E1 & E10 & E11 & E12 & E22)).
    apply (ro_step fx fx1 R 0xb51e4 R1 0xd628c M model src (PM.VShort n1) tg sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    assert (E11' : getr R1 (reg 11) = Z_to_bv 64 (n1 + k)) by (rewrite E11; f_equal; rewrite Z.mul_comm, Z.div_mul by lia; lia).
    assert (E27' : getr R1 (reg 22) = Z_to_bv 64 n1) by (rewrite E22; f_equal; rewrite Z.mul_comm, Z.div_mul by lia; lia).
    apply (call_resize fx1 R1 M model1 src (PM.VShort n1) tg sm cr LK Aw (n1 + k) 741924 E1 ltac:(split; [lia| reflexivity])); try assumption.
    + rewrite (KS1 2%nat) by inl. exact A2.
    + intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
    + cbn [PM.vs_size]. unfold PM.CHUNK. lia.
    + unfold PM.CHUNK. lia.
    + intros fx2 R2 M2 model2 LK2 Aw2 tb2 tg2 cr2 RP2 SZ2 _ SO2.
      refine (after_resize1 mu0 IH fx2 R2 M2 model2 src tb2 tg2 sm cr2 LK2 Aw2 w k n1 _ _ _ Hk HkC Hw SO2 SZ2 ltac:(lia) SZ CONS STEP _ PRG MU).
      * apply (lregs_pres R1 R2 w RP2). apply (lregs_keep R R1 w LR). ks_tac KS1.
      * rewrite (L5SAR.cs_of_preserved R1 R2 24%nat RP2) by inl. rewrite (KS1 24%nat) by inl. exact A24.
      * rewrite (L5SAR.cs_of_preserved R1 R2 22%nat RP2) by inl. exact E27'.
      * unfold PGSSRA1.fields_eq; exact I.
  - (* [comment removed for export] *)
    destruct VS as (W0' & W8 & W16 & Hn1 & Hc1 & Hce & DQ & CQ).
    pose proof (PMF.u8_of_u64 RSEGS M tb (c1 + 1) ltac:(lia) W0') as B0. pose proof (PMF.odd_byte c1 Hce ltac:(lia)) as ODB.
    assert (H39 : 0 <= (c1 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)); lia).
    LeanFeed.pfeed PP (PMASRDP.srdRL_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
       | 40%nat => (c1 + 1) mod 256 | 41%nat => n1 | 43%nat => k
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.u64_at _ _ (tb + _) _ => unfold MV; vis64 TAV
      | |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
      | |- PMASRDP.aligned _ _ => unfold PMASRDP.aligned; lia
      | |- _ => lia end]).
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS1 & KS1 & E1 & E10 & E11 & E12 & E22)).
    apply (ro_step fx fx1 R 0xb51e4 R1 0xd628c M model src (PM.VLong c1 n1 q1) tg sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    apply (call_resize fx1 R1 M model1 src (PM.VLong c1 n1 q1) tg sm cr LK Aw (n1 + k) 741924 E1 ltac:(split; [lia| reflexivity])); try assumption.
    + rewrite (KS1 2%nat) by inl. exact A2.
    + intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
    + cbn [PM.vs_size]. unfold PM.CHUNK. lia.
    + unfold PM.CHUNK. lia.
    + intros fx2 R2 M2 model2 LK2 Aw2 tb2 tg2 cr2 RP2 SZ2 _ SO2.
      refine (after_resize1 mu0 IH fx2 R2 M2 model2 src tb2 tg2 sm cr2 LK2 Aw2 w k n1 _ _ _ Hk HkC Hw SO2 SZ2 ltac:(lia) SZ CONS STEP _ PRG MU).
      * apply (lregs_pres R1 R2 w RP2). apply (lregs_keep R R1 w LR). ks_tac KS1.
      * rewrite (L5SAR.cs_of_preserved R1 R2 24%nat RP2) by inl. rewrite (KS1 24%nat) by inl. exact A24.
      * rewrite (L5SAR.cs_of_preserved R1 R2 22%nat RP2) by inl. exact E22.
      * unfold PGSSRA1.fields_eq; exact I.
Qed.

End Call.
End WithHeap.
End PGSSRA3.
