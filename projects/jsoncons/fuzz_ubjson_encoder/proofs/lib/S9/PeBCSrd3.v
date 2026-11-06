(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0S9 L5StepARB0S9.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PmSpecsAX PeSpecsAb PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCModelA PeCSpecsA PeCSpecsAb PmModelFactsA PeStepAB0 PmStep PmTxtKit2 PeBSrcKitJ PeBCReset1 PeBRsKit PmSpecs PeCSink PeCModel PeCSpecs PeCFrame PeCSrcD PeCTxtSpecsA PeBCSrcRead PeBCSrcFillTb PeBSrdP PeBCSrd1 PeBCSrd2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECSRD3B.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Lemma lit_shift (a b i : Z) : Z_to_bv 64 a = Z_to_bv 64 b -> Z_to_bv 64 (a + i) = Z_to_bv 64 (b + i).
Proof.
  intros E. apply bv_eq in E. rewrite !Z_to_bv_unsigned in E. apply bv_eq. rewrite !Z_to_bv_unsigned.
  rewrite <- (bv_wrap_add_idemp_l 64 a i), <- (bv_wrap_add_idemp_l 64 b i), E. reflexivity.
Qed.

Lemma bytes_at_samew M (a b : Z) (l : list Z) : Z_to_bv 64 a = Z_to_bv 64 b -> L5.bytes_at RSEGS M a l -> L5.bytes_at RSEGS M b l.
Proof. intros E BY i Hi. unfold L5.u8_at. rewrite <- (lit_shift a b (Z.of_nat i) E). exact (BY i Hi). Qed.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation pot := PECSRD1B.pot.
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
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.

Section Call.
Variables (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet) (LBX : list (Z * Z)) (FF LK0 : list fframe) (Aw0 : list (Z * Z)) (cr0 : credit).
Variables (S r fb len : Z) (s0 : PM.pst) (str : PM.vstr) (sm0 : PM.strm).
Variables (pl tl : list Z).
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis K0 : K [].
Hypothesis FRM0 : PMSPA.ffroomA 5 FF LK0.
Hypothesis FRS : PMSPA.ffrsA FF S.
Hypothesis FOK : PECA.frame_ok5 FF fb.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UNS0 : PM.vs_size (PM.p_tb s0) + PM.unread (PM.p_src s0) sm0 < 2 ^ 26.
Hypothesis STKSH0 : shadow_zero M0 (S - 22528) 2816.
Hypothesis POK : PECS.payload_ok pl.
Hypothesis TL0 : Z.of_nat (length tl) = PM.vs_size (PM.p_tb s0).
Hypothesis POS0 : 0 <= PEC.pos_of pl (PM.p_src s0) sm0.
Hypothesis RSZ : @PECTXSA.cstr_resize_spec SCFG_P RSEGS AD L ar HI.
Hypothesis FB : PECSB.fill_buffer_spec L ar HI.
Hypothesis FBT : PECFILLTBB.cfill_tb_spec L ar HI.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.pst) (sm' : PM.strm) (cr' : credit) (d : Z),
  regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 d -> 0 <= d <= len ->
  PMSPA.consumed (PM.p_src s0) (PM.p_src s') sm0 sm' = d -> PM.vs_size (PM.p_tb s') = PM.vs_size (PM.p_tb s0) + d ->
  d = Z.min len (PM.unread (PM.p_src s0) sm0) ->
  L5.bytes_at RSEGS M' (PM.vs_data (PMSPA.o_tb AD fb) (PM.p_tb s')) (tl ++ UbjRef.slice pl (PEC.pos_of pl (PM.p_src s0) sm0) d) ->
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M' (PMSPA.o_p AD fb) (PMSPA.o_is AD fb) s' -> PM.iss_at RSEGS AD PMSPA.accA M' (PMSPA.o_is AD fb) str sm' ->
  PM.tb_ok (PM.p_tb s') (PM.p_tg s') ->
  PM.p_more s' = PM.p_more s0 -> PM.p_done s' = PM.p_done s0 -> PM.p_depth s' = PM.p_depth s0 ->
  PM.p_b s' = PM.p_b s0 -> PM.p_k s' = PM.p_k s0 -> PM.p_stk s' = PM.p_stk s0 ->
  PMSPA.src_step (PM.p_src s0) (PM.p_src s') sm0 sm' ->
  PEC.content_ok RSEGS AD M' fb pl (PM.p_src s') str sm' ->
  L5CA.ahpres L ar LBX FF S (PMSPA.pm_scr 5) (PMSPA.W_srcf AD fb ++ [(PMSPA.o_tb AD fb, 24)]) M0 M' ->
  PMSPA.credit_keep cr0 cr' (pot L ar s0) (pot L ar s') ->
  model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K.

#[local] Abbreviation op := (PECSRD1B.op fb).
#[local] Abbreviation os := (PECSRD1B.os fb).
#[local] Abbreviation ois := (PECSRD1B.ois fb).
#[local] Abbreviation tb := (PECSRD1B.tb fb).
#[local] Abbreviation W0 := (PECSRD1B.W0 fb).
#[local] Abbreviation U := (PECSRD1B.U R0).
#[local] Abbreviation saves13 := (PECSRD1B.saves13 R0 S).
#[local] Abbreviation locals := (PECSRD1B.locals S fb len).
#[local] Abbreviation kept_rs := (PECSRD1B.kept_rs R0).
#[local] Abbreviation memrel := (PECSRD1B.memrel L ar M0 LBX FF S fb).
#[local] Abbreviation fields_eq := (PECSRD1B.fields_eq s0).
#[local] Abbreviation acct := (PECSRD1B.acct len s0 sm0).
#[local] Abbreviation st_ok := (PECSRD1B.st_ok L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb len s0 str pl).
#[local] Abbreviation lregs := (PECSRD1B.lregs R0 S fb).
#[local] Abbreviation tbdst := (PECSRD1B.tbdst fb).
#[local] Abbreviation lstate := (PECSRD1B.lstate L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb len s0 str sm0 pl tl).
#[local] Abbreviation IHt := (PECSRD1B.IHt L ar HI R0 M0 model0 K LBX FF LK0 Aw0 cr0 S fb len s0 str sm0 pl tl).
#[local] Abbreviation lregs_keep := (PECSRD1B.lregs_keep R0 S fb len Hlen).
#[local] Abbreviation lregs_set := (PECSRD1B.lregs_set R0 S fb len Hlen).
#[local] Abbreviation lregs_pres := (PECSRD1B.lregs_pres R0 S fb len Hlen).
#[local] Abbreviation geo := (PECSRD1B.geo fb).
#[local] Abbreviation fbb := (PECSRD1B.fbb FF fb FOK).
#[local] Abbreviation finish := (PECSRD1B.finish L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation callee_mem := (PECSRD1B.callee_mem L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation centry := (PECSRD1B.centry L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation call_resize := (PECSRD1B.call_resize L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation call_srcread := (PECSRD1B.call_srcread L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation call_filltb := (PECSRD1B.call_filltb L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation unread_nn := (PECSRD1B.unread_nn L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation TX := (PECSRD1B.TX fb s0 sm0 pl tl).
#[local] Abbreviation pos0 := (PECSRD1B.pos0 s0 sm0 pl).
#[local] Abbreviation pos_acct := (PECSRD1B.pos_acct L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation TX_len := (PECSRD1B.TX_len L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation vpack := (PECSRD1B.vpack L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation ro_step := (PECSRD1B.ro_step L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation outside_W0 := (PECSRD1B.outside_W0 L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat; bvr1 R0 23%nat; bvr1 R0 24%nat; bvr1 R0 25%nat; bvr1 R0 26%nat; bvr1 R0 27%nat.

#[local] Abbreviation after_read := (PECSRD2B.after_read L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
Ltac ks_tac KS := intros x Hx; apply KS; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx.

Lemma src_step_trans a b c sa sb sc : PMSPA.src_step a b sa sb -> PMSPA.src_step b c sb sc -> PMSPA.src_step a c sa sc.
Proof. clear.
  unfold PMSPA.src_step. intros (E1 & E2 & L1 & S1 & U1) (E3 & E4 & L2 & S2 & U2).
  split; [congruence|]. split; [congruence|]. split; [lia|]. split; [intros X; apply S2; apply S1; exact X| lia].
Qed.
Lemma mu_dec src src' sm sm' : PMSPA.src_step src src' sm sm' -> (PM.sm_st sm = 0 \/ PM.sm_st sm = 2) -> (PM.sm_st sm' = 0 \/ PM.sm_st sm' = 2) ->
  (PM.unread src' sm' < PM.unread src sm \/ (PM.sm_st sm = 0 /\ PM.sm_st sm' = 2)) -> PM.mu_src src' sm' < PM.mu_src src sm.
Proof. clear.
  unfold PM.mu_src. intros (_ & _ & _ & S2 & U) ST ST' H.
  destruct ST as [E|E]; destruct ST' as [E'|E']; rewrite ?E, ?E' in *; cbn [Z.eqb]; [lia|lia| specialize (S2 eq_refl); lia| lia].
Qed.

Lemma at_srcread mu0 (IH : IHt mu0) (fx : FPState) R M model s sm cr LK Aw (w k n p : Z) :
  lregs R w -> getr R (reg 1) = Z_to_bv 64 0xbbe2c -> getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 p -> getr R (reg 12) = Z_to_bv 64 k ->
  getr R (reg 24) = Z_to_bv 64 k -> getr R (reg 22) = Z_to_bv 64 n ->
  1 <= k <= w -> k <= PM.CHUNK -> w <= len -> tbdst s p k -> p = PM.vs_data tb (PM.p_tb s) + n ->
  st_ok M model s sm cr LK Aw -> PM.vs_size (PM.p_tb s) = n + k -> 0 <= n -> n = PM.vs_size (PM.p_tb s0) + (len - w) ->
  PMSPA.consumed (PM.p_src s0) (PM.p_src s) sm0 sm = len - w ->
  PMSPA.src_step (PM.p_src s0) (PM.p_src s) sm0 sm -> fields_eq s -> TX M (PM.p_tb s) (len - w) ->
  (1 <= PM.sr_rem (PM.p_src s) \/ PM.sm_st sm = 0) -> PM.mu_src (PM.p_src s) sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb9148 M model) K.
Proof using All.
  intros LR A1 A10 A11 A12 A24 A27 Hk HkC Hw DST Hp SO SZ Hn0 En CONS STEP FE TXh PRG MU.
  pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & KP).
  pose proof (unread_nn M model s sm cr LK Aw SO) as (UN & ST & RM & GE).
  apply (call_srcread fx R M model s sm cr LK Aw p k 0xbbe2c A1 ltac:(split; [lia| reflexivity]) A2 KP A10 A11 A12 ltac:(lia) DST SO).
  intros fx2 R2 M2 model2 LK2 Aw2 src2 sm2 d RP2 Y10 Hd CONS2 SHORT ZR STEP2 BYT TBK SO2.
  pose proof (unread_nn M2 model2 _ sm2 cr LK2 Aw2 SO2) as (UN2 & ST2 & RM2 & GE2). cbn [PMSPA.with_src PM.p_src] in UN2, RM2.
  refine (after_read mu0 IH fx2 R2 M2 model2 (PMSPA.with_src s src2) sm2 cr LK2 Aw2 w k d n (lregs_pres R R2 w RP2 LR) Y10 _ _ Hd Hk HkC Hw SO2 SZ Hn0 En _ _ FE _ _).
  - rewrite (L5SAR.cs_of_preserved R R2 24%nat RP2) by inl. exact A24.
  - rewrite (L5SAR.cs_of_preserved R R2 22%nat RP2) by inl. exact A27.
  - unfold PMSPA.consumed in *. cbn [PMSPA.with_src PM.p_src]. lia.
  - cbn [PMSPA.with_src PM.p_src]. exact (src_step_trans _ _ _ _ _ _ STEP STEP2).
  -
    unfold PECSRD1B.TX. cbn [PMSPA.with_src PM.p_tb].
    destruct (pos_acct M model s sm cr LK Aw (len - w) SO CONS) as (EPOS & P0 & P1 & _).
    pose proof (TX_len M model s sm cr LK Aw (len - w) SO CONS ltac:(lia)) as TL.
    rewrite (PECSD.slice_app pl pos0 (len - w) d) by lia. rewrite app_assoc.
    apply (proj2 (PECSD.bytes_at_app RSEGS M2 _ _ _)). split.
    + apply TBK; [rewrite TL; lia| rewrite TL; lia| exact TXh].
    + rewrite TL, <- EPOS. replace (PM.vs_data tb (PM.p_tb s) + (PM.vs_size (PM.p_tb s0) + (len - w))) with p by lia. exact BYT.
  - cbn [PMSPA.with_src PM.p_src]. enough (PM.mu_src src2 sm2 < PM.mu_src (PM.p_src s) sm) by lia.
    apply (mu_dec _ _ _ _ STEP2 ST ST2).
    unfold PMSPA.consumed in CONS2. destruct (Z.eq_dec d 0) as [D0|D0]; [right| left; lia].
    split; [| exact (ZR D0)].
    destruct PRG as [P1|P1]; [| exact P1]. exfalso. specialize (SHORT ltac:(lia)). unfold PM.unread in SHORT, CONS2. lia.
Qed.

Lemma after_resize1 mu0 (IH : IHt mu0) (fx : FPState) R M model s sm cr LK Aw (w k n : Z) :
  lregs R w -> getr R (reg 24) = Z_to_bv 64 k -> getr R (reg 22) = Z_to_bv 64 n ->
  1 <= k <= w -> k <= PM.CHUNK -> w <= len ->
  st_ok M model s sm cr LK Aw -> PM.vs_size (PM.p_tb s) = n + k -> 0 <= n -> n = PM.vs_size (PM.p_tb s0) + (len - w) ->
  PMSPA.consumed (PM.p_src s0) (PM.p_src s) sm0 sm = len - w ->
  PMSPA.src_step (PM.p_src s0) (PM.p_src s) sm0 sm -> fields_eq s -> TX M (PM.p_tb s) (len - w) ->
  (1 <= PM.sr_rem (PM.p_src s) \/ PM.sm_st sm = 0) -> PM.mu_src (PM.p_src s) sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xbbde4 M model) K.
Proof using All.
  intros LR A24 A27 Hk HkC Hw SO SZ Hn0 En CONS STEP FE TXh PRG MU.
  pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & KP).
  pose proof (unread_nn M model s sm cr LK Aw SO) as (UN & ST & RM & GE).
  assert (Hn : n < 67108864) by (unfold PMSPA.consumed in CONS; lia).
  pose proof (vpack M model s sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & _).
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
  pose proof LC as (L160 & L152 & L144 & L136 & L128 & L120 & L112).
  pose proof geo as (Eop & Eos & Eois & Etb).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  assert (D1 : S - 192 + 192 <= os \/ os + 296 <= S - 192) by (right; lia).
  assert (D2 : S - 192 + 192 <= tb \/ tb + 24 <= S - 192) by (right; lia).
  assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (left; lia).
  bvr.
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _).
  replace (op + 336) with tb in VS by lia.
  assert (HkC' : k <= 16384) by (unfold PM.CHUNK in HkC; exact HkC).
  set (MV := mrestrict (ahid Aw model) M) in *.
  revert VS SZ. destruct (PM.p_tb s) as [n1|c1 n1 q1] eqn:ETB; intros (VD & VC & VS) SZ; cbn [PM.vs_size] in SZ.
  -
    destruct VS as (Hn1 & B0). pose proof (PMF.even_byte n1) as EV.
    pose proof (PMBSRDP.srdQS_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
       | 40%nat => 2 * n1 | 43%nat => k | 46%nat => n
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) as PP.
    cbn beta iota in PP.
    L5SAR.feed PP ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
      | |- PMBSRDP.aligned _ _ => unfold PMBSRDP.aligned; lia
      | |- _ => lia end]).
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS1 & KS1 & E1 & E10 & E11 & E12)).
    apply (ro_step fx fx1 R 0xbbde4 R1 0xb9148 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    refine (at_srcread mu0 IH fx1 R1 M model1 s sm cr LK Aw w k n (tb + n + 1) _ E1 E10 E11 E12 _ _ Hk HkC Hw _ _ SO1 _ Hn0 En CONS STEP FE _ PRG MU).
    + apply (lregs_keep R R1 w LR). ks_tac KS1.
    + rewrite (KS1 24%nat) by inl. exact A24.
    + rewrite (KS1 22%nat) by inl. exact A27.
    + unfold PECSRD1B.tbdst. left. split; [exists n1; exact ETB|]. lia.
    + rewrite ETB. cbn [PM.vs_data]. lia.
    + rewrite ETB. exact SZ.
    + first [exact TXh| rewrite ETB; exact TXh].
  -
    destruct VS as (W0' & W8 & W16 & Hn1 & Hc1 & Hce & DQ & CQ).
    pose proof (PMF.u8_of_u64 RSEGS M tb (c1 + 1) ltac:(lia) W0') as B0. pose proof (PMF.odd_byte c1 Hce ltac:(lia)) as ODB.
    assert (H39 : 0 <= (c1 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)); lia).
    assert (IN : In (q1, c1) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own; rewrite ETB; cbn; right; right; left; reflexivity).
    destruct (WB _ IN) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in Q0, Q1, Q2, Q3, Q4, Q5.
    pose proof (PMBSRDP.srdQL_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
       | 40%nat => (c1 + 1) mod 256 | 42%nat => q1 | 43%nat => k | 46%nat => n
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) as PP.
    cbn beta iota in PP.
    L5SAR.feed PP ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.u64_at _ _ (tb + _) _ => unfold MV; vis64 TAV
      | |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
      | |- PMBSRDP.aligned _ _ => unfold PMBSRDP.aligned; lia
      | |- _ => lia end]).
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS1 & KS1 & E1 & E10 & E11 & E12)).
    apply (ro_step fx fx1 R 0xbbde4 R1 0xb9148 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    refine (at_srcread mu0 IH fx1 R1 M model1 s sm cr LK Aw w k n (q1 + n) _ E1 E10 E11 E12 _ _ Hk HkC Hw _ _ SO1 _ Hn0 En CONS STEP FE _ PRG MU).
    + apply (lregs_keep R R1 w LR). ks_tac KS1.
    + rewrite (KS1 24%nat) by inl. exact A24.
    + rewrite (KS1 22%nat) by inl. exact A27.
    + unfold PECSRD1B.tbdst. right. exists c1, n1, q1. split; [exact ETB|]. lia.
    + rewrite ETB. cbn [PM.vs_data]. lia.
    + rewrite ETB. exact SZ.
    + first [exact TXh| rewrite ETB; exact TXh].
Qed.

Lemma rpath mu0 (IH : IHt mu0) (fx : FPState) R M model s sm cr LK Aw (w k : Z) :
  lregs R w -> getr R (reg 24) = Z_to_bv 64 k -> 1 <= k <= w -> k <= PM.CHUNK -> w <= len ->
  st_ok M model s sm cr LK Aw -> acct s sm w -> TX M (PM.p_tb s) (len - w) ->
  (1 <= PM.sr_rem (PM.p_src s) \/ PM.sm_st sm = 0) -> PM.mu_src (PM.p_src s) sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xbbda4 M model) K.
Proof using All.
  intros LR A24 Hk HkC Hw SO (CONS & SZ & STEP & FE) TXh PRG MU.
  pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & KP).
  pose proof (unread_nn M model s sm cr LK Aw SO) as (UN & ST & RM & GE).
  pose proof (vpack M model s sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & _).
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
  pose proof LC as (L160 & L152 & L144 & L136 & L128 & L120 & L112).
  pose proof geo as (Eop & Eos & Eois & Etb).
  assert (D1 : S - 192 + 192 <= os \/ os + 296 <= S - 192) by (right; lia).
  assert (D2 : S - 192 + 192 <= tb \/ tb + 24 <= S - 192) by (right; lia).
  assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (left; lia).
  bvr.
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _).
  replace (op + 336) with tb in VS by lia.
  assert (HkC' : k <= 16384) by (unfold PM.CHUNK in HkC; exact HkC).
  assert (HSZ : PM.vs_size (PM.p_tb s) < 67108864) by (unfold PMSPA.consumed in CONS; lia).
  set (MV := mrestrict (ahid Aw model) M) in *.
  revert VS SZ HSZ. destruct (PM.p_tb s) as [n1|c1 n1 q1] eqn:ETB; intros (VD & VC & VS) SZ HSZ; cbn [PM.vs_size] in SZ, HSZ.
  -
    destruct VS as (Hn1 & B0). pose proof (PMF.even_byte n1) as EV.
    pose proof (PMBSRDP.srdRS_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
       | 40%nat => 2 * n1 | 43%nat => k
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) as PP.
    cbn beta iota in PP.
    L5SAR.feed PP ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
      | |- PMBSRDP.aligned _ _ => unfold PMBSRDP.aligned; lia
      | |- _ => lia end]).
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS1 & KS1 & E1 & E10 & E11 & E12 & E22)).
    apply (ro_step fx fx1 R 0xbbda4 R1 0xdbcf4 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    assert (E11' : getr R1 (reg 11) = Z_to_bv 64 (n1 + k)) by (rewrite E11; f_equal; rewrite Z.mul_comm, Z.div_mul by lia; lia).
    assert (E22' : getr R1 (reg 22) = Z_to_bv 64 n1) by (rewrite E22; f_equal; rewrite Z.mul_comm, Z.div_mul by lia; lia).
    apply (call_resize fx1 R1 M model1 s sm cr LK Aw (n1 + k) 769508 E1 ltac:(split; [lia| reflexivity])); try assumption.
    + rewrite (KS1 2%nat) by inl. exact A2.
    + intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
    + rewrite ETB. cbn [PM.vs_size]. unfold PM.CHUNK. lia.
    + unfold PM.CHUNK. lia.
    + intros fx2 R2 M2 model2 LK2 Aw2 tb2 tg2 cr2 RP2 SZ2 _ BYT2 SO2.
      refine (after_resize1 mu0 IH fx2 R2 M2 model2 (PMTK2.with_tb s tb2 tg2) sm cr2 LK2 Aw2 w k n1 _ _ _ Hk HkC Hw SO2 SZ2 ltac:(lia) SZ CONS STEP _ _ PRG MU).
      * apply (lregs_pres R1 R2 w RP2). apply (lregs_keep R R1 w LR). ks_tac KS1.
      * rewrite (L5SAR.cs_of_preserved R1 R2 24%nat RP2) by inl. rewrite (KS1 24%nat) by inl. exact A24.
      * rewrite (L5SAR.cs_of_preserved R1 R2 22%nat RP2) by inl. exact E22'.
      * destruct FE as (F1 & F2 & F3 & F4 & F5 & F6). unfold PECSRD1B.fields_eq. cbn [PMTK2.with_tb PM.p_more PM.p_done PM.p_depth PM.p_b PM.p_k PM.p_stk].
        repeat split; assumption.
      * unfold PECSRD1B.TX. cbn [PMTK2.with_tb PM.p_tb]. apply BYT2; [| first [exact TXh| rewrite ETB; exact TXh| rewrite <- ETB; exact TXh]].
        rewrite (TX_len M model s sm cr LK Aw (len - w) SO CONS ltac:(lia)). first [rewrite ETB| idtac]. cbn [PM.vs_size]. lia.
  -
    destruct VS as (W0' & W8 & W16 & Hn1 & Hc1 & Hce & DQ & CQ).
    pose proof (PMF.u8_of_u64 RSEGS M tb (c1 + 1) ltac:(lia) W0') as B0. pose proof (PMF.odd_byte c1 Hce ltac:(lia)) as ODB.
    assert (H39 : 0 <= (c1 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)); lia).
    pose proof (PMBSRDP.srdRL_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
       | 40%nat => (c1 + 1) mod 256 | 41%nat => n1 | 43%nat => k
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) as PP.
    cbn beta iota in PP.
    L5SAR.feed PP ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.u64_at _ _ (tb + _) _ => unfold MV; vis64 TAV
      | |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
      | |- PMBSRDP.aligned _ _ => unfold PMBSRDP.aligned; lia
      | |- _ => lia end]).
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS1 & KS1 & E1 & E10 & E11 & E12 & E22)).
    apply (ro_step fx fx1 R 0xbbda4 R1 0xdbcf4 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    apply (call_resize fx1 R1 M model1 s sm cr LK Aw (n1 + k) 769508 E1 ltac:(split; [lia| reflexivity])); try assumption.
    + rewrite (KS1 2%nat) by inl. exact A2.
    + intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
    + rewrite ETB. cbn [PM.vs_size]. unfold PM.CHUNK. lia.
    + unfold PM.CHUNK. lia.
    + intros fx2 R2 M2 model2 LK2 Aw2 tb2 tg2 cr2 RP2 SZ2 _ BYT2 SO2.
      refine (after_resize1 mu0 IH fx2 R2 M2 model2 (PMTK2.with_tb s tb2 tg2) sm cr2 LK2 Aw2 w k n1 _ _ _ Hk HkC Hw SO2 SZ2 ltac:(lia) SZ CONS STEP _ _ PRG MU).
      * apply (lregs_pres R1 R2 w RP2). apply (lregs_keep R R1 w LR). ks_tac KS1.
      * rewrite (L5SAR.cs_of_preserved R1 R2 24%nat RP2) by inl. rewrite (KS1 24%nat) by inl. exact A24.
      * rewrite (L5SAR.cs_of_preserved R1 R2 22%nat RP2) by inl. exact E22.
      * destruct FE as (F1 & F2 & F3 & F4 & F5 & F6). unfold PECSRD1B.fields_eq. cbn [PMTK2.with_tb PM.p_more PM.p_done PM.p_depth PM.p_b PM.p_k PM.p_stk].
        repeat split; assumption.
      * unfold PECSRD1B.TX. cbn [PMTK2.with_tb PM.p_tb]. apply BYT2; [| first [exact TXh| rewrite ETB; exact TXh| rewrite <- ETB; exact TXh]].
        rewrite (TX_len M model s sm cr LK Aw (len - w) SO CONS ltac:(lia)). first [rewrite ETB| idtac]. cbn [PM.vs_size]. lia.
Qed.

End Call.
End WithHeap.
End PECSRD3B.
