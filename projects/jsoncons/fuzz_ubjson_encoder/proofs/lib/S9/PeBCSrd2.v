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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCModelA PeCSpecsA PeCSpecsAb PmModelFactsA PeStepAB0 PmStep PmTxtKit2 PeBSrcKitJ PeBCReset1 PeBRsKit PmSpecs PeCSink PeCModel PeCSpecs PeCFrame PeCSrcD PeCTxtSpecsA PeBCSrcRead PeBCSrcFillTb PeBSrdP PeBCSrd1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECSRD2B.
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

Ltac ks_tac KS := intros x Hx; apply KS; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx.

Lemma after_shrink mu0 (IH : IHt mu0) (fx : FPState) R M model s sm cr LK Aw (w d : Z) :
  lregs R w -> getr R (reg 25) = Z_to_bv 64 d -> 0 <= d <= w -> d <= PM.CHUNK -> 1 <= w <= len ->
  st_ok M model s sm cr LK Aw -> acct s sm (w - d) -> TX M (PM.p_tb s) (len - (w - d)) -> PM.mu_src (PM.p_src s) sm < mu0 ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xbbefc M model) K.
Proof using All.
  intros LR A26 Hd HdC Hw SO AC TXh MU. unfold PM.CHUNK in HdC.
  pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & KP).
  pose proof (vpack M model s sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as (MR & SV & LC & _).
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
  pose proof LC as (L160 & L152 & L144 & L136 & L128 & L120 & L112).
  pose proof geo as (Eop & Eos & Eois & Etb).
  assert (D1 : S - 192 + 192 <= os \/ os + 296 <= S - 192) by (right; lia).
  assert (D2 : S - 192 + 192 <= tb \/ tb + 24 <= S - 192) by (right; lia).
  assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (left; lia).
  bvr.
  set (MV := mrestrict (ahid Aw model) M) in *.
  pose proof (PMBSRDP.srdF_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w | 44%nat => d
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) as PP.
  cbn beta iota in PP.
  L5SAR.feed PP ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- PMBSRDP.aligned _ _ => unfold PMBSRDP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & [(MS1 & KS1 & E8 & C0) | (MS1 & KS1 & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & C0)]).
  - apply (ro_step fx fx1 R 0xbbefc R1 0xbbd60 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    rewrite subw in C0 by lia.
    apply (IH fx1 R1 M model1 s sm cr LK Aw (w - d) MU).
    split; [|split; [exact SO1| split; [exact AC| split; [lia| exact TXh]]]].
    apply (lregs_set R R1 w (w - d) LR); [ks_tac KS1| exact E8].
  - apply (ro_step fx fx1 R 0xbbefc R1 0xbbf78 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    rewrite subw in C0 by lia.
    apply (finish fx1 R1 M model1 s sm cr LK Aw 0); try assumption.
    + intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [assumption|]). destruct Hx.
    + intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
    + rewrite E10. f_equal. lia.
    + lia.
    + replace (len - 0) with (len - (w - d)) by lia. exact TXh.
    + left. reflexivity.
    + replace 0 with (w - d) by lia. exact AC.
Qed.

Lemma after_read mu0 (IH : IHt mu0) (fx : FPState) R M model s sm cr LK Aw (w k d n : Z) :
  lregs R w -> getr R (reg 10) = Z_to_bv 64 d -> getr R (reg 24) = Z_to_bv 64 k -> getr R (reg 22) = Z_to_bv 64 n ->
  0 <= d <= k -> 1 <= k <= w -> k <= PM.CHUNK -> w <= len ->
  st_ok M model s sm cr LK Aw -> PM.vs_size (PM.p_tb s) = n + k -> 0 <= n -> n = PM.vs_size (PM.p_tb s0) + (len - w) ->
  PMSPA.consumed (PM.p_src s0) (PM.p_src s) sm0 sm = len - w + d ->
  PMSPA.src_step (PM.p_src s0) (PM.p_src s) sm0 sm -> fields_eq s -> TX M (PM.p_tb s) (len - w + d) ->
  PM.mu_src (PM.p_src s) sm < mu0 ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xbbe2c M model) K.
Proof using All.
  intros LR A10 A24 A27 Hd Hk HkC Hw SO SZ Hn0 En CONS STEP FE TXh MU. unfold PM.CHUNK in HkC.
  pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & KP).
  pose proof (unread_nn M model s sm cr LK Aw SO) as (UN & _).
  assert (Hn : 0 <= n < 67108864) by (unfold PMSPA.consumed in CONS; lia).
  pose proof (vpack M model s sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as (MR & SV & LC & _).
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
  pose proof LC as (L160 & L152 & L144 & L136 & L128 & L120 & L112).
  pose proof geo as (Eop & Eos & Eois & Etb).
  assert (D1 : S - 192 + 192 <= os \/ os + 296 <= S - 192) by (right; lia).
  assert (D2 : S - 192 + 192 <= tb \/ tb + 24 <= S - 192) by (right; lia).
  assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (left; lia).
  bvr.
  set (MV := mrestrict (ahid Aw model) M) in *.
  pose proof (PMBSRDP.srdE_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w | 43%nat => k
       | 44%nat => d | 46%nat => n
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) as PP.
  cbn beta iota in PP.
  L5SAR.feed PP ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- PMBSRDP.aligned _ _ => unfold PMBSRDP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & [(MS1 & KS1 & E1 & E10 & E11 & E12 & E25 & C0) | [(MS1 & KS1 & E8 & E25 & C0 & C1)
                 | (MS1 & KS1 & E1 & E2 & E8 & E9 & E10 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & C0 & C1)]]).
  -
    apply (ro_step fx fx1 R 0xbbe2c R1 0xdbcf4 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    assert (DK' : d < k).
    { destruct (Z.eq_dec d k) as [->|NE]; [rewrite Z.sub_diag, Zmod_0_l in C0; lia| lia]. }
    apply (call_resize fx1 R1 M model1 s sm cr LK Aw (d + n) 769788); try assumption.
    + split; [lia| reflexivity].
    + rewrite (KS1 2%nat) by inl. exact A2.
    + intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
    + unfold PM.CHUNK. lia.
    + unfold PM.CHUNK. lia.
    + intros fx2 R2 M2 model2 LK2 Aw2 tb2 tg2 cr2 RP2 SZ2 _ BYT2 SO2.
      apply (after_shrink mu0 IH fx2 R2 M2 model2 (PMTK2.with_tb s tb2 tg2) sm cr2 LK2 Aw2 w d); try assumption.
      * apply (lregs_pres R1 R2 w RP2). apply (lregs_keep R R1 w LR). ks_tac KS1.
      * rewrite (L5SAR.cs_of_preserved R1 R2 25%nat RP2) by inl. exact E25.
      * lia.
      * unfold PM.CHUNK. lia.
      * lia.
      * unfold PECSRD1B.acct. cbn [PMTK2.with_tb PM.p_src PM.p_tb]. split; [lia|]. split; [lia|]. split; [exact STEP|].
        destruct FE as (F1 & F2 & F3 & F4 & F5 & F6). unfold PECSRD1B.fields_eq. cbn [PMTK2.with_tb PM.p_more PM.p_done PM.p_depth PM.p_b PM.p_k PM.p_stk].
        repeat split; assumption.
      * unfold PECSRD1B.TX. cbn [PMTK2.with_tb PM.p_tb]. replace (len - (w - d)) with (len - w + d) by lia. apply BYT2; [| exact TXh].
        rewrite (TX_len M model s sm cr LK Aw (len - w + d) SO CONS ltac:(lia)). lia.
  -
    apply (ro_step fx fx1 R 0xbbe2c R1 0xbbd60 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    rewrite subw in C0 by lia.
    assert (DK' : d = k) by (apply (mod_lt1 (d - k)) in C1; lia). subst d.
    apply (IH fx1 R1 M model1 s sm cr LK Aw (w - k) MU).
    split; [|split; [exact SO1| split; [|split; [lia| replace (len - (w - k)) with (len - w + k) by lia; exact TXh]]]].
    + apply (lregs_set R R1 w (w - k) LR); [ks_tac KS1| exact E8].
    + unfold PECSRD1B.acct. split; [lia|]. split; [lia|]. split; [exact STEP| exact FE].
  -
    apply (ro_step fx fx1 R 0xbbe2c R1 0xbbf78 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    rewrite subw in C0 by lia.
    assert (DK' : d = k) by (apply (mod_lt1 (d - k)) in C1; lia). subst d.
    apply (finish fx1 R1 M model1 s sm cr LK Aw 0); try assumption.
    + intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [assumption|]). destruct Hx.
    + intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
    + rewrite E10. f_equal. lia.
    + lia.
    + replace (len - 0) with (len - w + k) by lia. exact TXh.
    + left. lia.
    + unfold PECSRD1B.acct. split; [lia|]. split; [lia|]. split; [exact STEP| exact FE].
Qed.

End Call.
End WithHeap.
End PECSRD2B.
