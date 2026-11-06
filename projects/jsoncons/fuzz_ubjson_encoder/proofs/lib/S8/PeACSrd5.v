(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreAS8 L5StepARS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PmSpecsAX PeSpecsAa PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCModelA PeCSpecsA PeCSpecsAa PmModelFactsA PeStepA PmStep PmTxtKit2 PeASrcKitJ PeACReset1 PeARsKit PmSpecs PeCSink PeCModel PeCSpecs PeCFrame PeCSrcD PeCTxtSpecsA PeACSrcRead PeACSrcFillTb PeASrdP PeACSrd1 PeACSrd2 PeACSrd3 PeACSrd4.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_b7934_b7938.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECSRD5A.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Lemma lit_shift (a b i : Z) : Z_to_bv 64 a = Z_to_bv 64 b -> Z_to_bv 64 (a + i) = Z_to_bv 64 (b + i).
Proof.
  intros E. apply bv_eq in E. rewrite !Z_to_bv_unsigned in E. apply bv_eq. rewrite !Z_to_bv_unsigned.
  rewrite <- (bv_wrap_add_idemp_l 64 a i), <- (bv_wrap_add_idemp_l 64 b i), E. reflexivity.
Qed.

Lemma bytes_at_samew M (a b : Z) (l : list Z) : Z_to_bv 64 a = Z_to_bv 64 b -> L5.bytes_at RSEGS M a l -> L5.bytes_at RSEGS M b l.
Proof. intros E BY i Hi. unfold L5.u8_at. rewrite <- (lit_shift a b (Z.of_nat i) E). exact (BY i Hi). Qed.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation pot := PECSRD1A.pot.
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
Hypothesis FB : PECSA.fill_buffer_spec L ar HI.
Hypothesis FBT : PECFILLTBA.cfill_tb_spec L ar HI.
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

#[local] Abbreviation op := (PECSRD1A.op fb).
#[local] Abbreviation os := (PECSRD1A.os fb).
#[local] Abbreviation ois := (PECSRD1A.ois fb).
#[local] Abbreviation tb := (PECSRD1A.tb fb).
#[local] Abbreviation W0 := (PECSRD1A.W0 fb).
#[local] Abbreviation U := (PECSRD1A.U R0).
#[local] Abbreviation saves13 := (PECSRD1A.saves13 R0 S).
#[local] Abbreviation locals := (PECSRD1A.locals S fb len).
#[local] Abbreviation kept_rs := (PECSRD1A.kept_rs R0).
#[local] Abbreviation memrel := (PECSRD1A.memrel L ar M0 LBX FF S fb).
#[local] Abbreviation fields_eq := (PECSRD1A.fields_eq s0).
#[local] Abbreviation acct := (PECSRD1A.acct len s0 sm0).
#[local] Abbreviation st_ok := (PECSRD1A.st_ok L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb len s0 str pl).
#[local] Abbreviation lregs := (PECSRD1A.lregs R0 S fb).
#[local] Abbreviation tbdst := (PECSRD1A.tbdst fb).
#[local] Abbreviation lstate := (PECSRD1A.lstate L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb len s0 str sm0 pl tl).
#[local] Abbreviation IHt := (PECSRD1A.IHt L ar HI R0 M0 model0 K LBX FF LK0 Aw0 cr0 S fb len s0 str sm0 pl tl).
#[local] Abbreviation lregs_keep := (PECSRD1A.lregs_keep R0 S fb len Hlen).
#[local] Abbreviation lregs_set := (PECSRD1A.lregs_set R0 S fb len Hlen).
#[local] Abbreviation lregs_pres := (PECSRD1A.lregs_pres R0 S fb len Hlen).
#[local] Abbreviation geo := (PECSRD1A.geo fb).
#[local] Abbreviation fbb := (PECSRD1A.fbb FF fb FOK).
#[local] Abbreviation finish := (PECSRD1A.finish L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation callee_mem := (PECSRD1A.callee_mem L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation centry := (PECSRD1A.centry L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation call_resize := (PECSRD1A.call_resize L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation call_srcread := (PECSRD1A.call_srcread L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation call_filltb := (PECSRD1A.call_filltb L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation unread_nn := (PECSRD1A.unread_nn L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation TX := (PECSRD1A.TX fb s0 sm0 pl tl).
#[local] Abbreviation pos0 := (PECSRD1A.pos0 s0 sm0 pl).
#[local] Abbreviation pos_acct := (PECSRD1A.pos_acct L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation TX_len := (PECSRD1A.TX_len L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation content_agree := (PECSRD1A.content_agree L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation tb_agree := (PECSRD1A.tb_agree L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation vpack := (PECSRD1A.vpack L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation ro_step := (PECSRD1A.ro_step L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation outside_W0 := (PECSRD1A.outside_W0 L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
Ltac bvr := bvr1 R0 1%nat; bvr1 R0 8%nat; bvr1 R0 9%nat; bvr1 R0 18%nat; bvr1 R0 19%nat; bvr1 R0 20%nat; bvr1 R0 21%nat; bvr1 R0 22%nat; bvr1 R0 23%nat; bvr1 R0 24%nat; bvr1 R0 25%nat; bvr1 R0 26%nat; bvr1 R0 27%nat.

#[local] Abbreviation rpath := (PECSRD3A.rpath L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
#[local] Abbreviation dpath := (PECSRD4A.dpath L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
Ltac ks_tac KS := intros x Hx; apply KS; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx.
Ltac kp_tac KS KP := intros x Hx; rewrite (KS x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx); apply KP; exact Hx.

Lemma src_step_refl a sa : PMSPA.src_step a a sa sa.
Proof. clear. unfold PMSPA.src_step. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros X; exact X| lia]. Qed.

Lemma head mu0 (IH : IHt mu0) (fx : FPState) R M model s sm cr LK Aw (w : Z) :
  lstate R M model s sm cr LK Aw w -> PM.mu_src (PM.p_src s) sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb7714 M model) K.
Proof using All.
  intros LS MU. pose proof LS as (LR & SO & AC & Hw & TXh).
  pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & KP).
  pose proof (unread_nn M model s sm cr LK Aw SO) as (UN & ST & RM & GE).
  pose proof (vpack M model s sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & _).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
  pose proof LC as (L184 & L176 & L168 & L160 & L152 & L144 & L136 & L128 & L120 & L112).
  pose proof geo as (Eop & Eos & Eois & Etb).
  assert (D1 : S - 192 + 192 <= os \/ os + 296 <= S - 192) by (right; lia).
  assert (D2 : S - 192 + 192 <= tb \/ tb + 24 <= S - 192) by (right; lia).
  assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (left; lia).
  bvr.
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _).
  destruct SRC as (F240 & _ & _ & _ & F272 & _ & F288 & _).
  replace (op + 24 + 240) with (os + 240) in F240 by lia.
  replace (op + 24 + 272) with (os + 272) in F272 by lia.
  replace (op + 24 + 288) with (os + 288) in F288 by lia.
  change PM.CHUNK with 16384 in F272, RM.
  pose proof (PMASKJ.iss_vis L ar C HI LY HIok _ FF LK cr Aw M model fb str sm S 22528 HH FOK IA STK) as ((I1 & I8 & INSH) & Zis & IWR & ICE & IVIS & AOI & IOSB).
  fold ois in I1, I8, INSH, Zis, IWR, ICE, IVIS, AOI, IOSB.
  pose proof (PMASKJ.img_shz_vis L ar C HI LY IL ICok ILY _ FF LK cr Aw M model 0x136e10 1 HH ltac:(lia) ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia)) as ZOT.
  assert (D4 : S - 192 + 192 <= ois \/ ois + 272 <= S - 192) by (right; lia).
  assert (D5 : os + 296 <= ois \/ ois + 272 <= os) by (right; lia).
  assert (D6 : tb + 24 <= ois \/ ois + 272 <= tb) by (right; lia).
  set (MV := mrestrict (ahid Aw model) M) in *.
  destruct (Z.eq_dec (PM.sr_rem (PM.p_src s)) 0) as [RZ|RNZ].
  -
    rewrite RZ in F288.
    pose proof IA as (I0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IOS & _).
    cbn [pa_vp_iss PMA.AD PeLayoutA.ADDR_A PeCLayoutA.CADDR_A] in I0.
    destruct IOS as (_ & U32 & _).
    pose proof (PMTK2.u8_of_u32 RSEGS M (ois + 120 + 32) (PM.sm_st sm) ltac:(lia) U32) as B152.
    rewrite Z.mod_small in B152 by lia.
    replace (ois + 120 + 32) with (ois + 152) in B152 by lia.
    assert (STR : 0 <= PM.sm_st sm <= 2) by lia.
    pose proof (PMASRDP.srdH0_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
       | 45%nat => ois | 62%nat => PM.sm_st sm
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) as PP.
    cbn beta iota in PP.
    L5SAR.feed PP ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
      | |- L5.u64_at _ _ ois _ => unfold MV; vis64 IVIS
      | |- L5.u8_at _ _ (ois + _) _ => unfold MV; vis8 IVIS
      | |- PMASRDP.aligned _ _ => unfold PMASRDP.aligned; lia
      | |- _ => lia end]).
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & [(MS1 & KS1 & E10 & E11 & E12 & E24 & C0 & C1) | [(MS1 & KS1 & E10 & E11 & E12 & E24 & C0 & C1)
                 | (MS1 & KS1 & E1 & E2 & E8 & E9 & E10 & E11 & E12 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & C0)]]).
    +
      apply (ro_step fx fx1 R 0xb7714 R1 0xb77b0 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
      assert (ST0 : PM.sm_st sm = 0) by (destruct ST as [E|E]; [exact E| rewrite E in C1; vm_compute in C1; discriminate]).
      apply (rpath mu0 IH fx1 R1 M model1 s sm cr LK Aw w w); try assumption.
      * apply (lregs_keep R R1 w LR). ks_tac KS1.
      * lia.
      * unfold PM.CHUNK. lia.
      * lia.
      * right. exact ST0.
    +
      apply (ro_step fx fx1 R 0xb7714 R1 0xb783c M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
      assert (ST0 : PM.sm_st sm = 0) by (destruct ST as [E|E]; [exact E| rewrite E in C1; vm_compute in C1; discriminate]).
      apply (dpath mu0 IH fx1 R1 M model1 s sm cr LK Aw w); try assumption.
      * apply (lregs_keep R R1 w LR). ks_tac KS1.
      * lia.
    +
      apply (ro_step fx fx1 R 0xb7714 R1 0xb7984 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
      assert (WEX : w = 0 \/ PM.unread (PM.p_src s) sm = 0).
      { right. assert (ST2 : PM.sm_st sm = 2) by (destruct ST as [E|E]; [exfalso; rewrite E in C0; vm_compute in C0; lia| exact E]).
        destruct SO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & CST2)). unfold PM.unread. rewrite RZ, (CST2 ST2). lia. }
      apply (finish fx1 R1 M model1 s sm cr LK Aw w); try assumption.
      all: first [ solve [intros x Hx; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [assumption|]); destruct Hx] | solve [kp_tac KS1 KP]
                 | solve [rewrite E10; f_equal; lia] | lia ].
  -
    assert (F256 : True) by exact I.
    pose proof (PMASRDP.srdH1_conc fx R MV (fun j => match j with 2%nat => S | 33%nat => PM.sr_rem (PM.p_src s) | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) as PP.
    cbn beta iota in PP.
    L5SAR.feed PP ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
      | |- L5.u64_at _ _ ois _ => unfold MV; vis64 IVIS
      | |- L5.u8_at _ _ (ois + _) _ => unfold MV; vis8 IVIS
      | |- PMASRDP.aligned _ _ => unfold PMASRDP.aligned; lia
      | |- _ => lia end]).
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & [(MS1 & KS1 & E10 & E24 & C0) | (MS1 & KS1 & E10 & E24 & C0)]);
      apply (ro_step fx fx1 R 0xb7714 R1 0xb77b0 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1); intros model1 SO1.
    + apply (rpath mu0 IH fx1 R1 M model1 s sm cr LK Aw w w); try assumption.
      * apply (lregs_keep R R1 w LR). ks_tac KS1.
      * lia.
      * unfold PM.CHUNK. lia.
      * lia.
      * left. lia.
    + apply (rpath mu0 IH fx1 R1 M model1 s sm cr LK Aw w 16384); try assumption.
      * apply (lregs_keep R R1 w LR). ks_tac KS1.
      * lia.
      * unfold PM.CHUNK. lia.
      * lia.
      * left. lia.
Qed.

Lemma loop (n : nat) : forall (fx : FPState) R M model s sm cr LK Aw w,
  (Z.to_nat (PM.mu_src (PM.p_src s) sm) < n)%nat -> lstate R M model s sm cr LK Aw w ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb7714 M model) K.
Proof using All.
  induction n as [|n IHn]; intros fx R M model s sm cr LK Aw w Hn LS; [lia|].
  assert (IHm : IHt (PM.mu_src (PM.p_src s) sm)).
  { intros fx' R' M' model' s' sm' cr' LK' Aw' w' Hlt LS'. apply (IHn fx' R' M' model' s' sm' cr' LK' Aw' w'); [|exact LS'].
    pose proof LS' as (_ & SO' & _). pose proof (unread_nn _ _ _ _ _ _ _ SO') as (UN' & _).
    assert (0 <= PM.mu_src (PM.p_src s') sm') by (unfold PM.mu_src; destruct (Z.eqb _ _); lia). lia. }
  exact (head _ IHm fx R M model s sm cr LK Aw w LS ltac:(lia)).
Qed.

Lemma entry_ok (fx : FPState) :
  ri_inv HI (PM.parser_own s0 ++ LBX) FF LK0 cr0 Aw0 M0 (vml_of model0) -> L5CA.amodel_ok Aw0 model0 -> L5CA.astk ar M0 S 22528 ->
  getr R0 (reg 10) = Z_to_bv 64 os -> getr R0 (reg 11) = Z_to_bv 64 tb -> getr R0 (reg 12) = Z_to_bv 64 len ->
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M0 op ois s0 -> PM.iss_at RSEGS AD PMSPA.accA M0 ois str sm0 -> PMSTA.base_okA RSEGS AD M0 ->
  PM.tb_ok (PM.p_tb s0) (PM.p_tg s0) -> PMSPA.accA M0 op PECA.RDR_BYTES ->
  PEC.content_ok RSEGS AD M0 fb pl (PM.p_src s0) str sm0 -> L5.bytes_at RSEGS M0 (PM.vs_data tb (PM.p_tb s0)) tl ->
  PMSPA.credit_le (pot L ar s0) cr0 ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R0 0xb763c M0 model0) K.
Proof using All.
  intros HH AM STK A10 A11 A12 PA IA BASE TBOK ACC0 CT0 TLB CRL.
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof geo as (Eop & Eos & Eois & Etb). pose proof fbb as (F1024 & rs & Hfb).
  pose proof (PMASKJ.mach_vis L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 HH BASE) as (V0 & V1 & V2).
  pose proof (PMASKJ.stk_vis L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 S 22528 192 HH STK ltac:(lia)) as (SL80 & SH80 & V3).
  pose proof (PMASKJ.src_vis L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 fb ois s0 S 22528 HH FOK PA STK)
    as ((O1 & O8 & OBIG) & OZ & OW & OCE & OAV & AO & OFS1 & OFS2).
  pose proof (PMARSK.tb_vis L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 fb ois s0 HH FOK PA)
    as ((T1 & T8 & TBIG) & TZ & TW & TCE & TAV & AT & TFS1 & TFS2).
  fold os in O1, O8, OBIG, OZ, OW, OCE, OAV, AO, OFS1, OFS2. fold tb in T1, T8, TBIG, TZ, TW, TCE, TAV, AT, TFS1, TFS2.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  unfold FS_BYTES in OFS2, TFS2, FSCEIL.
  assert (D1 : S - 192 + 192 <= os \/ os + 296 <= S - 192) by (right; lia).
  assert (D2 : S - 192 + 192 <= tb \/ tb + 24 <= S - 192) by (right; lia).
  assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (left; lia).
  set (MV := mrestrict (ahid Aw0 model0) M0) in *.
  pose proof (PMASRDP.srdA_conc fx R0 MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | _ => 0 end)) as PP.
  cbn beta iota in PP.
  L5SAR.feed PP ltac:(first [assumption | lazymatch goal with
      | |- PMASRDP.aligned _ _ => unfold PMASRDP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & EX).
  set (P := fun a => S - 192 <= a < S - 192 + 192).
  assert (FZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) by (intros a Ha N; apply FRZ1; [exact Ha| exact N]).
  assert (WOB : forall a, 0 <= a < 2 ^ 64 -> P a -> aclientw L ar (PM.parser_own s0 ++ LBX) FF 0 0 a /\ ~ (0x10000 <= a < 0x698000)).
  { intros a Ha Wa. unfold P in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| lia]. }

  assert (POST0 : forall M1 model1, ri_inv HI (PM.parser_own s0 ++ LBX) FF LK0 cr0 Aw0 M1 (vml_of model1) ->
                   mrestrict (ahid Aw0 model0) M1 = M1v -> mem_grows M0 M1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
                   memrel M1 /\ PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M1 op ois s0 /\ PM.iss_at RSEGS AD PMSPA.accA M1 ois str sm0 /\ PMSTA.base_okA RSEGS AD M1
                   /\ PMSPA.accA M1 op PECA.RDR_BYTES /\ PEC.content_ok RSEGS AD M1 fb pl (PM.p_src s0) str sm0 /\ TX M1 (PM.p_tb s0) 0).
  { intros M1 model1 HH1 VIS1 MGM1 FR1.
    assert (EKn : L5SAR.ek L ar LBX FF S 22528 W0 M0 M1).
    { apply (L5SAR.ek_piece L ar LBX FF S 22528 W0 M0 M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. unfold P in Pa.
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 _ S 22528 a HH SPT (L5SAR.aclient_appb L ar LBX (PM.parser_own s0) FF S 22528 a CA)) as [X|X]; lia. }
    pose proof (PMASKJ.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMASKJ.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
    assert (EKp : L5SAR.ek L ar (PM.parser_own s0 ++ LBX) FF S 22528 [] M0 M1).
    { apply (L5SAR.ek_piece L ar _ FF S 22528 [] M0 M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. unfold P in Pa.
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 _ S 22528 a HH SPT CA) as [X|X]; lia. }
    assert (AOP : PMSPA.aobjA FF op 384).
    { exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
    assert (AOI : PMSPA.aobjA FF ois 272).
    { exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
    assert (QIN : In (PM.sr_qc (PM.p_src s0), PM.CHUNK) (PM.parser_own s0 ++ LBX)) by (apply in_or_app; left; left; reflexivity).
    split; [split; [|split]|].
    - exact EKn.
    - apply L5SAR.dk_grows. exact MGM1.
    - exact (L5SAR.astk_grows ar M0 M1 S 22528 STK MGM1).
    - split; [apply (PMKA.parser_keepA RSEGS AD L ar _ FF S 22528 [] M0 M1 EKp PMKA.wapp_nil FRB BRB _ _ _ AOP); [apply incl_appl, incl_refl| intros i _ r0 []| | | |exact PA]|].
      { intros i _ r0 []. } { intros i _ r0 []. } { intros c0 n0 p0 _ i _ r0 []. }
      split; [apply (PMKA.iss_keepA RSEGS AD L ar _ FF S 22528 [] M0 M1 EKp PMKA.wapp_nil FRB BRB _ _ _ AOI); [intros x Hx; apply in_or_app; right; apply INCS; exact Hx| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA]|].
      split; [apply (PMASKJ.base_keep L ar C LY LBX FF S 22528 W0 M0 M1 EKn); [intros a Ha; apply outside_W0; pose proof (PMASKJ.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH); lia| exact BASE]|].
      split.
      { apply (PMFA.accA_agree M0 M1 op PECA.RDR_BYTES); [| exact ACC0].
        apply (PMKA.agsh_obj L ar _ FF S 22528 [] M0 M1 EKp PMKA.wapp_nil FRB op PECA.RDR_BYTES).
        apply (PMASKJ.aobj_fb FF fb); [exact FOK| clear - Eop; lia| unfold PECA.RDR_BYTES; clear - Eop; lia]. }
      split.
      { apply (content_agree M0 M1 s0 sm0 cr0 LK0 Aw0 (vml_of model0)); [| | | exact HH| exact PA| exact IA| exact CT0].
        - exact (proj1 (PMKA.agA_blk L ar _ FF S 22528 [] M0 M1 EKp PMKA.wapp_nil BRB _ _ QIN ltac:(intros i _ r0 []))).
        - intros B m Hin. exact (proj1 (PMKA.agA_blk L ar _ FF S 22528 [] M0 M1 EKp PMKA.wapp_nil BRB B m ltac:(apply in_or_app; right; exact Hin) ltac:(intros i _ r0 []))).
        - refine (proj1 (PMKA.agA_obj L ar _ FF S 22528 [] M0 M1 EKp PMKA.wapp_nil FRB (ois + 80) 24 _ ltac:(intros i _ r0 [])));
            apply (PMASKJ.aobj_fb FF fb); [exact FOK| clear - Eois; lia| clear - Eois; lia]. }

      unfold TX, UbjRef.slice. cbn [Z.to_nat firstn]. rewrite app_nil_r.
      apply (tb_agree M0 M1 s0 cr0 LK0 Aw0 _ tl (S - 192) (S - 192 + 192) PA HH FR1 ltac:(clear - TFS1 TFS2 FSCEIL SLO Etb; right; lia));
        [intros q9 c9 Hq9; destruct (WB _ Hq9) as ((_ & _ & _ & _ & Q94 & _) & _); cbn [fst snd] in Q94; right; clear - Q94 SLO; lia| rewrite TL0; clear; lia| exact TLB]. }
  assert (POST : forall M1 model1, ri_inv HI (PM.parser_own s0 ++ LBX) FF LK0 cr0 Aw0 M1 (vml_of model1) -> L5CA.amodel_ok Aw0 model1 -> model_rt model0 model1 ->
                   mrestrict (ahid Aw0 model0) M1 = M1v -> mem_grows M0 M1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
                   saves13 M1v -> locals M1v -> st_ok M1 model1 s0 sm0 cr0 LK0 Aw0 /\ TX M1 (PM.p_tb s0) 0).
  { intros M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1 SVv LCv.
    destruct (POST0 M1 model1 HH1 VIS1 MGM1 FR1) as (MR1 & PA1 & IA1 & BASE1 & ACC1 & CT1 & TX1).
    pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 HH) as (_ & VIS & _).
    assert (BK : forall k v, 8 <= k <= 192 -> L5.u64_at RSEGS M1v (S - k) v -> L5.u64_at RSEGS M1 (S - k) v).
    { intros k v Hk X. apply (proj1 (L5A.u64_at_vis (ahid Aw0 model0) M1 (S - k) v (VIS (S - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact X. }
    split; [| exact TX1].
    split; [exact MR1|].
    split.
    { destruct SVv as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
      repeat split; (apply BK; [lia| assumption]). }
    split.
    { destruct LCv as (L184 & L176 & L168 & L160 & L152 & L144 & L136 & L128 & L120 & L112).
      repeat split; (apply BK; [lia| assumption]). }
    split; [exact PA1|]. split; [exact IA1|]. split; [exact BASE1|].
    split; [exact TBOK|]. split; [exact HH1|]. split; [exact AM1|]. split; [exact MRT1|].
    split; [apply incl_refl|]. split; [apply incl_refl|]. split; [exact CRL|].
    split; [unfold PMSPA.credit_keep; lia|]. split; [exact ACC1| exact CT1]. }
  bvr.
  assert (FE0 : fields_eq s0) by (unfold PECSRD1A.fields_eq; repeat split).
  assert (AC0 : forall w, w = len -> acct s0 sm0 w).
  { intros w ->. unfold PECSRD1A.acct, PMSPA.consumed, PMSPA.src_step. split; [lia|]. split; [lia|].
    split; [split; [reflexivity|]; split; [reflexivity|]; split; [lia|]; split; [intros X; exact X| lia]| exact FE0]. }
  unfold PMSPA.cfg.
  destruct EX as [(MS & KS1 & E2 & E8 & E9 & E10 & E11 & E13 & E14 & E15 & E16 & E18 & E19 & E20 & E21 & E22 & E23 & E25 & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C23 & C24)
                 | (MS & KS1 & E10 & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14)].
  -
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xb763c R1 0xb7714 M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    pose proof (POST M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1 ltac:(repeat split; assumption) ltac:(repeat split; assumption)) as (SO1 & TX1).
    rewrite Z.sub_0_r, Z.mod_small in C10 by lia.
    pose proof (unread_nn M1 model1 s0 sm0 cr0 LK0 Aw0 SO1) as (UN & _).
    apply (loop (Nat.succ (Z.to_nat (PM.mu_src (PM.p_src s0) sm0))) fx1 R1 M1 model1 s0 sm0 cr0 LK0 Aw0 len); [apply Nat.lt_succ_diag_r|].
    split; [|split; [exact SO1| split; [exact (AC0 len eq_refl)| split; [lia| replace (len - len) with 0 by lia; exact TX1]]]].
    unfold PECSRD1A.lregs. do 10 (split; [assumption|]).
    intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). reflexivity.
  -
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xb763c R1 0xb7984 M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    assert (L0 : len = 0) by (rewrite Z.sub_0_r, Z.mod_small in C0 by lia; lia).

    destruct (POST0 M1 model1 HH1 VIS1 MGM1 FR1) as ((EK1 & DK1 & STK1) & PA1 & IA1 & BASE1 & ACC1 & CT1 & TX1).
    pose proof RAok as (Hr1 & Hr2).
    assert (RA : getr R1 (reg 1) = Z_to_bv 64 r) by (rewrite (KS1 1%nat) by inl; exact Rra0).
    apply (PMASKJ.ret_exit L ar C HI LY HIok fx1 R1 M1 model1 K _ FF LK0 cr0 Aw0 0xb7984 r W_b7934 HH1 AM1 F_b7934 eq_refl D_b7934 RA ltac:(lia) Hr2).
    intros model2 MRT2 AM2 HH2.
    apply (KONT fx1 R1 M1 model2 LK0 Aw0 s0 sm0 cr0 0).
    + apply L5SAR.preserved_by_index. intros x Hx. unfold L5SAR.cs_all in Hx.
      rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). reflexivity.
    + rewrite L5K.rl10, E10. f_equal. lia.
    + lia.
    + unfold PMSPA.consumed. lia.
    + lia.
    + pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & Q8 & Q9 & Q10 & _) & _).
      pose proof IA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & ST9) & _ & G1 & G2).
      unfold PM.unread. lia.
    + unfold TX, pos0, tb in TX1. exact TX1.
    + exact PA1.
    + exact IA1.
    + exact TBOK.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + apply src_step_refl.
    + exact CT1.
    + change (PMSPA.pm_scr 5) with 22528. apply (L5SAR.ahpres_of L ar LBX FF S 22528 _ M0 M1 EK1); [destruct STK1 as (_ & _ & _ & _ & D & _); exact D| exact DK1].
    + unfold PMSPA.credit_keep. lia.
    + eapply L5LZ.model_rt_trans; [exact MRT1| exact MRT2].
    + apply incl_refl.
    + apply incl_refl.
    + exact AM2.
    + exact HH2.
Qed.

End Call.

Theorem csrd_read_ok : @PECTXSA.cstr_resize_spec SCFG_P RSEGS AD L ar HI -> PECSA.fill_buffer_spec L ar HI -> PECFILLTBA.cfill_tb_spec L ar HI ->
  @PECTXSA.csrd_read_spec SCFG_P RSEGS AD L ar HI.
Proof.
  intros RSZ FB FBT. unfold PECTXSA.csrd_read_spec.
  intros fx R M model K LBX FF LK Aw cr sp r fb len pl tl s str sm HH AM K0 ENT FRM FRS FOK ALN A10 A11 A12 Hlen PA IA BASE ACC TBOK INCS UN UNS POK CT TL TLB CRL KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 5) with 22528 in *. change (22528 / 8) with 2816 in STKSH.
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5SAR.r11 in A11. rewrite L5SAR.r12 in A12.
  exact (entry_ok R M model K LBX FF LK Aw cr sp r fb len s str sm pl tl Rra RAok Rsp Rgp Rtp K0 FRM FRS FOK Hlen INCS UNS STKSH POK TL (proj1 (proj2 (proj2 CT))) RSZ FB FBT KONT
           fx HH AM ASTK A10 A11 A12 PA IA BASE TBOK ACC CT TLB CRL).
Qed.

End WithHeap.
End PECSRD5A.
