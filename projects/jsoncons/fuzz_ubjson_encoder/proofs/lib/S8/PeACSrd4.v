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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCModelA PeCSpecsA PeCSpecsAa PmModelFactsA PeStepA PmStep PmTxtKit2 PeASrcKitJ PeACReset1 PeARsKit PmSpecs PeCSink PeCModel PeCSpecs PeCFrame PeCSrcD PeCTxtSpecsA PeACSrcRead PeACSrcFillTb PeASrdP PeACSrd1 PeACSrd2 PeACSrd3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECSRD4A.
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

#[local] Abbreviation after_shrink := (PECSRD2A.after_shrink L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl tl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK Hlen INCS UNS0 STKSH0 POK TL0 POS0 RSZ FB FBT KONT).
Ltac ks_tac KS := intros x Hx; apply KS; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx.
Ltac kp_tac KS KP := intros x Hx; rewrite (KS x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx); apply KP; exact Hx.

Lemma with_src_eta (s : PM.pst) : PMSPA.with_src s (PM.SRC (PM.sr_qc (PM.p_src s)) (PM.sr_de (PM.p_src s)) (PM.sr_rem (PM.p_src s))) = s.
Proof. destruct s as [a b c [q d e] f g h i j]; reflexivity. Qed.

Lemma pos_step (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) M model s sm cr LK Aw (M1v : word -> option byte) :
  st_ok M model s sm cr LK Aw ->
  msteps RSEGS (L5SAR.st fx R pc (mrestrict (ahid Aw model) M)) (L5SAR.st fx1 R1 pc1 M1v) ->
  mem_grows (mrestrict (ahid Aw model) M) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (os + 256 <= a < os + 256 + 8) -> M1v (Z_to_bv 64 a) = mrestrict (ahid Aw model) M (Z_to_bv 64 a)) ->
  (forall M1 model1, st_ok M1 model1 s sm cr LK Aw ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (os + 256 <= a < os + 256 + 8) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
     srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 pc1 M1 model1) K) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R pc M model) K.
Proof using All.
  intros SO MS MG FRZ NEXT.
  pose proof (vpack M model s sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as ((EK & DK & STK) & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK & ACC & CT).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof geo as (Eop & Eos & Eois & Etb). pose proof fbb as (F1024 & rs & Hfb).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  pose proof PA as (_ & PD & _ & _ & _ & _ & _ & _ & _ & SRC & _).
  destruct SRC as (F240 & F248 & F256 & F264 & F272 & F280 & F288 & G1 & G2 & G3 & G4 & DC & CC & C240).
  replace (op + 24) with os in F240, F248, F256, F264, F272, F280, F288 by lia.
  set (P := fun a => os + 256 <= a < os + 256 + 8).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R pc R1 pc1 M1v P K HH AM MS MG).
  { intros a Ha N. apply FRZ; [exact Ha| exact N]. }
  { intros a Ha Wa. unfold P in Wa. split.
    - unfold aclientw, aclient_g. right; right; right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia.
    - lia. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
  apply NEXT; [| exact FR1].
  assert (AGO : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= os + 256 \/ os + 264 <= a) -> L5C.agree_on M M1 a n).
  { intros a n Ha Hn X i Hi. apply FR1; [lia| unfold P; lia]. }
  assert (AGSH : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n).
  { intros a n Ha Hn x Hx. unfold HeapIfaceA.S, HeapIfaceA.SB.
    assert (X8 : 0 <= x / 8 <= 17592186044416) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    apply FR1; [lia|]. unfold P. destruct OBIG; lia. }
  assert (BLKAP : forall q m, In (q, m) (PM.parser_own s ++ LBX) -> q + m <= os \/ os + 296 <= q).
  { intros q m Hq. destruct (PMASKJ.blk_obj_apart L ar C HI HIok _ FF LK cr Aw M _ q m os 296 HH Hq AO) as [X|X]; [left| right]; lia. }
  pose proof (PMASKJ.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  assert (AGB : forall q m, In (q, m) (PM.parser_own s ++ LBX) -> PMFA.agA M M1 q m).
  { intros q m Hq. destruct (BRB _ Hq) as (X0 & X1). cbn [fst snd] in X0, X1. destruct (BLKAP q m Hq) as [BF|BF]; (split; [apply AGO; lia| apply AGSH; lia]). }
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VS & VEC & _).
  pose proof VEC as (_ & _ & _ & Hk & _). pose proof (PM.pow2_pos (PM.p_k s) (proj1 Hk)) as P2.
  assert (VIN : In (PM.p_b s, 32 * 2 ^ PM.p_k s) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; right; left; reflexivity).
  assert (QIN : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  destruct (BRB _ VIN) as (VB0 & VB1). destruct (BRB _ QIN) as (QB0 & QB1). cbn [fst snd] in VB0, VB1, QB0, QB1.
  assert (PA1 : PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M1 op ois s).
  { rewrite <- (with_src_eta s).
    apply (PMASKJ.parser_src_fieldsA M M1 op ois s (PM.sr_de (PM.p_src s)) (PM.sr_rem (PM.p_src s)) PA);
      [lia| lia| | | | lia| cbv [PM.CHUNK] in *; lia| | lia| lia| | | exact MGM1| | | | | lia| lia| cbv [PM.CHUNK] in *; lia].
    - split; [apply AGO; lia| apply AGSH; lia].
    - split; [apply AGO; lia| apply AGSH; lia].
    - apply AGSH; lia.
    - exact (AGB _ _ QIN).
    - exact (AGB _ _ VIN).
    - intros c0 n0 p0 E. apply AGB. apply in_or_app; left. unfold PM.parser_own. rewrite E. right; right; left; reflexivity.
    - apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| replace (op + 288) with (os + 264) by lia; exact F264].
    - apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| replace (op + 296) with (os + 272) by lia; exact F272].
    - apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| replace (op + 304) with (os + 280) by lia; exact F280].
    - apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| replace (op + 312) with (os + 288) by lia; exact F288]. }
  set (Wp := [(os + 256, 8)]).
  assert (EK1 : L5SAR.ek L ar (PM.parser_own s ++ LBX) FF S 22528 Wp M M1).
  { apply (L5SAR.ek_piece L ar _ FF S 22528 Wp M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
    intros a Ha CA OWx Pa. unfold P in Pa. apply (OWx (os + 256, 8)); [unfold Wp; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
  assert (WAPPp : PMKA.wapp Wp) by (unfold Wp; apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct OBIG; [right| left]; lia| apply PMKA.wapp_nil]).
  pose proof (PMASKJ.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  assert (AOI : PMSPA.aobjA FF ois 272).
  { exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
  assert (IA1 : PM.iss_at RSEGS AD PMSPA.accA M1 ois str sm).
  { apply (PMKA.iss_keepA RSEGS AD L ar _ FF S 22528 Wp M M1 EK1 WAPPp FRB BRB _ _ _ AOI); [intros x Hx; apply in_or_app; right; apply INCS; exact Hx| | |exact IA].
    - intros i Hi r0 Hr. unfold Wp in Hr. unfold L5.in_rng. destruct Hr as [<-|[]]; cbn [fst snd]; lia.
    - intros c0 n0 p0 E i Hi r0 Hr. assert (Ip : In (p0, c0) (PM.parser_own s ++ LBX)) by (apply in_or_app; right; apply INCS; rewrite E; left; reflexivity).
      destruct (BLKAP _ _ Ip) as [X|X]; unfold Wp in Hr; unfold L5.in_rng; destruct Hr as [<-|[]]; cbn [fst snd]; lia. }
  assert (EKn : L5SAR.ek L ar LBX FF S 22528 W0 M M1).
  { apply (L5SAR.ek_piece L ar LBX FF S 22528 W0 M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
    intros a Ha CA OWx Pa. apply (OWx (os + 256, 40)); [unfold PECSRD1A.W0, PMSPA.W_srcf; left; reflexivity|].
    unfold L5.in_rng, P in *; cbn [fst snd] in *. lia. }
  pose proof (PMASKJ.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  destruct (WF _ Hfb) as (FF1 & FF2 & _). cbn [ff_addr ff_class fst snd] in FF1, FF2. change (ff_bytes 5) with 2048 in FF2. unfold FS_BYTES in FF2.
  split; [split; [|split]|].
  - exact (L5SAR.ek_trans L ar LBX FF S 22528 W0 M0 M M1 EK EKn).
  - apply (L5SAR.dk_trans L ar LBX FF S 22528 M0 M M1 DK). apply L5SAR.dk_grows. exact MGM1.
  - exact (L5SAR.astk_grows ar M M1 S 22528 STK MGM1).
  - split.
    { destruct SV as (S8 & S16' & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104).
      repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| assumption]). }
    split.
    { destruct LC as (L184 & L176 & L168 & L160 & L152 & L144 & L136 & L128 & L120 & L112).
      repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| assumption]). }
    split; [exact PA1|]. split; [exact IA1|].
    split; [apply (PMASKJ.base_keep L ar C LY LBX FF S 22528 W0 M M1 EKn); [intros a Ha; apply outside_W0; lia| exact BASE]|].
    split; [exact TBOK|]. split; [exact HH1|]. split; [exact AM1|]. split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1]|].
    split; [exact ILK|]. split; [exact IAW|]. split; [exact CRL|]. split; [exact CRK|].
    destruct (FRB _ Hfb) as (Fb0 & Fb1). cbn [ff_addr ff_class fst snd] in Fb0, Fb1. change (ff_bytes 5) with 2048 in Fb1.
    split.
    { apply (PMFA.accA_agree M M1 op PECA.RDR_BYTES); [apply AGSH; unfold PECA.RDR_BYTES; clear - Eop Fb0 Fb1; lia| exact ACC]. }
    apply (content_agree M M1 s sm cr LK Aw (vml_of model)); [| | apply AGO; clear - Eois Eos Fb0 Fb1; lia| exact HH| exact PA| exact IA| exact CT].
    + exact (proj1 (AGB _ _ QIN)).
    + intros B m Hin. exact (proj1 (AGB B m ltac:(apply in_or_app; right; exact Hin))).
Qed.

Lemma d_after_fill mu0 (IH : IHt mu0) (fx : FPState) R M model s sm cr LK Aw (w n c : Z) :
  lregs R w -> getr R (reg 10) = Z_to_bv 64 c -> getr R (reg 24) = Z_to_bv 64 16384 -> getr R (reg 27) = Z_to_bv 64 n ->
  0 <= c <= 16384 -> 16384 <= w <= len ->
  st_ok M model s sm cr LK Aw -> PM.vs_size (PM.p_tb s) = n + 16384 -> 0 <= n -> n = PM.vs_size (PM.p_tb s0) + (len - w) ->
  PMSPA.consumed (PM.p_src s0) (PM.p_src s) sm0 sm = len - w + c ->
  PMSPA.src_step (PM.p_src s0) (PM.p_src s) sm0 sm -> fields_eq s -> TX M (PM.p_tb s) (len - w + c) -> PM.mu_src (PM.p_src s) sm < mu0 ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb78b8 M model) K.
Proof using All.
  intros LR A10 A24 A27 Hc Hw SO SZ Hn0 En CONS STEP FE TXh MU.
  pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & KP).
  pose proof (unread_nn M model s sm cr LK Aw SO) as (UN & ST & RM & GE).
  assert (Hn : n < 67108864) by (unfold PMSPA.consumed in CONS; lia).
  pose proof (vpack M model s sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & _).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
  pose proof LC as (L184 & L176 & L168 & L160 & L152 & L144 & L136 & L128 & L120 & L112).
  pose proof geo as (Eop & Eos & Eois & Etb).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  assert (D1 : S - 192 + 192 <= os \/ os + 296 <= S - 192) by (right; lia).
  assert (D2 : S - 192 + 192 <= tb \/ tb + 24 <= S - 192) by (right; lia).
  assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (left; lia).
  bvr.
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _).
  destruct SRC as (_ & _ & F256 & _). replace (op + 24 + 256) with (os + 256) in F256 by lia.
  set (MV := mrestrict (ahid Aw model) M) in *.
  pose proof (PMASRDP.srdD3_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
       | 44%nat => c | 46%nat => n
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) as PP.
  cbn beta iota in PP.
  L5SAR.feed PP ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.u64_at _ _ (tb + _) _ => unfold MV; vis64 TAV
      | |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
      | |- L5.defined _ (os + 256) 8 => unfold MV; apply (proj2 (L5A.defined_vis (ahid Aw model) M (os + 256) 8 ltac:(apply OAV; lia))); exact F256
      | |- PMASRDP.aligned _ _ => unfold PMASRDP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & EX).
  destruct EX as [(MS1 & KS1 & E1 & E10 & E11 & E12 & E26 & C0) | [(MS1 & KS1 & E11 & E25 & E26 & C0 & C1)
                 | (MS1 & KS1 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & C0 & C1)]];
    apply (pos_step fx fx1 R 0xb78b8 R1 _ M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1); intros M1 model1 SO1 FM1;
    (assert (TX1 : TX M1 (PM.p_tb s) (len - w + c)) by
      (unfold PECSRD1A.TX; apply (tb_agree M M1 s cr LK Aw _ _ (os + 256) (os + 256 + 8) PA HH FM1);
         [left; clear - Eos Etb; lia
         | intros q9 c9 Hq9; destruct (PMASKJ.blk_obj_apart L ar C HI HIok _ FF LK cr Aw M _ q9 c9 os 296 HH Hq9 AO) as [X9|X9]; [right| left]; clear - X9; lia
         | rewrite (TX_len M model s sm cr LK Aw (len - w + c) SO CONS ltac:(lia)); lia
         | exact TXh])).
  -
    assert (DK' : c < 16384).
    { destruct (Z.eq_dec c 16384) as [->|NE]; [rewrite Z.sub_diag, Zmod_0_l in C0; lia| lia]. }
    apply (call_resize fx1 R1 M1 model1 s sm cr LK Aw (c + n) 751860 E1 ltac:(split; [lia| reflexivity])); try assumption.
    + rewrite (KS1 2%nat) by inl. exact A2.
    + kp_tac KS1 KP.
    + unfold PM.CHUNK. lia.
    + unfold PM.CHUNK. lia.
    + intros fx2 R2 M2 model2 LK2 Aw2 tb2 tg2 cr2 RP2 SZ2 _ BYT2 SO2.
      refine (after_shrink mu0 IH fx2 R2 M2 model2 (PMTK2.with_tb s tb2 tg2) sm cr2 LK2 Aw2 w c _ _ ltac:(lia) ltac:(unfold PM.CHUNK; lia) ltac:(lia) SO2 _ _ MU).
      * apply (lregs_pres R1 R2 w RP2). apply (lregs_keep R R1 w LR). ks_tac KS1.
      * rewrite (L5SAR.cs_of_preserved R1 R2 26%nat RP2) by inl. exact E26.
      * unfold PECSRD1A.acct. cbn [PMTK2.with_tb PM.p_src PM.p_tb]. split; [lia|]. split; [lia|]. split; [exact STEP|].
        destruct FE as (F1 & F2 & F3' & F4 & F5 & F6). unfold PECSRD1A.fields_eq. cbn [PMTK2.with_tb PM.p_more PM.p_done PM.p_depth PM.p_b PM.p_k PM.p_stk].
        repeat split; assumption.
      * unfold PECSRD1A.TX. cbn [PMTK2.with_tb PM.p_tb]. replace (len - (w - c)) with (len - w + c) by lia. apply BYT2; [| exact TX1].
        rewrite (TX_len M1 model1 s sm cr LK Aw (len - w + c) SO1 CONS ltac:(lia)). lia.
  -
    replace (18446744073709535232) with ((18446744073709551615 * 16384) mod 2 ^ 64) in C0 by reflexivity.
    rewrite subw in C0 by lia.
    assert (DK' : c = 16384) by (apply (mod_lt1 (c - 16384)) in C1; lia). subst c.
    apply (IH fx1 R1 M1 model1 s sm cr LK Aw (w - 16384) MU).
    split; [|split; [exact SO1| split; [|split; [lia| replace (len - (w - 16384)) with (len - w + 16384) by lia; exact TX1]]]].
    + apply (lregs_set R R1 w (w - 16384) LR); [ks_tac KS1| exact E25].
    + unfold PECSRD1A.acct. split; [lia|]. split; [lia|]. split; [exact STEP| exact FE].
  -
    replace (18446744073709535232) with ((18446744073709551615 * 16384) mod 2 ^ 64) in C0 by reflexivity.
    rewrite subw in C0 by lia.
    assert (DK' : c = 16384) by (apply (mod_lt1 (c - 16384)) in C1; lia). subst c.
    apply (finish fx1 R1 M1 model1 s sm cr LK Aw 0); try assumption.
    + intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [assumption|]). destruct Hx.
    + kp_tac KS1 KP.
    + rewrite E10. f_equal. lia.
    + lia.
    + replace (len - 0) with (len - w + 16384) by lia. exact TX1.
    + left. lia.
    + unfold PECSRD1A.acct. split; [lia|]. split; [lia|]. split; [exact STEP| exact FE].
Qed.

Lemma d_after_resize mu0 (IH : IHt mu0) (fx : FPState) R M model s sm cr LK Aw (w n : Z) :
  lregs R w -> getr R (reg 24) = Z_to_bv 64 16384 -> getr R (reg 27) = Z_to_bv 64 n -> 16384 <= w <= len ->
  st_ok M model s sm cr LK Aw -> PM.vs_size (PM.p_tb s) = n + 16384 -> 0 <= n -> n = PM.vs_size (PM.p_tb s0) + (len - w) ->
  PMSPA.consumed (PM.p_src s0) (PM.p_src s) sm0 sm = len - w ->
  PMSPA.src_step (PM.p_src s0) (PM.p_src s) sm0 sm -> fields_eq s -> TX M (PM.p_tb s) (len - w) ->
  PM.sr_rem (PM.p_src s) = 0 -> PM.sm_st sm = 0 -> PM.mu_src (PM.p_src s) sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb787c M model) K.
Proof using All.
  intros LR A24 A27 Hw SO SZ Hn0 En CONS STEP FE TXh RZ ST0 MU.
  pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & KP).
  pose proof (unread_nn M model s sm cr LK Aw SO) as (UN & ST & RM & GE).
  assert (Hn : n < 67108864) by (unfold PMSPA.consumed in CONS; lia).
  pose proof (vpack M model s sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & _).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
  pose proof LC as (L184 & L176 & L168 & L160 & L152 & L144 & L136 & L128 & L120 & L112).
  pose proof geo as (Eop & Eos & Eois & Etb).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  assert (D1 : S - 192 + 192 <= os \/ os + 296 <= S - 192) by (right; lia).
  assert (D2 : S - 192 + 192 <= tb \/ tb + 24 <= S - 192) by (right; lia).
  assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (left; lia).
  bvr.
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _).
  replace (op + 336) with tb in VS by lia.
  set (MV := mrestrict (ahid Aw model) M) in *.
  revert VS SZ. destruct (PM.p_tb s) as [n1|c1 n1 q1] eqn:ETB; intros (VD & VC & VS) SZ; cbn [PM.vs_size] in SZ.
  -
    exfalso. destruct VS as (Hn1 & _). lia.
  - destruct VS as (W0' & W8 & W16 & Hn1 & Hc1 & Hce & DQ & CQ).
    pose proof (PMF.u8_of_u64 RSEGS M tb (c1 + 1) ltac:(lia) W0') as B0. pose proof (PMF.odd_byte c1 Hce ltac:(lia)) as ODB.
    assert (H39 : 0 <= (c1 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)); lia).
    assert (IN : In (q1, c1) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own; rewrite ETB; cbn; right; right; left; reflexivity).
    destruct (WB _ IN) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in Q0, Q1, Q2, Q3, Q4, Q5.
    assert (F256 : True) by exact I.
    pose proof (PMASRDP.srdD2_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
       | 40%nat => (c1 + 1) mod 256 | 42%nat => q1 | 46%nat => n
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) as PP.
    cbn beta iota in PP.
    L5SAR.feed PP ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.u64_at _ _ (tb + _) _ => unfold MV; vis64 TAV
      | |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
      | |- L5.defined _ (os + 256) 8 => unfold MV; apply (proj2 (L5A.defined_vis (ahid Aw model) M (os + 256) 8 ltac:(apply OAV; lia))); exact F256
      | |- PMASRDP.aligned _ _ => unfold PMASRDP.aligned; lia
      | |- _ => lia end]).
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS1 & KS1 & E1 & E10 & E11 & E12)).
    apply (ro_step fx fx1 R 0xb787c R1 0xb58c8 M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    apply (call_filltb fx1 R1 M model1 s sm cr LK Aw (q1 + n) 751800 c1 n1 q1 E1 ltac:(split; [lia| reflexivity])); try assumption.
    + rewrite (KS1 2%nat) by inl. exact A2.
    + kp_tac KS1 KP.
    + lia.
    + unfold PM.CHUNK. lia.
    + intros fx2 R2 M2 model2 LK2 Aw2 sm2 c RP2 Y10 Hc G2 RSC RS2 STEP2 CHK TBK SO2.
      pose proof (unread_nn M2 model2 s sm2 cr LK2 Aw2 SO2) as (UN2 & ST2' & RM2 & GE2).
      assert (CONS2 : PMSPA.consumed (PM.p_src s) (PM.p_src s) sm sm2 = c).
      { unfold PMSPA.consumed, PM.unread. destruct STEP2 as (_ & E2 & _). lia. }
      refine (d_after_fill mu0 IH fx2 R2 M2 model2 s sm2 cr LK2 Aw2 w n c _ Y10 _ _ ltac:(unfold PM.CHUNK in Hc; lia) Hw SO2 _ Hn0 En _ _ FE _ _).
      * apply (lregs_pres R1 R2 w RP2). apply (lregs_keep R R1 w LR). ks_tac KS1.
      * rewrite (L5SAR.cs_of_preserved R1 R2 24%nat RP2) by inl. rewrite (KS1 24%nat) by inl. exact A24.
      * rewrite (L5SAR.cs_of_preserved R1 R2 27%nat RP2) by inl. rewrite (KS1 27%nat) by inl. exact A27.
      * rewrite ETB. cbn [PM.vs_size]. exact SZ.
      * unfold PMSPA.consumed in *. lia.
      * exact (PECSRD3A.src_step_trans _ _ _ _ _ _ STEP STEP2).
      *
        pose proof TXh as TX0. first [rewrite <- ETB in TX0| idtac]. unfold PECSRD1A.TX in TX0 |- *.
        destruct (pos_acct M model s sm cr LK Aw (len - w) SO CONS) as (EPOS & P0 & P1 & _).
        pose proof (TX_len M model s sm cr LK Aw (len - w) SO CONS ltac:(lia)) as TL.
        rewrite (PECSD.slice_app pl pos0 (len - w) c) by lia. rewrite app_assoc.
        apply (proj2 (PECSD.bytes_at_app RSEGS M2 _ _ _)). split.
        -- apply TBK; [rewrite TL; first [rewrite ETB| idtac]; cbn [PM.vs_data]; lia| rewrite TL; first [rewrite ETB| idtac]; cbn [PM.vs_size]; lia| exact TX0].
        -- rewrite TL, <- EPOS. first [rewrite ETB| idtac]. cbn [PM.vs_data]. unfold PEC.pos_of, PM.unread. rewrite RZ.
           replace (q1 + (PM.vs_size (PM.p_tb s0) + (len - w))) with (q1 + n) by lia.
           replace (blen pl - (0 + (PM.sm_eg sm - PM.sm_g sm))) with (blen pl - (PM.sm_eg sm - PM.sm_g sm)) by lia. exact CHK.
      * enough (PM.mu_src (PM.p_src s) sm2 < PM.mu_src (PM.p_src s) sm) by lia.
        apply (PECSRD3A.mu_dec _ _ _ _ STEP2 ST ST2').
        destruct (Z.ltb_spec c PM.CHUNK) as [LT|GE']; [right; split; [exact ST0| exact (proj2 (RSC LT))]| left].
        unfold PMSPA.consumed in CONS2. unfold PM.CHUNK in *. lia.
Qed.

Lemma dpath mu0 (IH : IHt mu0) (fx : FPState) R M model s sm cr LK Aw (w : Z) :
  lregs R w -> getr R (reg 24) = Z_to_bv 64 16384 -> 16384 <= w <= len ->
  st_ok M model s sm cr LK Aw -> acct s sm w -> TX M (PM.p_tb s) (len - w) ->
  PM.sr_rem (PM.p_src s) = 0 -> PM.sm_st sm = 0 -> PM.mu_src (PM.p_src s) sm <= mu0 ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb783c M model) K.
Proof using All.
  intros LR A24 Hw SO (CONS & SZ & STEP & FE) TXh RZ ST0 MU.
  pose proof LR as (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & KP).
  pose proof (unread_nn M model s sm cr LK Aw SO) as (UN & ST & RM & GE).
  pose proof (vpack M model s sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & _).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72 & Z80 & Z88 & Z96 & Z104).
  pose proof LC as (L184 & L176 & L168 & L160 & L152 & L144 & L136 & L128 & L120 & L112).
  pose proof geo as (Eop & Eos & Eois & Etb).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  assert (D1 : S - 192 + 192 <= os \/ os + 296 <= S - 192) by (right; lia).
  assert (D2 : S - 192 + 192 <= tb \/ tb + 24 <= S - 192) by (right; lia).
  assert (D3 : os + 296 <= tb \/ tb + 24 <= os) by (left; lia).
  bvr.
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _).
  replace (op + 336) with tb in VS by lia.
  assert (HSZ : PM.vs_size (PM.p_tb s) < 67108864) by (unfold PMSPA.consumed in CONS; lia).
  assert (F256 : True) by exact I.
  set (MV := mrestrict (ahid Aw model) M) in *.
  revert VS SZ HSZ. destruct (PM.p_tb s) as [n1|c1 n1 q1] eqn:ETB; intros (VD & VC & VS) SZ HSZ; cbn [PM.vs_size] in SZ, HSZ.
  -
    destruct VS as (Hn1 & B0). pose proof (PMF.even_byte n1) as EV.
    pose proof (PMASRDP.srdDS_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
       | 40%nat => 2 * n1
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) as PP.
    cbn beta iota in PP.
    L5SAR.feed PP ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.u64_at _ _ (tb + _) _ => unfold MV; vis64 TAV
      | |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
      | |- L5.defined _ (os + 256) 8 => unfold MV; apply (proj2 (L5A.defined_vis (ahid Aw model) M (os + 256) 8 ltac:(apply OAV; lia))); exact F256
      | |- PMASRDP.aligned _ _ => unfold PMASRDP.aligned; lia
      | |- _ => lia end]).
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS1 & KS1 & E1 & E10 & E11 & E12 & E27)).
    apply (ro_step fx fx1 R 0xb783c R1 0xd754c M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    assert (E11' : getr R1 (reg 11) = Z_to_bv 64 (n1 + 16384)) by (rewrite E11; f_equal; rewrite Z.mul_comm, Z.div_mul by lia; lia).
    assert (E27' : getr R1 (reg 27) = Z_to_bv 64 n1) by (rewrite E27; f_equal; rewrite Z.mul_comm, Z.div_mul by lia; lia).
    apply (call_resize fx1 R1 M model1 s sm cr LK Aw (n1 + 16384) 751740 E1 ltac:(split; [lia| reflexivity])); try assumption.
    + rewrite (KS1 2%nat) by inl. exact A2.
    + kp_tac KS1 KP.
    + rewrite ETB. cbn [PM.vs_size]. unfold PM.CHUNK. lia.
    + unfold PM.CHUNK. lia.
    + intros fx2 R2 M2 model2 LK2 Aw2 tb2 tg2 cr2 RP2 SZ2 _ BYT2 SO2.
      refine (d_after_resize mu0 IH fx2 R2 M2 model2 (PMTK2.with_tb s tb2 tg2) sm cr2 LK2 Aw2 w n1 _ _ _ Hw SO2 SZ2 ltac:(lia) SZ CONS STEP _ _ RZ ST0 MU).
      * apply (lregs_pres R1 R2 w RP2). apply (lregs_keep R R1 w LR). ks_tac KS1.
      * rewrite (L5SAR.cs_of_preserved R1 R2 24%nat RP2) by inl. rewrite (KS1 24%nat) by inl. exact A24.
      * rewrite (L5SAR.cs_of_preserved R1 R2 27%nat RP2) by inl. exact E27'.
      * destruct FE as (F1 & F2 & F3 & F4 & F5 & F6). unfold PECSRD1A.fields_eq. cbn [PMTK2.with_tb PM.p_more PM.p_done PM.p_depth PM.p_b PM.p_k PM.p_stk].
        repeat split; assumption.
      * unfold PECSRD1A.TX. cbn [PMTK2.with_tb PM.p_tb]. apply BYT2; [| first [exact TXh| rewrite ETB; exact TXh| rewrite <- ETB; exact TXh]].
        rewrite (TX_len M model s sm cr LK Aw (len - w) SO CONS ltac:(lia)). first [rewrite ETB| idtac]. cbn [PM.vs_size]. lia.
  -
    destruct VS as (W0' & W8 & W16 & Hn1 & Hc1 & Hce & DQ & CQ).
    pose proof (PMF.u8_of_u64 RSEGS M tb (c1 + 1) ltac:(lia) W0') as B0. pose proof (PMF.odd_byte c1 Hce ltac:(lia)) as ODB.
    assert (H39 : 0 <= (c1 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)); lia).
    pose proof (PMASRDP.srdDL_conc fx R MV (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => w
       | 40%nat => (c1 + 1) mod 256 | 41%nat => n1
       | 48%nat => U 1 | 49%nat => U 8 | 50%nat => U 9 | 51%nat => U 18 | 52%nat => U 19 | 53%nat => U 20 | 54%nat => U 21 | 55%nat => U 22
       | 56%nat => U 23 | 57%nat => U 24 | 58%nat => U 25 | 59%nat => U 26 | 60%nat => U 27 | _ => 0 end)) as PP.
    cbn beta iota in PP.
    L5SAR.feed PP ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.u64_at _ _ (tb + _) _ => unfold MV; vis64 TAV
      | |- L5.u8_at _ _ tb _ => unfold MV; vis8 TAV
      | |- L5.defined _ (os + 256) 8 => unfold MV; apply (proj2 (L5A.defined_vis (ahid Aw model) M (os + 256) 8 ltac:(apply OAV; lia))); exact F256
      | |- PMASRDP.aligned _ _ => unfold PMASRDP.aligned; lia
      | |- _ => lia end]).
    destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & (MS1 & KS1 & E1 & E10 & E11 & E12 & E27)).
    apply (ro_step fx fx1 R 0xb783c R1 0xd754c M model s sm cr LK Aw M1v SO MS1 MG1 FRZ1). intros model1 SO1.
    apply (call_resize fx1 R1 M model1 s sm cr LK Aw (n1 + 16384) 751740 E1 ltac:(split; [lia| reflexivity])); try assumption.
    + rewrite (KS1 2%nat) by inl. exact A2.
    + kp_tac KS1 KP.
    + rewrite ETB. cbn [PM.vs_size]. unfold PM.CHUNK. lia.
    + unfold PM.CHUNK. lia.
    + intros fx2 R2 M2 model2 LK2 Aw2 tb2 tg2 cr2 RP2 SZ2 _ BYT2 SO2.
      refine (d_after_resize mu0 IH fx2 R2 M2 model2 (PMTK2.with_tb s tb2 tg2) sm cr2 LK2 Aw2 w n1 _ _ _ Hw SO2 SZ2 ltac:(lia) SZ CONS STEP _ _ RZ ST0 MU).
      * apply (lregs_pres R1 R2 w RP2). apply (lregs_keep R R1 w LR). ks_tac KS1.
      * rewrite (L5SAR.cs_of_preserved R1 R2 24%nat RP2) by inl. rewrite (KS1 24%nat) by inl. exact A24.
      * rewrite (L5SAR.cs_of_preserved R1 R2 27%nat RP2) by inl. exact E27.
      * destruct FE as (F1 & F2 & F3 & F4 & F5 & F6). unfold PECSRD1A.fields_eq. cbn [PMTK2.with_tb PM.p_more PM.p_done PM.p_depth PM.p_b PM.p_k PM.p_stk].
        repeat split; assumption.
      * unfold PECSRD1A.TX. cbn [PMTK2.with_tb PM.p_tb]. apply BYT2; [| first [exact TXh| rewrite ETB; exact TXh| rewrite <- ETB; exact TXh]].
        rewrite (TX_len M model s sm cr LK Aw (len - w) SO CONS ltac:(lia)). first [rewrite ETB| idtac]. cbn [PM.vs_size]. lia.
Qed.

End Call.
End WithHeap.
End PECSRD4A.
