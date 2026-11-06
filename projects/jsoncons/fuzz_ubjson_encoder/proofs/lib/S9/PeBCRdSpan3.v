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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCModelA PeCSpecsA PeCSpecsAb PmModelFactsA PeStepAB0 PmStep PmTxtKit2 PeBSrcKitJ PeBCReset1 PeBRsKit PmSpecs PeCSink PeCModel PeCSpecs PeCFrame PeCSrcD PeCTxtSpecsA PeBRdSpanP PeBCRdSpan1 PeBCRdSpan2 PeBCRdSpan2b.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECRS3B.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Lemma pst_eta (s : PM.pst) :
  PM.PST (PM.p_more s) (PM.p_done s) (PM.p_depth s) (PM.p_src s) (PM.p_tb s) (PM.p_tg s) (PM.p_b s) (PM.p_k s) (PM.p_stk s) = s.
Proof. destruct s; reflexivity. Qed.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation pot := PECRS1B.pot.
Ltac pdestr PP := repeat match type of PP with _ /\ _ => let H := fresh "Q" in destruct PP as (H & PP) end.

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
Variable pl : list Z.
Hypothesis Rra0 : getr R0 (reg 1) = Z_to_bv 64 r.
Hypothesis RAok : L5.ra_ok r.
Hypothesis Rsp0 : getr R0 (reg 2) = Z_to_bv 64 S.
Hypothesis Rgp0 : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Rtp0 : getr R0 (reg 4) = Z_to_bv 64 (hl_tp L).
Hypothesis K0 : K [].
Hypothesis FRM0 : PMSPA.ffroomA 6 FF LK0.
Hypothesis FRS : PMSPA.ffrsA FF S.
Hypothesis FOK : PECA.frame_ok5 FF fb.
Hypothesis SA32 : S mod 32 = 0.
Hypothesis Hlen : 0 <= len < 2 ^ 64.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis UN0 : PM.unread (PM.p_src s0) sm0 < 2 ^ 26.
Hypothesis STKSH0 : shadow_zero M0 (S - 24576) 3072.
Hypothesis POK : PECS.payload_ok pl.
Hypothesis FBS : PECSB.fill_buffer_spec L ar HI.
Hypothesis SRDS : @PECTXSA.csrd_read_spec SCFG_P RSEGS AD L ar HI.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.pst) (sm' : PM.strm) (cr' : credit) (ptr n : Z),
  regs_preserved R0 R' -> getr R' 10%bv = Z_to_bv 64 ptr -> getr R' 11%bv = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
  ((ptr = 0 /\ n = 0) \/ (exists B m, In (B, m) (PM.parser_own s') /\ B <= ptr /\ ptr + n <= B + m) \/ (PMSPA.o_tb AD fb + 1 <= ptr /\ ptr + n <= PMSPA.o_tb AD fb + 24)) ->
  L5.defined M' ptr n -> PMSPA.accA M' ptr n -> L5.bytes_at RSEGS M' ptr (UbjRef.slice pl (PEC.pos_of pl (PM.p_src s0) sm0) n) ->
  n = Z.min len (blen pl - PEC.pos_of pl (PM.p_src s0) sm0) ->
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M' (PMSPA.o_p AD fb) (PMSPA.o_is AD fb) s' -> PM.iss_at RSEGS AD PMSPA.accA M' (PMSPA.o_is AD fb) str sm' ->
  PM.tb_ok (PM.p_tb s') (PM.p_tg s') ->
  PEC.content_ok RSEGS AD M' fb pl (PM.p_src s') str sm' ->
  PM.p_more s' = PM.p_more s0 -> PM.p_done s' = PM.p_done s0 -> PM.p_depth s' = PM.p_depth s0 ->
  PM.p_b s' = PM.p_b s0 -> PM.p_k s' = PM.p_k s0 -> PM.p_stk s' = PM.p_stk s0 ->
  PMSPA.src_step (PM.p_src s0) (PM.p_src s') sm0 sm' -> PMSPA.consumed (PM.p_src s0) (PM.p_src s') sm0 sm' = n ->
  L5CA.ahpres L ar LBX FF S (PMSPA.pm_scr 6) (PMSPA.W_srcf AD fb ++ [(PMSPA.o_tb AD fb, 24)]) M0 M' ->
  PMSPA.credit_keep cr0 cr' (pot L ar s0) (pot L ar s') ->
  model_rt model0 model' -> incl LK' LK0 -> incl Aw0 Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PM.parser_own s' ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' r M' model') K.

#[local] Abbreviation op := (PECRS1B.op fb).
#[local] Abbreviation os := (PECRS1B.os fb).
#[local] Abbreviation ois := (PECRS1B.ois fb).
#[local] Abbreviation tb := (PECRS1B.tb fb).
#[local] Abbreviation W0 := (PECRS1B.W0 fb).
#[local] Abbreviation U := (PECRS1B.U R0).
#[local] Abbreviation saves9 := (PECRS1B.saves9 R0 S).
#[local] Abbreviation kept_rs := (PECRS1B.kept_rs R0).
#[local] Abbreviation memrel := (PECRS1B.memrel L ar M0 LBX FF S fb).
#[local] Abbreviation fields_eq := (PECRS1B.fields_eq s0).
#[local] Abbreviation st_ok := (PECRS1B.st_ok L ar HI R0 M0 model0 LBX FF LK0 Aw0 cr0 S fb s0 str pl).
#[local] Abbreviation bregs := (PECRS1B.bregs R0 S fb len).
#[local] Abbreviation finish_rs := (PECRS1B.finish_rs L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK SA32 Hlen INCS UN0 STKSH0 POK FBS SRDS KONT).
#[local] Abbreviation call_srd := (PECRS1B.call_srd L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK SA32 Hlen INCS UN0 STKSH0 POK FBS SRDS KONT).
#[local] Abbreviation vpack := (PECRS1B.vpack L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK SA32 Hlen INCS UN0 STKSH0 POK FBS SRDS KONT).
#[local] Abbreviation content_agree := (PECRS1B.content_agree L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK SA32 Hlen INCS UN0 STKSH0 POK FBS SRDS KONT).
#[local] Abbreviation content_step := (PECRS1B.content_step L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK SA32 Hlen INCS UN0 STKSH0 POK FBS SRDS KONT).
#[local] Abbreviation outside_W0 := (PECRS1B.outside_W0 L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK SA32 Hlen INCS UN0 STKSH0 POK FBS SRDS KONT).

#[local] Abbreviation fast := (PECRS2B.fast L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK SA32 Hlen INCS UN0 STKSH0 POK FBS SRDS KONT).
#[local] Abbreviation slow := (PMARSP2b.slow L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK SA32 Hlen INCS UN0 STKSH0 POK FBS SRDS KONT).
#[local] Abbreviation call_fill := (PECRS1B.call_fill L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK SA32 Hlen INCS UN0 STKSH0 POK FBS SRDS KONT).
#[local] Abbreviation src_step_trans := PECRS2B.src_step_trans.
#[local] Abbreviation at_srd := (PECRS2B.at_srd L ar C HI LY HIok IL ICok ILY R0 M0 model0 K LBX FF LK0 Aw0 cr0 S r fb len s0 str sm0 pl Rra0 RAok Rsp0 Rgp0 Rtp0 K0 FRM0 FRS FOK SA32 Hlen INCS UN0 STKSH0 POK FBS SRDS KONT).
Ltac bvr1 x := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R0 (reg x))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 1%nat; bvr1 8%nat; bvr1 9%nat; bvr1 18%nat; bvr1 19%nat; bvr1 20%nat; bvr1 21%nat; bvr1 22%nat; bvr1 23%nat.
Ltac vis64 AV := lazymatch goal with |- L5.u64_at ?sg (mrestrict ?H ?M) ?a ?v =>
  apply (proj2 (L5A.u64_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac vis8 AV := lazymatch goal with |- L5.u8_at ?sg (mrestrict ?H ?M) ?a ?v =>
  apply (proj2 (L5A.u8_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.

Lemma after_fill (fx : FPState) R M model s sm sm1 cr LK Aw (c : Z) :
  bregs R -> getr R (reg 20) = Z_to_bv 64 (os + 264) -> getr R (reg 23) = Z_to_bv 64 ((os + 264) / 8 + 2147450880) ->
  getr R (reg 10) = Z_to_bv 64 c -> 0 <= c <= PM.CHUNK -> 1 <= len ->
  st_ok M model s sm1 cr LK Aw -> fields_eq s -> PMSPA.src_step (PM.p_src s0) (PM.p_src s) sm0 sm ->
  PMSPA.src_step (PM.p_src s) (PM.p_src s) sm sm1 -> PM.sr_rem (PM.p_src s) = 0 -> PM.sm_g sm1 = PM.sm_g sm + c ->
  PM.unread (PM.p_src s) sm = PM.unread (PM.p_src s0) sm0 -> 0 <= blen pl - (PM.sm_eg sm - PM.sm_g sm) ->
  L5.bytes_at RSEGS M (PM.sr_qc (PM.p_src s)) (UbjRef.slice pl (blen pl - (PM.sm_eg sm - PM.sm_g sm)) c) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xba790 M model) K.
Proof using All.
  intros BR0 A20 A23 A10 Hc Hl SO FE STEP STEP1 RZ G1 U00 P0 CHK. pose proof BR0 as (A2 & A8 & A9 & A18 & A19 & A21 & A22 & KP).
  pose proof (vpack M model s sm1 cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK & ACC & CT).
  pose proof (PECRS1B.geo fb) as (Eop & Eos & Eois & Etb). pose proof (PECRS1B.fbb FF fb FOK) as (F1024 & rs & Hfb).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & _).
  pose proof (PMBSKJ.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMBSKJ.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof (PMBSKJ.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  destruct (WF _ Hfb) as (FF1 & FF2 & _). cbn [ff_addr ff_class fst snd] in FF1, FF2.
  pose proof PA as (_ & PD & _ & _ & _ & _ & _ & _ & _ & SRC & _ & _ & _ & _ & VEC & _).
  destruct SRC as (F240 & F248 & F256 & F264 & F272 & F280 & F288 & Q1 & Q2 & Q3 & Q4 & DC & CC & C240).
  set (qc := PM.sr_qc (PM.p_src s)) in *.
  replace (op + 24) with os in * by lia. unfold PM.CHUNK in *.
  pose proof VEC as (_ & _ & _ & Hk & _). pose proof (PM.pow2_pos (PM.p_k s) (proj1 Hk)) as P2.
  assert (VIN : In (PM.p_b s, 32 * 2 ^ PM.p_k s) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; right; left; reflexivity).
  assert (QIN : In (qc, 16384) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  destruct (BRB _ QIN) as (QB0 & QB1). cbn [fst snd] in QB0, QB1. destruct (BRB _ VIN) as (VB0 & VB1). cbn [fst snd] in VB0, VB1.
  assert (BLKAP : forall q m, In (q, m) (PM.parser_own s ++ LBX) -> q + m <= fb \/ fb + 2048 <= q).
  { intros q m Hq. destruct (WB _ Hq) as (_ & _ & _ & _ & _ & FA & _). cbn [fst snd] in FA.
    destruct (FA (fb, 5, rs) (in_or_app _ _ _ (or_introl Hfb))) as [X|X]; cbn [ff_addr ff_class fst snd] in X; change (ff_bytes 5) with 2048 in X; [left|right]; lia. }
  assert (AOI : PMSPA.aobjA FF ois 272).
  { exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72).
  set (MV := mrestrict (ahid Aw model) M) in *.
  pose proof (PMBRSPP.arpB_conc fx R MV (fun j => match j with 2%nat => S | 34%nat => qc | 36%nat => os | 37%nat => tb | 38%nat => len | 43%nat => c | _ => 0 end)) as PP.
  cbn beta iota in PP.
  L5SAR.feed PP ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
      | |- PMBRSPP.aligned _ _ => unfold PMBRSPP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & EX).
  assert (CCs : L5.u64_at RSEGS M1v (os + 280) qc /\ L5.u64_at RSEGS M1v (os + 288) c).
  { destruct EX as [(_ & _ & _ & _ & _ & _ & C1 & C2) | (_ & _ & _ & _ & _ & _ & C1 & C2)]; split; assumption. }
  destruct CCs as (C1 & C2).
  set (P := fun a => os + 280 <= a < os + 280 + 16).
  set (s2 := PMSPA.with_src s (PM.SRC qc qc c)).
  assert (OWN2 : PM.parser_own s2 = PM.parser_own s) by reflexivity.

  assert (POST : forall M1 model1, ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M1 (vml_of model1) -> L5CA.amodel_ok Aw model1 -> model_rt model model1 ->
                   mrestrict (ahid Aw model) M1 = M1v -> mem_grows M M1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
                   st_ok M1 model1 s2 sm1 cr LK Aw).
  { intros M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1.
    assert (BK1 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
    { intros a v Ha Hb X. apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))). rewrite VIS1. exact X. }
    assert (AGO : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= os + 280 \/ os + 296 <= a) -> L5C.agree_on M M1 a n).
    { intros a n Ha Hn X i Hi. apply FR1; [lia| unfold P; clear - X Hi; lia]. }
    assert (AGSH : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n).
    { intros a n Ha Hn x Hx. unfold HeapIfaceA.S, HeapIfaceA.SB.
      assert (X8 : 0 <= x / 8 <= 17592186044416) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
      apply FR1; [lia|]. unfold P. clear - X8 OBIG. destruct OBIG; lia. }
    assert (AGB : forall q m, In (q, m) (PM.parser_own s ++ LBX) -> PMFA.agA M M1 q m).
    { intros q m Hq. destruct (BRB _ Hq) as (X0 & X1). cbn [fst snd] in X0, X1. destruct (BLKAP q m Hq) as [BF|BF]; (split; [apply AGO; lia| apply AGSH; lia]). }
    assert (PA1 : PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M1 op ois s2).
    { apply (PMBSKJ.parser_src_fieldsA M M1 op ois s qc c PA); [lia| lia| | | | lia| cbv [PM.CHUNK] in *; lia| | lia| lia| | | exact MGM1| | | | | lia| lia| cbv [PM.CHUNK] in *; lia].
      - split; [apply AGO; lia| apply AGSH; lia].
      - split; [apply AGO; lia| apply AGSH; lia].
      - apply AGSH; lia.
      - exact (AGB _ _ QIN).
      - exact (AGB _ _ VIN).
      - intros c0 n0 p0 E. apply AGB. apply in_or_app; left. unfold PM.parser_own. rewrite E. right; right; left; reflexivity.
      - apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| replace (op + 288) with (os + 264) by lia; exact F264].
      - apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| replace (op + 296) with (os + 272) by lia; exact F272].
      - replace (op + 304) with (os + 280) by lia. apply BK1; [lia| lia| exact C1].
      - replace (op + 312) with (os + 288) by lia. apply BK1; [lia| lia| exact C2]. }
    set (Wp := [(os + 280, 16)]).
    assert (EK1 : L5SAR.ek L ar (PM.parser_own s ++ LBX) FF S 24576 Wp M M1).
    { apply (L5SAR.ek_piece L ar _ FF S 24576 Wp M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. apply (OWx (os + 280, 16)); [left; reflexivity|]. unfold L5.in_rng, P in *; cbn [fst snd]. lia. }
    assert (WAPPp : PMKB.wapp Wp) by (apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct OBIG; [right| left]; lia| apply PMKB.wapp_nil]).
    assert (IA1 : PM.iss_at RSEGS AD PMSPA.accA M1 ois str sm1).
    { apply (PMKB.iss_keepA RSEGS AD L ar _ FF S 24576 Wp M M1 EK1 WAPPp FRB BRB _ _ _ AOI); [intros x Hx; apply in_or_app; right; apply INCS; exact Hx| | |exact IA].
      - intros i Hi r0 Hr. unfold Wp in Hr. unfold L5.in_rng. destruct Hr as [<-|[]]; cbn [fst snd]; lia.
      - intros c1 n1 p1 E i Hi r0 Hr. assert (Ip : In (p1, c1) (PM.parser_own s ++ LBX)) by (apply in_or_app; right; apply INCS; rewrite E; left; reflexivity).
        destruct (BLKAP _ _ Ip) as [X|X]; unfold Wp in Hr; unfold L5.in_rng; destruct Hr as [<-|[]]; cbn [fst snd]; lia. }
    assert (EKn : L5SAR.ek L ar LBX FF S 24576 W0 M M1).
    { apply (L5SAR.ek_piece L ar LBX FF S 24576 W0 M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. apply (OWx (os + 256, 40)); [unfold PECRS1B.W0, PMSPA.W_srcf; left; reflexivity|].
      unfold L5.in_rng, P in *; cbn [fst snd] in *. unfold PMSPA.o_src, PMSPA.o_p in *. cbn [pa_off_p ADDR_B] in *. lia. }
    split; [split; [|split]|].
    - exact (L5SAR.ek_trans L ar LBX FF S 24576 W0 M0 M M1 EK EKn).
    - apply (L5SAR.dk_trans L ar LBX FF S 24576 M0 M M1 DK). apply L5SAR.dk_grows. exact MGM1.
    - exact (L5SAR.astk_grows ar M M1 S 24576 STK MGM1).
    - split; [repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| assumption])|].
      split; [exact PA1|]. split; [exact IA1|].
      split; [apply (PMBSKJ.base_keep L ar C LY LBX FF S 24576 W0 M M1 EKn); [intros a Ha; apply outside_W0; lia| exact BASE]|].
      split; [exact TBOK|]. split; [rewrite OWN2; exact HH1|]. split; [exact AM1|]. split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1]|].
      split; [exact ILK|]. split; [exact IAW|]. split; [exact CRL|]. split; [exact CRK|].
      destruct (FRB _ Hfb) as (Fb0 & Fb1). cbn [ff_addr ff_class fst snd] in Fb0, Fb1. change (ff_bytes 5) with 2048 in Fb1.
      split; [apply (PMFA.accA_agree M M1 op PECA.RDR_BYTES); [apply AGSH; unfold PECA.RDR_BYTES; clear - Eop Fb0 Fb1; lia| exact ACC]|].

      pose proof CT as (CSZ & CBS & CPOS & _ & CST2). unfold PEC.pos_of, PM.unread in CPOS. rewrite RZ in CPOS.
      destruct STEP1 as (_ & EEG & _).
      unfold s2. unfold PEC.content_ok. cbn [PMSPA.with_src PM.p_src PM.sr_de PM.sr_rem PM.sr_qc].
      split; [exact CSZ|]. split.
      { exact (proj1 (proj2 (content_agree M M1 s sm1 cr LK Aw (vml_of model) (proj1 (AGB _ _ QIN)) (fun B m Hin => proj1 (AGB B m ltac:(apply in_or_app; right; exact Hin)))
                 ltac:(apply AGO; clear - Eois Eos Fb0 Fb1; lia) HH PA IA CT))). }
      unfold PEC.pos_of, PM.unread. cbn [PM.sr_de PM.sr_rem].
      split; [clear - P0 G1 EEG Hc; lia|]. split; [| exact CST2].
      replace (blen pl - (c + (PM.sm_eg sm1 - PM.sm_g sm1))) with (blen pl - (PM.sm_eg sm - PM.sm_g sm)) by (clear - G1 EEG; lia).
      apply (PECSD.bytes_agree RSEGS M M1 qc c); [apply PECF.slice_length_le; clear - Hc; lia| clear - QB0; lia| clear - QB1 Hc; unfold PM.CHUNK in *; lia| | exact CHK].
      intros i Hi. apply (proj1 (AGB _ _ QIN)). clear - Hi Hc; unfold PM.CHUNK in *; lia. }
  assert (STEP2 : PMSPA.src_step (PM.p_src s0) (PM.p_src s2) sm0 sm1).
  { apply (src_step_trans _ _ _ _ _ _ STEP). unfold s2. unfold PMSPA.src_step, PM.unread in *. cbn [PMSPA.with_src PM.p_src PM.sr_qc PM.sr_rem] in *.
    destruct STEP1 as (E1 & E2 & L1 & S1 & U1). split; [reflexivity|]. split; [exact E2|]. split; [exact L1|]. split; [exact S1| lia]. }
  assert (FE2 : fields_eq s2) by exact FE.
  assert (WOB : forall a, 0 <= a < 2 ^ 64 -> P a -> aclientw L ar (PM.parser_own s ++ LBX) FF 0 0 a /\ ~ (0x10000 <= a < 0x69c000)).
  { intros a Ha Wa. unfold P in Wa. split.
    - unfold aclientw, aclient_g. right; right; right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia.
    - lia. }
  assert (FZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) by (intros a Ha N; apply FRZ1; [exact Ha| exact N]).
  unfold PMSPA.cfg.
  destruct EX as [(MS & KS1 & E10 & E11 & E12 & Hlt & _) | (MS & KS1 & E10 & E11 & E12 & Hge & _)].
  -
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xba790 R1 0xba7d0 M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    pose proof (POST M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1) as SO1.
    apply (slow fx1 R1 M1 model1 s2 sm1 cr LK Aw); try assumption.
    + unfold PECRS1B.bregs.
      split; [rewrite (KS1 2%nat) by inl; exact A2|]. split; [rewrite (KS1 8%nat) by inl; exact A8|].
      split; [rewrite (KS1 9%nat) by inl; exact A9|]. split; [rewrite (KS1 18%nat) by inl; exact A18|].
      split; [rewrite (KS1 19%nat) by inl; exact A19|]. split; [rewrite (KS1 21%nat) by inl; exact A21|].
      split; [rewrite (KS1 22%nat) by inl; exact A22|].
      intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
    + rewrite <- U00. unfold s2, PM.unread. cbn [PMSPA.with_src PM.p_src PM.sr_rem]. rewrite RZ. destruct STEP1 as (_ & EEG & _). clear - G1 EEG; lia.
  -
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xba790 R1 0xba814 M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    pose proof (POST M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1) as SO1.
    assert (BR1 : bregs R1).
    { unfold PECRS1B.bregs.
      split; [rewrite (KS1 2%nat) by inl; exact A2|]. split; [rewrite (KS1 8%nat) by inl; exact A8|].
      split; [rewrite (KS1 9%nat) by inl; exact A9|]. split; [rewrite (KS1 18%nat) by inl; exact A18|].
      split; [rewrite (KS1 19%nat) by inl; exact A19|]. split; [rewrite (KS1 21%nat) by inl; exact A21|].
      split; [rewrite (KS1 22%nat) by inl; exact A22|].
      intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx. }
    apply (fast fx1 R1 M1 model1 s2 sm1 cr LK Aw); try assumption.
    all: unfold s2; cbn [PMSPA.with_src PM.p_src PM.sr_rem]; first [exact E12 | lia
               | (rewrite <- U00; unfold PM.unread; cbn [PM.sr_rem]; rewrite RZ; destruct STEP1 as (_ & EEG & _); clear - G1 EEG; lia) ].
Qed.

Lemma src_step_refl a sa : PMSPA.src_step a a sa sa.
Proof. clear. unfold PMSPA.src_step. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros X; exact X| lia]. Qed.

Lemma entry (fx : FPState) :
  ri_inv HI (PM.parser_own s0 ++ LBX) FF LK0 cr0 Aw0 M0 (vml_of model0) -> L5CA.amodel_ok Aw0 model0 -> L5CA.astk ar M0 S 24576 ->
  getr R0 (reg 10) = Z_to_bv 64 os -> getr R0 (reg 11) = Z_to_bv 64 len -> getr R0 (reg 12) = Z_to_bv 64 tb ->
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M0 op ois s0 -> PM.iss_at RSEGS AD PMSPA.accA M0 ois str sm0 -> PMSTA.base_okA RSEGS AD M0 ->
  PM.tb_ok (PM.p_tb s0) (PM.p_tg s0) -> PMSPA.credit_le (pot L ar s0) cr0 ->
  PMSPA.accA M0 op PECA.RDR_BYTES -> PEC.content_ok RSEGS AD M0 fb pl (PM.p_src s0) str sm0 ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R0 0xba6f4 M0 model0) K.
Proof using All.
  intros HH AM STK A10 A11 A12 PA IA BASE TBOK CRL ACC0 CT0.
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (PECRS1B.geo fb) as (Eop & Eos & Eois & Etb). pose proof (PECRS1B.fbb FF fb FOK) as (F1024 & rs & Hfb).
  pose proof (PMBSKJ.mach_vis L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 HH BASE) as (V0 & V1 & V2).
  pose proof (PMBSKJ.stk_vis L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 S 24576 80 HH STK ltac:(lia)) as (SL80 & SH80 & V3).
  pose proof (PMBSKJ.src_vis L ar C HI LY HIok _ FF LK0 cr0 Aw0 M0 model0 fb ois s0 S 24576 HH FOK PA STK)
    as ((O1 & O8 & OBIG) & OZ & OW & OCE & OAV & AO & OFS1 & OFS2).
  fold os in O1, O8, OBIG, OZ, OW, OCE, OAV, AO.
  pose proof PA as (_ & PD & _ & _ & _ & _ & _ & _ & _ & SRC & _).
  destruct SRC as (F240 & F248 & F256 & F264 & F272 & F280 & F288 & Q1 & Q2 & Q3 & Q4 & DC & CC & C240).
  set (qc := PM.sr_qc (PM.p_src s0)) in *. set (rem := PM.sr_rem (PM.p_src s0)) in *.
  replace (op + 24) with os in * by lia. unfold PM.CHUNK in *.
  assert (QIN : In (qc, 16384) (PM.parser_own s0 ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  destruct (PMBSKJ.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH _ QIN) as (QB0 & QB1). cbn [fst snd] in QB0, QB1.
  set (MV := mrestrict (ahid Aw0 model0) M0) in *.
  pose proof (PMBRSPP.arpA_conc fx R0 MV (fun j => match j with 2%nat => S | 33%nat => rem | 36%nat => os | 37%nat => tb | 38%nat => len | _ => 0 end)) as PP.
  cbn beta iota in PP.
  L5SAR.feed PP ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
      | |- PMBRSPP.aligned _ _ => unfold PMBRSPP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & EX).
  set (P := fun a => S - 80 <= a < S - 80 + 80).
  assert (FZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1v (Z_to_bv 64 a) = MV (Z_to_bv 64 a)) by (intros a Ha N; apply FRZ1; [exact Ha| exact N]).
  assert (WOB : forall a, 0 <= a < 2 ^ 64 -> P a -> aclientw L ar (PM.parser_own s0 ++ LBX) FF 0 0 a /\ ~ (0x10000 <= a < 0x69c000)).
  { intros a Ha Wa. unfold P in Wa. split; [|lia]. unfold aclientw, aclient_g. right; left. split; [lia| lia]. }

  assert (POST : forall M1 model1, ri_inv HI (PM.parser_own s0 ++ LBX) FF LK0 cr0 Aw0 M1 (vml_of model1) -> L5CA.amodel_ok Aw0 model1 -> model_rt model0 model1 ->
                   mrestrict (ahid Aw0 model0) M1 = M1v -> mem_grows M0 M1 -> (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)) ->
                   saves9 M1v -> st_ok M1 model1 s0 sm0 cr0 LK0 Aw0).
  { intros M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1 SVv.
    pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 HH) as (_ & VIS & _).
    assert (AG : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= S - 80 \/ S <= a) -> L5C.agree_on M0 M1 a n).
    { intros a n Ha Hn X i Hi. apply FR1; [lia| unfold P; clear - X Hi; lia]. }
    assert (AGSH : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M0 M1 a n).
    { intros a n Ha Hn x Hx. unfold HeapIfaceA.S, HeapIfaceA.SB.
      assert (X8 : 0 <= x / 8 <= 17592186044416) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
      apply FR1; [lia|]. unfold P. lia. }
    assert (EKn : L5SAR.ek L ar LBX FF S 24576 W0 M0 M1).
    { apply (L5SAR.ek_piece L ar LBX FF S 24576 W0 M0 M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. unfold P in Pa.
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 _ S 24576 a HH SPT (L5SAR.aclient_appb L ar LBX (PM.parser_own s0) FF S 24576 a CA)) as [X|X]; lia. }
    pose proof (PMBSKJ.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMBSKJ.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
    assert (EKp : L5SAR.ek L ar (PM.parser_own s0 ++ LBX) FF S 24576 [] M0 M1).
    { apply (L5SAR.ek_piece L ar _ FF S 24576 [] M0 M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
      intros a Ha CA OWx Pa. unfold P in Pa.
      destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 _ S 24576 a HH SPT CA) as [X|X]; lia. }
    assert (AOP : PMSPA.aobjA FF op 384).
    { exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
    assert (AOI : PMSPA.aobjA FF ois 272).
    { exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
    split; [split; [|split]|].
    - exact EKn.
    - apply L5SAR.dk_grows. exact MGM1.
    - exact (L5SAR.astk_grows ar M0 M1 S 24576 STK MGM1).
    - split.
      { destruct SVv as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72).
        assert (BK : forall k v, 8 <= k <= 80 -> L5.u64_at RSEGS M1v (S - k) v -> L5.u64_at RSEGS M1 (S - k) v).
        { intros k v Hk X. apply (proj1 (L5A.u64_at_vis (ahid Aw0 model0) M1 (S - k) v (VIS (S - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact X. }
        repeat split; (apply BK; [lia| assumption]). }
      split; [apply (PMKB.parser_keepA RSEGS AD L ar _ FF S 24576 [] M0 M1 EKp PMKB.wapp_nil FRB BRB _ _ _ AOP); [apply incl_appl, incl_refl| intros i _ r0 []| | | |exact PA]|].
      { intros i _ r0 []. } { intros i _ r0 []. } { intros c0 n0 p0 _ i _ r0 []. }
      split; [apply (PMKB.iss_keepA RSEGS AD L ar _ FF S 24576 [] M0 M1 EKp PMKB.wapp_nil FRB BRB _ _ _ AOI); [intros x Hx; apply in_or_app; right; apply INCS; exact Hx| intros i _ r0 []| intros c0 n0 p0 _ i _ r0 []| exact IA]|].
      split; [apply (PMBSKJ.base_keep L ar C LY LBX FF S 24576 W0 M0 M1 EKn); [intros a Ha; apply outside_W0; pose proof (PMBSKJ.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH); lia| exact BASE]|].
      split; [exact TBOK|]. split; [exact HH1|]. split; [exact AM1|]. split; [exact MRT1|].
      split; [apply incl_refl|]. split; [apply incl_refl|]. split; [exact CRL|].
      split; [unfold PMSPA.credit_keep; lia|].
      assert (QIN9 : In (PM.sr_qc (PM.p_src s0), PM.CHUNK) (PM.parser_own s0 ++ LBX)) by (apply in_or_app; left; left; reflexivity).
      split.
      { apply (PMFA.accA_agree M0 M1 op PECA.RDR_BYTES); [| exact ACC0].
        apply (PMKB.agsh_obj L ar _ FF S 24576 [] M0 M1 EKp PMKB.wapp_nil FRB op PECA.RDR_BYTES).
        apply (PMBSKJ.aobj_fb FF fb); [exact FOK| clear - Eop; lia| unfold PECA.RDR_BYTES; clear - Eop; lia]. }
      apply (content_agree M0 M1 s0 sm0 cr0 LK0 Aw0 (vml_of model0)); [| | | exact HH| exact PA| exact IA| exact CT0].
      + exact (proj1 (PMKB.agA_blk L ar _ FF S 24576 [] M0 M1 EKp PMKB.wapp_nil BRB _ _ QIN9 ltac:(intros i _ r0 []))).
      + intros B m Hin. exact (proj1 (PMKB.agA_blk L ar _ FF S 24576 [] M0 M1 EKp PMKB.wapp_nil BRB B m ltac:(apply in_or_app; right; exact Hin) ltac:(intros i _ r0 []))).
      + refine (proj1 (PMKB.agA_obj L ar _ FF S 24576 [] M0 M1 EKp PMKB.wapp_nil FRB (ois + 80) 24 _ ltac:(intros i _ r0 [])));
          apply (PMBSKJ.aobj_fb FF fb); [exact FOK| clear - Eois; lia| clear - Eois; lia]. }
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 1))) as BU1. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 8))) as BU8.
  pose proof (bv_unsigned_in_range 64 (getr R0 (reg 9))) as BU9. pose proof (bv_unsigned_in_range 64 (getr R0 (reg 18))) as BU18.
  change (bv_modulus 64) with (2 ^ 64) in *.
  assert (FE0 : fields_eq s0) by (unfold PECRS1B.fields_eq; repeat split).
  unfold PMSPA.cfg.
  destruct EX as [(MS & KS1 & E10 & E11 & Z0 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)
                 | [(MS & KS1 & E2 & E8 & E9 & E10 & E12 & E18 & E19 & E21 & E22 & Hle & Hr1 & Hl1 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)
                 | [(MS & KS1 & E2 & E8 & E9 & E10 & E12 & E18 & E19 & E21 & E22 & Hlt & Hr1 & Hl1 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)
                 | (MS & KS1 & E2 & E8 & E9 & E10 & E18 & E19 & E21 & E22 & Hr0 & Hl1 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8)]]].
  -
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xba6f4 R1 0xba950 M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    pose proof (POST M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1 ltac:(repeat split; assumption)) as SO1.
    assert (L0 : len = 0) by (rewrite Z.sub_0_r, Z.mod_small in Z0 by lia; lia).
    apply (finish_rs fx1 R1 M1 model1 s0 sm0 cr0 LK0 Aw0 0 0); try assumption.
    all: first [ rewrite (KS1 1%nat) by inl; unfold PECRS1B.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 2%nat) by inl; exact Rsp0
               | rewrite (KS1 8%nat) by inl; unfold PECRS1B.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 9%nat) by inl; unfold PECRS1B.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 18%nat) by inl; unfold PECRS1B.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 19%nat) by inl; unfold PECRS1B.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 20%nat) by inl; unfold PECRS1B.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 21%nat) by inl; unfold PECRS1B.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 22%nat) by inl; unfold PECRS1B.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | rewrite (KS1 23%nat) by inl; unfold PECRS1B.U; rewrite Z_to_bv_bv_unsigned; reflexivity
               | (intros x Hx; rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx); reflexivity)
               | lia
               | (left; split; reflexivity)
               | (intros i Hi; lia)
               | (unfold UbjRef.slice; cbn [Z.to_nat firstn]; apply PECSD.bytes_at_nil)
               | (rewrite L0; unfold PEC.pos_of, PM.unread; pose proof (PMBSKJ.iss_size_ltA M0 ois str sm0 IA) as ISZ;
                  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & QG2 & _) & _); clear - ISZ QG2; first [subst rem| idtac]; first [subst qc| idtac]; lia)
               | (unfold PMSPA.consumed; clear; lia)
               | apply src_step_refl ].
  -
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xba6f4 R1 0xba814 M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    pose proof (POST M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1 ltac:(repeat split; assumption)) as SO1.
    assert (BR1 : bregs R1).
    { unfold PECRS1B.bregs. do 7 (split; [assumption|]).
      intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). reflexivity. }
    apply (fast fx1 R1 M1 model1 s0 sm0 cr0 LK0 Aw0 BR1 E12); [rewrite Z.sub_0_r, Z.mod_small in Hr1, Hl1 by lia; lia| exact SO1| exact FE0| apply src_step_refl| reflexivity].
  -
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xba6f4 R1 0xba7d0 M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    pose proof (POST M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1 ltac:(repeat split; assumption)) as SO1.
    assert (BR1 : bregs R1).
    { unfold PECRS1B.bregs. do 7 (split; [assumption|]).
      intros x Hx. rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). reflexivity. }
    apply (slow fx1 R1 M1 model1 s0 sm0 cr0 LK0 Aw0 BR1); [rewrite Z.sub_0_r, Z.mod_small in Hl1 by lia; lia| exact SO1| exact FE0| apply src_step_refl| reflexivity].
  -
    apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M0 model0 fx fx1 R0 0xba6f4 R1 0xba754 M1v P K HH AM MS MG1 FZ WOB).
    intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.
    pose proof (POST M1 model1 HH1 AM1 MRT1 VIS1 MGM1 FR1 ltac:(repeat split; assumption)) as SO1.
    assert (RZ : rem = 0) by (rewrite Z.sub_0_r, Z.mod_small in Hr0 by lia; lia).
    assert (LP : 1 <= len) by (rewrite Z.sub_0_r, Z.mod_small in Hl1 by lia; lia).
    pose proof (vpack M1 model1 s0 sm0 cr0 LK0 Aw0 SO1) as (W0v & W1v & W2v & (SR1 & S16 & W3v) & SVV & (P1 & P8 & PBIG) & PZ & PW & PAV & _ & _ & _ & _ & OSS & _ & _ & _).
    pose proof SO1 as (_ & _ & PA1 & _).
    pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC1 & _).
    destruct SRC1 as (_ & _ & _ & G264 & G272 & _ & G288 & _). replace (op + 24) with os in * by lia. fold qc rem in G264, G288. rewrite RZ in G288.
    set (MV1 := mrestrict (ahid Aw0 model1) M1) in *.
    pose proof (PMBRSPP.arpR0_conc fx1 R1 MV1 (fun j => match j with 2%nat => S | 34%nat => qc | 36%nat => os | 37%nat => tb | 38%nat => len | _ => 0 end)) as PP.
    cbn beta iota in PP.
    L5SAR.feed PP ltac:(first [assumption | lazymatch goal with
        | |- L5.u64_at _ _ (os + _) _ => unfold MV1; vis64 PAV
        | |- PMBRSPP.aligned _ _ => unfold PMBRSPP.aligned; lia
        | |- _ => lia end]).
    destruct PP as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & [(MS2 & KS2 & F10 & F11 & F12 & Hgt) | (MS2 & KS2 & F1 & F10 & F11 & F12 & F20 & F23 & Hle)]).
    +
      apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M1 model1 fx1 fx2 R1 0xba754 R2 0xba7d0 M2v K HH1 AM1 MS2 MG2 FRZ2).
      intros M2 model2 HH2 AM2 MRT2 HID2 VIS2 MGM2 FR2.
      assert (E2' : M2 = M1) by (apply L5SAR.mem_eq_of_agree; exact FR2). subst M2.
      assert (SO2 : st_ok M1 model2 s0 sm0 cr0 LK0 Aw0).
      { pose proof SO1 as (X1 & X2 & X3 & X4 & X5 & X6 & _ & _ & X9 & X10 & X11 & X12 & X13).
        exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj HH2 (conj AM2 (conj (L5LZ.model_rt_trans _ _ _ X9 MRT2) (conj X10 (conj X11 (conj X12 X13)))))))))))). }
      assert (BR2 : bregs R2).
      { unfold PECRS1B.bregs.
        split; [rewrite (KS2 2%nat) by inl; exact E2|]. split; [rewrite (KS2 8%nat) by inl; exact E8|].
        split; [rewrite (KS2 9%nat) by inl; exact E9|]. split; [rewrite (KS2 18%nat) by inl; exact E18|].
        split; [rewrite (KS2 19%nat) by inl; exact E19|]. split; [rewrite (KS2 21%nat) by inl; exact E21|].
        split; [rewrite (KS2 22%nat) by inl; exact E22|].
        intros x Hx. rewrite (KS2 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). reflexivity. }
      apply (slow fx2 R2 M1 model2 s0 sm0 cr0 LK0 Aw0 BR2 LP SO2 FE0 (src_step_refl _ _) eq_refl).
    +
      apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK0 cr0 Aw0 M1 model1 fx1 fx2 R1 0xba754 R2 0xb9944 M2v K HH1 AM1 MS2 MG2 FRZ2).
      intros M2 model2 HH2 AM2 MRT2 HID2 VIS2 MGM2 FR2.
      assert (E2' : M2 = M1) by (apply L5SAR.mem_eq_of_agree; exact FR2). subst M2.
      assert (SO2 : st_ok M1 model2 s0 sm0 cr0 LK0 Aw0).
      { pose proof SO1 as (X1 & X2 & X3 & X4 & X5 & X6 & _ & _ & X9 & X10 & X11 & X12 & X13).
        exact (conj X1 (conj X2 (conj X3 (conj X4 (conj X5 (conj X6 (conj HH2 (conj AM2 (conj (L5LZ.model_rt_trans _ _ _ X9 MRT2) (conj X10 (conj X11 (conj X12 X13)))))))))))). }
      assert (KP2 : kept_rs R2).
      { intros x Hx. rewrite (KS2 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). rewrite (KS1 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). reflexivity. }
      assert (R2sp : getr R2 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (KS2 2%nat) by inl; exact E2).
      apply (call_fill fx2 R2 M1 model2 s0 sm0 cr0 LK0 Aw0 763792 F1 ltac:(split; [lia| reflexivity]) R2sp KP2 F10 F11 F12 SO2 RZ).
      intros fx3 R3 M3 model3 LK3 Aw3 sm3 c RP3 Y10 Hc G1 RSC RS2 STEP3 CHK3 ST23 SO3.
      assert (BR3 : bregs R3).
      { unfold PECRS1B.bregs.
        split; [rewrite (L5SAR.cs_of_preserved R2 R3 2%nat RP3) by inl; exact R2sp|].
        split; [rewrite (L5SAR.cs_of_preserved R2 R3 8%nat RP3) by inl; rewrite (KS2 8%nat) by inl; exact E8|].
        split; [rewrite (L5SAR.cs_of_preserved R2 R3 9%nat RP3) by inl; rewrite (KS2 9%nat) by inl; exact E9|].
        split; [rewrite (L5SAR.cs_of_preserved R2 R3 18%nat RP3) by inl; rewrite (KS2 18%nat) by inl; exact E18|].
        split; [rewrite (L5SAR.cs_of_preserved R2 R3 19%nat RP3) by inl; rewrite (KS2 19%nat) by inl; exact E19|].
        split; [rewrite (L5SAR.cs_of_preserved R2 R3 21%nat RP3) by inl; rewrite (KS2 21%nat) by inl; exact E21|].
        split; [rewrite (L5SAR.cs_of_preserved R2 R3 22%nat RP3) by inl; rewrite (KS2 22%nat) by inl; exact E22|].
        intros x Hx. rewrite (L5SAR.cs_of_preserved R2 R3 x RP3) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP2. exact Hx. }
      apply (after_fill fx3 R3 M3 model3 s0 sm0 sm3 cr0 LK3 Aw3 c BR3); try assumption.
      * rewrite (L5SAR.cs_of_preserved R2 R3 20%nat RP3) by inl. exact F20.
      * rewrite (L5SAR.cs_of_preserved R2 R3 23%nat RP3) by inl. exact F23.
      * apply src_step_refl.
      * reflexivity.
      * destruct CT0 as (_ & _ & CP0 & _). unfold PEC.pos_of, PM.unread in CP0. clear - CP0 RZ. first [subst rem| idtac]. lia.
Qed.

End Call.

Theorem read_span_ok : PECSB.fill_buffer_spec L ar HI -> @PECTXSA.csrd_read_spec SCFG_P RSEGS AD L ar HI -> PECSB.read_span_spec L ar HI.
Proof.
  intros FBS SRDS. unfold PECSB.read_span_spec, PECSPA.read_span_spec.
  intros fx R M model K LBX FF LK Aw cr sp r fb len pl s str sm HH AM K0 ENT FRM FRS FOK SA32 A10 A11 A12 HLEN PA IA BASE ACC TBOK INCS POK CT CRL KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 6) with 24576 in *. change (24576 / 8) with 3072 in STKSH.
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
  rewrite L5SAR.r11 in A11. rewrite L5SAR.r12 in A12.
  cbn [pa_read_span PeCLayoutB.CADDR_B].
  assert (UN : PM.unread (PM.p_src s) sm < 2 ^ 26).
  { destruct CT as (_ & _ & CP & _). destruct POK as [_ BL]. unfold PEC.pos_of in CP. clear - CP BL; lia. }
  exact (entry R M model K LBX FF LK Aw cr sp r fb len s str sm pl Rra RAok Rsp Rgp Rtp K0 FRM FRS FOK SA32 HLEN INCS UN STKSH POK FBS SRDS KONT fx
           HH AM ASTK A10 A11 A12 PA IA BASE TBOK CRL ACC CT).
Qed.

End WithHeap.
End PECRS3B.
