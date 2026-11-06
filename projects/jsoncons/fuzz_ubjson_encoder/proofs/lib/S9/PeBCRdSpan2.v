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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCModelA PeCSpecsA PeCSpecsAb PmModelFactsA PeStepAB0 PmStep PmTxtKit2 PeBSrcKitJ PeBCReset1 PeBRsKit PmSpecs PeCSink PeCModel PeCSpecs PeCFrame PeCSrcD PeCTxtSpecsA PeBRdSpanP PeBCRdSpan1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECRS2B.
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

Lemma src_step_trans a b c sa sb sc : PMSPA.src_step a b sa sb -> PMSPA.src_step b c sb sc -> PMSPA.src_step a c sa sc.
Proof. clear.
  unfold PMSPA.src_step. intros (E1 & E2 & L1 & S1 & U1) (E3 & E4 & L2 & S2 & U2).
  split; [congruence|]. split; [congruence|]. split; [lia|]. split; [intros X; apply S2; apply S1; exact X| lia].
Qed.
Ltac bvr1 x := let H := fresh "BU" in pose proof (bv_unsigned_in_range 64 (getr R0 (reg x))) as H; change (bv_modulus 64) with (2 ^ 64) in H.
Ltac bvr := bvr1 1%nat; bvr1 8%nat; bvr1 9%nat; bvr1 18%nat; bvr1 19%nat; bvr1 20%nat; bvr1 21%nat; bvr1 22%nat; bvr1 23%nat.
Ltac vis64 AV := lazymatch goal with |- L5.u64_at ?sg (mrestrict ?H ?M) ?a ?v =>
  apply (proj2 (L5A.u64_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.
Ltac vis8 AV := lazymatch goal with |- L5.u8_at ?sg (mrestrict ?H ?M) ?a ?v =>
  apply (proj2 (L5A.u8_at_vis H M a v ltac:(apply AV; lia) ltac:(lia) ltac:(lia))); assumption end.

Lemma fast (fx : FPState) R M model s sm cr LK Aw :
  bregs R -> getr R (reg 12) = Z_to_bv 64 (PM.sr_rem (PM.p_src s)) -> 1 <= len <= PM.sr_rem (PM.p_src s) ->
  st_ok M model s sm cr LK Aw -> fields_eq s -> PMSPA.src_step (PM.p_src s0) (PM.p_src s) sm0 sm ->
  PM.unread (PM.p_src s) sm = PM.unread (PM.p_src s0) sm0 ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xba814 M model) K.
Proof using All.
  intros (A2 & A8 & A9 & A18 & A19 & A21 & A22 & KP) A12 Hl SO FE STEP U0.
  pose proof (vpack M model s sm cr LK Aw SO) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO as ((EK & DK & STK) & SV & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK & ACC & CT).
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (PECRS1B.geo fb) as (Eop & Eos & Eois & Etb). pose proof (PECRS1B.fbb FF fb FOK) as (F1024 & rs & Hfb).
  pose proof PA as (_ & PD & _ & _ & _ & _ & _ & _ & _ & SRC & _).
  destruct SRC as (F240 & F248 & F256 & F264 & F272 & F280 & F288 & G1 & G2 & G3 & G4 & DC & CC & C240).
  set (qc := PM.sr_qc (PM.p_src s)) in *. set (de := PM.sr_de (PM.p_src s)) in *. set (rem := PM.sr_rem (PM.p_src s)) in *.
  replace (op + 24) with os in * by lia. unfold PM.CHUNK in *.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  assert (QIN : In (qc, 16384) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  destruct (WB _ QIN) as ((Q0 & Q1 & Q2 & Q3 & Q4 & Q5) & _). cbn [fst snd] in Q0, Q1, Q2, Q3, Q4, Q5.
  pose proof SV as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72). bvr.
  set (MV := mrestrict (ahid Aw model) M) in *.
  pose proof (PMBRSPP.arpF_conc fx R MV (fun j => match j with 2%nat => S | 33%nat => rem | 35%nat => de | 36%nat => os | 37%nat => tb | 38%nat => len
       | 44%nat => U 1 | 45%nat => U 8 | 46%nat => U 9 | 47%nat => U 18 | 48%nat => U 19 | 49%nat => U 20 | 50%nat => U 21 | 51%nat => U 22 | 52%nat => U 23
       | _ => 0 end)) as PP.
  cbn beta iota in PP.
  L5SAR.feed PP ltac:(first [assumption | lazymatch goal with
      | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
      | |- L5.u64_at _ _ (os + _) _ => unfold MV; vis64 OAV
      | |- L5.defined _ (os + 256) 8 => unfold MV; apply (proj2 (L5A.defined_vis (ahid Aw model) M (os + 256) 8 ltac:(apply OAV; lia))); exact F256
      | |- PMBRSPP.aligned _ _ => unfold PMBRSPP.aligned; lia
      | |- _ => lia end]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & E1 & E2 & E8 & E9 & E10 & E11 & E13 & E14 & E18 & E19 & E20 & E21 & E22 & E23 & C288 & C280).
  unfold PMSPA.cfg.
  set (P := fun a => os + 256 <= a < os + 256 + 8 \/ os + 280 <= a < os + 280 + 16).
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xba814 R1 0xba950 M1v P K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| intros X; apply N; left; exact X| intros X; apply N; right; exact X]. }
  { intros a Ha Wa. unfold P in Wa. split.
    - unfold aclientw, aclient_g. right; right; right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia.
    - lia. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1.

  set (s' := PMSPA.with_src s (PM.SRC qc (de + len) (rem - len))).
  assert (OWN' : PM.parser_own s' = PM.parser_own s) by reflexivity.
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M1 model1 HH1) as (_ & VIS1s & _).
  assert (BK1 : forall a v, os <= a -> a + 8 <= os + 296 -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha Hb X. apply (proj1 (L5A.u64_at_vis (ahid Aw model) M1 a v ltac:(apply OAV; lia) ltac:(lia) ltac:(lia))). rewrite VIS1. exact X. }
  assert (AGO : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (a + n <= os + 256 \/ os + 264 <= a) -> (a + n <= os + 280 \/ os + 296 <= a) -> L5C.agree_on M M1 a n).
  { intros a n Ha Hn X Y i Hi. apply FR1; [lia| unfold P; lia]. }
  assert (AGSH : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n).
  { intros a n Ha Hn x Hx. unfold HeapIfaceA.S, HeapIfaceA.SB.
    assert (X8 : 0 <= x / 8 <= 17592186044416) by (split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
    apply FR1; [lia|]. unfold P. destruct OBIG; lia. }
  assert (BLKAP : forall q m, In (q, m) (PM.parser_own s ++ LBX) -> q + m <= os \/ os + 296 <= q).
  { intros q m Hq. destruct (PMBSKJ.blk_obj_apart L ar C HI HIok _ FF LK cr Aw M _ q m os 296 HH Hq AO) as [X|X]; [left| right]; lia. }
  pose proof (PMBSKJ.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  assert (AGB : forall q m, In (q, m) (PM.parser_own s ++ LBX) -> PMFA.agA M M1 q m).
  { intros q m Hq. destruct (BRB _ Hq) as (X0 & X1). cbn [fst snd] in X0, X1. destruct (BLKAP q m Hq) as [BF|BF]; (split; [apply AGO; lia| apply AGSH; lia]). }
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VS & VEC & _).
  pose proof VEC as (_ & _ & _ & Hk & _). pose proof (PM.pow2_pos (PM.p_k s) (proj1 Hk)) as P2.
  assert (VIN : In (PM.p_b s, 32 * 2 ^ PM.p_k s) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; right; left; reflexivity).
  destruct (BRB _ VIN) as (VB0 & VB1). cbn [fst snd] in VB0, VB1.
  assert (PA1 : PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M1 op ois s').
  { apply (PMBSKJ.parser_src_fieldsA M M1 op ois s (de + len) (rem - len) PA); [lia| lia| | | | lia| cbv [PM.CHUNK]; lia| | lia| lia| | | exact MGM1| | | | | lia| lia| cbv [PM.CHUNK]; lia].
    - split; [apply AGO; lia| apply AGSH; lia].
    - split; [apply AGO; lia| apply AGSH; lia].
    - apply AGSH; lia.
    - exact (AGB _ _ QIN).
    - exact (AGB _ _ VIN).
    - intros c0 n0 p0 E. apply AGB. apply in_or_app; left. unfold PM.parser_own. rewrite E. right; right; left; reflexivity.
    - apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| replace (op + 288) with (os + 264) by lia; exact F264].
    - apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| replace (op + 296) with (os + 272) by lia; exact F272].
    - replace (op + 304) with (os + 280) by lia. apply BK1; [lia| lia| exact C280].
    - replace (op + 312) with (os + 288) by lia. apply BK1; [lia| lia| exact C288]. }
  set (Wp := [(os + 256, 8); (os + 280, 16)]).
  assert (EK1 : L5SAR.ek L ar (PM.parser_own s ++ LBX) FF S 24576 Wp M M1).
  { apply (L5SAR.ek_piece L ar _ FF S 24576 Wp M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
    intros a Ha CA OWx Pa. unfold P in Pa. destruct Pa as [X|X]; [apply (OWx (os + 256, 8))| apply (OWx (os + 280, 16))]; try (unfold Wp; cbn; auto); unfold L5.in_rng; cbn [fst snd]; lia. }
  assert (WAPPp : PMKB.wapp Wp).
  { unfold Wp. apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct OBIG; [right| left]; lia|].
    apply PMKB.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct OBIG; [right| left]; lia| apply PMKB.wapp_nil]. }
  pose proof (PMBSKJ.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  assert (AOI : PMSPA.aobjA FF ois 272).
  { exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
  assert (IA1 : PM.iss_at RSEGS AD PMSPA.accA M1 ois str sm).
  { apply (PMKB.iss_keepA RSEGS AD L ar _ FF S 24576 Wp M M1 EK1 WAPPp FRB BRB _ _ _ AOI); [intros x Hx; apply in_or_app; right; apply INCS; exact Hx| | |exact IA].
    - intros i Hi r0 Hr. unfold Wp in Hr. unfold L5.in_rng. destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; lia.
    - intros c0 n0 p0 E i Hi r0 Hr. assert (Ip : In (p0, c0) (PM.parser_own s ++ LBX)) by (apply in_or_app; right; apply INCS; rewrite E; left; reflexivity).
      destruct (BLKAP _ _ Ip) as [X|X]; unfold Wp in Hr; unfold L5.in_rng; destruct Hr as [<-|[<-|[]]]; cbn [fst snd]; lia. }
  assert (EKn : L5SAR.ek L ar LBX FF S 24576 W0 M M1).
  { apply (L5SAR.ek_piece L ar LBX FF S 24576 W0 M M1 P); [intros a Ha N; apply FR1; [exact Ha| exact N]|].
    intros a Ha CA OWx Pa. apply (OWx (os + 256, 40)); [unfold PECRS1B.W0, PMSPA.W_srcf; left; reflexivity|].
    unfold L5.in_rng, P in *; cbn [fst snd] in *. unfold PMSPA.o_src, PMSPA.o_p in *. cbn [pa_off_p ADDR_B] in *. lia. }
  pose proof (PMBSKJ.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  destruct (WF _ Hfb) as (FF1 & FF2 & _). cbn [ff_addr ff_class fst snd] in FF1, FF2. change (ff_bytes 5) with 2048 in FF2. unfold FS_BYTES in FF2.
  assert (SO1 : st_ok M1 model1 s' sm cr LK Aw).
  { split; [split; [|split]|].
    - exact (L5SAR.ek_trans L ar LBX FF S 24576 W0 M0 M M1 EK EKn).
    - apply (L5SAR.dk_trans L ar LBX FF S 24576 M0 M M1 DK). apply L5SAR.dk_grows. exact MGM1.
    - exact (L5SAR.astk_grows ar M M1 S 24576 STK MGM1).
    - split; [repeat split; (apply (L5C.u64_at_agree RSEGS M M1); [apply AGO; lia| lia| lia| assumption])|].
      split; [exact PA1|]. split; [exact IA1|].
      split; [apply (PMBSKJ.base_keep L ar C LY LBX FF S 24576 W0 M M1 EKn); [intros a Ha; apply outside_W0; lia| exact BASE]|].
      split; [exact TBOK|]. split; [rewrite OWN'; exact HH1|]. split; [exact AM1|]. split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1]|].
      split; [exact ILK|]. split; [exact IAW|]. split; [exact CRL|]. split; [exact CRK|].
      destruct (FRB _ Hfb) as (Fb0 & Fb1). cbn [ff_addr ff_class fst snd] in Fb0, Fb1. change (ff_bytes 5) with 2048 in Fb1.
      split; [apply (PMFA.accA_agree M M1 op PECA.RDR_BYTES); [apply AGSH; unfold PECA.RDR_BYTES; clear - Eop Fb0 Fb1; lia| exact ACC]|].

      pose proof CT as (CSZ & CBS & CPOS & CBW & CST2). unfold PEC.pos_of, PM.unread in CPOS, CBW. fold qc de rem in CBW. fold rem in CPOS.
      pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KGE).
      unfold s'. unfold PEC.content_ok. cbn [PMSPA.with_src PM.p_src PM.sr_de PM.sr_rem PM.sr_qc].
      split; [exact CSZ|]. split.
      { exact (proj1 (proj2 (content_agree M M1 s sm cr LK Aw (vml_of model) (proj1 (AGB _ _ QIN)) (fun B m Hin => proj1 (AGB B m ltac:(apply in_or_app; right; exact Hin)))
                 ltac:(apply AGO; clear - Eois Eos Fb0 Fb1; lia) HH PA IA CT))). }
      unfold PEC.pos_of, PM.unread. cbn [PM.sr_de PM.sr_rem].
      split; [clear - CPOS Hl; lia|]. split; [| exact CST2].
      replace (blen pl - (rem - len + (PM.sm_eg sm - PM.sm_g sm))) with (blen pl - (rem + (PM.sm_eg sm - PM.sm_g sm)) + len) by (clear; lia).
      apply (PECSD.bytes_agree RSEGS M M1 (de + len) (rem - len)); [apply PECF.slice_length_le; clear - Hl; lia| clear - Q0 G1 Hl; unfold qc, de in *; lia| clear - Q4 G3 Hl SLO SR1; unfold qc, de, rem in *; lia| | ].
      { intros i Hi. apply (proj1 (AGB _ _ QIN)). clear - Hi G1 G3 Hl; unfold qc, de, rem in *; lia. }
      apply (PECSD.window_advance RSEGS M pl de _ len rem); [clear - CPOS; lia| clear - Hl; lia| clear - KGE CSZ; lia| exact CBW]. }
  apply (finish_rs fx1 R1 M1 model1 s' sm cr LK Aw de len); try assumption.
  - intros x Hx. rewrite (KS1 x) by (revert x Hx; intros x Hx; cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx.
  - lia.
  - lia.
  - right. left. exists qc, 16384. split; [rewrite OWN'; left; reflexivity| lia].
  - intros i Hi. apply MGM1. replace (de + i) with (qc + (de - qc + i)) by lia. apply DC. lia.
  - pose proof PA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC1 & _). destruct SRC1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CC1 & _).
    change (PM.sr_qc (PM.p_src s')) with qc in CC1. unfold PM.CHUNK in CC1. intros x Hx. apply CC1. lia.
  -
    destruct CT as (CSZ & CBS & CPOS & CBW & CST2). unfold PEC.pos_of, PM.unread in CPOS, CBW. fold qc de rem in CBW. fold rem in CPOS.
    pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KGE).
    unfold PEC.pos_of. rewrite <- U0. unfold PM.unread. fold rem.
    apply (PECSD.bytes_agree RSEGS M M1 de len); [apply PECF.slice_length_le; clear - Hl; lia| clear - Q0 G1; unfold qc, de in *; lia| clear - Q4 G3 Hl SLO SR1; unfold qc, de, rem in *; lia| | ].
    + intros i Hi. apply (proj1 (AGB _ _ QIN)). clear - Hi G1 G3 Hl; unfold qc, de, rem in *; lia.
    + apply (PECSD.window_head RSEGS M pl de _ len rem); [clear - CPOS; lia| clear - Hl; lia| exact CBW].
  - unfold PEC.pos_of. rewrite <- U0. unfold PM.unread. fold rem. pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & KGE). clear - Hl KGE; lia.
  - unfold PMSPA.consumed, s'. rewrite <- U0. unfold PM.unread. cbn [PMSPA.with_src PM.p_src PM.sr_rem PM.sr_qc PM.sr_de]. fold rem. clear; lia.
  - apply (src_step_trans _ _ _ _ _ _ STEP). unfold s', PMSPA.src_step, PM.unread. cbn [PMSPA.with_src PM.p_src PM.sr_qc PM.sr_rem].
    split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [intros X; exact X| lia].
Qed.

Lemma at_srd (fx : FPState) R M model s sm cr LK Aw :
  getr R (reg 1) = Z_to_bv 64 764116 ->
  getr R (reg 2) = Z_to_bv 64 (S - 80) -> getr R (reg 8) = Z_to_bv 64 len -> getr R (reg 9) = Z_to_bv 64 tb -> getr R (reg 18) = Z_to_bv 64 os ->
  getr R (reg 19) = Z_to_bv 64 (tb / 8 + 2147450880) -> getr R (reg 21) = Z_to_bv 64 2147450880 -> getr R (reg 22) = Z_to_bv 64 ((os + 288) / 8 + 2147450880) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 tb -> getr R (reg 12) = Z_to_bv 64 len -> 1 <= len ->
  st_ok M model s sm cr LK Aw -> fields_eq s -> PMSPA.src_step (PM.p_src s0) (PM.p_src s) sm0 sm -> PM.vs_size (PM.p_tb s) = 0 ->
  PM.unread (PM.p_src s) sm = PM.unread (PM.p_src s0) sm0 ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xbbca0 M model) K.
Proof using All.
  intros A1 A2 A8 A9 A18 A19 A21 A22 KP A10 A11 A12 Hl SO FE STEP SZ0 U0.
  pose proof SO as (_ & _ & PA & IA & _).
  assert (UN : 0 <= PM.unread (PM.p_src s) sm < 2 ^ 26).
  { pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _). destruct SRC as (_ & _ & _ & _ & _ & _ & _ & _ & G2 & _).
    pose proof (PMBSKJ.iss_size_ltA M ois str sm IA). destruct STEP as (_ & _ & _ & _ & U1). unfold PM.unread in *. lia. }
  apply (call_srd fx R M model s sm cr LK Aw 764116 [] A1 ltac:(split; [lia| reflexivity]) A2 KP A10 A11 A12 SO ltac:(lia) ltac:(lia) ltac:(rewrite SZ0; reflexivity) (PECSD.bytes_at_nil RSEGS M _)).
  intros fx2 R2 M2 model2 LK2 Aw2 s2 sm2 cr2 d RP2 Y10 Hd CONS2 SZ2 NMIN2 TBC2 G1 G2 G3 G4 G5 G6 STEP2 SO2. cbn [app] in TBC2.
  pose proof (vpack M2 model2 s2 sm2 cr2 LK2 Aw2 SO2) as (V0 & V1 & V2 & (SR1 & S16 & V3) & SVV & (O1 & O8 & OBIG) & OZ & OW & OAV & (T1 & T8 & TBIG) & TZ & TW & TAV & OSS & TBS & AO & AT).
  pose proof SO2 as ((EK2 & DK2 & STK2) & SV2 & PA2 & IA2 & BASE2 & TBOK2 & HH2 & AM2 & MRT2 & ILK2 & IAW2 & CRL2 & CRK2 & ACC2 & CT2).
  pose proof (PECRS1B.geo fb) as (Eop & Eos & Eois & Etb).
  assert (UN2 : 0 <= PM.unread (PM.p_src s2) sm2).
  { pose proof PA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _). destruct SRC as (_ & _ & _ & _ & _ & _ & _ & _ & G2' & _).
    pose proof (PMBSKJ.iss_size_ltA M2 ois str sm2 IA2). unfold PM.unread in *. lia. }
  assert (Hd2 : d < 2 ^ 26) by (unfold PMSPA.consumed in CONS2; lia).
  assert (FE2 : fields_eq s2) by (destruct FE as (F1 & F2 & F3 & F4 & F5 & F6); unfold PECRS1B.fields_eq; repeat split; congruence).
  assert (STEP02 : PMSPA.src_step (PM.p_src s0) (PM.p_src s2) sm0 sm2) by exact (src_step_trans _ _ _ _ _ _ STEP STEP2).
  pose proof SV2 as (Z8 & Z16 & Z24 & Z32 & Z40 & Z48 & Z56 & Z64 & Z72). bvr.
  pose proof PA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _).
  replace (op + 336) with tb in VS by lia.
  assert (B2 : getr R2 (reg 2) = Z_to_bv 64 (S - 80)) by (rewrite (L5SAR.cs_of_preserved R R2 2%nat RP2) by inl; exact A2).
  assert (B8 : getr R2 (reg 8) = Z_to_bv 64 len) by (rewrite (L5SAR.cs_of_preserved R R2 8%nat RP2) by inl; exact A8).
  assert (B9 : getr R2 (reg 9) = Z_to_bv 64 tb) by (rewrite (L5SAR.cs_of_preserved R R2 9%nat RP2) by inl; exact A9).
  assert (B18 : getr R2 (reg 18) = Z_to_bv 64 os) by (rewrite (L5SAR.cs_of_preserved R R2 18%nat RP2) by inl; exact A18).
  assert (B19 : getr R2 (reg 19) = Z_to_bv 64 (tb / 8 + 2147450880)) by (rewrite (L5SAR.cs_of_preserved R R2 19%nat RP2) by inl; exact A19).
  assert (B21 : getr R2 (reg 21) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R R2 21%nat RP2) by inl; exact A21).
  assert (B22 : getr R2 (reg 22) = Z_to_bv 64 ((os + 288) / 8 + 2147450880)) by (rewrite (L5SAR.cs_of_preserved R R2 22%nat RP2) by inl; exact A22).
  assert (KP2 : forall x, In x [3; 4; 24; 25; 26; 27]%nat -> getr R2 (reg x) = getr R0 (reg x)).
  { intros x Hx. rewrite (L5SAR.cs_of_preserved R R2 x RP2) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP. exact Hx. }
  set (MV2 := mrestrict (ahid Aw2 model2) M2) in *.
  revert VS SZ2. destruct (PM.p_tb s2) as [n1|c1 n1 q1] eqn:ETB; intros (VD & VC & VS) SZ2; cbn [PM.vs_size] in SZ2, SZ0.
  -
    destruct VS as (Hn1 & BY0). pose proof (PMF.even_byte n1) as EV.
    pose proof (PMBRSPP.arpES_conc fx2 R2 MV2 (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => 2 * n1
         | 44%nat => U 1 | 45%nat => U 8 | 46%nat => U 9 | 47%nat => U 18 | 48%nat => U 19 | 49%nat => U 20 | 50%nat => U 21 | 51%nat => U 22 | 52%nat => U 23
         | _ => 0 end)) as PP.
    cbn beta iota in PP.
    L5SAR.feed PP ltac:(first [assumption | lazymatch goal with
        | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
        | |- L5.u8_at _ _ tb _ => unfold MV2; vis8 TAV
        | |- PMBRSPP.aligned _ _ => unfold PMBRSPP.aligned; lia
        | |- _ => lia end]).
    destruct PP as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23).
    unfold PMSPA.cfg.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK2 cr2 Aw2 M2 model2 fx2 fx3 R2 0xba8d4 R3 0xba950 M3v K HH2 AM2 MS3 MG3 FRZ3).
    intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
    assert (E3 : M3 = M2) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
    assert (SO3 : st_ok M2 model3 s2 sm2 cr2 LK2 Aw2).
    { split; [exact (conj EK2 (conj DK2 STK2))|]. split; [exact SV2|]. split; [exact PA2|]. split; [exact IA2|]. split; [exact BASE2|].
      split; [first [exact TBOK2| rewrite ETB; exact TBOK2]|]. split; [exact HH3|]. split; [exact AM3|]. split; [eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]|].
      split; [exact ILK2|]. split; [exact IAW2|]. split; [first [exact CRL2| rewrite ETB; exact CRL2]|]. split; [first [exact CRK2| rewrite ETB; exact CRK2]|].
      split; [exact ACC2| first [exact CT2| rewrite ETB; exact CT2]]. }
    replace (2 * n1 / 2) with n1 in E11 by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
    apply (finish_rs fx3 R3 M2 model3 s2 sm2 cr2 LK2 Aw2 (tb + 1) n1); try assumption.
    + intros x Hx. rewrite (KS3 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP2. exact Hx.
    + lia. + lia.
    + right. right. lia.
    + apply (L5.defined_sub M2 tb 24 (tb + 1) n1 VD); lia.
    + intros x Hx. apply VC. lia.
    +
      try rewrite ETB in TBC2. cbn [PM.vs_data] in TBC2. unfold PEC.pos_of in TBC2 |- *. rewrite U0 in TBC2.
      replace n1 with d by (clear - SZ2 SZ0; lia). exact TBC2.
    + unfold PEC.pos_of. rewrite <- U0. clear - NMIN2 SZ2 SZ0 UN; lia.
    + unfold PMSPA.consumed in CONS2 |- *. rewrite <- U0. clear - CONS2 SZ2 SZ0 UN; lia.
  -
    destruct VS as (W0' & W8 & W16 & Hn1 & Hc1 & Hce & DQ & CQ).
    pose proof (PMF.u8_of_u64 RSEGS M2 tb (c1 + 1) ltac:(lia) W0') as BY0. pose proof (PMF.odd_byte c1 Hce ltac:(lia)) as ODB.
    assert (H39 : 0 <= (c1 + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c1 + 1) 256 ltac:(lia)); lia).
    pose proof (PMBRSPP.arpEL_conc fx2 R2 MV2 (fun j => match j with 2%nat => S | 36%nat => os | 37%nat => tb | 38%nat => len | 39%nat => (c1 + 1) mod 256
         | 40%nat => n1 | 41%nat => q1
         | 44%nat => U 1 | 45%nat => U 8 | 46%nat => U 9 | 47%nat => U 18 | 48%nat => U 19 | 49%nat => U 20 | 50%nat => U 21 | 51%nat => U 22 | 52%nat => U 23
         | _ => 0 end)) as PP.
    cbn beta iota in PP.
    assert (Hq1 : 0 <= q1 < 2 ^ 64 /\ 0 <= n1 < 2 ^ 64).
    { pose proof (PMBSKJ.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH2 (q1, c1)) as X. cbn [fst snd] in X.
      destruct X as (X0 & X1); [apply in_or_app; left; unfold PM.parser_own; rewrite ETB; right; right; left; reflexivity|]. lia. }
    L5SAR.feed PP ltac:(first [assumption | lazymatch goal with
        | |- L5.u64_at _ _ (S - _) _ => apply SVV; [lia| assumption]
        | |- L5.u8_at _ _ tb _ => unfold MV2; vis8 TAV
        | |- L5.u64_at _ _ (tb + _) _ => unfold MV2; vis64 TAV
        | |- PMBRSPP.aligned _ _ => unfold PMBRSPP.aligned; lia
        | |- _ => lia end]).
    destruct PP as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23).
    unfold PMSPA.cfg.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK2 cr2 Aw2 M2 model2 fx2 fx3 R2 0xba8d4 R3 0xba950 M3v K HH2 AM2 MS3 MG3 FRZ3).
    intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
    assert (E3 : M3 = M2) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
    assert (SO3 : st_ok M2 model3 s2 sm2 cr2 LK2 Aw2).
    { split; [exact (conj EK2 (conj DK2 STK2))|]. split; [exact SV2|]. split; [exact PA2|]. split; [exact IA2|]. split; [exact BASE2|].
      split; [first [exact TBOK2| rewrite ETB; exact TBOK2]|]. split; [exact HH3|]. split; [exact AM3|]. split; [eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]|].
      split; [exact ILK2|]. split; [exact IAW2|]. split; [first [exact CRL2| rewrite ETB; exact CRL2]|]. split; [first [exact CRK2| rewrite ETB; exact CRK2]|].
      split; [exact ACC2| first [exact CT2| rewrite ETB; exact CT2]]. }
    apply (finish_rs fx3 R3 M2 model3 s2 sm2 cr2 LK2 Aw2 q1 n1); try assumption.
    + intros x Hx. rewrite (KS3 x) by (cbn in Hx; repeat (destruct Hx as [<-|Hx]; [inl|]); destruct Hx). apply KP2. exact Hx.
    + lia. + lia.
    + right. left. exists q1, c1. split; [unfold PM.parser_own; rewrite ETB; cbn; right; right; left; reflexivity| lia].
    + apply (L5.defined_sub M2 q1 c1 q1 n1 DQ); lia.
    + intros x Hx. apply CQ. lia.
    +
      try rewrite ETB in TBC2. cbn [PM.vs_data] in TBC2. unfold PEC.pos_of in TBC2 |- *. rewrite U0 in TBC2.
      replace n1 with d by (clear - SZ2 SZ0; lia). exact TBC2.
    + unfold PEC.pos_of. rewrite <- U0. clear - NMIN2 SZ2 SZ0 UN; lia.
    + unfold PMSPA.consumed in CONS2 |- *. rewrite <- U0. clear - CONS2 SZ2 SZ0 UN; lia.
Qed.

End Call.
End WithHeap.
End PECRS2B.
