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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeCModelA PeCSpecsA PeCSpecsAb PmModelFactsA PeStepAB0 PmStep PmTxtKit2 PeBSrcKitJ PeBCReset1 PeBRsKit PmSpecs PeCSink PeCModel PeCSpecs PeCFrame PeCSrcD PeCTxtSpecsA PeBRdSpanP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_ba900_ba904.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECRS1B.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Lemma pst_eta (s : PM.pst) :
  PM.PST (PM.p_more s) (PM.p_done s) (PM.p_depth s) (PM.p_src s) (PM.p_tb s) (PM.p_tg s) (PM.p_b s) (PM.p_k s) (PM.p_stk s) = s.
Proof. destruct s; reflexivity. Qed.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation pot := (fun L ar (s : PM.pst) => PMSPA.scA L (PM.pot_text (PMSPA.HV L ar) (PM.p_tb s) (PM.p_tg s))).

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

Definition op : Z := PMSPA.o_p AD fb.
Definition os : Z := PMSPA.o_src AD fb.
Definition ois : Z := PMSPA.o_is AD fb.
Definition tb : Z := PMSPA.o_tb AD fb.
Definition W0 : list L5.range := PMSPA.W_srcf AD fb ++ [(PMSPA.o_tb AD fb, 24)].
Definition U (x : nat) : Z := bv_unsigned (getr R0 (reg x)).

Definition saves9 (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (U 1) /\ L5.u64_at RSEGS M (S - 16) (U 8) /\ L5.u64_at RSEGS M (S - 24) (U 9) /\ L5.u64_at RSEGS M (S - 32) (U 18)
  /\ L5.u64_at RSEGS M (S - 40) (U 19) /\ L5.u64_at RSEGS M (S - 48) (U 20) /\ L5.u64_at RSEGS M (S - 56) (U 21) /\ L5.u64_at RSEGS M (S - 64) (U 22)
  /\ L5.u64_at RSEGS M (S - 72) (U 23).
Definition kept_rs (R : bvmap 5 word) : Prop := forall x, In x [3; 4; 24; 25; 26; 27]%nat -> getr R (reg x) = getr R0 (reg x).
Definition memrel (M : word -> option byte) : Prop :=
  L5SAR.ek L ar LBX FF S 24576 W0 M0 M /\ L5SAR.dk L ar LBX FF S 24576 M0 M /\ L5CA.astk ar M S 24576.
Definition fields_eq (s : PM.pst) : Prop :=
  PM.p_more s = PM.p_more s0 /\ PM.p_done s = PM.p_done s0 /\ PM.p_depth s = PM.p_depth s0 /\ PM.p_b s = PM.p_b s0 /\ PM.p_k s = PM.p_k s0 /\ PM.p_stk s = PM.p_stk s0.
Definition st_ok (M : word -> option byte) (model : Model) (s : PM.pst) (sm : PM.strm) (cr : credit) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
  memrel M /\ saves9 M /\ PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M op ois s /\ PM.iss_at RSEGS AD PMSPA.accA M ois str sm
  /\ PMSTA.base_okA RSEGS AD M /\ PM.tb_ok (PM.p_tb s) (PM.p_tg s)
  /\ ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M (vml_of model) /\ L5CA.amodel_ok Aw model /\ model_rt model0 model
  /\ incl LK LK0 /\ incl Aw0 Aw
  /\ PMSPA.credit_le (pot L ar s) cr /\ PMSPA.credit_keep cr0 cr (pot L ar s0) (pot L ar s)
  /\ PMSPA.accA M op PECA.RDR_BYTES
  /\ PEC.content_ok RSEGS AD M fb pl (PM.p_src s) str sm.

Definition bregs (R : bvmap 5 word) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 80) /\ getr R (reg 8) = Z_to_bv 64 len /\ getr R (reg 9) = Z_to_bv 64 tb
  /\ getr R (reg 18) = Z_to_bv 64 os /\ getr R (reg 19) = Z_to_bv 64 (os + 288) /\ getr R (reg 21) = Z_to_bv 64 2147450880
  /\ getr R (reg 22) = Z_to_bv 64 ((os + 288) / 8 + 2147450880) /\ kept_rs R.

Lemma geo : op = fb + 592 /\ os = fb + 616 /\ ois = fb + 96 /\ tb = fb + 592 + 336.
Proof. clear. unfold op, os, ois, tb, PMSPA.o_src, PMSPA.o_tb, PMSPA.o_p, PMSPA.o_is. cbn [pa_off_p pa_off_is AD PeCLayoutB.CADDR_B]. repeat split; lia. Qed.
Lemma fbb : fb mod 1024 = 0 /\ exists rs, In (fb, 5, rs) FF.
Proof. clear - FOK. destruct FOK as (X & Y). split; [| exact X]. apply Z.mod_divide in Y; [| clear; lia]. destruct Y as [k ->]. replace (k * 2048) with ((k * 2) * 1024) by (clear; lia). apply Z_mod_mult. Qed.

Lemma inW_W0 a : (exists r0, In r0 W0 /\ L5.in_rng r0 a) -> fb + 96 + 40 <= a < fb + 592 + 360.
Proof using All.
  intros (r0 & Hin & Hr). unfold W0, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_tb, PMSPA.o_is, PMSPA.o_p in Hin.
  cbn [pa_off_p pa_off_is AD PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B app] in Hin. unfold L5.in_rng in Hr.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; lia.
Qed.
Lemma outside_W0 a : (a < fb + 136 \/ fb + 592 + 360 <= a) -> L5.outside W0 a.
Proof using All. intros Ha r0 Hr0 Hin. assert (I : exists r1, In r1 W0 /\ L5.in_rng r1 a) by (exists r0; split; assumption). apply inW_W0 in I. lia. Qed.
Lemma wapp_W0 : (fb + 2048 <= 2147446784 \/ 17594333495296 <= fb) -> PMKB.wapp W0.
Proof using All.
  intros X r0 Hr. unfold W0, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_tb, PMSPA.o_is, PMSPA.o_p in Hr. cbn [pa_off_p pa_off_is AD PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B app] in Hr.
  unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; destruct X; [left|right|left|right|left|right|left|right]; lia.
Qed.

Lemma finish_rs (fx : FPState) R M model s sm cr LK Aw (ptr n : Z) :
  getr R (reg 1) = Z_to_bv 64 (U 1) -> getr R (reg 2) = Z_to_bv 64 S ->
  getr R (reg 8) = Z_to_bv 64 (U 8) -> getr R (reg 9) = Z_to_bv 64 (U 9) -> getr R (reg 18) = Z_to_bv 64 (U 18) ->
  getr R (reg 19) = Z_to_bv 64 (U 19) -> getr R (reg 20) = Z_to_bv 64 (U 20) -> getr R (reg 21) = Z_to_bv 64 (U 21) ->
  getr R (reg 22) = Z_to_bv 64 (U 22) -> getr R (reg 23) = Z_to_bv 64 (U 23) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 ptr -> getr R (reg 11) = Z_to_bv 64 n -> 0 <= n <= len -> n < 2 ^ 26 ->
  ((ptr = 0 /\ n = 0) \/ (exists B m, In (B, m) (PM.parser_own s) /\ B <= ptr /\ ptr + n <= B + m) \/ (tb + 1 <= ptr /\ ptr + n <= tb + 24)) ->
  L5.defined M ptr n -> PMSPA.accA M ptr n ->
  L5.bytes_at RSEGS M ptr (UbjRef.slice pl (PEC.pos_of pl (PM.p_src s0) sm0) n) -> n = Z.min len (blen pl - PEC.pos_of pl (PM.p_src s0) sm0) ->
  PMSPA.consumed (PM.p_src s0) (PM.p_src s) sm0 sm = n ->
  st_ok M model s sm cr LK Aw -> fields_eq s -> PMSPA.src_step (PM.p_src s0) (PM.p_src s) sm0 sm ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xba950 M model) K.
Proof using All.
  intros E1 E2 E8 E9 E18 E19 E20 E21 E22 E23 KP E10 E11 Hn Hn2 LOC DEF ACCp BYT NMIN CONSN ((EK & DK & STK) & _ & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK & ACC & CT)
         (F1 & F2 & F3 & F4 & F5 & F6) STEP.
  pose proof RAok as (Hr1 & Hr2).
  assert (RA : getr R (reg 1) = Z_to_bv 64 r) by (rewrite E1; unfold U; rewrite Z_to_bv_bv_unsigned; exact Rra0).
  unfold PMSPA.cfg.
  apply (PMBSKJ.ret_exit L ar C HI LY HIok fx R M model K _ FF LK cr Aw 0xba950 r W_ba900 HH AM F_ba900 eq_refl D_ba900 RA ltac:(lia) Hr2).
  intros model1 MRT1 AM1 HH1.
  apply (KONT fx R M model1 LK Aw s sm cr ptr n); try assumption.
  - apply L5SAR.preserved_by_index. intros x Hx. unfold L5SAR.cs_all in Hx. cbn in Hx.
    destruct Hx as [<-|Hx]; [rewrite E2, Rsp0; reflexivity|].
    destruct Hx as [<-|Hx]; [apply KP; cbn; auto|]. destruct Hx as [<-|Hx]; [apply KP; cbn; auto|].
    destruct Hx as [<-|Hx]; [rewrite E8; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E9; apply Z_to_bv_bv_unsigned|].
    destruct Hx as [<-|Hx]; [rewrite E18; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E19; apply Z_to_bv_bv_unsigned|].
    destruct Hx as [<-|Hx]; [rewrite E20; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E21; apply Z_to_bv_bv_unsigned|].
    destruct Hx as [<-|Hx]; [rewrite E22; apply Z_to_bv_bv_unsigned|]. destruct Hx as [<-|Hx]; [rewrite E23; apply Z_to_bv_bv_unsigned|].
    apply KP. destruct Hx as [<-|[<-|[<-|[<-|[]]]]]; cbn; auto 12.
  - change (PMSPA.pm_scr 6) with 24576. apply (L5SAR.ahpres_of L ar LBX FF S 24576 _ M0 M EK); [destruct STK as (_ & _ & _ & _ & D & _); exact D| exact DK].
  - eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1].
Qed.

Lemma content_agree M M' s sm cr LK Aw V :
  L5C.agree_on M M' (PM.sr_qc (PM.p_src s)) PM.CHUNK -> (forall B m, In (B, m) LBX -> L5C.agree_on M M' B m) -> L5C.agree_on M M' (ois + 80) 24 ->
  ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M V ->
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M op ois s -> PM.iss_at RSEGS AD PMSPA.accA M ois str sm ->
  PEC.content_ok RSEGS AD M fb pl (PM.p_src s) str sm -> PEC.content_ok RSEGS AD M' fb pl (PM.p_src s) str sm.
Proof using All.
  intros AGQ AGX AGS HH PA IA CT.
  pose proof (PMBSKJ.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMBSKJ.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof fbb as (F1024 & rs & Hfb). pose proof geo as (Eop & Eos & Eois & Etb).
  destruct (FRB _ Hfb) as (Fb0 & Fb1). cbn [ff_addr ff_class fst snd] in Fb0, Fb1. change (ff_bytes 5) with 2048 in Fb1.
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _) & _).
  pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _). destruct VS as (_ & _ & VSF).
  assert (QIN : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  destruct (BRB _ QIN) as (Q0 & Q4). cbn [fst snd] in Q0, Q4.
  apply (PECF.content_ok_agree RSEGS AD M M' fb pl (PM.p_src s) str sm); unfold PMSP.o_is; cbn [pa_off_is PeCLayoutB.CADDR_B];
    [clear - Fb0; lia| clear - Fb1; lia| rewrite Eois in AGS; exact AGS| | clear - Q0; lia| clear - Q4; unfold PM.CHUNK in *; lia| exact G1| exact G2| exact G3| exact AGQ| | exact CT].
  - intros c n q E. subst str. cbn in VSF. destruct VSF as (_ & _ & _ & Hn & _).
    assert (SIN : In (q, c) (PM.parser_own s ++ LBX)) by (apply in_or_app; right; apply INCS; left; reflexivity).
    destruct (BRB _ SIN) as (B0 & B4). cbn [fst snd] in B0, B4. split; [clear - B0; lia|]. split; [clear - B4; lia|]. split; [clear - Hn; lia| exact (AGX _ _ (INCS _ (or_introl eq_refl)))].
  - intros n E. subst str. cbn in VSF. clear - VSF; lia.
Qed.

Lemma content_step M M' s sm cr LK Aw V (sp' scr' : Z) (W' : list L5.range) (src' : PM.srcst) (sm' : PM.strm) :
  ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M V -> PM.iss_at RSEGS AD PMSPA.accA M ois str sm ->
  L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF sp' scr' W' M M' -> PMKB.wapp W' ->
  (forall i, ois + 80 <= i < ois + 80 + 24 -> L5.outside W' i) ->
  (forall c n q, str = PM.VLong c n q -> forall i, q <= i < q + c -> L5.outside W' i) ->
  0 <= PEC.pos_of pl src' sm' -> L5.bytes_at RSEGS M' (PM.sr_de src') (UbjRef.slice pl (PEC.pos_of pl src' sm') (PM.sr_rem src')) ->
  (PM.sm_st sm' = 2 -> PM.sm_g sm' = PM.sm_eg sm') ->
  PEC.content_ok RSEGS AD M fb pl (PM.p_src s) str sm -> PEC.content_ok RSEGS AD M' fb pl src' str sm'.
Proof using All.
  intros HH IA HP WAPP OUTS OUTL POS' BC' ST2' CT.
  pose proof (PMBSKJ.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMBSKJ.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof fbb as (F1024 & rs & Hfb). pose proof geo as (Eop & Eos & Eois & Etb).
  destruct (FRB _ Hfb) as (Fb0 & Fb1). cbn [ff_addr ff_class fst snd] in Fb0, Fb1. change (ff_bytes 5) with 2048 in Fb1.
  pose proof HP as (EKr & _).
  pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _). destruct VS as (_ & _ & VSF).
  assert (AOS : PMSPA.aobjA FF (ois + 80) 24) by (apply (PMBSKJ.aobj_fb FF fb); [exact FOK| clear - Eois; lia| clear - Eois; lia]).
  apply (PECF.content_ok_step RSEGS AD M M' fb pl (PM.p_src s) str sm src' sm'); unfold PMSP.o_is; cbn [pa_off_is PeCLayoutB.CADDR_B];
    [clear - Fb0; lia| clear - Fb1; lia| | | | exact POS'| exact BC'| exact ST2'| exact CT].
  - rewrite <- Eois. exact (proj1 (PMKB.agA_obj L ar _ FF sp' scr' W' M M' EKr WAPP FRB (ois + 80) 24 AOS OUTS)).
  - intros c1 n1 q1 E. rewrite E in VSF. cbn in VSF. destruct VSF as (_ & _ & _ & Hn1 & _).
    assert (SIN : In (q1, c1) (PM.parser_own s ++ LBX)) by (apply in_or_app; right; apply INCS; rewrite E; left; reflexivity).
    destruct (BRB _ SIN) as (B0 & B4). cbn [fst snd] in B0, B4.
    split; [clear - B0; lia|]. split; [clear - B4; lia|]. split; [clear - Hn1; lia|].
    exact (proj1 (PMKB.agA_blk L ar _ FF sp' scr' W' M M' EKr WAPP BRB q1 c1 SIN (OUTL c1 n1 q1 E))).
  - intros n E. rewrite E in VSF. cbn in VSF. clear - VSF; lia.
Qed.

Lemma wapp_wsrc M s cr LK Aw V : ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M V -> PMKB.wapp (PMSPA.W_src AD fb (PM.p_src s)).
Proof using All.
  intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & _).
  pose proof fbb as (F1024 & rs & Hfb).
  destruct (WF _ Hfb) as (FF1 & FF2 & _). cbn [ff_addr ff_class fst snd] in FF1, FF2. change (ff_bytes 5) with 2048 in FF2.
  unfold app_mem, FS_BYTES in FSAPP, FF1, FF2.
  assert (WAPP0 : PMKB.wapp W0) by (apply wapp_W0; destruct FSAPP as (_ & [Y|Y] & _); unfold BIGSHADOW_LO, BIGSHADOW_HI in Y; [left|right]; lia).
  assert (QIN : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  destruct (WB _ QIN) as ((_ & _ & _ & _ & _ & (_ & QAPP & _)) & _). cbn [fst snd] in QAPP.
  unfold PMSPA.W_src. apply PMKB.wapp_app.
  - intros r0 Hr0. apply WAPP0. unfold W0. apply in_or_app. left. exact Hr0.
  - apply PMKB.wapp_cons; [cbn [fst snd]; exact QAPP| apply PMKB.wapp_nil].
Qed.
Lemma wsrc_outside M s cr LK Aw V : ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M V ->
  (forall i, ois + 80 <= i < ois + 80 + 24 -> L5.outside (PMSPA.W_src AD fb (PM.p_src s)) i)
  /\ (forall c n q, str = PM.VLong c n q -> forall i, q <= i < q + c -> L5.outside (PMSPA.W_src AD fb (PM.p_src s)) i).
Proof using All.
  intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  pose proof fbb as (F1024 & rs & Hfb). pose proof geo as (Eop & Eos & Eois & Etb).
  assert (QIN : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  assert (QAP : PM.sr_qc (PM.p_src s) + PM.CHUNK <= fb \/ fb + 2048 <= PM.sr_qc (PM.p_src s)).
  { destruct (WB _ QIN) as (_ & _ & _ & _ & _ & FA & _). cbn [fst snd] in FA.
    destruct (FA (fb, 5, rs) (in_or_app _ _ _ (or_introl Hfb))) as [X0|X0]; cbn [ff_addr ff_class fst snd] in X0; change (ff_bytes 5) with 2048 in X0; [left|right]; lia. }
  split.
  - intros i Hi r0 Hr0 Hin. unfold PMSPA.W_src, PMSPA.W_srcf in Hr0. fold os ois in Hr0. cbn [app] in Hr0. unfold L5.in_rng in Hin.
    destruct Hr0 as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin; [clear - Hi Hin Eos Eois; lia| clear - Hi Hin; lia| clear - Hi Hin; lia| clear - Hi Hin QAP Eois; unfold PM.CHUNK in *; lia].
  - intros c1 n1 q1 E i Hi r0 Hr0 Hin. assert (SIN : In (q1, c1) (PM.parser_own s ++ LBX)) by (apply in_or_app; right; apply INCS; rewrite E; left; reflexivity).
    unfold PMSPA.W_src, PMSPA.W_srcf in Hr0. fold os ois in Hr0. cbn [app] in Hr0. unfold L5.in_rng in Hin.
    destruct (WB _ SIN) as (_ & _ & _ & _ & _ & FA & _). cbn [fst snd] in FA.
    destruct (FA (fb, 5, rs) (in_or_app _ _ _ (or_introl Hfb))) as [X0|X0]; cbn [ff_addr ff_class fst snd] in X0; change (ff_bytes 5) with 2048 in X0;
      (destruct Hr0 as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin; [clear - Hi Hin X0 Eos Eois; lia| clear - Hi Hin X0 Eois; lia| clear - Hi Hin X0 Eois; lia|]);
      (assert (NE : q1 <> PM.sr_qc (PM.p_src s)) by
        (intros EQ; apply (PMBSKJ.fst_neq_appA (PM.parser_own s) LBX (PM.sr_qc (PM.p_src s)) PM.CHUNK q1 c1 (PMBSKJ.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH)); [left; reflexivity| apply INCS; rewrite E; left; reflexivity| symmetry; exact EQ]);
       destruct (PMBSKJ.blk_apart L ar C HI HIok _ _ _ _ _ _ _ _ _ _ _ HH SIN QIN NE) as [Zb|Zb]; clear - Hi Hin Zb; lia).
Qed.

Lemma callee_mem M M' (BX : list (Z * Z)) scr' (W' : list L5.range) :
  memrel M -> saves9 M -> 0 <= scr' -> 80 + scr' <= 24576 -> ar_stack_top ar <= 2 ^ 47 ->
  L5CA.ahpres L ar (BX ++ LBX) FF (S - 80) scr' W' M M' ->
  (forall a, aclient L ar LBX FF S 24576 a -> L5.outside W0 a -> L5.outside W' a) -> (forall a, S - 80 <= a < S -> L5.outside W' a) ->
  memrel M' /\ saves9 M' /\ L5SAR.ek L ar LBX FF S 24576 W0 M M'.
Proof using All.
  intros (EK & DK & STK) SV Hs Hs2 TOP HP HW HWS.
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  assert (EKn : L5SAR.ek L ar LBX FF S 24576 W0 M M').
  { apply (L5SAR.ek_callee L ar LBX BX FF [] S 24576 (S - 80) scr' W0 W' M M' HP); [lia|lia| exact HW]. }
  assert (DKn : L5SAR.dk L ar LBX FF S 24576 M M') by (apply (L5SAR.dk_callee L ar LBX BX FF [] S 24576 (S - 80) scr' W' M M' HP); lia).
  assert (KEEPS : forall k v, 8 <= k <= 80 -> L5.u64_at RSEGS M (S - k) v -> L5.u64_at RSEGS M' (S - k) v).
  { intros k v Hk X. apply (L5C.u64_at_agree RSEGS M M'); [|lia|lia|exact X].
    intros i Hi. destruct HP as (P & _). apply P. split; [lia|]. split.
    - apply (L5SAR.stack_client L ar (BX ++ LBX) FF (S - 80) scr' i); lia.
    - apply HWS. lia. }
  split; [split; [|split]|].
  - exact (L5SAR.ek_trans L ar LBX FF S 24576 W0 M0 M M' EK EKn).
  - exact (L5SAR.dk_trans L ar LBX FF S 24576 M0 M M' DK DKn).
  - apply (PMKB.astk_after_ahpres L ar _ FF M M' S 24576 (S - 80) scr' W' STK HP); lia.
  - split; [|exact EKn]. destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72).
    repeat split; (apply KEEPS; [lia| assumption]).
Qed.

Lemma call_fill (fx : FPState) R M model s sm cr LK Aw (X : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 80) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 (PM.sr_qc (PM.p_src s)) -> getr R (reg 12) = Z_to_bv 64 PM.CHUNK ->
  st_ok M model s sm cr LK Aw -> PM.sr_rem (PM.p_src s) = 0 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (sm' : PM.strm) (c : Z),
     regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 c -> 0 <= c <= PM.CHUNK -> PM.sm_g sm' = PM.sm_g sm + c ->
     (c < PM.CHUNK -> PM.sm_g sm' = PM.sm_eg sm /\ PM.sm_st sm' = 2) -> (PM.sm_st sm = 2 -> c = 0) ->
     PMSPA.src_step (PM.p_src s) (PM.p_src s) sm sm' ->
     L5.bytes_at RSEGS M' (PM.sr_qc (PM.p_src s)) (UbjRef.slice pl (blen pl - (PM.sm_eg sm - PM.sm_g sm)) c) ->
     (PM.sm_st sm' = 2 -> PM.sm_g sm' = PM.sm_eg sm') ->
     st_ok M' model' s sm' cr LK' Aw' ->
     srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' X M' model') K) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb9944 M model) K.
Proof using All.
  intros A1 RAX A2 KP A10 A11 A12 SO RZ NEXT.
  pose proof SO as (MR & SV & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK & ACC & CT).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
  pose proof fbb as (F1024 & rs & Hfb). pose proof geo as (Eop & Eos & Eois & Etb).
  destruct (WF _ Hfb) as (FF1 & FF2 & _). cbn [ff_addr ff_class fst snd] in FF1, FF2. change (ff_bytes 5) with 2048 in FF2.
  unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FF1, FF2.
  pose proof (PMBSKJ.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMBSKJ.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  assert (QIN0 : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  destruct (BRB _ QIN0) as (QB0 & QB1). cbn [fst snd] in QB0, QB1.
  assert (STKr : L5CA.astk ar M (S - 80) 18432).
  { apply (L5SAR.astk_sub ar M M S 24576 80 18432 STK (fun _ Y => Y)); [lia|lia|lia|]. replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  assert (WAPP0 : PMKB.wapp W0) by (apply wapp_W0; destruct FSAPP as (_ & [Y|Y] & _); unfold BIGSHADOW_LO, BIGSHADOW_HI in Y; [left|right]; lia).
  assert (STKSH : shadow_zero M (S - 80 - 18432) (18432 / 8)).
  { change (18432 / 8) with 2304.
    assert (M8a : (S - 24576) mod 8 = 0) by (apply PMKB.mod16_8'; replace (S - 24576) with (S + (-1536) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
    assert (M8b : (S - 80 - 18432) mod 8 = 0) by (apply PMKB.mod16_8'; replace (S - 80 - 18432) with (S + (-1157) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
    apply (PMKB.shadow_zero_sub M (S - 24576) 3072); [exact M8a| exact M8b| lia| lia| lia|].
    apply (PMKB.stksh_keepA L ar LBX FF S 24576 W0 M0 M EK WAPP0 (S - 24576) 3072); [lia|lia|lia| exact M8a| lia| exact STKSH0]. }
  assert (FRM : PMSPA.ffroomA 3 FF LK) by (apply (PMBRSK.ffroom_incl 6 3 FF LK0 LK FRM0 ILK NDF); lia).
  pose proof FBS as SR. unfold PECSB.fill_buffer_spec, PECSPA.fill_buffer_spec, PECSPA.csrc_spec in SR. cbn [pa_fill_buffer AD PeCLayoutB.CADDR_B] in SR.
  apply (SR fx R M model K LBX FF LK Aw cr (S - 80) X fb pl s str sm [] HH AM K0).
  { unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
    split; [rewrite (KP 3%nat) by (cbn; auto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; auto); exact Rtp0|].
    change (PMSPA.pm_scr 3) with 18432. split; [exact STKr| exact STKSH]. }
  { exact FRM. }
  { intros f Hf. specialize (FRS f Hf). lia. }
  { exact FOK. }
  { clear - A16. replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  { rewrite L5K.rl10. exact A10. }
  { unfold PECSPA.fill_args. rewrite L5K.rl10, L5SAR.r11, L5SAR.r12. split; [exact A12|]. exists os, (PM.sr_qc (PM.p_src s)).
    pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & Q264 & _) & _).
    split; [exact A10|]. split; [clear - Eos FF1 FF2 FSAPP; lia|]. split; [exact A11|]. split; [clear - QB0 QB1; unfold PM.CHUNK in *; lia|].
    replace (os + 264) with (op + 24 + 264) by (clear - Eos Eop; lia). exact Q264. }
  { reflexivity. }
  { exact PA. } { exact IA. } { exact BASE. } { exact ACC. } { exact INCS. } { exact POK. } { exact CT. }
  intros fx' R' M' model' LK' Aw' src' sm' RP PA' IA' STEP RES HP MRT' ILK' IAW' AM' HH'.
  change (PMSPA.pm_scr 3) with 18432 in HP. rewrite app_nil_r in HP.
  destruct RES as (-> & c & Y10 & Hc & G & RSC & RS2 & CHK & ST2').
  rewrite pst_eta in PA'.
  apply (NEXT fx' R' M' model' LK' Aw' sm' c RP Y10 Hc G RSC RS2 STEP CHK ST2').
  destruct (callee_mem M M' (PM.parser_own s) 18432 (PMSPA.W_src AD fb (PM.p_src s)) MR SV ltac:(lia) ltac:(lia) TOP HP) as (MR' & SV' & EKn).
  { intros a CA OW r0 Hr0 Hin. unfold PMSPA.W_src in Hr0. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
    - apply (OW r0); [unfold W0; apply in_or_app; left; exact Hr0| exact Hin].
    -
      apply (PMBRS1.own_not_aclient L ar C HI HIok (PM.parser_own s) LBX FF LK cr Aw M _ (PM.sr_qc (PM.p_src s)) PM.CHUNK a S 24576 HH); [left; reflexivity| unfold L5.in_rng in Hin; cbn [fst snd] in Hin; exact Hin| exact CA]. }
  { intros a Ha r0 Hr0 Hin. unfold PMSPA.W_src, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in Hr0. cbn [pa_off_p pa_off_is AD PMB.AD PeLayoutA.ADDR_B PeCLayoutB.CADDR_B app] in Hr0.
    unfold L5.in_rng in Hin. destruct Hr0 as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin; [lia|lia|lia|].
    assert (QIN : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
    destruct (WB _ QIN) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4. unfold PM.CHUNK in *. lia. }
  split; [exact MR'|]. split; [exact SV'|]. split; [exact PA'|]. split; [exact IA'|].
  split.
  { apply (PMBSKJ.base_keep L ar C LY LBX FF S 24576 W0 M M' EKn); [| exact BASE].
    intros a Ha. apply outside_W0. pose proof (PMBSKJ.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI. lia. }
  split; [exact TBOK|]. split; [exact HH'|]. split; [exact AM'|]. split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT']|].
  split; [intros x Hx; apply ILK; apply ILK'; exact Hx|]. split; [intros x Hx; apply IAW'; apply IAW; exact Hx|].
  split; [exact CRL|]. split; [exact CRK|].
  pose proof HP as (EKr & _). pose proof (wapp_wsrc M s cr LK Aw _ HH) as WAPP'. destruct (wsrc_outside M s cr LK Aw _ HH) as (OUTS & OUTL).
  split.
  { apply (PMFA.accA_agree M M' op PECA.RDR_BYTES); [| exact ACC].
    apply (PMKB.agsh_obj L ar _ FF (S - 80) 18432 _ M M' EKr WAPP' FRB op PECA.RDR_BYTES).
    apply (PMBSKJ.aobj_fb FF fb); [exact FOK| clear - Eop; lia| unfold PECA.RDR_BYTES; clear - Eop; lia]. }

  pose proof CT as (_ & _ & CPOS & _ & _). unfold PEC.pos_of, PM.unread in CPOS. pose proof STEP as (_ & EEG & _).
  apply (content_step M M' s sm cr LK Aw _ (S - 80) 18432 _ (PM.p_src s) sm' HH IA HP WAPP' OUTS OUTL); [| | exact ST2'| exact CT].
  - unfold PEC.pos_of, PM.unread. rewrite RZ in *. clear - CPOS G Hc EEG. lia.
  - rewrite RZ. unfold UbjRef.slice. cbn [Z.to_nat firstn]. apply PECSD.bytes_at_nil.
Qed.

Lemma call_srd (fx : FPState) R M model s sm cr LK Aw (X : Z) (tl : list Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 80) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 tb -> getr R (reg 12) = Z_to_bv 64 len ->
  st_ok M model s sm cr LK Aw -> PM.unread (PM.p_src s) sm < 2 ^ 26 -> PM.vs_size (PM.p_tb s) + PM.unread (PM.p_src s) sm < 2 ^ 26 ->
  Z.of_nat (length tl) = PM.vs_size (PM.p_tb s) -> L5.bytes_at RSEGS M (PM.vs_data tb (PM.p_tb s)) tl ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (s' : PM.pst) (sm' : PM.strm) (cr' : credit) (d : Z),
     regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 d -> 0 <= d <= len ->
     PMSPA.consumed (PM.p_src s) (PM.p_src s') sm sm' = d -> PM.vs_size (PM.p_tb s') = PM.vs_size (PM.p_tb s) + d ->
     d = Z.min len (PM.unread (PM.p_src s) sm) ->
     L5.bytes_at RSEGS M' (PM.vs_data tb (PM.p_tb s')) (tl ++ UbjRef.slice pl (PEC.pos_of pl (PM.p_src s) sm) d) ->
     PM.p_more s' = PM.p_more s -> PM.p_done s' = PM.p_done s -> PM.p_depth s' = PM.p_depth s ->
     PM.p_b s' = PM.p_b s -> PM.p_k s' = PM.p_k s -> PM.p_stk s' = PM.p_stk s ->
     PMSPA.src_step (PM.p_src s) (PM.p_src s') sm sm' ->
     st_ok M' model' s' sm' cr' LK' Aw' ->
     srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' X M' model') K) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xbbca0 M model) K.
Proof using All.
  intros A1 RAX A2 KP A10 A11 A12 SO UN UNS TLEN TBC NEXT.
  pose proof SO as (MR & SV & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK & ACC & CT).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
  pose proof fbb as (F1024 & rs & Hfb). pose proof geo as (Eop & Eos & Eois & Etb).
  destruct (WF _ Hfb) as (FF1 & FF2 & _). cbn [ff_addr ff_class fst snd] in FF1, FF2. change (ff_bytes 5) with 2048 in *.
  unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FF1, FF2.
  assert (STKr : L5CA.astk ar M (S - 80) 22528).
  { apply (L5SAR.astk_sub ar M M S 24576 80 22528 STK (fun _ Y => Y)); [lia|lia|lia|]. replace (S - 80) with (S + (-5) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  assert (WAPP0 : PMKB.wapp W0) by (apply wapp_W0; destruct FSAPP as (_ & [Y|Y] & _); unfold BIGSHADOW_LO, BIGSHADOW_HI in Y; [left|right]; lia).
  assert (STKSH : shadow_zero M (S - 80 - 22528) (22528 / 8)).
  { change (22528 / 8) with 2816.
    assert (M8a : (S - 24576) mod 8 = 0) by (apply PMKB.mod16_8'; replace (S - 24576) with (S + (-1536) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
    assert (M8b : (S - 80 - 22528) mod 8 = 0) by (apply PMKB.mod16_8'; replace (S - 80 - 22528) with (S + (-1413) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
    apply (PMKB.shadow_zero_sub M (S - 24576) 3072); [exact M8a| exact M8b| lia| lia| lia|].
    apply (PMKB.stksh_keepA L ar LBX FF S 24576 W0 M0 M EK WAPP0 (S - 24576) 3072); [lia|lia|lia| exact M8a| lia| exact STKSH0]. }
  assert (FRM : PMSPA.ffroomA 5 FF LK) by (apply (PMBRSK.ffroom_incl 6 5 FF LK0 LK FRM0 ILK NDF); lia).
  pose proof SRDS as SR. unfold PECTXSA.csrd_read_spec in SR. cbn [pa_srd_read AD PeCLayoutB.CADDR_B] in SR.
  apply (SR fx R M model K LBX FF LK Aw cr (S - 80) X fb len pl tl s str sm HH AM K0).
  { unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
    split; [rewrite (KP 3%nat) by (cbn; auto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; auto); exact Rtp0|].
    change (PMSPA.pm_scr 5) with 22528. split; [exact STKr| exact STKSH]. }
  { exact FRM. }
  { intros f Hf. specialize (FRS f Hf). lia. }
  { exact FOK. }
  { clear - SA32. pose proof (Z.div_mod S 32 ltac:(lia)) as DM. replace (S - 80) with (16 + (S / 32 - 3) * 32) by lia. rewrite Z.mod_add by lia. reflexivity. }
  { rewrite L5K.rl10. exact A10. }
  { rewrite L5SAR.r11. exact A11. }
  { rewrite L5SAR.r12. exact A12. }
  { exact Hlen. }
  { exact PA. } { exact IA. } { exact BASE. } { exact ACC. } { exact TBOK. } { exact INCS. } { exact UN. } { exact UNS. } { exact POK. } { exact CT. } { exact TLEN. } { exact TBC. } { exact CRL. }
  intros fx' R' M' model' LK' Aw' s' sm' cr' d RP Y10 Hd CONS SZ NMIN TBC' PA' IA' TB' G1 G2 G3 G4 G5 G6 STEP CT' HP CK MRT' ILK' IAW' AM' HH'.
  change (PMSPA.pm_scr 5) with 22528 in HP.
  apply (NEXT fx' R' M' model' LK' Aw' s' sm' cr' d RP Y10 Hd CONS SZ NMIN TBC' G1 G2 G3 G4 G5 G6 STEP).
  destruct (callee_mem M M' [] 22528 W0 MR SV ltac:(lia) ltac:(lia) TOP HP) as (MR' & SV' & EKn).
  { intros a _ O. exact O. }
  { intros a Ha. apply outside_W0. lia. }
  split; [exact MR'|]. split; [exact SV'|]. split; [exact PA'|]. split; [exact IA'|].
  split.
  { apply (PMBSKJ.base_keep L ar C LY LBX FF S 24576 W0 M M' EKn); [| exact BASE].
    intros a Ha. apply outside_W0. pose proof (PMBSKJ.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI. lia. }
  split; [exact TB'|]. split; [exact HH'|]. split; [exact AM'|]. split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT']|].
  split; [intros x Hx; apply ILK; apply ILK'; exact Hx|]. split; [intros x Hx; apply IAW'; apply IAW; exact Hx|].
  split; [unfold PMSPA.credit_keep, PMSPA.credit_le in *; destruct CRL as (CL1 & CL2); destruct CK as (CK1 & CK2); split; lia|].
  split; [unfold PMSPA.credit_keep, PMSPA.credit_le in *; destruct CRK as (CR1 & CR2); destruct CK as (CK1 & CK2); split; lia|].
  split; [| exact CT'].
  pose proof (PMBSKJ.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  apply (PMFA.accA_agree M M' op PECA.RDR_BYTES); [| exact ACC].
  apply (PMKB.agsh_obj L ar LBX FF S 24576 W0 M M' EKn WAPP0 FRB op PECA.RDR_BYTES).
  apply (PMBSKJ.aobj_fb FF fb); [exact FOK| clear - Eop; lia| unfold PECA.RDR_BYTES; clear - Eop; lia].
Qed.

Lemma vpack M model s sm cr LK Aw :
  st_ok M model s sm cr LK Aw ->
  let H := ahid Aw model in let MV := mrestrict H M in
  L5.img_clear MV 65536 1306624 /\ L5.u64_at RSEGS MV 1335544 2147450880 /\ L5.u32_at RSEGS MV 1335552 1
  /\ (140735332487248 <= S <= 2 ^ 47 /\ S mod 16 = 0 /\ L5.writable RSEGS MV (S - 80) 80)
  /\ (forall k v, 8 <= k <= 80 -> L5.u64_at RSEGS M (S - k) v -> L5.u64_at RSEGS MV (S - k) v)
  /\ (6930432 <= os <= 140737488355032 /\ os mod 8 = 0 /\ (2147446784 + 17592186048512 <= os \/ os + 296 <= 2147446784))
  /\ L5KA.zeros_at MV ((os + 8) / 8 + 2147450880) 36 /\ L5.writable RSEGS MV os 296 /\ (forall a n, os <= a -> a + n <= os + 296 -> L5A.avis H a n)
  /\ (6930432 <= tb <= 140737488355304 /\ tb mod 8 = 0 /\ (2147446784 + 17592186048512 <= tb \/ tb + 24 <= 2147446784))
  /\ L5KA.zeros_at MV (tb / 8 + 2147450880) 3 /\ L5.writable RSEGS MV tb 24 /\ (forall a n, tb <= a -> a + n <= tb + 24 -> L5A.avis H a n)
  /\ os + 296 <= S - 80 /\ tb + 24 <= S - 80 /\ PMSPA.aobjA FF os 296 /\ PMSPA.aobjA FF tb 24.
Proof using All.
  intros (MR & SV & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK & ACC & CT) H MV.
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (PMBSKJ.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
  pose proof (PMBSKJ.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model S 24576 80 HH STK ltac:(lia)) as (SL80 & SH80 & V3).
  pose proof (PMBSKJ.src_vis L ar C HI LY HIok _ FF LK cr Aw M model fb ois s S 24576 HH FOK PA STK)
    as ((O1 & O8 & OBIG) & OZ & OW & OCE & OAV & AO & OFS1 & OFS2).
  pose proof (PMBRSK.tb_vis L ar C HI LY HIok _ FF LK cr Aw M model fb ois s HH FOK PA)
    as ((T1 & T8 & TBIG) & TZ & TW & TCE & TAV & AT & TFS1 & TFS2).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (_ & VIS & _).
  fold os in O1, O8, OBIG, OZ, OW, OCE, OAV, AO. fold tb in T1, T8, TBIG, TZ, TW, TCE, TAV, AT.
  split; [exact V0|]. split; [exact V1|]. split; [exact V2|].
  split; [split; [lia| split; [exact A16| exact V3]]|].
  split.
  { intros k v Hk X. apply (proj2 (L5A.u64_at_vis H M (S - k) v (VIS (S - k) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact X. }
  split; [split; [lia| split; [exact O8| exact OBIG]]|]. split; [exact OZ|]. split; [exact OW|]. split; [exact OAV|].
  split; [split; [lia| split; [exact T8| exact TBIG]]|]. split; [exact TZ|]. split; [exact TW|]. split; [exact TAV|].
  split; [lia|]. split; [lia|]. split; [exact AO| exact AT].
Qed.

End Call.
End WithHeap.
End PECRS1B.
