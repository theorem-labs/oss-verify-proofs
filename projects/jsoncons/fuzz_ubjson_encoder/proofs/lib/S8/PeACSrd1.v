(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality Permutation.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceA L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreAS8 L5StepARS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PmSpecsAX PeSpecsAa PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCModelA PeCSpecsA PeCSpecsAa PmModelFactsA PeStepA PmStep PmTxtKit2 PeASrcKitJ PeACReset1 PeARsKit PmSpecs PeCSink PeCModel PeCSpecs PeCFrame PeCSrcD PeCTxtSpecsA PeACSrcRead PeACSrcFillTb PeASrdP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_b7934_b7938.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECSRD1A.
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
Abbreviation pot := (fun L ar (s : PM.pst) => PMSPA.scA L (PM.pot_text (PMSPA.HV L ar) (PM.p_tb s) (PM.p_tg s))).

Lemma nodup_perm (l l' : list (Z * Z)) : Permutation l l' -> base.NoDup (map fst l) -> base.NoDup (map fst l').
Proof.
  intros P ND. apply NoDup_ListNoDup. apply NoDup_ListNoDup in ND.
  eapply Permutation_NoDup; [|exact ND]. apply Permutation_map. exact P.
Qed.
Lemma own_with_src (s : PM.pst) src' : PM.sr_qc src' = PM.sr_qc (PM.p_src s) -> PM.parser_own (PMSPA.with_src s src') = PM.parser_own s.
Proof. intros E. unfold PM.parser_own, PMSPA.with_src, PM.src_own. cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]. rewrite E. reflexivity. Qed.
Lemma with_src_id (s : PM.pst) : PMSPA.with_src s (PM.p_src s) = s.
Proof. destruct s; reflexivity. Qed.
Lemma pst_with_src (s : PM.pst) src' :
  PM.PST (PM.p_more s) (PM.p_done s) (PM.p_depth s) src' (PM.p_tb s) (PM.p_tg s) (PM.p_b s) (PM.p_k s) (PM.p_stk s) = PMSPA.with_src s src'.
Proof. destruct s; reflexivity. Qed.
Lemma pst_eta (s : PM.pst) :
  PM.PST (PM.p_more s) (PM.p_done s) (PM.p_depth s) (PM.p_src s) (PM.p_tb s) (PM.p_tg s) (PM.p_b s) (PM.p_k s) (PM.p_stk s) = s.
Proof. destruct s; reflexivity. Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Lemma perm_tb (s : PM.pst) (LB : list (Z * Z)) FF LK cr Aw M V :
  ri_inv HI (PM.parser_own s ++ LB) FF LK cr Aw M V ->
  ri_inv HI (PM.vs_own (PM.p_tb s) ++ (PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s) ++ LB)) FF LK cr Aw M V.
Proof.
  intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & NDF & _).
  apply (HAJ.aior_perm _ _ _ _ _ HIok _ _ FF FF LK cr Aw M V HH).
  - intros b. unfold PM.parser_own. rewrite !in_app_iff. tauto.
  - apply (nodup_perm (PM.parser_own s ++ LB)); [|exact ND].
    unfold PM.parser_own. set (X := PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s)).
    replace ((PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s) ++ PM.vs_own (PM.p_tb s)) ++ LB) with (X ++ PM.vs_own (PM.p_tb s) ++ LB)
      by (unfold X; rewrite <- !app_assoc; reflexivity).
    replace (PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s) ++ LB) with (X ++ LB) by (unfold X; rewrite <- !app_assoc; reflexivity).
    apply Permutation_app_swap_app.
  - intros f. tauto.
  - rewrite map_app in NDF. apply stdpp.list_relations.list.NoDup_app in NDF. exact (proj1 NDF).
Qed.
Lemma perm_tb_back (s : PM.pst) (tb : PM.vstr) (tg : Z) (LB : list (Z * Z)) FF LK cr Aw M V :
  ri_inv HI (PM.vs_own tb ++ (PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s) ++ LB)) FF LK cr Aw M V ->
  ri_inv HI (PM.parser_own (PMTK2.with_tb s tb tg) ++ LB) FF LK cr Aw M V.
Proof.
  intros HH. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND & NDF & _).
  apply (HAJ.aior_perm _ _ _ _ _ HIok _ _ FF FF LK cr Aw M V HH).
  - intros b. unfold PM.parser_own, PMTK2.with_tb. cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]. rewrite !in_app_iff. tauto.
  - apply (nodup_perm (PM.vs_own tb ++ (PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s) ++ LB))); [|exact ND].
    unfold PM.parser_own, PMTK2.with_tb. cbn [PM.p_src PM.p_b PM.p_k PM.p_tb].
    set (X := PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s)).
    replace ((PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s) ++ PM.vs_own tb) ++ LB) with (X ++ PM.vs_own tb ++ LB)
      by (unfold X; rewrite <- !app_assoc; reflexivity).
    replace (PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s) ++ LB) with (X ++ LB) by (unfold X; rewrite <- !app_assoc; reflexivity).
    apply Permutation_sym. apply Permutation_app_swap_app.
  - intros f. tauto.
  - rewrite map_app in NDF. apply stdpp.list_relations.list.NoDup_app in NDF. exact (proj1 NDF).
Qed.

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
Definition W0 : list L5.range := PMSPA.W_srcf AD fb ++ [(PMSPA.o_tb AD fb, 24)].
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

Definition op : Z := PMSPA.o_p AD fb.
Definition os : Z := PMSPA.o_src AD fb.
Definition ois : Z := PMSPA.o_is AD fb.
Definition tb : Z := PMSPA.o_tb AD fb.
Definition U (x : nat) : Z := bv_unsigned (getr R0 (reg x)).

Definition saves13 (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 8) (U 1) /\ L5.u64_at RSEGS M (S - 16) (U 8) /\ L5.u64_at RSEGS M (S - 24) (U 9) /\ L5.u64_at RSEGS M (S - 32) (U 18)
  /\ L5.u64_at RSEGS M (S - 40) (U 19) /\ L5.u64_at RSEGS M (S - 48) (U 20) /\ L5.u64_at RSEGS M (S - 56) (U 21) /\ L5.u64_at RSEGS M (S - 64) (U 22)
  /\ L5.u64_at RSEGS M (S - 72) (U 23) /\ L5.u64_at RSEGS M (S - 80) (U 24) /\ L5.u64_at RSEGS M (S - 88) (U 25) /\ L5.u64_at RSEGS M (S - 96) (U 26)
  /\ L5.u64_at RSEGS M (S - 104) (U 27).
Definition locals (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (S - 184) len /\ L5.u64_at RSEGS M (S - 176) ((os + 256) / 8 + 2147450880) /\ L5.u64_at RSEGS M (S - 168) (os + 256)
  /\ L5.u64_at RSEGS M (S - 160) ((os + 240) / 8 + 2147450880) /\ L5.u64_at RSEGS M (S - 152) (os + 240)
  /\ L5.u64_at RSEGS M (S - 144) ((tb + 8) / 8 + 2147450880) /\ L5.u64_at RSEGS M (S - 136) ((tb + 16) / 8 + 2147450880)
  /\ L5.u64_at RSEGS M (S - 128) (tb + 16) /\ L5.u64_at RSEGS M (S - 120) (tb + 8) /\ L5.u64_at RSEGS M (S - 112) (tb + 1).
Definition kept_rs (R : bvmap 5 word) : Prop := forall x, In x [3; 4]%nat -> getr R (reg x) = getr R0 (reg x).
Definition memrel (M : word -> option byte) : Prop :=
  L5SAR.ek L ar LBX FF S 22528 W0 M0 M /\ L5SAR.dk L ar LBX FF S 22528 M0 M /\ L5CA.astk ar M S 22528.
Definition fields_eq (s : PM.pst) : Prop :=
  PM.p_more s = PM.p_more s0 /\ PM.p_done s = PM.p_done s0 /\ PM.p_depth s = PM.p_depth s0 /\ PM.p_b s = PM.p_b s0 /\ PM.p_k s = PM.p_k s0 /\ PM.p_stk s = PM.p_stk s0.

Definition acct (s : PM.pst) (sm : PM.strm) (w : Z) : Prop :=
  PMSPA.consumed (PM.p_src s0) (PM.p_src s) sm0 sm = len - w /\ PM.vs_size (PM.p_tb s) = PM.vs_size (PM.p_tb s0) + (len - w)
  /\ PMSPA.src_step (PM.p_src s0) (PM.p_src s) sm0 sm /\ fields_eq s.
Definition st_ok (M : word -> option byte) (model : Model) (s : PM.pst) (sm : PM.strm) (cr : credit) (LK : list fframe) (Aw : list (Z * Z)) : Prop :=
  memrel M /\ saves13 M /\ locals M /\ PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M op ois s /\ PM.iss_at RSEGS AD PMSPA.accA M ois str sm
  /\ PMSTA.base_okA RSEGS AD M /\ PM.tb_ok (PM.p_tb s) (PM.p_tg s)
  /\ ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M (vml_of model) /\ L5CA.amodel_ok Aw model /\ model_rt model0 model
  /\ incl LK LK0 /\ incl Aw0 Aw
  /\ PMSPA.credit_le (pot L ar s) cr /\ PMSPA.credit_keep cr0 cr (pot L ar s0) (pot L ar s)
  /\ PMSPA.accA M op PECA.RDR_BYTES
  /\ PEC.content_ok RSEGS AD M fb pl (PM.p_src s) str sm.

Definition pos0 : Z := PEC.pos_of pl (PM.p_src s0) sm0.
Definition TX (M : word -> option byte) (tbv : PM.vstr) (a : Z) : Prop :=
  L5.bytes_at RSEGS M (PM.vs_data tb tbv) (tl ++ UbjRef.slice pl pos0 a).

Definition lregs (R : bvmap 5 word) (w : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 192) /\ getr R (reg 8) = Z_to_bv 64 (tb / 8 + 2147450880) /\ getr R (reg 9) = Z_to_bv 64 tb
  /\ getr R (reg 18) = Z_to_bv 64 os /\ getr R (reg 19) = Z_to_bv 64 (os + 272) /\ getr R (reg 20) = Z_to_bv 64 2147450880
  /\ getr R (reg 21) = Z_to_bv 64 ((os + 272) / 8 + 2147450880) /\ getr R (reg 22) = Z_to_bv 64 (os + 288)
  /\ getr R (reg 23) = Z_to_bv 64 ((os + 288) / 8 + 2147450880) /\ getr R (reg 25) = Z_to_bv 64 w /\ kept_rs R.

Lemma geo : op = fb + 592 /\ os = fb + 616 /\ ois = fb + 96 /\ tb = fb + 592 + 336.
Proof. clear. unfold op, os, ois, tb, PMSPA.o_src, PMSPA.o_tb, PMSPA.o_p, PMSPA.o_is. cbn [pa_off_p pa_off_is AD PeCLayoutA.CADDR_A]. repeat split; lia. Qed.
Lemma fbb : fb mod 1024 = 0 /\ exists rs, In (fb, 5, rs) FF.
Proof. clear - FOK. destruct FOK as (X & Y). split; [| exact X]. apply Z.mod_divide in Y; [| clear; lia]. destruct Y as [k ->]. replace (k * 2048) with ((k * 2) * 1024) by (clear; lia). apply Z_mod_mult. Qed.
Lemma inW_W0 a : (exists r0, In r0 W0 /\ L5.in_rng r0 a) -> fb + 96 + 40 <= a < fb + 592 + 360.
Proof using All.
  intros (r0 & Hin & Hr). unfold W0, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_tb, PMSPA.o_is, PMSPA.o_p in Hin.
  cbn [pa_off_p pa_off_is AD PMA.AD PeLayoutA.ADDR_A PeCLayoutA.CADDR_A app] in Hin. unfold L5.in_rng in Hr.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hr; lia.
Qed.
Lemma outside_W0 a : (a < fb + 136 \/ fb + 592 + 360 <= a) -> L5.outside W0 a.
Proof using All. intros Ha r0 Hr0 Hin. assert (I : exists r1, In r1 W0 /\ L5.in_rng r1 a) by (exists r0; split; assumption). apply inW_W0 in I. lia. Qed.
Lemma wapp_W0 : (fb + 2048 <= 2147446784 \/ 17594333495296 <= fb) -> PMKA.wapp W0.
Proof using All.
  intros X r0 Hr. unfold W0, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_tb, PMSPA.o_is, PMSPA.o_p in Hr. cbn [pa_off_p pa_off_is AD PMA.AD PeLayoutA.ADDR_A PeCLayoutA.CADDR_A app] in Hr.
  unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; destruct X; [left|right|left|right|left|right|left|right]; lia.
Qed.

Lemma unread_nn M model s sm cr LK Aw : st_ok M model s sm cr LK Aw ->
  0 <= PM.unread (PM.p_src s) sm /\ (PM.sm_st sm = 0 \/ PM.sm_st sm = 2) /\ 0 <= PM.sr_rem (PM.p_src s) <= PM.CHUNK /\ PM.sm_g sm <= PM.sm_eg sm.
Proof using All.
  intros (_ & _ & _ & PA & IA & _).
  destruct PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & Q8 & Q9 & Q10 & _) & _).
  destruct IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & ST) & _ & G1 & G2).
  unfold PM.unread. split; [lia|]. split; [exact ST|]. split; [unfold PM.CHUNK in *; lia| exact G2].
Qed.

Lemma pos_acct M model s sm cr LK Aw a : st_ok M model s sm cr LK Aw -> PMSPA.consumed (PM.p_src s0) (PM.p_src s) sm0 sm = a ->
  PEC.pos_of pl (PM.p_src s) sm = pos0 + a /\ 0 <= pos0 /\ pos0 + a <= blen pl /\ a <= PM.unread (PM.p_src s0) sm0.
Proof using All.
  intros SO CONS. pose proof (unread_nn M model s sm cr LK Aw SO) as (UN & _).
  destruct SO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & CPOS & _)).
  unfold pos0, PEC.pos_of, PMSPA.consumed in *. lia.
Qed.
Lemma TX_len M model s sm cr LK Aw a : st_ok M model s sm cr LK Aw -> PMSPA.consumed (PM.p_src s0) (PM.p_src s) sm0 sm = a -> 0 <= a ->
  Z.of_nat (length (tl ++ UbjRef.slice pl pos0 a)) = PM.vs_size (PM.p_tb s0) + a.
Proof using All.
  intros SO CONS Ha. destruct (pos_acct M model s sm cr LK Aw a SO CONS) as (_ & P0 & P1 & _).
  rewrite length_app, Nat2Z.inj_add, TL0, (PECSD.slice_len pl pos0 a); [lia| lia| lia| lia].
Qed.

Lemma finish (fx : FPState) R M model s sm cr LK Aw (w : Z) :
  getr R (reg 1) = Z_to_bv 64 (U 1) -> getr R (reg 2) = Z_to_bv 64 S ->
  (forall x, In x [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R (reg x) = Z_to_bv 64 (U x)) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 (len - w) -> 0 <= w <= len ->
  TX M (PM.p_tb s) (len - w) -> (w = 0 \/ PM.unread (PM.p_src s) sm = 0) ->
  st_ok M model s sm cr LK Aw -> acct s sm w ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb7984 M model) K.
Proof using All.
  intros E1 E2 ES KP E10 Hw TXh WEX SOh (CONS & SZ & STEP & (F1 & F2 & F3 & F4 & F5 & F6)).
  pose proof SOh as ((EK & DK & STK) & _ & _ & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK & ACC & CT).
  pose proof (unread_nn M model s sm cr LK Aw SOh) as (UN & _). clear SOh.
  assert (EQD : len - w = Z.min len (PM.unread (PM.p_src s0) sm0)) by (unfold PMSPA.consumed in CONS; clear - CONS UN WEX Hw; lia).
  unfold TX, pos0, tb in TXh.
  pose proof RAok as (Hr1 & Hr2).
  assert (RA : getr R (reg 1) = Z_to_bv 64 r) by (rewrite E1; unfold U; rewrite Z_to_bv_bv_unsigned; exact Rra0).
  unfold PMSPA.cfg.
  apply (PMASKJ.ret_exit L ar C HI LY HIok fx R M model K _ FF LK cr Aw 0xb7984 r W_b7934 HH AM F_b7934 eq_refl D_b7934 RA ltac:(lia) Hr2).
  intros model1 MRT1 AM1 HH1.
  apply (KONT fx R M model1 LK Aw s sm cr (len - w)); try assumption; try lia.
  - apply L5SAR.preserved_by_index. intros x Hx. unfold L5SAR.cs_all in Hx.
    destruct Hx as [<-|Hx]; [rewrite E2, Rsp0; reflexivity|].
    destruct Hx as [<-|Hx]; [apply KP; cbn; auto|]. destruct Hx as [<-|Hx]; [apply KP; cbn; auto|].
    rewrite (ES x) by (cbn in Hx; cbn; tauto). unfold U. apply Z_to_bv_bv_unsigned.
  - change (PMSPA.pm_scr 5) with 22528. apply (L5SAR.ahpres_of L ar LBX FF S 22528 _ M0 M EK); [destruct STK as (_ & _ & _ & _ & D & _); exact D| exact DK].
  - eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1].
Qed.

Lemma callee_mem M M' (BX : list (Z * Z)) scr' (W' : list L5.range) :
  memrel M -> saves13 M -> locals M -> 0 <= scr' -> 192 + scr' <= 22528 -> ar_stack_top ar <= 2 ^ 47 ->
  L5CA.ahpres L ar (BX ++ LBX) FF (S - 192) scr' W' M M' ->
  (forall a, aclient L ar LBX FF S 22528 a -> L5.outside W0 a -> L5.outside W' a) -> (forall a, S - 192 <= a < S -> L5.outside W' a) ->
  memrel M' /\ saves13 M' /\ locals M' /\ L5SAR.ek L ar LBX FF S 22528 W0 M M'.
Proof using All.
  intros (EK & DK & STK) SV LC Hs Hs2 TOP HP HW HWS.
  pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  assert (EKn : L5SAR.ek L ar LBX FF S 22528 W0 M M').
  { apply (L5SAR.ek_callee L ar LBX BX FF [] S 22528 (S - 192) scr' W0 W' M M' HP); [lia|lia| exact HW]. }
  assert (DKn : L5SAR.dk L ar LBX FF S 22528 M M') by (apply (L5SAR.dk_callee L ar LBX BX FF [] S 22528 (S - 192) scr' W' M M' HP); lia).
  assert (KEEPS : forall k v, 8 <= k <= 192 -> L5.u64_at RSEGS M (S - k) v -> L5.u64_at RSEGS M' (S - k) v).
  { intros k v Hk X. apply (L5C.u64_at_agree RSEGS M M'); [|lia|lia|exact X].
    intros i Hi. destruct HP as (P & _). apply P. split; [lia|]. split.
    - apply (L5SAR.stack_client L ar (BX ++ LBX) FF (S - 192) scr' i); lia.
    - apply HWS. lia. }
  split; [split; [|split]|].
  - exact (L5SAR.ek_trans L ar LBX FF S 22528 W0 M0 M M' EK EKn).
  - exact (L5SAR.dk_trans L ar LBX FF S 22528 M0 M M' DK DKn).
  - apply (PMKA.astk_after_ahpres L ar _ FF M M' S 22528 (S - 192) scr' W' STK HP); lia.
  - split; [|split; [|exact EKn]].
    + destruct SV as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104).
      repeat split; (apply KEEPS; [lia| assumption]).
    + destruct LC as (L1 & L2 & L3 & L4 & L5' & L6 & L7 & L8 & L9 & L10).
      repeat split; (apply KEEPS; [lia| assumption]).
Qed.

Lemma content_agree M M' s sm cr LK Aw V :
  L5C.agree_on M M' (PM.sr_qc (PM.p_src s)) PM.CHUNK -> (forall B m, In (B, m) LBX -> L5C.agree_on M M' B m) -> L5C.agree_on M M' (ois + 80) 24 ->
  ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M V ->
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M op ois s -> PM.iss_at RSEGS AD PMSPA.accA M ois str sm ->
  PEC.content_ok RSEGS AD M fb pl (PM.p_src s) str sm -> PEC.content_ok RSEGS AD M' fb pl (PM.p_src s) str sm.
Proof using All.
  intros AGQ AGX AGS HH PA IA CT.
  pose proof (PMASKJ.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMASKJ.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof fbb as (F1024 & rs & Hfb). pose proof geo as (Eop & Eos & Eois & Etb).
  destruct (FRB _ Hfb) as (Fb0 & Fb1). cbn [ff_addr ff_class fst snd] in Fb0, Fb1. change (ff_bytes 5) with 2048 in Fb1.
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _) & _).
  pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _). destruct VS as (_ & _ & VSF).
  assert (QIN : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  destruct (BRB _ QIN) as (Q0 & Q4). cbn [fst snd] in Q0, Q4.
  apply (PECF.content_ok_agree RSEGS AD M M' fb pl (PM.p_src s) str sm); unfold PMSP.o_is; cbn [pa_off_is PeCLayoutA.CADDR_A];
    [clear - Fb0; lia| clear - Fb1; lia| rewrite Eois in AGS; exact AGS| | clear - Q0; lia| clear - Q4; unfold PM.CHUNK in *; lia| exact G1| exact G2| exact G3| exact AGQ| | exact CT].
  - intros c n q E. subst str. cbn in VSF. destruct VSF as (_ & _ & _ & Hn & _).
    assert (SIN : In (q, c) (PM.parser_own s ++ LBX)) by (apply in_or_app; right; apply INCS; left; reflexivity).
    destruct (BRB _ SIN) as (B0 & B4). cbn [fst snd] in B0, B4. split; [clear - B0; lia|]. split; [clear - B4; lia|]. split; [clear - Hn; lia| exact (AGX _ _ (INCS _ (or_introl eq_refl)))].
  - intros n E. subst str. cbn in VSF. clear - VSF; lia.
Qed.

Lemma content_step M M' s sm cr LK Aw V scr' (W' : list L5.range) (src' : PM.srcst) (sm' : PM.strm) :
  ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M V -> PM.iss_at RSEGS AD PMSPA.accA M ois str sm ->
  L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF (S - 192) scr' W' M M' -> PMKA.wapp W' ->
  (forall i, ois + 80 <= i < ois + 80 + 24 -> L5.outside W' i) ->
  (forall c n q, str = PM.VLong c n q -> forall i, q <= i < q + c -> L5.outside W' i) ->
  0 <= PEC.pos_of pl src' sm' -> L5.bytes_at RSEGS M' (PM.sr_de src') (UbjRef.slice pl (PEC.pos_of pl src' sm') (PM.sr_rem src')) ->
  (PM.sm_st sm' = 2 -> PM.sm_g sm' = PM.sm_eg sm') ->
  PEC.content_ok RSEGS AD M fb pl (PM.p_src s) str sm -> PEC.content_ok RSEGS AD M' fb pl src' str sm'.
Proof using All.
  intros HH IA HP WAPP OUTS OUTL POS' BC' ST2' CT.
  pose proof (PMASKJ.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMASKJ.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof fbb as (F1024 & rs & Hfb). pose proof geo as (Eop & Eos & Eois & Etb).
  destruct (FRB _ Hfb) as (Fb0 & Fb1). cbn [ff_addr ff_class fst snd] in Fb0, Fb1. change (ff_bytes 5) with 2048 in Fb1.
  pose proof HP as (EKr & _).
  pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _). destruct VS as (_ & _ & VSF).
  assert (AOS : PMSPA.aobjA FF (ois + 80) 24) by (apply (PMASKJ.aobj_fb FF fb); [exact FOK| clear - Eois; lia| clear - Eois; lia]).
  apply (PECF.content_ok_step RSEGS AD M M' fb pl (PM.p_src s) str sm src' sm'); unfold PMSP.o_is; cbn [pa_off_is PeCLayoutA.CADDR_A];
    [clear - Fb0; lia| clear - Fb1; lia| | | | exact POS'| exact BC'| exact ST2'| exact CT].
  - rewrite <- Eois. exact (proj1 (PMKA.agA_obj L ar _ FF (S - 192) scr' W' M M' EKr WAPP FRB (ois + 80) 24 AOS OUTS)).
  - intros c1 n1 q1 E. rewrite E in VSF. cbn in VSF. destruct VSF as (_ & _ & _ & Hn1 & _).
    assert (SIN : In (q1, c1) (PM.parser_own s ++ LBX)) by (apply in_or_app; right; apply INCS; rewrite E; left; reflexivity).
    destruct (BRB _ SIN) as (B0 & B4). cbn [fst snd] in B0, B4.
    split; [clear - B0; lia|]. split; [clear - B4; lia|]. split; [clear - Hn1; lia|].
    exact (proj1 (PMKA.agA_blk L ar _ FF (S - 192) scr' W' M M' EKr WAPP BRB q1 c1 SIN (OUTL c1 n1 q1 E))).
  - intros n E. rewrite E in VSF. cbn in VSF. clear - VSF; lia.
Qed.

Lemma wapp_src M s cr LK Aw V (p k : Z) :
  ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M V -> (p + k <= BIGSHADOW_LO \/ BIGSHADOW_HI <= p) ->
  PMKA.wapp (PMSPA.W_src AD fb (PM.p_src s) ++ [(p, k)]).
Proof using All.
  intros HH Hp. pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & _).
  pose proof fbb as (F1024 & rs & Hfb).
  destruct (WF _ Hfb) as (FF1 & FF2 & _). cbn [ff_addr ff_class fst snd] in FF1, FF2. change (ff_bytes 5) with 2048 in FF2.
  unfold app_mem, FS_BYTES in FSAPP, FF1, FF2.
  assert (WAPP0 : PMKA.wapp W0) by (apply wapp_W0; destruct FSAPP as (_ & [Y|Y] & _); unfold BIGSHADOW_LO, BIGSHADOW_HI in Y; [left|right]; lia).
  assert (QIN : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  destruct (WB _ QIN) as ((_ & _ & _ & _ & _ & (_ & QAPP & _)) & _). cbn [fst snd] in QAPP.
  unfold PMSPA.W_src. apply PMKA.wapp_app; [apply PMKA.wapp_app|].
  - intros r0 Hr0. apply WAPP0. unfold W0. apply in_or_app. left. exact Hr0.
  - apply PMKA.wapp_cons; [cbn [fst snd]; exact QAPP| apply PMKA.wapp_nil].
  - apply PMKA.wapp_cons; [cbn [fst snd]; exact Hp| apply PMKA.wapp_nil].
Qed.

Lemma tb_keep M M' s cr LK Aw V scr' (p k : Z) (l : list Z) :
  ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M V -> PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M op ois s ->
  L5CA.ahpres L ar (PM.parser_own s ++ LBX) FF (S - 192) scr' (PMSPA.W_src AD fb (PM.p_src s) ++ [(p, k)]) M M' ->
  PMKA.wapp (PMSPA.W_src AD fb (PM.p_src s) ++ [(p, k)]) ->
  PM.vs_data tb (PM.p_tb s) + Z.of_nat (length l) <= p -> Z.of_nat (length l) <= PM.vs_size (PM.p_tb s) ->
  L5.bytes_at RSEGS M (PM.vs_data tb (PM.p_tb s)) l -> L5.bytes_at RSEGS M' (PM.vs_data tb (PM.p_tb s)) l.
Proof using All.
  intros HH PA HP WAPP Hp Hl BY.
  pose proof (PMASKJ.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMASKJ.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & _).
  pose proof fbb as (F1024 & rs & Hfb). pose proof geo as (Eop & Eos & Eois & Etb).
  destruct (FRB _ Hfb) as (Fb0 & Fb1). cbn [ff_addr ff_class fst snd] in Fb0, Fb1. change (ff_bytes 5) with 2048 in Fb1.
  pose proof HP as (EKr & _).
  set (W' := PMSPA.W_src AD fb (PM.p_src s) ++ [(p, k)]) in *.
  assert (QIN : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  destruct (BRB _ QIN) as (Q0 & Q4). cbn [fst snd] in Q0, Q4.

  assert (QAP : PM.sr_qc (PM.p_src s) + PM.CHUNK <= fb \/ fb + 2048 <= PM.sr_qc (PM.p_src s)).
  { destruct (WB _ QIN) as (_ & _ & _ & _ & _ & FA & _). cbn [fst snd] in FA.
    destruct (FA (fb, 5, rs) (in_or_app _ _ _ (or_introl Hfb))) as [X0|X0]; cbn [ff_addr ff_class fst snd] in X0; change (ff_bytes 5) with 2048 in X0; [left|right]; lia. }

  assert (WIN : forall i r0, In r0 W' -> L5.in_rng r0 i -> (os + 256 <= i < os + 296 \/ ois + 40 <= i < ois + 48 \/ ois + 152 <= i < ois + 156)
                                          \/ (PM.sr_qc (PM.p_src s) <= i < PM.sr_qc (PM.p_src s) + PM.CHUNK) \/ p <= i < p + k).
  { intros i r0 Hin Hr. unfold W', PMSPA.W_src, PMSPA.W_srcf in Hin. fold os ois in Hin. cbn [app] in Hin.
    unfold L5.in_rng in Hr. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hr; [left|left|left|right; left|right; right]; clear - Hr; lia. }
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _).
  replace (op + 336) with tb in VS by (clear - Eop Etb; lia).
  revert Hp Hl BY VS. destruct (PM.p_tb s) as [n1|c1 n1 q1] eqn:ETB; intros Hp Hl BY (VD & _ & VS); cbn [PM.vs_data PM.vs_size] in Hp, Hl, BY |- *.
  -
    destruct VS as (Hn1 & _).
    assert (AOT : PMSPA.aobjA FF (tb + 1) (Z.of_nat (length l))) by (apply (PMASKJ.aobj_fb FF fb); [exact FOK| clear - Etb; lia| clear - Etb Hl Hn1; lia]).
    apply (PECSD.bytes_agree RSEGS M M' (tb + 1) (Z.of_nat (length l))); [clear; lia| clear - Etb Fb0; lia| clear - Hl Hn1 Etb Fb1; lia| | exact BY].
    refine (proj1 (PMKA.agA_obj L ar _ FF (S - 192) scr' W' M M' EKr WAPP FRB (tb + 1) (Z.of_nat (length l)) AOT _)).
    intros i Hi r0 Hr0 Hin. destruct (WIN i r0 Hr0 Hin) as [X|[X|X]]; [clear - Hi X Hl Hn1 Etb Eos Eois; lia| clear - Hi X QAP Etb Hl Hn1; unfold PM.CHUNK in *; lia| clear - Hi X Hp; lia].
  -
    destruct VS as (_ & _ & _ & Hn1 & Hc1 & _).
    assert (TIN : In (q1, c1) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own; rewrite ETB; cbn; right; right; left; reflexivity).
    destruct (BRB _ TIN) as (B0 & B4). cbn [fst snd] in B0, B4.

    assert (NE : PM.sr_qc (PM.p_src s) <> q1).
    { apply (PMASKJ.fst_neq_appA (PM.src_own (PM.p_src s)) (PM.vec_own (PM.p_b s) (PM.p_k s) ++ PM.vs_own (PM.p_tb s) ++ LBX) _ PM.CHUNK q1 c1).
      - replace (PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s) ++ PM.vs_own (PM.p_tb s) ++ LBX) with (PM.parser_own s ++ LBX)
          by (unfold PM.parser_own; rewrite <- !app_assoc; reflexivity).
        exact (PMASKJ.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH).
      - unfold PM.src_own. left. reflexivity.
      - apply in_or_app. right. apply in_or_app. left. rewrite ETB. left. reflexivity. }
    pose proof (PMASKJ.blk_apart L ar C HI HIok _ _ _ _ _ _ _ _ _ _ _ HH QIN TIN NE) as AP.
    apply (PECSD.bytes_agree RSEGS M M' q1 (Z.of_nat (length l))); [clear; lia| clear - B0; lia| clear - B4 Hl Hn1 Hc1; lia| | exact BY].
    intros i Hi. apply EKr. split; [clear - Hi B0 B4 Hl Hn1 Hc1; lia|]. split.
    + unfold aclient, aclient_g. left. exists (q1, c1). split; [exact TIN| cbn [fst snd]; clear - Hi Hl Hn1 Hc1; lia].
    + intros r0 Hr0 Hin. destruct (WIN i r0 Hr0 Hin) as [X|[X|X]].
      *
        destruct (WB _ TIN) as (_ & _ & _ & _ & _ & FA & _). cbn [fst snd] in FA.
        destruct (FA (fb, 5, rs) (in_or_app _ _ _ (or_introl Hfb))) as [X0|X0]; cbn [ff_addr ff_class fst snd] in X0; change (ff_bytes 5) with 2048 in X0;
          clear - Hi X X0 Hl Hn1 Hc1 Eos Eois; lia.
      * clear - Hi X AP Hl Hn1 Hc1; unfold PM.CHUNK in *; lia.
      * clear - Hi X Hp; lia.
Qed.

Lemma tb_agree M M1 s cr LK Aw V (l : list Z) (lo hi : Z) :
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M op ois s -> ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M V ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (lo <= i < hi) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> (hi <= tb \/ tb + 24 <= lo) ->
  (forall q c, In (q, c) (PM.parser_own s ++ LBX) -> hi <= q \/ q + c <= lo) ->
  Z.of_nat (length l) <= PM.vs_size (PM.p_tb s) ->
  L5.bytes_at RSEGS M (PM.vs_data tb (PM.p_tb s)) l -> L5.bytes_at RSEGS M1 (PM.vs_data tb (PM.p_tb s)) l.
Proof using All.
  intros PA HH FRZ Htb Hblk Hl BY.
  pose proof (PMASKJ.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMASKJ.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof fbb as (F1024 & rs & Hfb). pose proof geo as (Eop & Eos & Eois & Etb).
  destruct (FRB _ Hfb) as (Fb0 & Fb1). cbn [ff_addr ff_class fst snd] in Fb0, Fb1. change (ff_bytes 5) with 2048 in Fb1.
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _).
  replace (op + 336) with tb in VS by (clear - Eop Etb; lia).
  revert Hl BY VS. destruct (PM.p_tb s) as [n1|c1 n1 q1] eqn:ETB; intros Hl BY (VD & _ & VS); cbn [PM.vs_data PM.vs_size] in Hl, BY |- *.
  - destruct VS as (Hn1 & _).
    apply (PECSD.bytes_agree RSEGS M M1 (tb + 1) (Z.of_nat (length l))); [clear; lia| clear - Etb Fb0; lia| clear - Hl Hn1 Etb Fb1; lia| | exact BY].
    intros i Hi. apply FRZ; [clear - Hi Hl Hn1 Etb Fb0 Fb1; lia| clear - Hi Hl Hn1 Htb; lia].
  - destruct VS as (_ & _ & _ & Hn1 & Hc1 & _).
    assert (TIN : In (q1, c1) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own; rewrite ETB; cbn; right; right; left; reflexivity).
    destruct (BRB _ TIN) as (B0 & B4). cbn [fst snd] in B0, B4.
    apply (PECSD.bytes_agree RSEGS M M1 q1 (Z.of_nat (length l))); [clear; lia| clear - B0; lia| clear - B4 Hl Hn1 Hc1; lia| | exact BY].
    intros i Hi. apply FRZ; [clear - Hi Hl Hn1 Hc1 B0 B4; lia|]. destruct (Hblk q1 c1 TIN) as [X9|X9]; clear - Hi Hl Hn1 Hc1 X9; lia.
Qed.

Lemma centry (R : bvmap 5 word) M model s sm cr LK Aw (X h : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 192) -> kept_rs R -> st_ok M model s sm cr LK Aw -> 1 <= h <= 4 ->
  PMSPA.entryA AD L ar R M (S - 192) X h /\ PMSPA.ffroomA h FF LK /\ PMSPA.ffrsA FF (S - 192).
Proof using All.
  intros A1 RAX A2 KP SO Hh.
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK & ACC & CT).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
  pose proof fbb as (F1024 & rs & Hfb).
  destruct (WF _ Hfb) as (FF1 & FF2 & _). cbn [ff_addr ff_class fst snd] in FF1, FF2. change (ff_bytes 5) with 2048 in FF2.
  unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FF1, FF2.
  assert (STKr : L5CA.astk ar M (S - 192) (PMSPA.pm_scr h)).
  { apply (L5SAR.astk_sub ar M M S 22528 192 (PMSPA.pm_scr h) STK (fun _ Y => Y)); unfold PMSPA.pm_scr; [lia|lia|lia|].
    replace (S - 192) with (S + (-12) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  assert (WAPP0 : PMKA.wapp W0) by (apply wapp_W0; destruct FSAPP as (_ & [Y|Y] & _); unfold BIGSHADOW_LO, BIGSHADOW_HI in Y; [left|right]; lia).
  assert (STKSH : shadow_zero M (S - 192 - PMSPA.pm_scr h) (PMSPA.pm_scr h / 8)).
  { assert (M8a : (S - 22528) mod 8 = 0) by (apply PMKA.mod16_8'; replace (S - 22528) with (S + (-1408) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
    assert (M8b : (S - 192 - PMSPA.pm_scr h) mod 8 = 0).
    { apply PMKA.mod16_8'. unfold PMSPA.pm_scr. replace (S - 192 - (12288 + 2048 * h)) with (S + (-(780 + 128 * h)) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    assert (G8 : PMSPA.pm_scr h / 8 = 1536 + 256 * h).
    { unfold PMSPA.pm_scr. replace (12288 + 2048 * h) with ((1536 + 256 * h) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
    rewrite G8. unfold PMSPA.pm_scr in M8b |- *.
    apply (PMKA.shadow_zero_sub M (S - 22528) 2816); [exact M8a| exact M8b| lia| lia| lia|].
    apply (PMKA.stksh_keepA L ar LBX FF S 22528 W0 M0 M EK WAPP0 (S - 22528) 2816); [lia|lia|lia| exact M8a| lia| exact STKSH0]. }
  assert (FRM : PMSPA.ffroomA h FF LK) by (apply (PMARSK.ffroom_incl 5 h FF LK0 LK FRM0 ILK NDF); lia).
  split; [|split; [exact FRM| intros f Hf; specialize (FRS f Hf); lia]].
  unfold PMSPA.entryA. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [exact RAX|]. split; [exact A2|].
  split; [rewrite (KP 3%nat) by (cbn; auto); exact Rgp0|]. split; [rewrite (KP 4%nat) by (cbn; auto); exact Rtp0|].
  split; [exact STKr| exact STKSH].
Qed.

Lemma call_resize (fx : FPState) R M model s sm cr LK Aw (nn X : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 192) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 tb -> getr R (reg 11) = Z_to_bv 64 nn ->
  0 <= nn <= PM.vs_size (PM.p_tb s) + PM.CHUNK -> nn < 2 ^ 26 + PM.CHUNK ->
  st_ok M model s sm cr LK Aw ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (tb' : PM.vstr) (tg' : Z) (cr' : credit),
     regs_preserved R R' -> PM.vs_size tb' = nn -> (nn <= PM.vs_cap (PM.p_tb s) -> PM.vs_own tb' = PM.vs_own (PM.p_tb s) /\ tg' = PM.p_tg s) ->
     (forall l, Z.of_nat (length l) <= Z.min nn (PM.vs_size (PM.p_tb s)) ->
        L5.bytes_at RSEGS M (PM.vs_data tb (PM.p_tb s)) l -> L5.bytes_at RSEGS M' (PM.vs_data tb tb') l) ->
     st_ok M' model' (PMTK2.with_tb s tb' tg') sm cr' LK' Aw' ->
     srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' X M' model') K) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xd754c M model) K.
Proof using All.
  intros A1 RAX A2 KP A10 A11 Hn1 Hn2 SO NEXT.
  destruct (centry R M model s sm cr LK Aw X 1 A1 RAX A2 KP SO ltac:(lia)) as (ENT & FRM & FRS').
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK & ACC & CT).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
  pose proof fbb as (F1024 & rs & Hfb). pose proof geo as (Eop & Eos & Eois & Etb).
  destruct (WF _ Hfb) as (FF1 & FF2 & _). cbn [ff_addr ff_class fst snd] in FF1, FF2. change (ff_bytes 5) with 2048 in FF2.
  pose proof (PMASKJ.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB. pose proof (PMASKJ.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB.
  pose proof (PMARSK.tb_vis L ar C HI LY HIok _ FF LK cr Aw M model fb ois s HH FOK PA) as ((T1 & T8 & TBIG) & _ & _ & _ & _ & AT & TFS1 & TFS2).
  fold tb in T1, T8, TBIG, AT, TFS1, TFS2.
  unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FF1, FF2, TFS1, TFS2.
  pose proof PA as (_ & PD & _ & _ & _ & _ & _ & _ & _ & SRC & _ & _ & _ & VS & VEC & _).
  replace (op + 336) with tb in VS by lia.
  pose proof VEC as (_ & _ & _ & Hk & _). pose proof (PM.pow2_pos (PM.p_k s) (proj1 Hk)) as P2.
  assert (VIN : In (PM.p_b s, 32 * 2 ^ PM.p_k s) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; right; left; reflexivity).
  assert (QIN : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  destruct (BRB _ QIN) as (QB0 & QB1). destruct (BRB _ VIN) as (VB0 & VB1). cbn [fst snd] in QB0, QB1, VB0, VB1.
  assert (BLKAP : forall q m, In (q, m) (PM.parser_own s ++ LBX) -> q + m <= fb \/ fb + 2048 <= q).
  { intros q m Hq. destruct (WB _ Hq) as (_ & _ & _ & _ & _ & FA & _). cbn [fst snd] in FA.
    destruct (FA (fb, 5, rs) (in_or_app _ _ _ (or_introl Hfb))) as [X0|X0]; cbn [ff_addr ff_class fst snd] in X0; change (ff_bytes 5) with 2048 in X0; [left|right]; lia. }
  set (LB' := PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s) ++ LBX).
  pose proof (perm_tb s LBX FF LK cr Aw M _ HH) as HH'. fold LB' in HH'.
  pose proof RSZ as RS. unfold PECTXSA.cstr_resize_spec in RS. cbn [pa_str_resize AD PeCLayoutA.CADDR_A] in RS.
  apply (RS fx R M model K LB' FF LK Aw cr tb nn (S - 192) X (PM.p_tg s) (PM.p_tb s) HH' AM K0 ENT FRM FRS').
  { rewrite L5K.rl10. exact A10. }
  { rewrite L5SAR.r11. exact A11. }
  { exact AT. } { exact T8. } { exact VS. } { exact TBOK. } { exact Hn1. } { exact Hn2. } { exact CRL. }
  intros fx' R' M' model' LK' Aw' tb' tg' cr' RP VS' SZ TB' BYT OWN HP CK MRT' ILK' IAW' AM' HH2.
  change (PMSPA.pm_scr 1) with 14336 in HP.
  apply (NEXT fx' R' M' model' LK' Aw' tb' tg' cr' RP SZ OWN BYT).
  assert (HPc : L5CA.ahpres L ar ((PM.src_own (PM.p_src s) ++ PM.vec_own (PM.p_b s) (PM.p_k s)) ++ LBX) FF (S - 192) 14336 [(tb, 24)] M M')
    by (rewrite <- app_assoc; exact HP).
  destruct (callee_mem M M' _ 14336 [(tb, 24)] MR SV LC ltac:(lia) ltac:(lia) TOP HPc) as (MR' & SV' & LC' & EKn).
  { intros a _ O r0 [<-|[]] Hin. apply (O (PMSPA.o_tb AD fb, 24)); [unfold W0; apply in_or_app; right; left; reflexivity| exact Hin]. }
  { intros a Ha r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia. }
  set (Wt := [(tb, 24)]).
  assert (WAPPt : PMKA.wapp Wt) by (apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; destruct TBIG; [right| left]; lia| apply PMKA.wapp_nil]).
  pose proof HP as (EKr & _ & DKr).
  assert (EKt : L5SAR.ek L ar LB' FF (S - 192) 14336 Wt M M') by exact EKr.
  assert (INLB : forall b, In b LB' -> In b (PM.parser_own s ++ LBX)).
  { intros b Hb. unfold LB' in Hb. unfold PM.parser_own. rewrite !in_app_iff in *. tauto. }
  assert (BRB' : forall b, In b LB' -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) by (intros b Hb; exact (BRB b (INLB b Hb))).
  assert (OUTB : forall q m, In (q, m) (PM.parser_own s ++ LBX) -> forall i, q <= i < q + m -> L5.outside Wt i).
  { intros q m Hq i Hi r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. destruct (BLKAP q m Hq); lia. }
  assert (AOI : PMSPA.aobjA FF ois 272).
  { exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
  assert (PD' : L5.defined M' op 384).
  { intros i Hi. apply DKr; [lia| |apply PD; exact Hi].
    unfold aclient, aclient_g. right; right; right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
  assert (PA' : PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M' op ois (PMTK2.with_tb s tb' tg')).
  { apply (PMARSK.parser_tb_setA M M' op ois s tb' tg' PA); [lia| lia| | | | lia| unfold PM.CHUNK in *; lia| | lia| lia| | |].
    - apply (PMKA.agA_obj L ar LB' FF (S - 192) 14336 Wt M M' EKt WAPPt FRB).
      + exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia.
      + intros i Hi r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia.
    - apply (PMKA.agA_obj L ar LB' FF (S - 192) 14336 Wt M M' EKt WAPPt FRB).
      + exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia.
      + intros i Hi r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia.
    - apply (PMKA.agsh_obj L ar LB' FF (S - 192) 14336 Wt M M' EKt WAPPt FRB).
      exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia.
    - apply (PMKA.agA_blk L ar LB' FF (S - 192) 14336 Wt M M' EKt WAPPt BRB'); [unfold LB', PM.src_own; apply in_or_app; left; left; reflexivity| exact (OUTB _ _ QIN)].
    - apply (PMKA.agA_blk L ar LB' FF (S - 192) 14336 Wt M M' EKt WAPPt BRB');
        [unfold LB', PM.vec_own; apply in_or_app; right; apply in_or_app; left; left; reflexivity| exact (OUTB _ _ VIN)].
    - replace (op + 336) with tb by lia. exact VS'.
    - exact PD'. }
  assert (IA' : PM.iss_at RSEGS AD PMSPA.accA M' ois str sm).
  { apply (PMKA.iss_keepA RSEGS AD L ar LB' FF (S - 192) 14336 Wt M M' EKt WAPPt FRB BRB' _ _ _ AOI); [| | |exact IA].
    - intros x Hx. unfold LB'. rewrite !in_app_iff. right; right. apply INCS. exact Hx.
    - intros i Hi r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. lia.
    - intros c n p E i Hi. apply (OUTB p c); [apply in_or_app; right; apply INCS; rewrite E; left; reflexivity| exact Hi]. }
  split; [exact MR'|]. split; [exact SV'|]. split; [exact LC'|]. split; [exact PA'|]. split; [exact IA'|].
  split.
  { apply (PMASKJ.base_keep L ar C LY LBX FF S 22528 W0 M M' EKn); [| exact BASE].
    intros a Ha. apply outside_W0. pose proof (PMASKJ.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI. lia. }
  split; [exact TB'|]. split; [apply perm_tb_back; exact HH2|]. split; [exact AM'|].
  split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT']|].
  split; [intros x Hx; apply ILK; apply ILK'; exact Hx|]. split; [intros x Hx; apply IAW'; apply IAW; exact Hx|].
  cbn [PMTK2.with_tb PM.p_tb PM.p_tg PM.p_src].
  unfold PMSPA.credit_keep, PMSPA.credit_le in CRL, CK, CRK |- *. destruct CRL as (CL1 & CL2). destruct CK as (CK1 & CK2). destruct CRK as (CR1 & CR2).
  split; [split; lia|]. split; [split; lia|].
  split.
  { apply (PMFA.accA_agree M M' op PECA.RDR_BYTES); [| exact ACC].
    apply (PMKA.agsh_obj L ar LB' FF (S - 192) 14336 Wt M M' EKt WAPPt FRB op PECA.RDR_BYTES).
    apply (PMASKJ.aobj_fb FF fb); [exact FOK| clear - Eop; lia| unfold PECA.RDR_BYTES; clear - Eop; lia]. }
  apply (content_agree M M' s sm cr LK Aw (vml_of model)); [| | | exact HH| exact PA| exact IA| exact CT].
  + exact (proj1 (PMKA.agA_blk L ar LB' FF (S - 192) 14336 Wt M M' EKt WAPPt BRB' _ _ ltac:(unfold LB', PM.src_own; apply in_or_app; left; left; reflexivity) (OUTB _ _ QIN))).
  + intros B m Hin. assert (BIN : In (B, m) (PM.parser_own s ++ LBX)) by (apply in_or_app; right; exact Hin).
    exact (proj1 (PMKA.agA_blk L ar LB' FF (S - 192) 14336 Wt M M' EKt WAPPt BRB' _ _ ltac:(unfold LB'; rewrite !in_app_iff; right; right; exact Hin) (OUTB _ _ BIN))).
  + refine (proj1 (PMKA.agA_obj L ar LB' FF (S - 192) 14336 Wt M M' EKt WAPPt FRB (ois + 80) 24 _ _)).
    * apply (PMASKJ.aobj_fb FF fb); [exact FOK| clear - Eois; lia| clear - Eois; lia].
    * intros i Hi r0 [<-|[]] Hin. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. clear - Hi Hin Eois Etb. lia.
Qed.

Definition tbdst (s : PM.pst) (p k : Z) : Prop :=
  ((exists n, PM.p_tb s = PM.VShort n) /\ tb + 1 <= p /\ p + k <= tb + 24)
  \/ (exists c n q, PM.p_tb s = PM.VLong c n q /\ q <= p /\ p + k <= q + c).

Lemma call_srcread (fx : FPState) R M model s sm cr LK Aw (p k X : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 192) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 p -> getr R (reg 12) = Z_to_bv 64 k ->
  1 <= k <= PM.CHUNK -> tbdst s p k -> st_ok M model s sm cr LK Aw ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (src' : PM.srcst) (sm' : PM.strm) (d : Z),
     regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 d -> 0 <= d <= k ->
     PMSPA.consumed (PM.p_src s) src' sm sm' = d -> (d < k -> PM.unread src' sm' = 0) ->
     (d = 0 -> PM.sm_st sm' = 2) -> PMSPA.src_step (PM.p_src s) src' sm sm' ->
     L5.bytes_at RSEGS M' p (UbjRef.slice pl (PEC.pos_of pl (PM.p_src s) sm) d) ->
     (forall l, PM.vs_data tb (PM.p_tb s) + Z.of_nat (length l) <= p -> Z.of_nat (length l) <= PM.vs_size (PM.p_tb s) ->
        L5.bytes_at RSEGS M (PM.vs_data tb (PM.p_tb s)) l -> L5.bytes_at RSEGS M' (PM.vs_data tb (PM.p_tb s)) l) ->
     st_ok M' model' (PMSPA.with_src s src') sm' cr LK' Aw' ->
     srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' X M' model') K) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb540c M model) K.
Proof using All.
  intros A1 RAX A2 KP A10 A11 A12 Hk DST SO NEXT.
  destruct (centry R M model s sm cr LK Aw X 4 A1 RAX A2 KP SO ltac:(lia)) as (ENT & FRM & FRS').
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK & ACC & CT).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
  pose proof fbb as (F1024 & rs & Hfb). pose proof geo as (Eop & Eos & Eois & Etb).
  destruct (WF _ Hfb) as (FF1 & FF2 & _). cbn [ff_addr ff_class fst snd] in FF1, FF2. change (ff_bytes 5) with 2048 in FF2.
  pose proof (PMASKJ.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  pose proof (PMARSK.tb_vis L ar C HI LY HIok _ FF LK cr Aw M model fb ois s HH FOK PA) as ((T1 & T8 & TBIG) & _ & _ & _ & _ & AT & TFS1 & TFS2).
  fold tb in T1, T8, TBIG, AT, TFS1, TFS2.
  unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FF1, FF2, TFS1, TFS2.
  assert (QIN : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  assert (DSTB : 0 <= p /\ p + k <= 2 ^ 47 /\ forall a, p <= a < p + k -> (tb <= a < tb + 24) \/ exists B m, In (B, m) (PM.parser_own s) /\ B <= a < B + m).
  { destruct DST as [(_ & D1 & D2)|(c & n & q & E & D1 & D2)].
    - split; [lia|]. split; [lia|]. intros a Ha. left. lia.
    - assert (IN : In (q, c) (PM.parser_own s)) by (unfold PM.parser_own; rewrite E; cbn; right; right; left; reflexivity).
      destruct (BRB (q, c) ltac:(apply in_or_app; left; exact IN)) as (Q0 & Q4). cbn [fst snd] in Q0, Q4.
      split; [lia|]. split; [lia|]. intros a Ha. right. exists q, c. split; [exact IN| lia]. }
  destruct DSTB as (Dp0 & Dp1 & DIN).
  pose proof (PECREADA.src_read_gen L ar C HI LY HIok IL ICok ILY FB) as SR. cbn [pa_src_read AD PeCLayoutA.CADDR_A] in SR.
  apply (SR fx R M model K LBX FF LK Aw cr (S - 192) X fb pl s str sm [(p, k)] HH AM K0 ENT FRM FRS' FOK).
  { rewrite L5K.rl10. exact A10. }
  { exists p, k. rewrite L5SAR.r11, L5SAR.r12. split; [exact A11|]. split; [exact A12|]. split; [exact Hk|].
    unfold PMSPA.read_dst. right. exact DST. }
  { exists p, k. rewrite L5SAR.r11, L5SAR.r12. split; [exact A11|]. split; [exact A12|]. split; [lia|]. split; [unfold PM.CHUNK in Hk; lia| reflexivity]. }
  { exact PA. } { exact IA. } { exact BASE. } { exact ACC. } { exact INCS. } { exact POK. } { exact CT. }
  intros fx' R' M' model' LK' Aw' src' sm' RP PA' IA' STEP RES ZR HP MRT' ILK' IAW' AM' HH'.
  rewrite (pst_with_src s src') in PA'.
  change (PMSPA.pm_scr 4) with 20480 in HP.
  destruct RES as (CW & p' & k' & d & Y11 & Y12 & Hp' & Hk' & Hkk & Y10 & Hd & CONS & SHORT & DEF' & BYT).
  assert (pk : p' = p /\ k' = k).
  { rewrite L5SAR.r11 in Y11. rewrite L5SAR.r12 in Y12. rewrite A11 in Y11. rewrite A12 in Y12. apply (f_equal bv_unsigned) in Y11, Y12.
    unfold PM.CHUNK in Hk, Hk'. rewrite !L5.unsigned_lit in Y11, Y12 by lia. split; congruence. }
  destruct pk as (-> & ->).
  assert (QC : PM.sr_qc src' = PM.sr_qc (PM.p_src s)) by (destruct STEP as (E & _); exact E).
  assert (WAPP' : PMKA.wapp (PMSPA.W_src AD fb (PM.p_src s) ++ [(p, k)])).
  { apply (wapp_src M s cr LK Aw _ p k HH). unfold BIGSHADOW_LO, BIGSHADOW_HI.
    destruct DST as [(_ & D1 & D2)|(c & n & q & E & D1 & D2)]; [clear - D1 D2 TBIG; lia|].
    assert (IN : In (q, c) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; unfold PM.parser_own; rewrite E; cbn; right; right; left; reflexivity).
    destruct (WB _ IN) as ((_ & _ & _ & _ & _ & (_ & QAPP & _)) & _). cbn [fst snd] in QAPP. unfold BIGSHADOW_LO, BIGSHADOW_HI in QAPP. clear - QAPP D1 D2; lia. }
  apply (NEXT fx' R' M' model' LK' Aw' src' sm' d RP Y10 Hd CONS SHORT ltac:(intros D0; apply ZR; clear - D0 CONS; lia) STEP BYT).
  { intros l Hl1 Hl2. exact (tb_keep M M' s cr LK Aw _ 20480 p k l HH PA HP WAPP' Hl1 Hl2). }
  destruct (callee_mem M M' (PM.parser_own s) 20480 (PMSPA.W_src AD fb (PM.p_src s) ++ [(p, k)]) MR SV LC ltac:(lia) ltac:(lia) TOP HP) as (MR' & SV' & LC' & EKn).
  { intros a CA OW r0 Hr0 Hin. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
    - unfold PMSPA.W_src in Hr0. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
      + apply (OW r0); [unfold W0; apply in_or_app; left; exact Hr0| exact Hin].
      + apply (PMARS1.own_not_aclient L ar C HI HIok (PM.parser_own s) LBX FF LK cr Aw M _ (PM.sr_qc (PM.p_src s)) PM.CHUNK a S 22528 HH);
          [left; reflexivity| unfold L5.in_rng in Hin; cbn [fst snd] in Hin; exact Hin| exact CA].
    - unfold L5.in_rng in Hin. cbn [fst snd] in Hin. destruct (DIN a Hin) as [X0|(B & m & HB & Ha)].
      + apply (OW (PMSPA.o_tb AD fb, 24)); [unfold W0; apply in_or_app; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; exact X0].
      + apply (PMARS1.own_not_aclient L ar C HI HIok (PM.parser_own s) LBX FF LK cr Aw M _ B m a S 22528 HH HB Ha CA). }
  { intros a Ha r0 Hr0 Hin. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
    - unfold PMSPA.W_src in Hr0. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
      + exact (outside_W0 a ltac:(lia) r0 ltac:(unfold W0; apply in_or_app; left; exact Hr0) Hin).
      + destruct (WB _ QIN) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold PM.CHUNK in *. lia.
    - unfold L5.in_rng in Hin. cbn [fst snd] in Hin. destruct (DIN a Hin) as [X0|(B & m & HB & Ha')]; [lia|].
      destruct (WB (B, m) ltac:(apply in_or_app; left; exact HB)) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4. lia. }
  split; [exact MR'|]. split; [exact SV'|]. split; [exact LC'|]. split; [exact PA'|]. split; [exact IA'|].
  split.
  { apply (PMASKJ.base_keep L ar C LY LBX FF S 22528 W0 M M' EKn); [| exact BASE].
    intros a Ha. apply outside_W0. pose proof (PMASKJ.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI. lia. }
  split; [exact TBOK|]. split; [rewrite (own_with_src s src' QC); exact HH'|]. split; [exact AM'|].
  split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT']|].
  split; [intros x Hx; apply ILK; apply ILK'; exact Hx|]. split; [intros x Hx; apply IAW'; apply IAW; exact Hx|].
  split; [exact CRL|]. split; [exact CRK|].
  pose proof (PMASKJ.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof HP as (EKr & _).
  assert (AOI : PMSPA.aobjA FF ois 272) by (apply (PMASKJ.aobj_fb FF fb); [exact FOK| clear - Eois; lia| clear - Eois; lia]).
  split.
  { cbn [PMSPA.with_src PM.p_src]. apply (PMFA.accA_agree M M' op PECA.RDR_BYTES); [| exact ACC].
    apply (PMKA.agsh_obj L ar _ FF (S - 192) 20480 _ M M' EKr WAPP' FRB op PECA.RDR_BYTES).
    apply (PMASKJ.aobj_fb FF fb); [exact FOK| clear - Eop; lia| unfold PECA.RDR_BYTES; clear - Eop; lia]. }
  cbn [PMSPA.with_src PM.p_src]. destruct CW as (CPOS' & CBW' & CST2').
  apply (content_step M M' s sm cr LK Aw _ 20480 _ src' sm' HH IA HP WAPP'); [| | exact (proj1 CPOS')| exact CBW'| exact CST2'| exact CT].
  - intros i Hi r0 Hr0 Hin. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
    + unfold PMSPA.W_src, PMSPA.W_srcf in Hr0. fold os ois in Hr0. cbn [app] in Hr0. unfold L5.in_rng in Hin.
      destruct Hr0 as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin; [clear - Hi Hin Eos Eois; lia| clear - Hi Hin; lia| clear - Hi Hin; lia|].
      destruct (WB _ QIN) as (_ & _ & _ & _ & _ & FA & _). cbn [fst snd] in FA.
      destruct (FA (fb, 5, rs) (in_or_app _ _ _ (or_introl Hfb))) as [X0|X0]; cbn [ff_addr ff_class fst snd] in X0; change (ff_bytes 5) with 2048 in X0; clear - Hi Hin X0 Eois; unfold PM.CHUNK in *; lia.
    + unfold L5.in_rng in Hin. cbn [fst snd] in Hin. destruct (DIN i Hin) as [X0|(B & m & HB & Hi')]; [clear - Hi X0 Eois Etb; lia|].
      destruct (PMASKJ.blk_obj_apart L ar C HI HIok _ FF LK cr Aw M _ B m ois 272 HH ltac:(apply in_or_app; left; exact HB) AOI) as [Zb|Zb]; clear - Hi Hi' Zb; lia.
  - intros c1 n1 q1 E i Hi r0 Hr0 Hin. assert (SIN : In (q1, c1) (PM.parser_own s ++ LBX)) by (apply in_or_app; right; apply INCS; rewrite E; left; reflexivity).
    apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
    + unfold PMSPA.W_src, PMSPA.W_srcf in Hr0. fold os ois in Hr0. cbn [app] in Hr0. unfold L5.in_rng in Hin.
      destruct (WB _ SIN) as (_ & _ & _ & _ & _ & FA & _). cbn [fst snd] in FA.
      destruct (FA (fb, 5, rs) (in_or_app _ _ _ (or_introl Hfb))) as [X0|X0]; cbn [ff_addr ff_class fst snd] in X0; change (ff_bytes 5) with 2048 in X0;
        (destruct Hr0 as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin; [clear - Hi Hin X0 Eos Eois; lia| clear - Hi Hin X0 Eois; lia| clear - Hi Hin X0 Eois; lia|]).
      *
        assert (NE : q1 <> PM.sr_qc (PM.p_src s)).
        { intros EQ. apply (PMASKJ.fst_neq_appA (PM.parser_own s) LBX (PM.sr_qc (PM.p_src s)) PM.CHUNK q1 c1 (PMASKJ.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH)); [left; reflexivity| apply INCS; rewrite E; left; reflexivity| symmetry; exact EQ]. }
        destruct (PMASKJ.blk_apart L ar C HI HIok _ _ _ _ _ _ _ _ _ _ _ HH SIN QIN NE) as [Zb|Zb]; clear - Hi Hin Zb; lia.
      * assert (NE : q1 <> PM.sr_qc (PM.p_src s)).
        { intros EQ. apply (PMASKJ.fst_neq_appA (PM.parser_own s) LBX (PM.sr_qc (PM.p_src s)) PM.CHUNK q1 c1 (PMASKJ.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH)); [left; reflexivity| apply INCS; rewrite E; left; reflexivity| symmetry; exact EQ]. }
        destruct (PMASKJ.blk_apart L ar C HI HIok _ _ _ _ _ _ _ _ _ _ _ HH SIN QIN NE) as [Zb|Zb]; clear - Hi Hin Zb; lia.
    + unfold L5.in_rng in Hin. cbn [fst snd] in Hin. destruct (DIN i Hin) as [X0|(B & m & HB & Hi')].
      * destruct (WB _ SIN) as (_ & _ & _ & _ & _ & FA & _). cbn [fst snd] in FA.
        destruct (FA (fb, 5, rs) (in_or_app _ _ _ (or_introl Hfb))) as [X1|X1]; cbn [ff_addr ff_class fst snd] in X1; change (ff_bytes 5) with 2048 in X1; clear - Hi X0 X1 Etb; lia.
      *
        assert (NE : q1 <> B).
        { intros EQ. apply (PMASKJ.fst_neq_appA (PM.parser_own s) LBX B m q1 c1 (PMASKJ.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH)); [exact HB| apply INCS; rewrite E; left; reflexivity| symmetry; exact EQ]. }
        destruct (PMASKJ.blk_apart L ar C HI HIok _ _ _ _ _ _ _ _ _ _ _ HH SIN ltac:(apply in_or_app; left; exact HB) NE) as [Zb|Zb]; clear - Hi Hi' Zb; lia.
Qed.

Lemma call_filltb (fx : FPState) R M model s sm cr LK Aw (p X c0 n0 q0 : Z) :
  getr R (reg 1) = Z_to_bv 64 X -> L5.ra_ok X -> getr R (reg 2) = Z_to_bv 64 (S - 192) -> kept_rs R ->
  getr R (reg 10) = Z_to_bv 64 os -> getr R (reg 11) = Z_to_bv 64 p -> getr R (reg 12) = Z_to_bv 64 PM.CHUNK ->
  PM.p_tb s = PM.VLong c0 n0 q0 -> q0 <= p -> p + PM.CHUNK <= q0 + c0 -> st_ok M model s sm cr LK Aw -> PM.sr_rem (PM.p_src s) = 0 ->
  (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (sm' : PM.strm) (c : Z),
     regs_preserved R R' -> getr R' (reg 10) = Z_to_bv 64 c -> 0 <= c <= PM.CHUNK -> PM.sm_g sm' = PM.sm_g sm + c ->
     (c < PM.CHUNK -> PM.sm_g sm' = PM.sm_eg sm /\ PM.sm_st sm' = 2) -> (PM.sm_st sm = 2 -> c = 0) ->
     PMSPA.src_step (PM.p_src s) (PM.p_src s) sm sm' ->
     L5.bytes_at RSEGS M' p (UbjRef.slice pl (blen pl - (PM.sm_eg sm - PM.sm_g sm)) c) ->
     (forall l, PM.vs_data tb (PM.p_tb s) + Z.of_nat (length l) <= p -> Z.of_nat (length l) <= PM.vs_size (PM.p_tb s) ->
        L5.bytes_at RSEGS M (PM.vs_data tb (PM.p_tb s)) l -> L5.bytes_at RSEGS M' (PM.vs_data tb (PM.p_tb s)) l) ->
     st_ok M' model' s sm' cr LK' Aw' ->
     srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx' R' X M' model') K) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb58c8 M model) K.
Proof using All.
  intros A1 RAX A2 KP A10 A11 A12 ETB D1 D2 SO RZ NEXT.
  destruct (centry R M model s sm cr LK Aw X 3 A1 RAX A2 KP SO ltac:(lia)) as (ENT & FRM & FRS').
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK & ACC & CT).
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & TOP & NDL & NDF & _).
  pose proof fbb as (F1024 & rs & Hfb). pose proof geo as (Eop & Eos & Eois & Etb).
  destruct (WF _ Hfb) as (FF1 & FF2 & _). cbn [ff_addr ff_class fst snd] in FF1, FF2. change (ff_bytes 5) with 2048 in FF2.
  unfold app_mem, FS_BYTES in FSAPP, FSCEIL, FF1, FF2.
  assert (QIN : In (PM.sr_qc (PM.p_src s), PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
  assert (IN : In (q0, c0) (PM.parser_own s)) by (unfold PM.parser_own; rewrite ETB; cbn; right; right; left; reflexivity).
  destruct (WB (q0, c0) ltac:(apply in_or_app; left; exact IN)) as ((Q0 & _ & _ & _ & Q4 & _) & _). cbn [fst snd] in Q0, Q4.
  pose proof FBT as SR. unfold PECFILLTBA.cfill_tb_spec, PECSPA.csrc_spec in SR. cbn [pa_fill_buffer AD PeCLayoutA.CADDR_A] in SR.
  apply (SR fx R M model K LBX FF LK Aw cr (S - 192) X fb pl s str sm [(p, PM.CHUNK)] HH AM K0 ENT FRM FRS' FOK).
  { clear - A16. replace (S - 192) with (S + (-12) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  { rewrite L5K.rl10. exact A10. }
  { unfold PMSPA.tbfill_args. exists p. rewrite L5SAR.r11, L5SAR.r12. split; [exact A11|]. split; [exact A12|]. exists c0, n0, q0. split; [exact ETB|]. lia. }
  { unfold PMSPA.tbfill_W. exists p. rewrite L5SAR.r11. split; [exact A11|]. split; [unfold PM.CHUNK in *; lia| reflexivity]. }
  { exact PA. } { exact IA. } { exact BASE. } { exact ACC. } { exact INCS. } { exact POK. } { exact CT. }
  intros fx' R' M' model' LK' Aw' src' sm' RP PA' IA' STEP RES HP MRT' ILK' IAW' AM' HH'.
  change (PMSPA.pm_scr 3) with 18432 in HP.
  destruct RES as (-> & p'' & c & Y11 & Y10 & Hc & G & RSC & RS2 & DEF' & CHK & ST2').
  assert (Epw : Z_to_bv 64 p'' = Z_to_bv 64 p) by (rewrite <- A11; symmetry; rewrite <- L5SAR.r11; exact Y11).
  apply (bytes_at_samew M' p'' p _ Epw) in CHK. clear DEF' Y11 Epw.
  rewrite pst_eta in PA'.
  assert (WAPP' : PMKA.wapp (PMSPA.W_src AD fb (PM.p_src s) ++ [(p, PM.CHUNK)])).
  { apply (wapp_src M s cr LK Aw _ p PM.CHUNK HH). destruct (WB _ ltac:(apply in_or_app; left; exact IN)) as ((_ & _ & _ & _ & _ & (_ & QAPP & _)) & _). cbn [fst snd] in QAPP.
    unfold BIGSHADOW_LO, BIGSHADOW_HI in *. clear - QAPP D1 D2; lia. }
  apply (NEXT fx' R' M' model' LK' Aw' sm' c RP Y10 Hc G RSC RS2 STEP CHK).
  { intros l Hl1 Hl2. exact (tb_keep M M' s cr LK Aw _ 18432 p PM.CHUNK l HH PA HP WAPP' Hl1 Hl2). }
  destruct (callee_mem M M' (PM.parser_own s) 18432 (PMSPA.W_src AD fb (PM.p_src s) ++ [(p, PM.CHUNK)]) MR SV LC ltac:(lia) ltac:(lia) TOP HP) as (MR' & SV' & LC' & EKn).
  { intros a CA OW r0 Hr0 Hin. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
    - unfold PMSPA.W_src in Hr0. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
      + apply (OW r0); [unfold W0; apply in_or_app; left; exact Hr0| exact Hin].
      + apply (PMARS1.own_not_aclient L ar C HI HIok (PM.parser_own s) LBX FF LK cr Aw M _ (PM.sr_qc (PM.p_src s)) PM.CHUNK a S 22528 HH);
          [left; reflexivity| unfold L5.in_rng in Hin; cbn [fst snd] in Hin; exact Hin| exact CA].
    - unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
      apply (PMARS1.own_not_aclient L ar C HI HIok (PM.parser_own s) LBX FF LK cr Aw M _ q0 c0 a S 22528 HH IN ltac:(unfold PM.CHUNK in *; lia) CA). }
  { intros a Ha r0 Hr0 Hin. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
    - unfold PMSPA.W_src in Hr0. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
      + exact (outside_W0 a ltac:(lia) r0 ltac:(unfold W0; apply in_or_app; left; exact Hr0) Hin).
      + destruct (WB _ QIN) as ((Q0' & _ & _ & _ & Q4' & _) & _). cbn [fst snd] in Q0', Q4'. unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold PM.CHUNK in *. lia.
    - unfold L5.in_rng in Hin. cbn [fst snd] in Hin. unfold PM.CHUNK in *. lia. }
  split; [exact MR'|]. split; [exact SV'|]. split; [exact LC'|]. split; [exact PA'|]. split; [exact IA'|].
  split.
  { apply (PMASKJ.base_keep L ar C LY LBX FF S 22528 W0 M M' EKn); [| exact BASE].
    intros a Ha. apply outside_W0. pose proof (PMASKJ.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI. lia. }
  split; [exact TBOK|]. split; [exact HH'|]. split; [exact AM'|].
  split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT']|].
  split; [intros x Hx; apply ILK; apply ILK'; exact Hx|]. split; [intros x Hx; apply IAW'; apply IAW; exact Hx|].
  split; [exact CRL|]. split; [exact CRK|].
  pose proof (PMASKJ.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof HP as (EKr & _).
  split.
  { apply (PMFA.accA_agree M M' op PECA.RDR_BYTES); [| exact ACC].
    apply (PMKA.agsh_obj L ar _ FF (S - 192) 18432 _ M M' EKr WAPP' FRB op PECA.RDR_BYTES).
    apply (PMASKJ.aobj_fb FF fb); [exact FOK| clear - Eop; lia| unfold PECA.RDR_BYTES; clear - Eop; lia]. }

  assert (AOI : PMSPA.aobjA FF ois 272) by (apply (PMASKJ.aobj_fb FF fb); [exact FOK| clear - Eois; lia| clear - Eois; lia]).
  pose proof CT as (_ & _ & CPOS & _ & _). unfold PEC.pos_of, PM.unread in CPOS. pose proof STEP as (_ & EEG & _).
  apply (content_step M M' s sm cr LK Aw _ 18432 _ (PM.p_src s) sm' HH IA HP WAPP'); [| | | | exact ST2'| exact CT].
  - intros i Hi r0 Hr0 Hin. apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
    + unfold PMSPA.W_src, PMSPA.W_srcf in Hr0. fold os ois in Hr0. cbn [app] in Hr0. unfold L5.in_rng in Hin.
      destruct Hr0 as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin; [clear - Hi Hin Eos Eois; lia| clear - Hi Hin; lia| clear - Hi Hin; lia|].
      destruct (WB _ QIN) as (_ & _ & _ & _ & _ & FA & _). cbn [fst snd] in FA.
      destruct (FA (fb, 5, rs) (in_or_app _ _ _ (or_introl Hfb))) as [X0|X0]; cbn [ff_addr ff_class fst snd] in X0; change (ff_bytes 5) with 2048 in X0; clear - Hi Hin X0 Eois; unfold PM.CHUNK in *; lia.
    + unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
      destruct (PMASKJ.blk_obj_apart L ar C HI HIok _ FF LK cr Aw M _ q0 c0 ois 272 HH ltac:(apply in_or_app; left; exact IN) AOI) as [Zb|Zb]; clear - Hi Hin Zb D1 D2; unfold PM.CHUNK in *; lia.
  - intros c1 n1 q1 E i Hi r0 Hr0 Hin. assert (SIN : In (q1, c1) (PM.parser_own s ++ LBX)) by (apply in_or_app; right; apply INCS; rewrite E; left; reflexivity).
    apply in_app_or in Hr0. destruct Hr0 as [Hr0|[<-|[]]].
    + unfold PMSPA.W_src, PMSPA.W_srcf in Hr0. fold os ois in Hr0. cbn [app] in Hr0. unfold L5.in_rng in Hin.
      destruct (WB _ SIN) as (_ & _ & _ & _ & _ & FA & _). cbn [fst snd] in FA.
      destruct (FA (fb, 5, rs) (in_or_app _ _ _ (or_introl Hfb))) as [X0|X0]; cbn [ff_addr ff_class fst snd] in X0; change (ff_bytes 5) with 2048 in X0;
        (destruct Hr0 as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hin; [clear - Hi Hin X0 Eos Eois; lia| clear - Hi Hin X0 Eois; lia| clear - Hi Hin X0 Eois; lia|]).
      * assert (NE : q1 <> PM.sr_qc (PM.p_src s)).
        { intros EQ. apply (PMASKJ.fst_neq_appA (PM.parser_own s) LBX (PM.sr_qc (PM.p_src s)) PM.CHUNK q1 c1 (PMASKJ.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH)); [left; reflexivity| apply INCS; rewrite E; left; reflexivity| symmetry; exact EQ]. }
        destruct (PMASKJ.blk_apart L ar C HI HIok _ _ _ _ _ _ _ _ _ _ _ HH SIN QIN NE) as [Zb|Zb]; clear - Hi Hin Zb; lia.
      * assert (NE : q1 <> PM.sr_qc (PM.p_src s)).
        { intros EQ. apply (PMASKJ.fst_neq_appA (PM.parser_own s) LBX (PM.sr_qc (PM.p_src s)) PM.CHUNK q1 c1 (PMASKJ.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH)); [left; reflexivity| apply INCS; rewrite E; left; reflexivity| symmetry; exact EQ]. }
        destruct (PMASKJ.blk_apart L ar C HI HIok _ _ _ _ _ _ _ _ _ _ _ HH SIN QIN NE) as [Zb|Zb]; clear - Hi Hin Zb; lia.
    + unfold L5.in_rng in Hin. cbn [fst snd] in Hin.
      assert (NE : q1 <> q0).
      { intros EQ. apply (PMASKJ.fst_neq_appA (PM.parser_own s) LBX q0 c0 q1 c1 (PMASKJ.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH)); [exact IN| apply INCS; rewrite E; left; reflexivity| symmetry; exact EQ]. }
      destruct (PMASKJ.blk_apart L ar C HI HIok _ _ _ _ _ _ _ _ _ _ _ HH SIN ltac:(apply in_or_app; left; exact IN) NE) as [Zb|Zb]; clear - Hi Hin Zb D1 D2; unfold PM.CHUNK in *; lia.
  - unfold PEC.pos_of, PM.unread. rewrite RZ in *. clear - CPOS G Hc EEG. lia.
  - rewrite RZ. unfold UbjRef.slice. cbn [Z.to_nat firstn]. apply PECSD.bytes_at_nil.
Qed.

Lemma lregs_keep R R1 w : lregs R w -> (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25]%nat -> getr R1 (reg x) = getr R (reg x)) -> lregs R1 w.
Proof.
  intros (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & KP) E.
  unfold lregs. rewrite !E by (cbn; tauto). repeat split; try assumption.
  intros x Hx. rewrite E by (cbn in Hx |- *; tauto). apply KP. exact Hx.
Qed.
Lemma lregs_pres R R' w : regs_preserved R R' -> lregs R w -> lregs R' w.
Proof. intros RP LR. apply (lregs_keep R R' w LR). intros x Hx. apply (L5SAR.cs_of_preserved R R' x RP). unfold L5SAR.cs_all. cbn in Hx |- *. tauto. Qed.

Lemma lregs_set R R1 w w' : lregs R w -> (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23]%nat -> getr R1 (reg x) = getr R (reg x)) ->
  getr R1 (reg 25) = Z_to_bv 64 w' -> lregs R1 w'.
Proof.
  intros (A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & KP) E E25.
  unfold lregs. rewrite !E by (cbn; tauto). repeat split; try assumption.
  intros x Hx. rewrite E by (cbn in Hx |- *; tauto). apply KP. exact Hx.
Qed.

Lemma ro_step (fx fx1 : FPState) R (pc : Z) R1 (pc1 : Z) M model s sm cr LK Aw (M1v : word -> option byte) :
  st_ok M model s sm cr LK Aw ->
  msteps RSEGS (L5SAR.st fx R pc (mrestrict (ahid Aw model) M)) (L5SAR.st fx1 R1 pc1 M1v) ->
  mem_grows (mrestrict (ahid Aw model) M) M1v ->
  (forall a, 0 <= a < 2 ^ 64 -> M1v (Z_to_bv 64 a) = mrestrict (ahid Aw model) M (Z_to_bv 64 a)) ->
  (forall model1, st_ok M model1 s sm cr LK Aw -> srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 pc1 M model1) K) ->
  srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R pc M model) K.
Proof using All.
  intros SO MS MG FRZ NEXT.
  pose proof SO as (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK & ACC & CT).
  unfold PMSPA.cfg.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R pc R1 pc1 M1v K HH AM MS MG FRZ).
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1.
  assert (E : M1 = M) by (apply L5SAR.mem_eq_of_agree; exact FR1). subst M1.
  apply NEXT. split; [exact MR|]. split; [exact SV|]. split; [exact LC|]. split; [exact PA|]. split; [exact IA|]. split; [exact BASE|].
  split; [exact TBOK|]. split; [exact HH1|]. split; [exact AM1|].
  split; [eapply L5LZ.model_rt_trans; [exact MRT| exact MRT1]|]. split; [exact ILK|]. split; [exact IAW|]. split; [exact CRL|]. split; [exact CRK|].
  split; [exact ACC| exact CT].
Qed.

Lemma vpack M model s sm cr LK Aw :
  st_ok M model s sm cr LK Aw ->
  let H := ahid Aw model in let MV := mrestrict H M in
  L5.img_clear MV 65536 1286144 /\ L5.u64_at RSEGS MV 1317368 2147450880 /\ L5.u32_at RSEGS MV 1317376 1
  /\ (140735332487360 <= S <= 2 ^ 47 /\ S mod 16 = 0 /\ L5.writable RSEGS MV (S - 192) 192)
  /\ (forall k v, 8 <= k <= 192 -> L5.u64_at RSEGS M (S - k) v -> L5.u64_at RSEGS MV (S - k) v)
  /\ (6914048 <= os <= 140737488355032 /\ os mod 8 = 0 /\ (2147446784 + 17592186048512 <= os \/ os + 296 <= 2147446784))
  /\ L5KA.zeros_at MV ((os + 8) / 8 + 2147450880) 36 /\ L5.writable RSEGS MV os 296 /\ (forall a n, os <= a -> a + n <= os + 296 -> L5A.avis H a n)
  /\ (6914048 <= tb <= 140737488355304 /\ tb mod 8 = 0 /\ (2147446784 + 17592186048512 <= tb \/ tb + 24 <= 2147446784))
  /\ L5KA.zeros_at MV (tb / 8 + 2147450880) 3 /\ L5.writable RSEGS MV tb 24 /\ (forall a n, tb <= a -> a + n <= tb + 24 -> L5A.avis H a n)
  /\ os + 296 <= S - 192 /\ tb + 24 <= S - 192 /\ PMSPA.aobjA FF os 296 /\ PMSPA.aobjA FF tb 24.
Proof using All.
  intros (MR & SV & LC & PA & IA & BASE & TBOK & HH & AM & MRT & ILK & IAW & CRL & CRK & ACC & CT) H MV.
  pose proof MR as (EK & DK & STK). pose proof STK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  pose proof (PMASKJ.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (V0 & V1 & V2).
  pose proof (PMASKJ.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model S 22528 192 HH STK ltac:(lia)) as (SL80 & SH80 & V3).
  pose proof (PMASKJ.src_vis L ar C HI LY HIok _ FF LK cr Aw M model fb ois s S 22528 HH FOK PA STK)
    as ((O1 & O8 & OBIG) & OZ & OW & OCE & OAV & AO & OFS1 & OFS2).
  pose proof (PMARSK.tb_vis L ar C HI LY HIok _ FF LK cr Aw M model fb ois s HH FOK PA)
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

Definition lstate (R : bvmap 5 word) (M : word -> option byte) (model : Model) (s : PM.pst) (sm : PM.strm) (cr : credit) (LK : list fframe) (Aw : list (Z * Z)) (w : Z) : Prop :=
  lregs R w /\ st_ok M model s sm cr LK Aw /\ acct s sm w /\ 1 <= w <= len /\ TX M (PM.p_tb s) (len - w).
Definition IHt (mu0 : Z) : Prop :=
  forall (fx : FPState) R M model s sm cr LK Aw w, PM.mu_src (PM.p_src s) sm < mu0 -> lstate R M model s sm cr LK Aw w ->
    srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx R 0xb7714 M model) K.

End Call.
End WithHeap.
End PECSRD1A.
