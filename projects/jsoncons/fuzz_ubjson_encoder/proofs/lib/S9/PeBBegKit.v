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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx PmSpecsA PmSpecsAX PeSpecsAb.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModelFactsA PeStepAB0 PmStep PmParStep PmParKit PeBSrcKitJ PeBParKit PeBCReset1.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMBBK.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.

Definition push_st (s : PM.pst) (b k : Z) (c : PM.pstate) : PM.pst :=
  PM.PST (PM.p_more s) (PM.p_done s) (PM.p_depth s) (PM.p_src s) (PM.p_tb s) (PM.p_tg s) b k (PM.p_stk s ++ [c]).

Lemma aacc_sub (M : word -> option byte) a k a' k' : aacc M a k -> a <= a' -> a' + k' <= a + k -> aacc M a' k'.
Proof. intros AC H1 H2 x Hx. apply AC. lia. Qed.

Lemma parser_push_updA (M M' : word -> option byte) op ois s b' k' c :
  PM.parser_at RSEGS PeCLayoutB.CADDR_B PMSPA.accA PMSPA.annA M op ois s -> 0 <= op -> op + 384 <= 2 ^ 64 ->
  PMFA.agA M M' op 360 -> PMFA.agsh M M' op 384 -> L5.defined M' op 384 ->
  PM.vec_at RSEGS PMSPA.accA PMSPA.annA M' (op + 360) b' k' (PM.p_stk s ++ [c]) ->
  0 <= PM.sr_qc (PM.p_src s) -> PM.sr_qc (PM.p_src s) + PM.CHUNK <= 2 ^ 64 -> PMFA.agA M M' (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  (forall c0 n p, PM.p_tb s = PM.VLong c0 n p -> PMFA.agA M M' p c0) ->
  PM.parser_at RSEGS PeCLayoutB.CADDR_B PMSPA.accA PMSPA.annA M' op ois (push_st s b' k' c).
Proof.
  intros (H0 & D & C24 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3) Ho Ho' AG SH D' VEC' Hq Hq' AGQ AGT.
  pose proof AG as [AGd _].
  unfold push_st, PM.parser_at. cbn [PM.p_more PM.p_done PM.p_depth PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_stk].
  assert (AG4 : forall a n, op <= a -> a + n <= op + 360 -> PMFA.agA M M' a n).
  { intros a n X1 X2. split; [eapply (L5C.agree_on_sub M M'); [exact AGd|lia|lia]| intros x Hx; apply SH; lia]. }
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply (AG4 op 8); lia| lia| lia| exact H0]|].
  split; [exact D'|].
  split; [apply (PMFA.accA_agree M M' op 24); [intros x Hx; apply SH; lia| exact C24]|].
  split; [apply (L5C.u8_at_agree RSEGS M M'); [apply (AG4 (op + 8) 1); lia|lia|lia|exact H8]|].
  split; [apply (L5C.u8_at_agree RSEGS M M'); [apply (AG4 (op + 9) 1); lia|lia|lia|exact H9]|].
  split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 12) 4); lia|lia|lia|exact H12]|].
  split; [apply (L5C.u8_at_agree RSEGS M M'); [apply (AG4 (op + 16) 1); lia|lia|lia|exact H16]|].
  split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 20) 4); lia|lia|lia|exact H20]|].
  split; [apply (PMFA.nullis_at_agreeA RSEGS PeCLayoutB.CADDR_B M M' (op + 32)); [lia|lia| apply AG4; lia| exact NI]|].
  split; [apply (PMFA.src_fields_at_agreeA RSEGS M M' (op + 24)); [lia|lia|exact Hq|exact Hq'| apply AG4; lia| exact AGQ| exact SRC]|].
  split; [apply (PMF.u32_at_agree RSEGS M M'); [apply (AG4 (op + 320) 4); lia|lia|lia|exact H320]|].
  split; [apply (L5C.u64_at_agree RSEGS M M'); [apply (AG4 (op + 328) 8); lia|lia|lia|exact H328]|].
  split; [apply (PMFA.accA_agree M M' (op + 320) 64); [intros x Hx; apply SH; lia| exact C320]|].
  split; [apply (PMFA.vstr_at_agreeA RSEGS M M' (op + 336)); [lia|lia| apply AG4; lia| exact AGT| exact TB]|].
  split; [exact VEC'|].
  split; [exact B1|]. split; [exact B2| exact B3].
Qed.

Lemma stack_shape_push (stk : list PM.pstate) c : PM.stack_shape stk -> (Z.of_nat (length stk) <= PM.MAX_DEPTH)%Z ->
  PM.pstate_ok c -> ~ PM.mode_bottom (PM.ps_mode c) -> PM.stack_shape (stk ++ [c]).
Proof.
  intros (H1 & H2 & H3 & H4 & H5) HL Hc Hm. unfold PM.stack_shape. rewrite length_app. cbn [length].
  split; [lia|]. split; [rewrite Nat2Z.inj_add; cbn; unfold PM.MAX_DEPTH in *; lia|].
  split; [rewrite app_nth1 by lia; exact H3|].
  split.
  - intros i Hi. destruct (Nat.lt_ge_cases i (length stk)) as [Lt|Ge].
    + rewrite app_nth1 by exact Lt. apply H4. lia.
    + assert (E : i = length stk) by lia. subst i. rewrite app_nth2 by lia. rewrite Nat.sub_diag. exact Hm.
  - intros i Hi. destruct (Nat.lt_ge_cases i (length stk)) as [Lt|Ge].
    + rewrite app_nth1 by exact Lt. apply H5. exact Lt.
    + assert (E : i = length stk) by lia. subst i. rewrite app_nth2 by lia. rewrite Nat.sub_diag. exact Hc.
Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.

Lemma ri_swap12 x y l FF1 LK cr Aw M V : ri_inv HI (x :: y :: l) FF1 LK cr Aw M V -> ri_inv HI (y :: x :: l) FF1 LK cr Aw M V.
Proof. exact (PMBRS1.ri_swap12 L ar C HI HIok x y l FF1 LK cr Aw M V). Qed.

Lemma stk_credit s crc : PM.tb_ok (PM.p_tb s) (PM.p_tg s) -> PM.vs_cap (PM.p_tb s) <= 2 ^ 27 -> 0 <= PM.p_k s <= 10 ->
  PMSPA.credit_le (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s)) crc ->
  acredit_ok L crc (32 * 2 ^ (PM.p_k s + 1))
  /\ forall s', PM.p_k s' = PM.p_k s + 1 -> PM.p_tb s' = PM.p_tb s -> PM.p_tg s' = PM.p_tg s ->
       PMSPA.credit_keep crc (adebit L crc (32 * 2 ^ (PM.p_k s + 1))) (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s)) (PMSPA.scA L (PM.pot_parser (PMSPA.HV L ar) s')).
Proof.
  intros (Tg & Tc & _) Cap Hk (CR1 & CR2). pose proof (PMB.ly_cost L C LY) as (K8 & B3 & BO).
  assert (P : 2 ^ (PM.p_k s + 1 + 1) = 2 * 2 ^ (PM.p_k s + 1)) by (rewrite Z.pow_add_r by lia; lia).
  assert (P11 : 2 ^ (PM.p_k s + 1) <= 2048) by (change 2048 with (2 ^ 11); apply Z.pow_le_mono_r; lia).
  assert (P0 : 1 <= 2 ^ (PM.p_k s + 1)) by (apply (Zpow_facts.Zpower_le_monotone 2 0 (PM.p_k s + 1)); lia).
  unfold PMSPA.scA, PM.pot_parser, PM.credit_add, PM.pot_stack, PM.pot_text, PMSPA.HV, LibIfaceAB.heap_view in *.
  cbn [fst snd HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead] in *. rewrite K8, B3, BO in *.
  split.
  - unfold acredit_ok. rewrite K8, B3, BO. split; lia.
  - intros s' Ek Et Eg. unfold PMSPA.credit_keep, adebit. rewrite K8, B3, BO. cbn [fst snd]. rewrite Ek, Et, Eg, P. split; lia.
Qed.

End WithHeap.
End PMBBK.
