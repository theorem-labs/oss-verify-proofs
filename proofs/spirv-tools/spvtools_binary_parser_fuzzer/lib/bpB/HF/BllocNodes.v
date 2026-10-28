(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Bcfg BAmb BRelSpec BSimInv BExitSim BPropExec BCatExec BCatSim BSeqExec BStreamExec BMmapSim BAllocSim BFileSim BShapeAlg BNodes BStoreOk BAgentLib BAgentNodes Bap04 BRefNodes.
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section ModelLevel.
  Context {SC : StepCfg}.

  Lemma place_not_refusal : forall i m a nZ,
    bv_unsigned (in_sysno i) = 222%Z ->
    place_ok (m_vmmaps m) a nZ = true -> (0 <= nZ)%Z ->
    refusal_b i m a = false.
  Proof.
    intros i m a nZ Hno Hp HnZ. rewrite (refusal_b_mmap i m a Hno).
    apply bv_eqb_neq. intros ->.
    destruct (place_ok_unpack _ _ _ Hp) as (_ & _ & Htop & _).
    pose proof (alloc_top_lt (m_vmmaps m)) as Hlt.
    rewrite (errno_ret_unsigned ENOMEM) in Htop by (unfold ENOMEM; lia).
    unfold ENOMEM, alloc_top, stack_max_size, two_pow_64 in *.
    pose proof (word_unsigned_range (vm_init_sp (m_vmmaps m))). unfold two_pow_64 in *. lia.
  Qed.

  Lemma errno_is_refusal_mmap : forall i m,
    bv_unsigned (in_sysno i) = 222%Z ->
    refusal_b i m (errno_ret ENOMEM) = true.
  Proof. intros i m Hno. rewrite (refusal_b_mmap i m _ Hno). apply bv_eqb_refl. Qed.

  Lemma errno_is_refusal_mprotect : forall i m,
    bv_unsigned (in_sysno i) = 226%Z ->
    refusal_b i m (errno_ret ENOMEM) = true.
  Proof. intros i m Hno. rewrite (refusal_b_mprotect i m _ Hno). apply bv_eqb_refl. Qed.

  Lemma zero_not_refusal_mprotect : forall i m,
    bv_unsigned (in_sysno i) = 226%Z ->
    refusal_b i m (Z_to_bv 64 0) = false.
  Proof.
    intros i m Hno. rewrite (refusal_b_mprotect i m _ Hno). apply bv_eqb_neq.
    intros E. apply (f_equal bv_unsigned) in E. rewrite (errno_ret_unsigned ENOMEM) in E by (unfold ENOMEM; lia).
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. unfold ENOMEM, two_pow_64 in E. lia.
  Qed.

  Lemma alloc_refusal_spurious {AF : AllocForced SC} : forall i m eff eff' m' evs',
    injected_family_off the_scfg i = true ->
    refusal_b i m (eff_ret eff) = true ->
    syscall_spec i m (Ok eff' m' evs') ->
    refusal_b i m (eff_ret eff') = false ->
    spurious_refusal_cfg the_scfg i m eff.
  Proof.
    intros i m eff eff' m' evs' Hoff Hr Hspec Hnr. split; [exact Hoff|]. split; [exact Hr|].
    exists eff', m', evs'. auto.
  Qed.
End ModelLevel.

Section WithSegs.
Variable segs : list Segment.
Context {SC : StepCfg} {AF : AllocForced SC}.

Lemma mprotect_outcome_si : forall ms x8 model (addr : word) (len : Z),
  bv_unsigned x8 = 226%Z ->
  ms_gpr ms 0 = addr -> ms_gpr ms 1 = Z_to_bv 64 len -> ms_gpr ms 2 = Z_to_bv 64 3 ->
  (0 < len)%Z -> (bv_unsigned addr + page_round_up_Z len < 2 ^ 64)%Z ->
  (bv_unsigned addr mod page_size = 0)%Z ->
  let n := Z_to_bv 64 (page_round_up_Z len) in
  map_contains (vm_noaccess (m_vmmaps model)) addr n = true ->
  map_contains (vm_maps (m_vmmaps model)) addr n = true ->
  forall o, syscall_spec (sys_input segs ms x8) model o <->
    mprotect_err_out model o
    \/ (mprotect_budget_ok model addr n = true
        /\ o = Ok (mkEffect (Z_to_bv 64 0) [] [(addr, n)]) (mprotect_model addr n model) []).
Proof.
  intros ms x8 model addr len Hno H0 H1 H2 Hlen Hnw Hal n Hna Hma o.
  pose proof (u64_range addr). pose proof (page_round_up_Z_bounds len ltac:(lia)).
  assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
  rewrite (syscall_spec_226 _ model o) by (rewrite in_sysno_sys_input; exact Hno).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, H0, H2.
  rewrite <- mprotect_model_next_eq.
  rewrite (mprotect_expose_outcome addr (ms_gpr ms 1) (Z_to_bv 64 3) _ model o); rewrite ?Hu1;
    [reflexivity | vm_compute; reflexivity | exact Hal | unfold w_is0; apply bv_eqb_neq; intros E;
     apply (f_equal bv_unsigned) in E; rewrite Hu1 in E; change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E; lia
    | unfold two_pow_64; lia | vm_compute; reflexivity | exact Hna | exact Hma].
Qed.

End WithSegs.
