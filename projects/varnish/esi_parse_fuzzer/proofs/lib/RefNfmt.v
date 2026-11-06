(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec SimInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ShapeAlg Nodes StoreOk AgentLib Agenxn8 RefNodes.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.Stredvh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Agenxn8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefNodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.
Context {BW : BWorld}.

Lemma rz_read_dir_mapped : forall regs (pc : word) mem model w fd (cnt : Z) K,
  fetch_word segs pc = Some w -> is_ecall w = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  getr regs 17 = Z_to_bv 64 63 ->
  getr regs 10 = fd -> (bv_unsigned fd < 2 ^ 32)%Z ->
  fd_lookup (m_fds model) fd = Some FdDir ->
  getr regs 12 = Z_to_bv 64 cnt ->
  (1 <= cnt)%Z -> (cnt <= 2 ^ 24)%Z ->
  (bv_unsigned (getr regs 11) + cnt <= TASK_SIZE)%Z ->
  store_ok segs mem (getr regs 11) (Z.to_nat cnt) = true ->
  realizes segs (mkCfg (mkst (regupd regs 10 (errno_ret EISDIR)) (v_addi pc 4) mem (seg_rom segs)) model) K ->
  realizes segs (mkCfg (mkst regs pc mem (seg_rom segs)) model) K.
Proof.
  intros regs pc mem model w fd cnt K HF HE Hh Hlazy H17 Hfd Hfd32 Hlk H12 Hc1 H64 Hover Hok Hc.
  eapply rz_sys; [exact Hh | exact Hlazy | exact HF | exact HE |].
  eapply rz_ret_only_silent; [exact Hh | reflexivity | | exact Hh | exact Hlazy | rewrite adv_set_epend; exact Hc].
  intros o. rewrite (syscall_spec_63 _ model o) by (rewrite in_sysno_si, H17; apply u64_lit; lia).
  rewrite in_arg0_si, in_arg1_si, in_arg2_si, ms_gpr_epend0, ms_gpr_epend1, ms_gpr_epend2, Hfd, (fd32_id fd Hfd32).
  apply (read_dir_outcome fd _ _ _ model o Hlk).
  apply access_okb_intro. rewrite H12, u64_lit by lia. exact Hover.
Qed.

End WithSegs.
