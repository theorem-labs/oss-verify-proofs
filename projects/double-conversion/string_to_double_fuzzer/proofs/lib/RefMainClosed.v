(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ModelAmb.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec ShapeAlg Spec LibIface RefStartup RefPilotOOM RefMain
  RefUsage RefOpenFail RefOpenFailBranch RefTargetPhase RefTargetPhaseK RefLim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Existing Instance PropExec.fx0.

Lemma usage_stmt_ok : usage_stmt.
Proof.
  unfold usage_stmt. intros sp0 av envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 lim Hva Hve Hvsp Hfits Htid ME Hargc.
  exact (ref_usage_w sp0 av envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 lim Hva Hve Hvsp Hfits Htid ME Hargc).
Qed.

Lemma open_fail_stmt_ok : open_fail_stmt.
Proof.
  unfold open_fail_stmt. intros sp0 a0s path envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 lim Hva Hve Hvsp Hfits Htid ME Hcase.
  destruct Hcase as [Hlong | [Hemp | (Hlen & Hne & Hns & Hnd & Habs)]].
  - exact (ref_open_fail_toolong_w sp0 a0s path envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 lim Hva Hve Hvsp Hfits Htid ME Hlong).
  - exact (ref_open_fail_empty_w sp0 a0s path envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 lim Hva Hve Hvsp Hfits Htid ME Hemp).
  - exact (ref_open_fail_absent_w sp0 a0s path envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 lim Hva Hve Hvsp Hfits Htid ME
             Hlen Hne Hns Hnd Habs).
Qed.

Lemma open_err_stmt_ok {AL : AllocLim} : open_err_stmt.
Proof.
  unfold open_err_stmt. intros sp0 a0s path envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Hfits ME.
  exact (open_err_branch_cannot_open sp0 a0s path envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Hfits ME).
Qed.


Theorem ref_realizes_spec_closed {AL : AllocLim} : LibIface.lib_stmt_P ->
  forall sp brk mbase (rdraw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk rsegs brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    realizes rsegs
      (init_config rsegs rpc rph sp brk mbase rdraw LIM inp)
      (spec (in_argv inp) (in_fs inp)).
Proof.
  intros HLP.
  exact (ref_realizes_spec (RefTargetPhase.target_phase HLP) (RefTargetPhaseK.target_phase_k HLP)
           usage_stmt_ok open_fail_stmt_ok open_err_stmt_ok).
Qed.
