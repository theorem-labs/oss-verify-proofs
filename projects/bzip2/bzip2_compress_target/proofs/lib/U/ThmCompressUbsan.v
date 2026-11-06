(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW StartupRnd.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Heap Require AllocIface AllocTight AllocCover. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require AllocLayout0. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Heap Require AllocDcv. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require S0H_Iface S0H_Tight S0H_Cover S0H_Entry S0H_EntryTP.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Heap Require AllocIface. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require AllocLayout0. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Heap Require AllocTight AllocCover.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeilLia.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require S0H_Dcv.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Heap.AllocIface OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Heap.AllocTight OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Heap.AllocCover OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Heap.AllocLayout0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Heap.AllocDcv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Heap.S0H_Iface OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Heap.S0H_Tight OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Heap.S0H_Cover OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Heap.S0H_Entry OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Heap.S0H_EntryTP OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.Heap.S0H_Dcv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require LibWritev.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Spec04.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Spec U.S0HarnStmt U.S0B2BCStmt U.S0B2BDStmt U.S0HarnBody U.S0Printf0 U.S0TargetPhase U.S0Printf0Proof U.S0GrowStmt U.S0Grow U.S0Refused U.S0Main.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.LibWritev.ShapeEF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec04 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.S0HarnStmt OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.S0B2BCStmt OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.S0B2BDStmt OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.S0HarnBody OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.S0Printf0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.S0TargetPhase OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.S0Printf0Proof OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.S0GrowStmt OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.S0Grow OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.S0Refused OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.U.S0Main.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Contracts.
  Context {ACEIL__ : ACeil} {RUNW__ : RunW}.
  Hypothesis HARN_S0 : harn_spec S0_alloc S0_cover S0I.

  (* [comment removed for export] *)
  Lemma s0_realizes04 :
    forall sp brk mbase (rnd : EntryDraw) (inp : ProcInput),
      valid_sp sp -> valid_brk s0segs brk -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
      valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
      alloc_ceiling = (bv_unsigned sp - 8388608)%Z ->
      run_guard = bv_unsigned (canary_w rnd) -> run_secret = bv_unsigned (secret_word rnd) ->
      realizes s0segs
        (init_config s0segs Ubsan.M.init_pc
                     Ubsan.M.phdrs sp brk mbase rnd target_alloc_limit inp)
        (spec04 (in_argv inp) (in_fs inp)).
  Proof.
    apply S0Main.ref_realizes_spec.
    - exact (S0TargetPhase.target_phase S0_alloc S0_cover HARN_S0 printf0_first_s0 S0_HE0).
    - exact (S0Grow.big_file_cps S0_alloc S0_tight S0_cover HARN_S0 S0_HTC printf0_first_s0 S0_HE0W
               S0Refused.refused_tail_ok).
  Qed.

End Contracts.

