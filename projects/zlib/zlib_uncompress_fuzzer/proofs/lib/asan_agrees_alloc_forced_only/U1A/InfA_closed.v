(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Tac Arr FP Bytes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg RtCells AProto ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U1A Require Import U2AObj U2AIface U2AIface_fit2_draft InfABase InfAIface InfA_w7base InfA_w6base.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U1A Require Import AdlU UwA ItA_top IfA_top InfA_itcall.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U1A Require Import InfA_stored InfA_copy InfA_lit InfA_check InfA_length InfA_table InfA_lenlensL InfA_codelens InfA_cld3 InfA_w7top InfA_top.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section T.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variable fflag : alayout -> Z -> Z -> Z.
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis AI_fake_flag : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
    rw_cells asegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
    /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
    /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
    /\ ~ in_ranges CI (fflag L cls F).
  Hypothesis AI_fake_release : forall L RNG st LB m cls F N,
    AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
    AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
  Hypothesis SM0 : SM0_stmt AI fflag rng_fs.
  Hypothesis SM2 : SM2_stmt AI fflag rng_fs.

  Lemma ITAB : inflate_table_stmtA AI rng_fs.
  Proof. exact (inflate_table_proofA AI fflag rng_fs AI_fake_flag AI_fake_release SM2). Qed.

  Lemma ENV : forall L RNG LB tp ly, rng_fs L RNG -> atmost1_c2 LB -> tp = Z_to_bv 64 ATP ->
    l_SP ly + 16 < al_top L -> rng RNG (l_lo ly) (al_top L - l_lo ly) -> itcall_env AI rng_fs L RNG LB tp ly.
  Proof. intros L RNG LB tp ly H1 H2 H3 H4 H5. exact (conj ITAB (conj H1 (conj H2 (conj H3 (conj H4 H5))))). Qed.

  Theorem inflate_closed : forall haswin, inflate_stmtA AI rng_fs haswin.
  Proof.
    apply (inflate_core AI fflag rng_fs AI_fake_flag AI_fake_release SM0 (updatewindow_old_proofA AI) (updatewindow_new_proofA AI)).
    - intros. apply stored_arm.
    - intros. apply copy__arm.
    - intros. apply copy_arm.
    - intros. apply garm_arm. apply table_garm. apply (lenlens_garm AI rng_fs); [apply ENV; assumption|].
      apply codelens_garm2. apply (cldone_thm AI rng_fs); [apply ENV; assumption|]. apply (g_LEN_ AI inflate_fast_proofA).
    - intros. apply garm_arm. apply (lenlens_garm AI rng_fs); [apply ENV; assumption|].
      apply codelens_garm2. apply (cldone_thm AI rng_fs); [apply ENV; assumption|]. apply (g_LEN_ AI inflate_fast_proofA).
    - intros. apply garm_arm. apply codelens_garm.
      apply (cldone_thm AI rng_fs); [apply ENV; assumption|]. apply (g_LEN_ AI inflate_fast_proofA).
    - intros. apply (A_LEN_ AI rng_fs inflate_fast_proofA); assumption.
    - intros. apply (A_LEN AI rng_fs inflate_fast_proofA); assumption.
    - intros. apply (A_LENEXT AI rng_fs); assumption.
    - intros. apply (A_DIST AI rng_fs); assumption.
    - intros. apply (A_DISTEXT AI rng_fs); assumption.
    - intros. apply (A_MATCH AI rng_fs); assumption.
    - intros. apply lit_arm.
    - intros. apply check_arm. exact adler32_U.
    - intros. apply length_arm.
  Qed.
End T.
End CANSEC1.
