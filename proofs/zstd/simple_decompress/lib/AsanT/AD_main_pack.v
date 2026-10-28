(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes InitMem RunConst.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter Prog AsanCtrl AsanEmbed Harness ProgA AsanProgDeps AsanHandoff.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib Require Import AsanMain.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AProto AMalloc_iface AProg_kit AHarness_iface Strnlen_iface ADriver_iface AD_main AMain_asm.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section Packed.
  Variable AI : AMallocIface.
  Variable rng_fs : alayout -> footprint -> Prop.
  Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv (aci AI).
  Hypothesis CLI_CI : forall iv, In iv cli_img_ranges -> In iv (aci AI).
  Hypothesis CI_WF : forall iv, In iv (aci AI) -> 0 <= fst iv.
  Hypothesis DMALLOC : dmalloc_stmt AI.
  Hypothesis DFREE : dfree_stmt AI.
  Hypothesis DFREEN : dfree_null_stmt AI.
  Hypothesis ASHENV : ashenv_law AI.
  Hypothesis FUZZ : fuzz_oneA_stmt AI rng_fs.
  Hypothesis HSTRN : strnlen_a_stmt.

  (* [comment removed for export] *)
  Corollary adrv_of_walks : forall (A0 : (nat -> Z) -> alw),
    (forall en inp w V m ms mo,
       valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp -> bmain_open en inp w V m ms mo ->
       atop_of (en_sp en) = ATOP ->
       exists L, apat_mainA AI rng_fs L (RNG0 A0 V mo) inp (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ms) ->
    adrv_stmt A0.
  Proof.
    intros A0 APAT. apply (adrv_of_parts A0 (apat_mainA AI rng_fs) APAT).
    intros L RNG inp s0 ms HP. eapply amain_packed; eassumption.
  Qed.
End Packed.
End CANSEC1.
