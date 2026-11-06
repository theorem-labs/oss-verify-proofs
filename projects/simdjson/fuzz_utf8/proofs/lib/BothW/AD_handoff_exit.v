(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AS Require Import MainExport MainFactsBoth.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import BImg ARepInit_kit F_syscalls StdioFiles Stdio_kit AExit F_module_dtor_pre AD_handoff_md AD_hokit AAtexit_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section Handoff.
  Variables (V : nat -> Z) (m : word -> option byte).
  Hypothesis HM : Forall (mfact_ok bsegs V m) both_mem_facts.
  Ltac go := repeat match goal with |- _ /\ _ => split end; ho_cells V m HM.

  (* [comment removed for export] *)
  Lemma mdtor_rt_init : mdtor_rt m.
  Proof. unfold mdtor_rt. go. Qed.
  Lemma mdtor_pre_init : mdtor_pre m.
  Proof.
    unfold mdtor_pre. split; [exact mdtor_rt_init|]. split; [ho_cells V m HM|]. split; [ho_cells V m HM|]. split; [ho_cells V m HM|].
    split; [exact (gdesc_init V m HM)|]. split; [exact (godr_init V m HM)|]. split; [exact (gsh_init V m HM)|].
    exact (garr_init V m HM).
  Qed.

  (* [comment removed for export] *)
  Lemma atexit_main_init : ATEXIT TBL_MAIN m.
  Proof.
    unfold ATEXIT. exists (repeat (Z_to_bv 64 0) 29), (repeat (Z_to_bv 64 0) 29).
    unfold atexit_cells, TBL_MAIN, ATX_FIN, ATX_LOCK, ATX_SLOT, ATX_HEAD, ATX_BUILTIN, ATX_F, ATX_A.
    cbn [rev app map fst snd repeat length Z.of_nat Pos.of_succ_nat Pos.succ].
    repeat match goal with |- _ /\ _ => split end; try reflexivity; ho_cells V m HM.
  Qed.

  (* [comment removed for export] *)
  Lemma exit_cells_init :
       rw_cells bsegs m 0x6afa60 [C4 (Z_to_bv 64 (V 44%nat))]                            (* [comment removed for export] *)
    /\ rw_cells bsegs m 0x6cfd78 [C4 (Z_to_bv 64 0)]                                   (* [comment removed for export] *)
    /\ rw_cells bsegs m 0x6cfd98 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)]   (* [comment removed for export] *)
    /\ rw_cells bsegs m 0x171ff0 [C8 (Z_to_bv 64 0x178878)]                           (* [comment removed for export] *)
    /\ rw_cells bsegs m 0x178894 [C1 (Z_to_bv 8 0)]                                   (* [comment removed for export] *)
    /\ rw_cells bsegs m 0x20cf20 [C1 (Z_to_bv 8 0)]                                   (* [comment removed for export] *)
    /\ rw_cells bsegs m 0x172e08 [C8 (Z_to_bv 64 0x16bf28); C8 (Z_to_bv 64 0x16bf18)] (* [comment removed for export] *)
    /\ rw_cells bsegs m 0x16bf18 [C8 (Z_to_bv 64 0xb38c8); C8 (Z_to_bv 64 0x59000)]  (* [comment removed for export] *)
    /\ rw_cells bsegs m 0x177a10 [C1 (Z_to_bv 8 0)]                                   (* [comment removed for export] *)
    /\ rw_cells bsegs m 0x171fc8 [C8 (Z_to_bv 64 0x152b80); C8 (Z_to_bv 64 0)]       (* [comment removed for export] *)
    /\ rw_cells bsegs m 0x173e60 [C8 (Z_to_bv 64 0x173e60)]                           (* [comment removed for export] *)
    /\ rw_cells bsegs m 0x6d0310 [C8 (Z_to_bv 64 0)] /\ rw_cells bsegs m 0x176de8 [C8 (Z_to_bv 64 RSTDIN)] /\ rw_cells bsegs m RSTDIN stdin_cells
    /\ rw_cells bsegs m 0x176ed8 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells bsegs m 0x176cf8 [C8 (Z_to_bv 64 RSTDERR)]
    /\ rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)].
  Proof. unfold stdin_cells. go. Qed.
End Handoff.
End CANSEC1.
