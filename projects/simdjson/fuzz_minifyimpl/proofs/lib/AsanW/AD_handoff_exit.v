(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import MainExport MainFactsAsan.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg ARepInit_kit F_syscalls StdioFiles Stdio_kit AExit F_module_dtor_pre AD_handoff_md AD_hokit AAtexit_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section Handoff.
  Variables (V : nat -> Z) (m : word -> option byte).
  Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
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
       rw_cells asegs m 0x6a4d40 [C4 (Z_to_bv 64 (V 44%nat))]                            (* [comment removed for export] *)
    /\ rw_cells asegs m 0x6c5058 [C4 (Z_to_bv 64 0)]                                   (* [comment removed for export] *)
    /\ rw_cells asegs m 0x6c5078 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 (Z_to_bv 64 0)]   (* [comment removed for export] *)
    /\ rw_cells asegs m 0x167010 [C8 (Z_to_bv 64 0x16dbb8)]                           (* [comment removed for export] *)
    /\ rw_cells asegs m 0x16dbd4 [C1 (Z_to_bv 8 0)]                                   (* [comment removed for export] *)
    /\ rw_cells asegs m 0x202260 [C1 (Z_to_bv 8 0)]                                   (* [comment removed for export] *)
    /\ rw_cells asegs m 0x167e20 [C8 (Z_to_bv 64 0x160ca0); C8 (Z_to_bv 64 0x160c90)] (* [comment removed for export] *)
    /\ rw_cells asegs m 0x160c90 [C8 (Z_to_bv 64 0xb45a8); C8 (Z_to_bv 64 0x5a2b8)]  (* [comment removed for export] *)
    /\ rw_cells asegs m 0x16cd50 [C1 (Z_to_bv 8 0)]                                   (* [comment removed for export] *)
    /\ rw_cells asegs m 0x166fe8 [C8 (Z_to_bv 64 0x1478f8); C8 (Z_to_bv 64 0)]       (* [comment removed for export] *)
    /\ rw_cells asegs m 0x168e60 [C8 (Z_to_bv 64 0x168e60)]                           (* [comment removed for export] *)
    /\ rw_cells asegs m 0x6c55f0 [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m 0x16ba18 [C8 (Z_to_bv 64 RSTDIN)] /\ rw_cells asegs m RSTDIN stdin_cells
    /\ rw_cells asegs m 0x16bb08 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells asegs m 0x16b928 [C8 (Z_to_bv 64 RSTDERR)]
    /\ rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)].
  Proof. unfold stdin_cells. go. Qed.
End Handoff.
End CANSEC1.
