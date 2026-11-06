(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RF_syscalls RF_pad R_Exit RF_printf_iface Stdio_iface R_Startup.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.


From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition stderr_cells0 : list cell :=
  file_cells (Z_to_bv 64 5) 0 0 0 F_STDIO_WRITE 0x55410 0 2 (Z_to_bv 64 0) 0xffffffff (repeat (Z_to_bv 8 0) 80).

Lemma stderr_cells0_image : forall (m : word -> option byte),
  (forall a : word, (0x23000 <= bv_unsigned a < 0x56000)%Z -> outside rcrt_written (bv_unsigned a) -> m a = None) ->
  rw_cells rsegs m RSTDERR stderr_cells0.
Proof.
  intros m NONE.
  apply (rw_cells_recast rsegs m RSTDERR [CB (length (cells_bytes stderr_cells0)) (cells_bytes stderr_cells0)] stderr_cells0).
  - apply (rw_cells_image0 rsegs m RSTDERR (cells_bytes stderr_cells0)).
    + intros a Ha. change (Z.of_nat (length (cells_bytes stderr_cells0))) with 232%Z in Ha.
      apply NONE; [lia|]. cbn [outside rcrt_written]. lia.
    + vm_compute. reflexivity.
    + lia.
    + change (Z.of_nat (length (cells_bytes stderr_cells0))) with 232%Z. lia.
  - cbn. repeat split; exact I.
  - vm_compute. reflexivity.
  - reflexivity.
Qed.

Theorem stderr_wfile0_init : forall (m : word -> option byte),
  (forall a : word, (0x23000 <= bv_unsigned a < 0x56000)%Z -> outside rcrt_written (bv_unsigned a) -> m a = None) ->
  stderr_wfile0 m.
Proof.
  intros m NONE. exists (Z_to_bv 64 5), (Z_to_bv 64 0), 0, 0, (repeat (Z_to_bv 8 0) 80).
  split; [exact (stderr_cells0_image m NONE)|].
  split; [reflexivity|]. split; [left; reflexivity|]. lia.
Qed.
End RC__1.
