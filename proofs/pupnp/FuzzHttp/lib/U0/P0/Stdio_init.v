(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Malloc Require Import InitMem.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Stdio_base Printf_lib F_printf_iface Stdio_iface.
Import ListNotations.
Open Scope Z_scope.

Lemma rw_cells_recast4 : forall m A cs cs',
  rw_cells rsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells rsegs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.

Definition stderr_cells0 : list cell :=
  file_cells (Z_to_bv 64 5) 0 0 0 F_STDIO_WRITE RSTDERR_BUF 0 2 (Z_to_bv 64 0) 0xffffffff (repeat (Z_to_bv 8 0) 80).

Lemma stderr_cells0_image : forall (m : word -> option byte),
  (forall a : word, (RSTDERR <= bv_unsigned a < RSTDERR + 232)%Z -> m a = None) ->
  rw_cells rsegs m RSTDERR stderr_cells0.
Proof.
  intros m NONE.
  apply (rw_cells_recast4 m RSTDERR [CB (length (cells_bytes stderr_cells0)) (cells_bytes stderr_cells0)] stderr_cells0).
  - apply (rw_cells_image0 rsegs m RSTDERR (cells_bytes stderr_cells0)).
    + intros a Ha. change (Z.of_nat (length (cells_bytes stderr_cells0))) with 232%Z in Ha. apply NONE. lia.
    + vm_compute. reflexivity.
    + lia.
    + change (Z.of_nat (length (cells_bytes stderr_cells0))) with 232%Z. lia.
  - cbn. repeat split; exact I.
  - vm_compute. reflexivity.
  - reflexivity.
Qed.

Theorem stderr_wfile0_init : forall (m : word -> option byte),
  (forall a : word, (RSTDERR <= bv_unsigned a < RSTDERR + 232)%Z -> m a = None) ->
  stderr_wfile0 m.
Proof.
  intros m NONE. exists (Z_to_bv 64 5), (Z_to_bv 64 0), 0, 0, (repeat (Z_to_bv 8 0) 80).
  split; [exact (stderr_cells0_image m NONE)|].
  split; [reflexivity|]. split; [left; reflexivity|]. lia.
Qed.

Definition stdout_cells0 : list cell :=
  file_cells (Z_to_bv 64 5) 0 0 0 F_STDOUT_WRITE RSTDOUT_BUF 1024 1 (Z_to_bv 64 0) 10 (repeat (Z_to_bv 8 0) 80).

Lemma stdout_cells0_image : forall (m : word -> option byte),
  (forall a : word, (RSTDOUT <= bv_unsigned a < RSTDOUT + 232)%Z -> m a = None) ->
  rw_cells rsegs m RSTDOUT stdout_cells0.
Proof.
  intros m NONE.
  apply (rw_cells_recast4 m RSTDOUT [CB (length (cells_bytes stdout_cells0)) (cells_bytes stdout_cells0)] stdout_cells0).
  - apply (rw_cells_image0 rsegs m RSTDOUT (cells_bytes stdout_cells0)).
    + intros a Ha. change (Z.of_nat (length (cells_bytes stdout_cells0))) with 232%Z in Ha. apply NONE. lia.
    + vm_compute. reflexivity.
    + lia.
    + change (Z.of_nat (length (cells_bytes stdout_cells0))) with 232%Z. lia.
  - cbn. repeat split; exact I.
  - vm_compute. reflexivity.
  - reflexivity.
Qed.

Lemma stdout_buf0_image : forall (m : word -> option byte),
  (forall a : word, (RSTDOUT_BUF <= bv_unsigned a < RSTDOUT_BUF + 1024)%Z -> m a = None) ->
  rw_cells rsegs m RSTDOUT_BUF [CB 1024 (repeat (Z_to_bv 8 0) 1024)].
Proof.
  intros m NONE.
  apply (rw_cells_image0 rsegs m RSTDOUT_BUF (repeat (Z_to_bv 8 0) 1024)).
  - intros a Ha. rewrite repeat_length in Ha. apply NONE. lia.
  - vm_compute. reflexivity.
  - lia.
  - rewrite repeat_length. lia.
Qed.

Theorem stdout_file_init : forall (m : word -> option byte),
  (forall a : word, (RSTDOUT <= bv_unsigned a < RSTDOUT + 232)%Z -> m a = None) ->
  (forall a : word, (RSTDOUT_BUF <= bv_unsigned a < RSTDOUT_BUF + 1024)%Z -> m a = None) ->
  stdout_file m stdout_init.
Proof.
  intros m N1 N2. exists (Z_to_bv 64 5), (Z_to_bv 64 0), (repeat (Z_to_bv 8 0) 80), (repeat (Z_to_bv 8 0) 1024).
  cbn [so_active so_buf so_lbf_nl so_first stdout_init].
  split; [exact (stdout_cells0_image m N1)|].
  split; [reflexivity|].
  split; [exact (stdout_buf0_image m N2)|].
  split; [reflexivity|]. split; [unfold zlength; cbn; lia|]. intros _; reflexivity.
Qed.

Lemma stdout_init_flags_104 : Z.land (bv_unsigned (Z_to_bv 64 5)) 104 = 0.
Proof. reflexivity. Qed.
