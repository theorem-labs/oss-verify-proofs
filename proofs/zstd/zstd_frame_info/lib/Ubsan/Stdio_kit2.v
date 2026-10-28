(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac ITree Nodes Decode SysStep Image.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma rw_cells_recast3 : forall m A cs cs', rw_cells usegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells usegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

(* [comment removed for export] *)
Lemma fmt_bytes_at : forall m A f, mem_inv usegs m -> ro_bytes_b usegs A (zb f) = true -> 0 <= A -> A + zlength f <= 2^64 ->
  bytes_at usegs m A (zb f).
Proof.
  intros m A f MI RB H0 H1.
  Local Ltac2 Set LiaHints.tbl := fun () => "0010<1312052108.7000004S2H1".
pose proof (ro_cells_bytes_at usegs m A _ (ro_cells_image usegs m A (zb f) MI RB H0 ltac:(rewrite zb_length; unfold zlength in H1; lia))) as B.
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Ltac forall_range := repeat (apply Forall_cons; [lia|]); apply Forall_nil.
