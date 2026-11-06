(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac ITree Nodes Decode SysStep Image.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import SFModel F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma rw_cells_recast3 : forall m A cs cs', rw_cells asegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells asegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fmt_bytes_at : forall m A f, mem_inv asegs m -> ro_bytes_b asegs A (zb f) = true -> 0 <= A -> A + zlength f <= 2^64 ->
  bytes_at asegs m A (zb f).
Proof.
  intros m A f MI RB H0 H1.
  Local Ltac2 Set LiaHints.tbl := fun () => "0010<1312052108.8000004S2H1".
pose proof (ro_cells_bytes_at asegs m A _ (ro_cells_image asegs m A (zb f) MI RB H0 ltac:(rewrite zb_length; unfold zlength in H1; lia))) as B.
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

End CANSEC1.
Ltac forall_range := repeat (apply Forall_cons; [lia|]); apply Forall_nil.
