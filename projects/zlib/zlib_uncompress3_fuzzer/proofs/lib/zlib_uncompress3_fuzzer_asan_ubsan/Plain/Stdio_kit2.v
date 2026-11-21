(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Lib Require Import Tac ITree Nodes Decode SysStep Image.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Common Require Import SFModel F_fmt_fp_lib.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Spec Require Import Prelim.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Plain Require Import PImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rw_cells_recast3 : forall m A cs cs', rw_cells psegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells psegs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.

Lemma fmt_bytes_at : forall m A f, mem_inv psegs m -> ro_bytes_b psegs A (zb f) = true -> 0 <= A -> A + zlength f <= 2^64 ->
  bytes_at psegs m A (zb f).
Proof.
  intros m A f MI RB H0 H1.
  pose proof (ro_cells_bytes_at psegs m A _ (ro_cells_image psegs m A (zb f) MI RB H0 ltac:(rewrite zb_length; unfold zlength in H1; lia))) as B.
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Ltac forall_range := repeat (apply Forall_cons; [lia|]); apply Forall_nil.
