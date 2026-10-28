(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BBytes BZBridge BacX BSFModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface B6_rip B6_memset B6_memcpy B6_memmove B6_strlen B6_strncmp3 B6_imemcpy B6_imemmove.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma asan_memset_ok : asan_memset_stmt.
Proof.
  unfold asan_memset_stmt. intros.
  eapply amemset_body; eassumption.
Qed.

Lemma asan_memcpy_ok : asan_memcpy_stmt.
Proof.
  unfold asan_memcpy_stmt, amemcpy_stmt_at. intros.
  eapply amemcpy_body; try eassumption. apply ACONST_memcpyp. assumption.
Qed.

Lemma memcpy_icpt_ok : memcpy_icpt_stmt.
Proof.
  unfold memcpy_icpt_stmt, amemcpy_stmt_at. intros.
  eapply imemcpy_body; try eassumption. apply ACONST_memcpyp. assumption.
Qed.

Lemma asan_memmove_ok : asan_memmove_stmt.
Proof.
  unfold asan_memmove_stmt, amemmove_stmt_at. intros.
  eapply amemmove_body; eassumption.
Qed.

Lemma memmove_icpt_ok : memmove_icpt_stmt.
Proof.
  unfold memmove_icpt_stmt, amemmove_stmt_at. intros.
  eapply imemmove_body; eassumption.
Qed.

Lemma strlen_icpt_ok : strlen_icpt_stmt.
Proof.
  unfold strlen_icpt_stmt. intros.
  eapply astrlen_body; try eassumption.
  - apply ACONST_strlenp. assumption.
  - apply (proj1 (ACONST_cflags _ ltac:(eassumption))).
Qed.

Lemma strncmp_icpt_ok : strncmp_icpt_stmt.
Proof.
  unfold strncmp_icpt_stmt. intros.
  eapply astrncmp_body; try eassumption.
  apply (proj2 (ACONST_cflags _ ltac:(eassumption))).
Qed.

End HCW.

