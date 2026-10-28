(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge TacX SFModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface
     N6_rip N6_memset N6_memcpy N6_memmove N6_strlen N6_strncmp3 N6_imemcpy.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

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

(* [comment removed for export] *)

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

