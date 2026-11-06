(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxPlan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxQNode.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require FxMchr.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require AsanQSites AsanQcsNode.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXD.FxMchr.FxQcsChk OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQSites OSSVerify.Proofs.fast_float.from_chars.lib.FXD.AsanQcsNode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition QS_MEMMOVE_S : qsite := QS 0x60f58 (rr 13) (rr 15) (rr 11) (rr 14) (rr 16) (rr 17) true (Z_to_bv 13 (0x61124 - 0x60f84)) false.
Definition QS_MEMMOVE_D : qsite := QS 0x60fa4 (rr 13) (rr 15) (rr 10) (rr 14) (rr 16) (rr 17) true (Z_to_bv 13 (0x61224 - 0x60fd0)) false.
Lemma QS_MEMMOVE_S_ok : qsite_ok ASEGSQ QS_MEMMOVE_S. Proof. qsite_tac. Qed.
Lemma QS_MEMMOVE_D_ok : qsite_ok ASEGSQ QS_MEMMOVE_D. Proof. qsite_tac. Qed.

(* [comment removed for export] *)
Definition QS_AMEMMOVE_S : qsite := QS 0x608f4 (rr 13) (rr 15) (rr 11) (rr 14) (rr 16) (rr 17) true (Z_to_bv 13 (0x60abc - 0x60920)) false.
Definition QS_AMEMMOVE_D : qsite := QS 0x60940 (rr 13) (rr 15) (rr 10) (rr 14) (rr 16) (rr 17) true (Z_to_bv 13 (0x60b60 - 0x6096c)) false.
Lemma QS_AMEMMOVE_S_ok : qsite_ok ASEGSQ QS_AMEMMOVE_S. Proof. qsite_tac. Qed.
Lemma QS_AMEMMOVE_D_ok : qsite_ok ASEGSQ QS_AMEMMOVE_D. Proof. qsite_tac. Qed.

(* [comment removed for export] *)
Definition QSS_MEMCPY_S : qssite := QSS QS_MEMCPY_S 0x61714 (rr 15) (rr 16) (rr 17) (rr 15) (rr 16) (Z_to_bv 13 (0x6145c - 0x61744)).
Definition QSS_MEMCPY_D : qssite := QSS QS_MEMCPY_D 0x61814 (rr 15) (rr 16) (rr 17) (rr 15) (rr 16) (Z_to_bv 13 (0x614a4 - 0x61844)).
Definition QSS_MEMMOVE_S : qssite := QSS QS_MEMMOVE_S 0x61124 (rr 16) (rr 15) (rr 17) (rr 15) (rr 16) (Z_to_bv 13 (0x60f88 - 0x61154)).
Definition QSS_MEMMOVE_D : qssite := QSS QS_MEMMOVE_D 0x61224 (rr 16) (rr 15) (rr 17) (rr 15) (rr 16) (Z_to_bv 13 (0x60fd4 - 0x61254)).
(* [comment removed for export] *)
Definition QSS_AMEMMOVE_S : qssite := QSS QS_AMEMMOVE_S 0x60abc (rr 16) (rr 15) (rr 17) (rr 15) (rr 16) (Z_to_bv 13 (0x60924 - 0x60aec)).
Definition QSS_AMEMMOVE_D : qssite := QSS QS_AMEMMOVE_D 0x60b60 (rr 16) (rr 15) (rr 17) (rr 15) (rr 16) (Z_to_bv 13 (0x60970 - 0x60b90)).

Ltac qssite_tac Hq := cbn [qssite_ok]; split; [exact Hq|]; cbv zeta;
  repeat split; try (let Hc := fresh "Hc" in intro Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate); try qins_tac;
  try (apply bv_eq; vm_compute; reflexivity).
Lemma QSS_MEMCPY_S_ok : qssite_ok ASEGSQ QSS_MEMCPY_S. Proof. qssite_tac QS_MEMCPY_S_ok. Qed.
Lemma QSS_MEMCPY_D_ok : qssite_ok ASEGSQ QSS_MEMCPY_D. Proof. qssite_tac QS_MEMCPY_D_ok. Qed.
Lemma QSS_MEMMOVE_S_ok : qssite_ok ASEGSQ QSS_MEMMOVE_S. Proof. qssite_tac QS_MEMMOVE_S_ok. Qed.
Lemma QSS_MEMMOVE_D_ok : qssite_ok ASEGSQ QSS_MEMMOVE_D. Proof. qssite_tac QS_MEMMOVE_D_ok. Qed.
Lemma QSS_AMEMMOVE_S_ok : qssite_ok ASEGSQ QSS_AMEMMOVE_S. Proof. qssite_tac QS_AMEMMOVE_S_ok. Qed.
Lemma QSS_AMEMMOVE_D_ok : qssite_ok ASEGSQ QSS_AMEMMOVE_D. Proof. qssite_tac QS_AMEMMOVE_D_ok. Qed.

(* [comment removed for export] *)
Definition QSSITES_P : list qssite := [QSS_MEMCPY_S; QSS_MEMCPY_D; QSS_MEMMOVE_S; QSS_MEMMOVE_D; QSS_AMEMMOVE_S; QSS_AMEMMOVE_D].
Lemma QSSITES_P_ok : Forall (qssite_ok ASEGSQ) QSSITES_P.
Proof.
  unfold QSSITES_P. apply Forall_cons; [exact QSS_MEMCPY_S_ok|]. apply Forall_cons; [exact QSS_MEMCPY_D_ok|].
  apply Forall_cons; [exact QSS_MEMMOVE_S_ok|]. apply Forall_cons; [exact QSS_MEMMOVE_D_ok|].
  apply Forall_cons; [exact QSS_AMEMMOVE_S_ok|]. apply Forall_cons; [exact QSS_AMEMMOVE_D_ok|]. apply Forall_nil.
Qed.
