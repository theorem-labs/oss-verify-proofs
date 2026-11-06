(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxQNode.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxMchr.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanQSites AsanQcsNode.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMchr.FxQcsChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQSites OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQcsNode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition QS_MEMMOVE_S : qsite := QS 0x60f4c (rr 13) (rr 15) (rr 11) (rr 14) (rr 16) (rr 17) true (Z_to_bv 13 (0x61118 - 0x60f78)) false.
Definition QS_MEMMOVE_D : qsite := QS 0x60f98 (rr 13) (rr 15) (rr 10) (rr 14) (rr 16) (rr 17) true (Z_to_bv 13 (0x61218 - 0x60fc4)) false.
Lemma QS_MEMMOVE_S_ok : qsite_ok ASEGSQ QS_MEMMOVE_S. Proof. qsite_tac. Qed.
Lemma QS_MEMMOVE_D_ok : qsite_ok ASEGSQ QS_MEMMOVE_D. Proof. qsite_tac. Qed.

(* [comment removed for export] *)
Definition QS_AMEMMOVE_S : qsite := QS 0x608e8 (rr 13) (rr 15) (rr 11) (rr 14) (rr 16) (rr 17) true (Z_to_bv 13 (0x60ab0 - 0x60914)) false.
Definition QS_AMEMMOVE_D : qsite := QS 0x60934 (rr 13) (rr 15) (rr 10) (rr 14) (rr 16) (rr 17) true (Z_to_bv 13 (0x60b54 - 0x60960)) false.
Lemma QS_AMEMMOVE_S_ok : qsite_ok ASEGSQ QS_AMEMMOVE_S. Proof. qsite_tac. Qed.
Lemma QS_AMEMMOVE_D_ok : qsite_ok ASEGSQ QS_AMEMMOVE_D. Proof. qsite_tac. Qed.

(* [comment removed for export] *)
Definition QSS_MEMCPY_S : qssite := QSS QS_MEMCPY_S 0x61708 (rr 15) (rr 16) (rr 17) (rr 15) (rr 16) (Z_to_bv 13 (0x61450 - 0x61738)).
Definition QSS_MEMCPY_D : qssite := QSS QS_MEMCPY_D 0x61808 (rr 15) (rr 16) (rr 17) (rr 15) (rr 16) (Z_to_bv 13 (0x61498 - 0x61838)).
Definition QSS_MEMMOVE_S : qssite := QSS QS_MEMMOVE_S 0x61118 (rr 16) (rr 15) (rr 17) (rr 15) (rr 16) (Z_to_bv 13 (0x60f7c - 0x61148)).
Definition QSS_MEMMOVE_D : qssite := QSS QS_MEMMOVE_D 0x61218 (rr 16) (rr 15) (rr 17) (rr 15) (rr 16) (Z_to_bv 13 (0x60fc8 - 0x61248)).
(* [comment removed for export] *)
Definition QSS_AMEMMOVE_S : qssite := QSS QS_AMEMMOVE_S 0x60ab0 (rr 16) (rr 15) (rr 17) (rr 15) (rr 16) (Z_to_bv 13 (0x60918 - 0x60ae0)).
Definition QSS_AMEMMOVE_D : qssite := QSS QS_AMEMMOVE_D 0x60b54 (rr 16) (rr 15) (rr 17) (rr 15) (rr 16) (Z_to_bv 13 (0x60964 - 0x60b84)).

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
(* [comment removed for export] *)
