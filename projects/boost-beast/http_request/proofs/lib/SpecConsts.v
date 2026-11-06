(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Lemma rw_bytes_max_ge17 : (131072 <= rw_bytes_max)%Z.
Proof. unfold rw_bytes_max. lia. Qed.

Lemma rw_bytes_max_val : rw_bytes_max = 131072%Z.
Proof. reflexivity. Qed.

Lemma rw_bytes_max_nonneg : (0 <= rw_bytes_max)%Z.
Proof. pose proof rw_bytes_max_ge17. lia. Qed.

(* [comment removed for export] *)
Lemma MAX_RW_COUNT_val : MAX_RW_COUNT = 0x7ffff000%Z.
Proof. reflexivity. Qed.

Lemma rw_bytes_max_le_MAX_RW_COUNT : (rw_bytes_max <= MAX_RW_COUNT)%Z.
Proof. unfold rw_bytes_max, MAX_RW_COUNT. lia. Qed.

(* [comment removed for export] *)
Lemma TASK_SIZE_val : TASK_SIZE = 0x800000000000%Z.
Proof. reflexivity. Qed.
