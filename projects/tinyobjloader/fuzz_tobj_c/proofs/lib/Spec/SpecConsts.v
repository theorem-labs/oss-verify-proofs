(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition max_write_total : Z := 262144.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma max_write_total_le_rw_count_clamp : max_write_total <= MAX_RW_COUNT.
Proof. unfold max_write_total, MAX_RW_COUNT. lia. Qed.

Lemma max_write_total_eq_2_18 : max_write_total = 2 ^ 18.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma rw_bytes_max_ge_2_17 : 2 ^ 17 <= rw_bytes_max.
Proof. unfold rw_bytes_max. lia. Qed.

(* [comment removed for export] *)
Definition max_read_count : Z := 65536.

Lemma max_read_count_lt_rw_count_clamp : max_read_count < MAX_RW_COUNT.
Proof. unfold max_read_count, MAX_RW_COUNT. lia. Qed.

Lemma max_read_count_le_rw_count_clamp : max_read_count <= MAX_RW_COUNT.
Proof. unfold max_read_count, MAX_RW_COUNT. lia. Qed.

(* [comment removed for export] *)
Lemma task_size_val : TASK_SIZE = 2 ^ 47.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sp_window_hi_task_size : sp_window_hi = TASK_SIZE.
Proof. reflexivity. Qed.

Lemma path_max_val : path_max = 4096%nat.
Proof. reflexivity. Qed.
