(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)

From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition access_ok_walk_max : Z := 131072%Z.

Definition task_size_max : Z := 0x800000000000%Z.

Lemma task_size_max_eq : task_size_max = TASK_SIZE.
Proof. reflexivity. Qed.

Lemma rw_bytes_max_ge17 : (131072 <= rw_bytes_max)%Z.
Proof. unfold rw_bytes_max. lia. Qed.

Lemma rw_bytes_max_ge18 : (131072 <= rw_bytes_max)%Z.
Proof. exact rw_bytes_max_ge17. Qed.

Lemma rw_bytes_max_nonneg : (0 <= rw_bytes_max)%Z.
Proof. pose proof rw_bytes_max_ge17. lia. Qed.

Lemma access_ok_walk_max_ge17 : (131072 <= access_ok_walk_max)%Z.
Proof. unfold access_ok_walk_max. lia. Qed.

Lemma access_ok_walk_max_le_rw : (access_ok_walk_max <= rw_bytes_max)%Z.
Proof. unfold access_ok_walk_max, rw_bytes_max. lia. Qed.
