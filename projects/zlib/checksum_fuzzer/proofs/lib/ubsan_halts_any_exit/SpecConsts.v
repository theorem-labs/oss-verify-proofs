(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
(* the package's own imports *)
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Lemma rw_bytes_max_ge17 : (131072 <= rw_bytes_max)%Z.
Proof. unfold rw_bytes_max. lia. Qed.
Lemma rw_bytes_max_ge16 : (65536 <= rw_bytes_max)%Z.
Proof. pose proof rw_bytes_max_ge17. lia. Qed.
Lemma task_size_ge47 : (2 ^ 47 <= TASK_SIZE)%Z.
Proof. unfold TASK_SIZE. cbv. discriminate. Qed.
Lemma access_okb_true_intro_Z : forall (buf : word) (cnt : Z),
  (0 <= cnt)%Z ->
  (bv_unsigned buf + cnt <= 2 ^ 47)%Z ->
  access_okb buf cnt = true.
Proof.
  intros buf cnt Hc H. unfold access_okb.
  pose proof task_size_ge47.
  pose proof (bv_unsigned_in_range 64 buf) as [Hb _].
  apply Bool.andb_true_iff. split; apply Z.leb_le; lia.
Qed.
Lemma rw_bytes_max_nonneg : (0 <= rw_bytes_max)%Z.
Proof. pose proof rw_bytes_max_ge17. lia. Qed.
