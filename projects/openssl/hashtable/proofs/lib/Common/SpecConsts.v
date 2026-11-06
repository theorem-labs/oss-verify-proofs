(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma rw_bytes_max_ge17 : (131072 <= rw_bytes_max)%Z.
Proof. unfold rw_bytes_max. lia. Qed.

Lemma rw_bytes_max_nonneg : (0 <= rw_bytes_max)%Z.
Proof. pose proof rw_bytes_max_ge17. lia. Qed.

(* [comment removed for export] *)
Lemma access_okb_true_intro : forall (buf : word) (cnt : Z),
  (0 <= cnt)%Z ->
  (bv_unsigned buf + cnt <= 2 ^ 47)%Z ->
  access_okb buf cnt = true.
Proof.
  intros buf cnt Hc H. unfold access_okb, TASK_SIZE.
  pose proof (bv_unsigned_in_range 64 buf) as [Hb _].
  apply Bool.andb_true_iff. split; apply Z.leb_le; lia.
Qed.
