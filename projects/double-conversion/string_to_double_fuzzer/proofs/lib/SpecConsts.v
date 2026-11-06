(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require BvKH.   (* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma rw_bytes_max_val : rw_bytes_max = 131072%Z.
Proof. reflexivity. Qed.

Lemma rw_bytes_max_ge17 : (131072 <= rw_bytes_max)%Z.
Proof. unfold rw_bytes_max. lia. Qed.

Lemma rw_bytes_max_nonneg : (0 <= rw_bytes_max)%Z.
Proof. pose proof rw_bytes_max_ge17. lia. Qed.

(* [comment removed for export] *)
Lemma task_size_val : TASK_SIZE = 0x800000000000%Z.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma access_okb_true_intro : forall (buf : word) (len : Z),
  (0 <= len)%Z ->
  (bv_unsigned buf + len <= 0x800000000000)%Z ->
  access_okb buf len = true.
Proof.
  intros buf len Hlen H. unfold access_okb. rewrite task_size_val.
  pose proof (bv_unsigned_in_range 64 buf) as [Hb _].
  apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Lemma modeled_rw_count_small : forall count : word,
  (bv_unsigned count <= 131072)%Z -> modeled_rw_count count = true.
Proof. intros count H. unfold modeled_rw_count. apply Z.leb_le. rewrite rw_bytes_max_val. exact H. Qed.

(* [comment removed for export] *)
Lemma modeled_rw_range_small : forall buf count : word,
  (bv_unsigned count <= 131072)%Z -> modeled_rw_range buf count = true.
Proof. intros buf count H. unfold modeled_rw_range. rewrite (modeled_rw_count_small count H). reflexivity. Qed.

Lemma modeled_rw_range_inrange : forall buf count : word,
  (bv_unsigned buf + bv_unsigned count <= 0x800000000000)%Z -> modeled_rw_range buf count = true.
Proof.
  intros buf count H. unfold modeled_rw_range.
  pose proof (bv_unsigned_in_range 64 count) as [Hc _].
  rewrite (access_okb_true_intro buf (bv_unsigned count) Hc H). apply orb_true_r.
Qed.
