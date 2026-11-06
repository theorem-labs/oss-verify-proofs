(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import ABase.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition AQUAR_Q : Z := 0xd0f70.               (* [comment removed for export] *)
Definition AQ_MAX : Z := 0xd0fb0.                (* [comment removed for export] *)
Definition AQ_MIN : Z := 0xd0fb8.                (* [comment removed for export] *)
Definition AQ_MAXC : Z := 0xd0fc0.               (* [comment removed for export] *)
Definition AQ_MUTEX : Z := 0xd1008.              (* [comment removed for export] *)
Definition AQ_GCACHE : Z := 0xd1010.             (* [comment removed for export] *)
Definition aq_tcache (L : alayout) : Z := al_t L + 80.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AIA_BASE : Z := 0xd5500.              (* [comment removed for export] *)
Definition AIA_SIZE : Z := 0x81030.               (* [comment removed for export] *)
Definition AIA_MAP1 : Z := 0xd5508.              (* [comment removed for export] *)
Definition AIA_MAP1_LEN : Z := 0x40000.
Definition AIA_FLAG : Z := 0x163d88.              (* [comment removed for export] *)
Definition AFHOOK : Z := 0x165dc8.                (* [comment removed for export] *)
End CANSEC1.

(* [comment removed for export] *)
Definition qsz (lst : Z) : Z := if lst =? 0 then 8 else 8192.
Arguments qsz : simpl never.
Lemma qsz_0 : qsz 0 = 8.
Proof. reflexivity. Qed.
Lemma qsz_eq0 : forall lst, lst = 0 -> qsz lst = 8.
Proof. intros lst ->. reflexivity. Qed.
Lemma qsz_nz : forall lst, lst <> 0 -> qsz lst = 8192.
Proof. intros lst H. unfold qsz. destruct (Z.eqb_spec lst 0); [contradiction| reflexivity]. Qed.
Lemma qsz_pos : forall lst, 0 < lst -> qsz lst = 8192.
Proof. intros lst H. apply qsz_nz. lia. Qed.
Lemma qsz_bound : forall lst, 8 <= qsz lst <= 8192.
Proof. intros lst. unfold qsz. destruct (lst =? 0); lia. Qed.
(* [comment removed for export] *)
Lemma qsz_int : forall lst, 0 <= lst -> lst < 18446744073709551616 ->
  exists z, 0 <= z <= 1 /\ qsz lst = 8 + 8184 * z /\ z <= lst /\ lst <= 18446744073709551616 * z.
Proof.
  intros lst H0 H1. unfold qsz. destruct (Z.eqb_spec lst 0) as [E|NE]; [exists 0| exists 1]; lia.
Qed.
