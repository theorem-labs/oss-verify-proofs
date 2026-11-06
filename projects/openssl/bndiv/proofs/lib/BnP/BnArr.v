(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnMem.
From OSSVerify.Proofs.openssl.bndiv.lib.BnP Require Import BnKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma wlimbs_len : forall l, length (wlimbs l) = length l.
Proof. intros. unfold wlimbs. apply length_map. Qed.
Lemma wlimbs_app : forall a b, wlimbs (a ++ b) = wlimbs a ++ wlimbs b.
Proof. intros. unfold wlimbs. apply map_app. Qed.
Lemma wlimbs_firstn : forall k l, wlimbs (firstn k l) = firstn k (wlimbs l).
Proof. intros. unfold wlimbs. symmetry. apply firstn_map. Qed.
Lemma wlimbs_skipn : forall k l, wlimbs (skipn k l) = skipn k (wlimbs l).
Proof. intros. unfold wlimbs. symmetry. apply skipn_map. Qed.
Lemma wlimbs_repeat : forall x k, wlimbs (repeat x k) = repeat (Z_to_bv 64 x) k.
Proof. intros. unfold wlimbs. apply map_repeat. Qed.

(* [comment removed for export] *)
Lemma lbytes_repeat0 : forall k, u64s (wlimbs (repeat 0 k)) = repeat (Z_to_bv 8 0) (8 * k).
Proof. intros. rewrite wlimbs_repeat. apply u64s_repeat0. Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma limbarr_app : forall m A l1 l2,
  u64arr segs m A (wlimbs (l1 ++ l2)) <-> u64arr segs m A (wlimbs l1) /\ u64arr segs m (A + 8 * Z.of_nat (length l1)) (wlimbs l2).
Proof. intros m A l1 l2. rewrite wlimbs_app, u64arr_app, wlimbs_len. tauto. Qed.

Lemma limbarr_split : forall m A l k, (k <= length l)%nat ->
  (u64arr segs m A (wlimbs l) <-> u64arr segs m A (wlimbs (firstn k l)) /\ u64arr segs m (A + 8 * Z.of_nat k) (wlimbs (skipn k l))).
Proof.
  intros m A l k Hk. rewrite <- (firstn_skipn k l) at 1. rewrite limbarr_app, firstn_length_le by exact Hk. tauto.
Qed.

(* [comment removed for export] *)
Lemma limbarr_limbs_at : forall m A l, u64arr segs m A (wlimbs l) <-> limbs_at segs m A l /\ wr_at segs m A (8 * Z.of_nat (length l)).
Proof. intros m A l. unfold u64arr, limbs_at, lbytes. rewrite wlimbs_len. tauto. Qed.

(* [comment removed for export] *)
Lemma limbarr_bytes : forall m A l, u64arr segs m A (wlimbs l) -> bytes_at segs m A (u64s (wlimbs l)).
Proof. intros m A l [H _]. exact H. Qed.

Lemma limbarr_CB : forall m A l, u64arr segs m A (wlimbs l) -> rw_cells segs m A [CB (8 * length l) (u64s (wlimbs l))].
Proof. intros m A l H. apply u64arr_CB in H. rewrite wlimbs_len in H. exact H. Qed.

End WithSegs.
