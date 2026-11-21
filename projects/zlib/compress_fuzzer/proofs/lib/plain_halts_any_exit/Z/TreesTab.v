(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma arr_dflt_upd : forall {A} l (a : parr A) ofs, arr_dflt (arr_upd a ofs l) = arr_dflt a.
Proof. induction l as [|x l IH]; intros; cbn [arr_upd]; [reflexivity|]. rewrite IH. apply arr_dflt_set. Qed.

Lemma arr_of_list_dflt : forall l i, arr_dflt (arr_of_list l) i = 0.
Proof. intros. unfold arr_of_list, parr_of_list. rewrite arr_dflt_upd. unfold arr_make. rewrite arr_dflt_init. reflexivity. Qed.

Definition tab_bounded (a : arr) (n : nat) (B : Z) : bool :=
  forallb (fun j => (0 <=? arr_get a (Z.of_nat j)) && (arr_get a (Z.of_nat j) <? B)) (seq 0 n).

Lemma tab_bounded_all : forall l B,
  tab_bounded (arr_of_list l) (length l) B = true -> 0 < B ->
  forall i, 0 <= arr_get (arr_of_list l) i < B.
Proof.
  intros l B H HB i.
  destruct (Z_lt_le_dec i 0) as [Hi|Hi]; [|destruct (Z_lt_le_dec i (zlength l)) as [Hj|Hj]].
  - rewrite arr_get_oob by (rewrite arr_len_of_list; lia). rewrite arr_of_list_dflt. lia.
  - unfold tab_bounded in H. rewrite forallb_forall in H.
    specialize (H (Z.to_nat i) ltac:(apply in_seq; unfold zlength in Hj; lia)). rewrite Z2Nat.id in H by lia.
    apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
  - rewrite arr_get_oob by (rewrite arr_len_of_list; lia). rewrite arr_of_list_dflt. lia.
Qed.

Lemma length_code_bound : forall i, 0 <= arr_get length_code_a i < 29.
Proof. apply tab_bounded_all; [vm_compute; reflexivity | lia]. Qed.
Lemma dist_code_bound : forall i, 0 <= arr_get dist_code_a i < 30.
Proof. apply tab_bounded_all; [vm_compute; reflexivity | lia]. Qed.
Lemma extra_lbits_bound : forall i, 0 <= arr_get extra_lbits_a i < 6.
Proof. apply tab_bounded_all; [vm_compute; reflexivity | lia]. Qed.
Lemma base_length_bound : forall i, 0 <= arr_get base_length_a i < 259.
Proof. apply tab_bounded_all; [vm_compute; reflexivity | lia]. Qed.
Lemma extra_dbits_bound : forall i, 0 <= arr_get extra_dbits_a i < 14.
Proof. apply tab_bounded_all; [vm_compute; reflexivity | lia]. Qed.
Lemma base_dist_bound : forall i, 0 <= arr_get base_dist_a i < 24577.
Proof. apply tab_bounded_all; [vm_compute; reflexivity | lia]. Qed.
Lemma extra_blbits_bound : forall i, 0 <= arr_get extra_blbits_a i < 8.
Proof. apply tab_bounded_all; [vm_compute; reflexivity | lia]. Qed.
Lemma bl_order_bound : forall i, 0 <= arr_get bl_order_a i < 19.
Proof. apply tab_bounded_all; [vm_compute; reflexivity | lia]. Qed.
Lemma static_ltree_fc_bound : forall i, 0 <= arr_get static_ltree_fc i < 512.
Proof. apply tab_bounded_all; [vm_compute; reflexivity | lia]. Qed.
Lemma static_ltree_dl_bound : forall i, 0 <= arr_get static_ltree_dl i < 10.
Proof. apply tab_bounded_all; [vm_compute; reflexivity | lia]. Qed.
Lemma static_dtree_fc_bound : forall i, 0 <= arr_get static_dtree_fc i < 32.
Proof. apply tab_bounded_all; [vm_compute; reflexivity | lia]. Qed.
Lemma static_dtree_dl_bound : forall i, 0 <= arr_get static_dtree_dl i < 6.
Proof. apply tab_bounded_all; [vm_compute; reflexivity | lia]. Qed.

