(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintRelG.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateTaintBitsG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition tl_pb (s : deflate_state) (c : Z) : arr :=
  arr_set (arr_set (arr_set (ds_pending_buf s) (ds_lit_bufsize s + ds_sym_next s) (wrap8 0))
                   (ds_lit_bufsize s + (ds_sym_next s + 1)) (wrap8 0))
          (ds_lit_bufsize s + (ds_sym_next s + 1 + 1)) (wrap8 (wrap8 c)).
Definition tl_fc (s : deflate_state) (c : Z) : arr :=
  arr_set (ds_dyn_ltree_fc s) (wrap8 c) (wrap16 (arr_get (ds_dyn_ltree_fc s) (wrap8 c) + 1)).

Lemma tr_tally_lit_shape s c :
  fst (tr_tally_lit s c) = set_dyn_ltree_fc (set_sym_next (set_pending_buf s (tl_pb s c)) (ds_sym_next s + 1 + 1 + 1)) (tl_fc s c)
  /\ snd (tr_tally_lit s c) = Z.eqb (ds_sym_next s + 1 + 1 + 1) (ds_sym_end s).
Proof. split; destruct s; reflexivity. Qed.
Lemma tl_pb_len s c : arr_len (tl_pb s c) = arr_len (ds_pending_buf s).
Proof. unfold tl_pb. rewrite !arr_len_set. reflexivity. Qed.
Lemma tl_fc_len s c : arr_len (tl_fc s c) = arr_len (ds_dyn_ltree_fc s).
Proof. unfold tl_fc. rewrite !arr_len_set. reflexivity. Qed.

Definition td_pb (s : deflate_state) (d l : Z) : arr :=
  arr_set (arr_set (arr_set (ds_pending_buf s) (ds_lit_bufsize s + ds_sym_next s) (wrap8 (wrap16 d)))
                   (ds_lit_bufsize s + (ds_sym_next s + 1)) (wrap8 (Z.shiftr (wrap16 d) 8)))
          (ds_lit_bufsize s + (ds_sym_next s + 1 + 1)) (wrap8 (wrap8 l)).
Definition td_lcode (l : Z) : Z := arr_get length_code_a (wrap8 l) + LITERALS + 1.
Definition td_dcode (d : Z) : Z := d_code (wrap16 (wrap16 d - 1)).
Definition td_fc (s : deflate_state) (l : Z) : arr :=
  arr_set (ds_dyn_ltree_fc s) (td_lcode l) (wrap16 (arr_get (ds_dyn_ltree_fc s) (td_lcode l) + 1)).
Definition td_fd (s : deflate_state) (d : Z) : arr :=
  arr_set (ds_dyn_dtree_fc s) (td_dcode d) (wrap16 (arr_get (ds_dyn_dtree_fc s) (td_dcode d) + 1)).

Lemma tr_tally_dist_shape s d l :
  fst (tr_tally_dist s d l) = set_dyn_dtree_fc (set_dyn_ltree_fc (set_sym_next (set_pending_buf s (td_pb s d l)) (ds_sym_next s + 1 + 1 + 1)) (td_fc s l)) (td_fd s d)
  /\ snd (tr_tally_dist s d l) = Z.eqb (ds_sym_next s + 1 + 1 + 1) (ds_sym_end s).
Proof. split; destruct s; reflexivity. Qed.
Lemma td_pb_len s d l : arr_len (td_pb s d l) = arr_len (ds_pending_buf s).
Proof. unfold td_pb. rewrite !arr_len_set. reflexivity. Qed.
Lemma td_fc_len s l : arr_len (td_fc s l) = arr_len (ds_dyn_ltree_fc s).
Proof. unfold td_fc. rewrite !arr_len_set. reflexivity. Qed.
Lemma td_fd_len s d : arr_len (td_fd s d) = arr_len (ds_dyn_dtree_fc s).
Proof. unfold td_fd. rewrite !arr_len_set. reflexivity. Qed.

Lemma INVG_tr_tally_lit s c : INVG s -> INVG (fst (tr_tally_lit s c)).
Proof.
  intros I. rewrite (proj1 (tr_tally_lit_shape s c)). pose proof (tl_pb_len s c) as L1. pose proof (tl_fc_len s c) as L2.
  pose proof (ig_tl s I) as TL. destruct I; constructor; dsr; rewrite ?L1, ?L2; try assumption; try lia.
Qed.
Lemma INVG_tr_tally_dist s d l : INVG s -> INVG (fst (tr_tally_dist s d l)).
Proof.
  intros I. rewrite (proj1 (tr_tally_dist_shape s d l)). pose proof (td_pb_len s d l) as L1. pose proof (td_fc_len s l) as L2. pose proof (td_fd_len s d) as L3.
  pose proof (ig_tl s I) as TL. destruct I; constructor; dsr; rewrite ?L1, ?L2, ?L3; try assumption; try lia.
Qed.

Lemma wrap8_byte z : 0 <= wrap8 z < 256.
Proof. pose proof (wrap8_range z). change (2 ^ 8) with 256 in H. exact H. Qed.

Lemma tl_pb_aeq B s1 s2 c : ds_lit_bufsize s2 = ds_lit_bufsize s1 -> ds_sym_next s2 = ds_sym_next s1 ->
  aeq B (ds_pending_buf s1) (ds_pending_buf s2) ->
  aeq (Bx B (ds_lit_bufsize s1 + ds_sym_next s1) (ds_lit_bufsize s1 + ds_sym_next s1 + 3)) (tl_pb s1 c) (tl_pb s2 c).
Proof.
  intros E1 E2 A. unfold tl_pb. rewrite E1, E2.
  eapply aeq_mono; [apply aeq_set, aeq_set, aeq_set; exact A|].
  unfold Bx. intros i [X|X]; [left; left; left; exact X|].
  destruct (Z.eq_dec i (ds_lit_bufsize s1 + ds_sym_next s1)); [left; left; right; lia|].
  destruct (Z.eq_dec i (ds_lit_bufsize s1 + (ds_sym_next s1 + 1))); [left; right; lia|right; lia].
Qed.
Lemma td_pb_aeq B s1 s2 d l : ds_lit_bufsize s2 = ds_lit_bufsize s1 -> ds_sym_next s2 = ds_sym_next s1 ->
  aeq B (ds_pending_buf s1) (ds_pending_buf s2) ->
  aeq (Bx B (ds_lit_bufsize s1 + ds_sym_next s1) (ds_lit_bufsize s1 + ds_sym_next s1 + 3)) (td_pb s1 d l) (td_pb s2 d l).
Proof.
  intros E1 E2 A. unfold td_pb. rewrite E1, E2.
  eapply aeq_mono; [apply aeq_set, aeq_set, aeq_set; exact A|].
  unfold Bx. intros i [X|X]; [left; left; left; exact X|].
  destruct (Z.eq_dec i (ds_lit_bufsize s1 + ds_sym_next s1)); [left; left; right; lia|].
  destruct (Z.eq_dec i (ds_lit_bufsize s1 + (ds_sym_next s1 + 1))); [left; right; lia|right; lia].
Qed.

Lemma fc_aeq_bump (P : Z -> Prop) a b n len : aeq P a b -> arr_len a = len -> 0 <= n < len -> P n ->
  aeq P (arr_set a n (wrap16 (arr_get a n + 1))) (arr_set b n (wrap16 (arr_get b n + 1))).
Proof.
  intros A L Hn Pn. rewrite <- (aeq_get _ _ _ n A ltac:(rewrite L; exact Hn) Pn). apply aeq_set_keep. exact A.
Qed.

Lemma tr_tally_lit_rel W C B bnd ms pm s1 s2 c :
  REL W C B bnd ms pm s1 s2 -> INVG s1 -> INVG s2 ->
  snd (tr_tally_lit s1 c) = snd (tr_tally_lit s2 c)
  /\ REL W C (Bx B (ds_lit_bufsize s1 + ds_sym_next s1) (ds_lit_bufsize s1 + ds_sym_next s1 + 3)) bnd ms pm
         (fst (tr_tally_lit s1 c)) (fst (tr_tally_lit s2 c)).
Proof.
  intros R I1 I2. rewrite (proj1 (tr_tally_lit_shape s1 c)), (proj1 (tr_tally_lit_shape s2 c)), (proj2 (tr_tally_lit_shape s1 c)), (proj2 (tr_tally_lit_shape s2 c)).
  rewrite (rel_sym_next _ _ _ _ _ _ _ _ R). split; [rel_fields R; reflexivity|].
  eapply rel_set_dyn_ltree_fc.
  - apply rel_set_sym_next. eapply rel_set_pending_buf; [exact R|]. apply tl_pb_aeq; [apply (rel_lbs _ _ _ _ _ _ _ _ R)|apply (rel_sym_next _ _ _ _ _ _ _ _ R)|exact (r_pb _ _ _ _ _ _ _ _ R)].
  - unfold tl_fc. pose proof (wrap8_byte c). eapply fc_aeq_bump; [exact (r_lfc _ _ _ _ _ _ _ _ R)|exact (proj1 (ig_tl s1 I1))|lia|unfold L_CODES; lia].
Qed.

Lemma tr_tally_dist_rel W C B bnd ms pm s1 s2 d l :
  REL W C B bnd ms pm s1 s2 -> INVG s1 -> INVG s2 ->
  snd (tr_tally_dist s1 d l) = snd (tr_tally_dist s2 d l)
  /\ REL W C (Bx B (ds_lit_bufsize s1 + ds_sym_next s1) (ds_lit_bufsize s1 + ds_sym_next s1 + 3)) bnd ms pm
         (fst (tr_tally_dist s1 d l)) (fst (tr_tally_dist s2 d l)).
Proof.
  intros R I1 I2. rewrite (proj1 (tr_tally_dist_shape s1 d l)), (proj1 (tr_tally_dist_shape s2 d l)), (proj2 (tr_tally_dist_shape s1 d l)), (proj2 (tr_tally_dist_shape s2 d l)).
  rewrite (rel_sym_next _ _ _ _ _ _ _ _ R). split; [rel_fields R; reflexivity|].
  pose proof (length_code_bound (wrap8 l)) as HL.
  assert (HD : 0 <= d_code (wrap16 (wrap16 d - 1)) < 30) by (unfold d_code; destruct (Z.ltb _ 256); apply dist_code_bound).
  eapply rel_set_dyn_dtree_fc; [eapply rel_set_dyn_ltree_fc|].
  - apply rel_set_sym_next. eapply rel_set_pending_buf; [exact R|]. apply td_pb_aeq; [apply (rel_lbs _ _ _ _ _ _ _ _ R)|apply (rel_sym_next _ _ _ _ _ _ _ _ R)|exact (r_pb _ _ _ _ _ _ _ _ R)].
  - unfold td_fc, td_lcode in *. eapply fc_aeq_bump; [exact (r_lfc _ _ _ _ _ _ _ _ R)|exact (proj1 (ig_tl s1 I1))|unfold LITERALS, L_CODES in *; lia|unfold LITERALS, L_CODES in *; lia].
  - unfold td_fd, td_dcode in *. dsr. eapply fc_aeq_bump; [exact (r_dfc _ _ _ _ _ _ _ _ R)|exact (proj1 (proj2 (proj2 (ig_tl s1 I1))))|unfold D_CODES in *; lia|unfold D_CODES in *; lia].
Qed.
