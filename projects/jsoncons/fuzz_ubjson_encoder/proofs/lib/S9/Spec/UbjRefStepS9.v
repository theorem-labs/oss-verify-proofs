(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
Import ListNotations.
Open Scope Z_scope.

Section StepArms.
Variable p : list Z.
Variables (s : st) (t : pstate) (r : list pstate).
Hypothesis NH : halted s = false.
Hypothesis HS : s_stk s = t :: r.

Local Ltac arm := unfold step; rewrite NH, HS; cbn [ps_mode]; try reflexivity.

Lemma step_array_more : ps_mode t = Marray -> ps_idx t < ps_len t -> step p s = ret_if_ec (r_tv p (top_upd ps_inc s)).
Proof. intros M L. arm. rewrite M. replace (ps_idx t <? ps_len t) with true by (symmetry; apply Z.ltb_lt; exact L). reflexivity. Qed.
Lemma step_array_end : ps_mode t = Marray -> ps_len t <= ps_idx t -> step p s = r_end s.
Proof. intros M L. arm. rewrite M. replace (ps_idx t <? ps_len t) with false by (symmetry; apply Z.ltb_ge; exact L). reflexivity. Qed.
Lemma step_tarray_more : ps_mode t = Mtarray -> ps_idx t < ps_len t -> step p s = ret_if_ec (r_value p (ps_type t) (top_upd ps_inc s)).
Proof. intros M L. arm. rewrite M. replace (ps_idx t <? ps_len t) with true by (symmetry; apply Z.ltb_lt; exact L). reflexivity. Qed.
Lemma step_tarray_end : ps_mode t = Mtarray -> ps_len t <= ps_idx t -> step p s = r_end s.
Proof. intros M L. arm. rewrite M. replace (ps_idx t <? ps_len t) with false by (symmetry; apply Z.ltb_ge; exact L). reflexivity. Qed.

Lemma step_iarray_eof : ps_mode t = Miarray -> blen p <= s_pos s -> step p s = w_halt true (r_fail s).
Proof. intros M L. arm. rewrite M. replace (blen p <=? s_pos s) with true by (symmetry; apply Z.leb_le; exact L). reflexivity. Qed.
Lemma step_iarray_close : ps_mode t = Miarray -> s_pos s < blen p -> bat p (s_pos s) = 93 -> step p s = ret_if_ec (r_end (w_pos (s_pos s + 1) s)).
Proof.
  intros M L B. arm. rewrite M. replace (blen p <=? s_pos s) with false by (symmetry; apply Z.leb_gt; exact L). rewrite B. reflexivity.
Qed.
Lemma step_iarray_full : ps_mode t = Miarray -> s_pos s < blen p -> bat p (s_pos s) <> 93 -> MAX_ITEMS < ps_idx t + 1 ->
  step p s = w_halt true (r_fail (top_upd ps_inc s)).
Proof.
  intros M L B F. arm. rewrite M. replace (blen p <=? s_pos s) with false by (symmetry; apply Z.leb_gt; exact L).
  replace (bat p (s_pos s) =? 93) with false by (symmetry; apply Z.eqb_neq; exact B).
  replace (MAX_ITEMS <? ps_idx t + 1) with true by (symmetry; apply Z.ltb_lt; exact F). reflexivity.
Qed.
Lemma step_iarray_item : ps_mode t = Miarray -> s_pos s < blen p -> bat p (s_pos s) <> 93 -> ps_idx t + 1 <= MAX_ITEMS ->
  step p s = ret_if_ec (r_tv p (top_upd ps_inc s)).
Proof.
  intros M L B F. arm. rewrite M. replace (blen p <=? s_pos s) with false by (symmetry; apply Z.leb_gt; exact L).
  replace (bat p (s_pos s) =? 93) with false by (symmetry; apply Z.eqb_neq; exact B).
  replace (MAX_ITEMS <? ps_idx t + 1) with false by (symmetry; apply Z.ltb_ge; exact F). reflexivity.
Qed.

Lemma step_key_more : ps_mode t = Mkey -> ps_idx t < ps_len t ->
  step p s = (let s' := r_key p (top_upd ps_inc s) in if s_ec s' then w_halt true s' else top_upd (ps_mode_set Mval) s').
Proof. intros M L. arm. rewrite M. replace (ps_idx t <? ps_len t) with true by (symmetry; apply Z.ltb_lt; exact L). reflexivity. Qed.
Lemma step_key_end : ps_mode t = Mkey -> ps_len t <= ps_idx t -> step p s = r_end s.
Proof. intros M L. arm. rewrite M. replace (ps_idx t <? ps_len t) with false by (symmetry; apply Z.ltb_ge; exact L). reflexivity. Qed.
Lemma step_val : ps_mode t = Mval -> step p s = ret_if_ec (r_tv p (top_upd (ps_mode_set Mkey) s)).
Proof. intros M. arm. rewrite M. reflexivity. Qed.
Lemma step_tkey_more : ps_mode t = Mtkey -> ps_idx t < ps_len t ->
  step p s = (let s' := r_key p (top_upd ps_inc s) in if s_ec s' then w_halt true s' else top_upd (ps_mode_set Mtval) s').
Proof. intros M L. arm. rewrite M. replace (ps_idx t <? ps_len t) with true by (symmetry; apply Z.ltb_lt; exact L). reflexivity. Qed.
Lemma step_tkey_end : ps_mode t = Mtkey -> ps_len t <= ps_idx t -> step p s = r_end s.
Proof. intros M L. arm. rewrite M. replace (ps_idx t <? ps_len t) with false by (symmetry; apply Z.ltb_ge; exact L). reflexivity. Qed.
Lemma step_tval : ps_mode t = Mtval -> step p s = ret_if_ec (r_value p (ps_type t) (top_upd (ps_mode_set Mtkey) s)).
Proof. intros M. arm. rewrite M. reflexivity. Qed.

Lemma step_ikey_eof : ps_mode t = Mikey -> blen p <= s_pos s -> step p s = w_halt true (r_fail s).
Proof. intros M L. arm. rewrite M. replace (blen p <=? s_pos s) with true by (symmetry; apply Z.leb_le; exact L). reflexivity. Qed.
Lemma step_ikey_close : ps_mode t = Mikey -> s_pos s < blen p -> bat p (s_pos s) = 125 -> step p s = ret_if_ec (r_end (w_pos (s_pos s + 1) s)).
Proof.
  intros M L B. arm. rewrite M. replace (blen p <=? s_pos s) with false by (symmetry; apply Z.leb_gt; exact L). rewrite B. reflexivity.
Qed.
Lemma step_ikey_full : ps_mode t = Mikey -> s_pos s < blen p -> bat p (s_pos s) <> 125 -> MAX_ITEMS < ps_idx t + 1 ->
  step p s = w_halt true (r_fail (top_upd ps_inc s)).
Proof.
  intros M L B F. arm. rewrite M. replace (blen p <=? s_pos s) with false by (symmetry; apply Z.leb_gt; exact L).
  replace (bat p (s_pos s) =? 125) with false by (symmetry; apply Z.eqb_neq; exact B).
  replace (MAX_ITEMS <? ps_idx t + 1) with true by (symmetry; apply Z.ltb_lt; exact F). reflexivity.
Qed.
Lemma step_ikey_item : ps_mode t = Mikey -> s_pos s < blen p -> bat p (s_pos s) <> 125 -> ps_idx t + 1 <= MAX_ITEMS ->
  step p s = (let s' := r_key p (top_upd ps_inc s) in if s_ec s' then w_halt true s' else top_upd (ps_mode_set Mival) s').
Proof.
  intros M L B F. arm. rewrite M. replace (blen p <=? s_pos s) with false by (symmetry; apply Z.leb_gt; exact L).
  replace (bat p (s_pos s) =? 125) with false by (symmetry; apply Z.eqb_neq; exact B).
  replace (MAX_ITEMS <? ps_idx t + 1) with false by (symmetry; apply Z.ltb_ge; exact F). reflexivity.
Qed.
Lemma step_ival : ps_mode t = Mival -> step p s = ret_if_ec (r_tv p (top_upd (ps_mode_set Mikey) s)).
Proof. intros M. arm. rewrite M. reflexivity. Qed.
Lemma step_root : ps_mode t = Mroot -> step p s = ret_if_ec (r_tv p (top_upd (ps_mode_set Maccept) s)).
Proof. intros M. arm. rewrite M. reflexivity. Qed.
Lemma step_accept : ps_mode t = Maccept -> r = [] -> step p s = w_done true (w_more false (w_stk [] s)).
Proof. intros M R. arm. rewrite M. rewrite R. reflexivity. Qed.
End StepArms.
