(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PESENCM.

#[local] Transparent e_end_value.

Definition ebump (r : list eitem) : list eitem :=
  match r with [] => [] | e :: r' => EI (ei_kind e) (ei_len e) ((ei_cnt e + 1) mod TWO64) :: r' end.
Lemma ebump_length r : length (ebump r) = length r.
Proof. destruct r; reflexivity. Qed.
Lemma eev_w_estk r s : e_end_value (w_estk r s) = w_estk (ebump r) s.
Proof. unfold e_end_value. cbn [s_estk w_estk]. destruct r as [|e r']; [destruct s; reflexivity| reflexivity]. Qed.

Lemma e_end_indef X e0 rr : s_estk X = e0 :: rr -> ei_indef e0 = true ->
  e_end X = ST (s_stk X) (s_pos X) (s_more X) (s_done X) (s_halt X) (s_depth X) (s_ec X) (ebump rr) (s_edepth X - 1) (s_lo X + 1) (s_hi X + 1) (s_bad X).
Proof. intros H1 H2. unfold e_end. rewrite H1, H2. cbv zeta. rewrite eev_w_estk. destruct X; reflexivity. Qed.
Lemma e_end_lt X e0 rr : s_estk X = e0 :: rr -> ei_indef e0 = false -> ei_cnt e0 < ei_len e0 ->
  e_end X = ST (s_stk X) (s_pos X) (s_more X) (s_done X) (s_halt X) (s_depth X) true (s_estk X) (s_edepth X - 1) (s_lo X) (s_hi X) (s_bad X).
Proof. intros H1 H2 H3. unfold e_end. rewrite H1, H2. cbv zeta. replace (ei_cnt e0 <? ei_len e0) with true by (symmetry; apply Z.ltb_lt; exact H3). destruct X; cbn in H1 |- *. subst. reflexivity. Qed.
Lemma e_end_gt X e0 rr : s_estk X = e0 :: rr -> ei_indef e0 = false -> ei_len e0 < ei_cnt e0 ->
  e_end X = ST (s_stk X) (s_pos X) (s_more X) (s_done X) (s_halt X) (s_depth X) true (s_estk X) (s_edepth X - 1) (s_lo X) (s_hi X) (s_bad X).
Proof.
  intros H1 H2 H3. unfold e_end. rewrite H1, H2. cbv zeta. replace (ei_cnt e0 <? ei_len e0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (ei_len e0 <? ei_cnt e0) with true by (symmetry; apply Z.ltb_lt; exact H3). destruct X; cbn in H1 |- *. subst. reflexivity.
Qed.
Lemma e_end_eq X e0 rr : s_estk X = e0 :: rr -> ei_indef e0 = false -> ei_cnt e0 = ei_len e0 ->
  e_end X = ST (s_stk X) (s_pos X) (s_more X) (s_done X) (s_halt X) (s_depth X) (s_ec X) (ebump rr) (s_edepth X - 1) (s_lo X) (s_hi X) (s_bad X).
Proof.
  intros H1 H2 H3. unfold e_end. rewrite H1, H2. cbv zeta. replace (ei_cnt e0 <? ei_len e0) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (ei_len e0 <? ei_cnt e0) with false by (symmetry; apply Z.ltb_ge; lia). rewrite eev_w_estk. destruct X; reflexivity.
Qed.
Lemma e_end_nil X : s_estk X = [] -> s_bad (e_end X) = true.
Proof. intros H. unfold e_end. rewrite H. reflexivity. Qed.

Lemma Forall_ebump rr : Forall ei_ok rr -> Forall ei_ok (ebump rr).
Proof. intros H. destruct rr as [|e r]; [constructor| exact (Forall_ei_bump e r H)]. Qed.

Lemma e_begin_indef_err kd X : MAX_DEPTH < s_edepth X + 1 ->
  e_begin_indef kd X = ST (s_stk X) (s_pos X) (s_more X) (s_done X) (s_halt X) (s_depth X) true (s_estk X) (s_edepth X + 1) (s_lo X) (s_hi X) (s_bad X).
Proof. intros H. unfold e_begin_indef. cbv zeta. cbn [s_edepth w_edepth]. replace (MAX_DEPTH <? s_edepth X + 1) with true by (symmetry; apply Z.ltb_lt; exact H). destruct X; reflexivity. Qed.
Lemma e_begin_indef_ok kd X : s_edepth X + 1 <= MAX_DEPTH ->
  e_begin_indef kd X = ST (s_stk X) (s_pos X) (s_more X) (s_done X) (s_halt X) (s_depth X) (s_ec X) (EI kd 0 0 :: s_estk X) (s_edepth X + 1) (s_lo X + 1) (s_hi X + 1) (s_bad X).
Proof. intros H. unfold e_begin_indef. cbv zeta. cbn [s_edepth w_edepth]. replace (MAX_DEPTH <? s_edepth X + 1) with false by (symmetry; apply Z.ltb_ge; lia). destruct X; reflexivity. Qed.
End PESENCM.
