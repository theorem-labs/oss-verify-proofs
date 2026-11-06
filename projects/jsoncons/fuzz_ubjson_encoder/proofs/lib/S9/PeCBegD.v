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

Module PECBD.

Definition but_pos (a b : st) : Prop :=
  s_stk a = s_stk b /\ s_more a = s_more b /\ s_done a = s_done b /\ s_halt a = s_halt b /\ s_depth a = s_depth b /\ s_ec a = s_ec b
  /\ s_estk a = s_estk b /\ s_edepth a = s_edepth b /\ s_lo a = s_lo b /\ s_hi a = s_hi b /\ s_bad a = s_bad b.
Lemma but_pos_refl a : but_pos a a.
Proof. repeat split; reflexivity. Qed.
Lemma but_pos_w_pos a v : but_pos (w_pos v a) a.
Proof. destruct a; repeat split; reflexivity. Qed.
Lemma but_pos_w_pos_l a b v : but_pos a b -> but_pos (w_pos v a) b.
Proof. intros H. destruct H as (?&?&?&?&?&?&?&?&?&?&?). destruct a, b; cbn in *; subst; repeat split; reflexivity. Qed.
Lemma but_pos_sym a b : but_pos a b -> but_pos b a.
Proof. intros H. destruct H as (?&?&?&?&?&?&?&?&?&?&?). repeat split; symmetry; assumption. Qed.
Lemma but_pos_trans a b c : but_pos a b -> but_pos b c -> but_pos a c.
Proof. intros H1 H2. destruct H1 as (?&?&?&?&?&?&?&?&?&?&?). destruct H2 as (?&?&?&?&?&?&?&?&?&?&?). repeat split; congruence. Qed.
Lemma but_pos_r_fail a b : but_pos a b -> but_pos (r_fail a) (r_fail b).
Proof. intros H. destruct H as (?&?&?&?&?&?&?&?&?&?&?). destruct a, b; cbn in *; subst; repeat split; reflexivity. Qed.
Lemma but_pos_w_more a b v : but_pos a b -> but_pos (w_more v a) (w_more v b).
Proof. intros H. destruct H as (?&?&?&?&?&?&?&?&?&?&?). destruct a, b; cbn in *; subst; repeat split; reflexivity. Qed.
Lemma but_pos_w_ec a b v : but_pos a b -> but_pos (w_ec v a) (w_ec v b).
Proof. intros H. destruct H as (?&?&?&?&?&?&?&?&?&?&?). destruct a, b; cbn in *; subst; repeat split; reflexivity. Qed.
Lemma r_fail_more a : s_more (r_fail a) = false. Proof. reflexivity. Qed.
Lemma r_fail_ec a : s_ec (r_fail a) = true. Proof. reflexivity. Qed.
Lemma r_fail_eq a : r_fail a = w_more false (w_ec true a). Proof. reflexivity. Qed.
Lemma w_more_same s : s_more s = true -> w_more true s = s.
Proof. destruct s; cbn; intros ->; reflexivity. Qed.

Definition X1 (X : st) : st := w_depth (s_depth X + 1) X.
Lemma X1_fields X : s_stk (X1 X) = s_stk X /\ s_pos (X1 X) = s_pos X /\ s_more (X1 X) = s_more X /\ s_done (X1 X) = s_done X
  /\ s_halt (X1 X) = s_halt X /\ s_depth (X1 X) = s_depth X + 1 /\ s_ec (X1 X) = s_ec X /\ s_estk (X1 X) = s_estk X
  /\ s_edepth (X1 X) = s_edepth X /\ s_lo (X1 X) = s_lo X /\ s_hi (X1 X) = s_hi X /\ s_bad (X1 X) = s_bad X.
Proof. destruct X; cbn; repeat split; reflexivity. Qed.
Lemma w_pos_fields v X : s_stk (w_pos v X) = s_stk X /\ s_pos (w_pos v X) = v /\ s_more (w_pos v X) = s_more X /\ s_done (w_pos v X) = s_done X
  /\ s_halt (w_pos v X) = s_halt X /\ s_depth (w_pos v X) = s_depth X /\ s_ec (w_pos v X) = s_ec X /\ s_estk (w_pos v X) = s_estk X
  /\ s_edepth (w_pos v X) = s_edepth X /\ s_lo (w_pos v X) = s_lo X /\ s_hi (w_pos v X) = s_hi X /\ s_bad (w_pos v X) = s_bad X.
Proof. destruct X; cbn; repeat split; reflexivity. Qed.
Lemma w_stk_fields v X : s_stk (w_stk v X) = v /\ s_pos (w_stk v X) = s_pos X /\ s_more (w_stk v X) = s_more X /\ s_done (w_stk v X) = s_done X
  /\ s_halt (w_stk v X) = s_halt X /\ s_depth (w_stk v X) = s_depth X /\ s_ec (w_stk v X) = s_ec X /\ s_estk (w_stk v X) = s_estk X
  /\ s_edepth (w_stk v X) = s_edepth X /\ s_lo (w_stk v X) = s_lo X /\ s_hi (w_stk v X) = s_hi X /\ s_bad (w_stk v X) = s_bad X.
Proof. destruct X; cbn; repeat split; reflexivity. Qed.
Lemma w_pos_w_pos a b X : w_pos a (w_pos b X) = w_pos a X.
Proof. destruct X; reflexivity. Qed.

Definition m_indef (obj : bool) : pmode := if obj then Mikey else Miarray.
Definition m_count (obj : bool) : pmode := if obj then Mkey else Marray.
Definition m_typed (obj : bool) : pmode := if obj then Mtkey else Mtarray.
Definition k_indef (obj : bool) : Z := if obj then 1 else 3.
Definition k_len (obj : bool) : Z := if obj then 0 else 2.

Lemma rb_depth p obj X : MAX_DEPTH < s_depth X + 1 -> r_begin p obj X = r_fail (X1 X).
Proof. intros H. unfold r_begin, X1. cbv zeta. cbn [s_depth w_depth]. replace (MAX_DEPTH <? s_depth X + 1) with true by (symmetry; apply Z.ltb_lt; exact H). reflexivity. Qed.

Section Deep.
Variables (p : list Z) (obj : bool) (X : st).
Hypothesis DOK : s_depth X + 1 <= MAX_DEPTH.
Let pos := s_pos X.
Lemma rb_unfold : r_begin p obj X =
  (if blen p <=? pos then r_fail (X1 X)
   else if bat p pos =? 36 then
     if blen p <=? pos + 1 then r_fail (X1 X)
     else if blen p <=? pos + 2 then r_fail (X1 X)
     else if bat p (pos + 2) =? 35 then r_counted p (m_typed obj) (bat p (pos + 1)) (k_len obj) (w_pos (pos + 3) (X1 X))
     else r_fail (X1 X)
   else if bat p pos =? 35 then r_counted p (m_count obj) 0 (k_len obj) (w_pos (pos + 1) (X1 X))
   else w_more true (e_begin_indef (k_indef obj) (w_stk (PS (m_indef obj) 0 0 0 :: s_stk X) (X1 X)))).
Proof.
  unfold r_begin, X1, pos. cbv zeta. cbn [s_depth s_pos s_stk w_depth].
  replace (MAX_DEPTH <? s_depth X + 1) with false by (symmetry; apply Z.ltb_ge; exact DOK).
  destruct obj; reflexivity.
Qed.
Lemma rb_eof : blen p <= pos -> r_begin p obj X = r_fail (X1 X).
Proof. intros H. rewrite rb_unfold. replace (blen p <=? pos) with true by (symmetry; apply Z.leb_le; exact H). reflexivity. Qed.
Lemma rb_indef : pos < blen p -> bat p pos <> 36 -> bat p pos <> 35 ->
  r_begin p obj X = w_more true (e_begin_indef (k_indef obj) (w_stk (PS (m_indef obj) 0 0 0 :: s_stk X) (X1 X))).
Proof.
  intros H A B. rewrite rb_unfold. replace (blen p <=? pos) with false by (symmetry; apply Z.leb_gt; exact H).
  replace (bat p pos =? 36) with false by (symmetry; apply Z.eqb_neq; exact A). replace (bat p pos =? 35) with false by (symmetry; apply Z.eqb_neq; exact B). reflexivity.
Qed.
Lemma rb_count : pos < blen p -> bat p pos = 35 -> r_begin p obj X = r_counted p (m_count obj) 0 (k_len obj) (w_pos (pos + 1) (X1 X)).
Proof.
  intros H B. rewrite rb_unfold. replace (blen p <=? pos) with false by (symmetry; apply Z.leb_gt; exact H).
  replace (bat p pos =? 36) with false by (symmetry; apply Z.eqb_neq; rewrite B; discriminate). rewrite B. reflexivity.
Qed.
Lemma rb_typed_eof1 : pos < blen p -> bat p pos = 36 -> blen p <= pos + 1 -> r_begin p obj X = r_fail (X1 X).
Proof.
  intros H A E. rewrite rb_unfold. replace (blen p <=? pos) with false by (symmetry; apply Z.leb_gt; exact H).
  rewrite A. cbn [Z.eqb Pos.eqb]. replace (blen p <=? pos + 1) with true by (symmetry; apply Z.leb_le; exact E). reflexivity.
Qed.
Lemma rb_typed_eof2 : pos < blen p -> bat p pos = 36 -> pos + 1 < blen p -> blen p <= pos + 2 -> r_begin p obj X = r_fail (X1 X).
Proof.
  intros H A E1 E2. rewrite rb_unfold. replace (blen p <=? pos) with false by (symmetry; apply Z.leb_gt; exact H).
  rewrite A. cbn [Z.eqb Pos.eqb]. replace (blen p <=? pos + 1) with false by (symmetry; apply Z.leb_gt; exact E1).
  replace (blen p <=? pos + 2) with true by (symmetry; apply Z.leb_le; exact E2). reflexivity.
Qed.
Lemma rb_typed_bad : pos < blen p -> bat p pos = 36 -> pos + 2 < blen p -> bat p (pos + 2) <> 35 -> r_begin p obj X = r_fail (X1 X).
Proof.
  intros H A E1 B. rewrite rb_unfold. replace (blen p <=? pos) with false by (symmetry; apply Z.leb_gt; exact H).
  rewrite A. cbn [Z.eqb Pos.eqb]. replace (blen p <=? pos + 1) with false by (symmetry; apply Z.leb_gt; lia).
  replace (blen p <=? pos + 2) with false by (symmetry; apply Z.leb_gt; exact E1).
  replace (bat p (pos + 2) =? 35) with false by (symmetry; apply Z.eqb_neq; exact B). reflexivity.
Qed.
Lemma rb_typed : pos < blen p -> bat p pos = 36 -> pos + 2 < blen p -> bat p (pos + 2) = 35 ->
  r_begin p obj X = r_counted p (m_typed obj) (bat p (pos + 1)) (k_len obj) (w_pos (pos + 3) (X1 X)).
Proof.
  intros H A E1 B. rewrite rb_unfold. replace (blen p <=? pos) with false by (symmetry; apply Z.leb_gt; exact H).
  rewrite A. cbn [Z.eqb Pos.eqb]. replace (blen p <=? pos + 1) with false by (symmetry; apply Z.leb_gt; lia).
  replace (blen p <=? pos + 2) with false by (symmetry; apply Z.leb_gt; exact E1). rewrite B. reflexivity.
Qed.
End Deep.

Lemma rc_none p m ty kd s : get_length p (s_pos s) = None -> r_counted p m ty kd s = r_fail s.
Proof. intros H. unfold r_counted. rewrite H. reflexivity. Qed.
Lemma rc_pending p m ty kd s n pos1 : get_length p (s_pos s) = Some (n, pos1) -> s_ec s = true -> r_counted p m ty kd s = w_pos pos1 s.
Proof. intros H E. unfold r_counted. rewrite H, E. reflexivity. Qed.
Lemma rc_big p m ty kd s n pos1 : get_length p (s_pos s) = Some (n, pos1) -> s_ec s = false -> MAX_ITEMS < n -> r_counted p m ty kd s = r_fail s.
Proof. intros H E B. unfold r_counted. rewrite H, E. replace (MAX_ITEMS <? n) with true by (symmetry; apply Z.ltb_lt; exact B). reflexivity. Qed.
Lemma rc_ok p m ty kd s n pos1 : get_length p (s_pos s) = Some (n, pos1) -> s_ec s = false -> n <= MAX_ITEMS ->
  r_counted p m ty kd s = w_more true (e_begin_len kd n (w_stk (PS m n ty 0 :: s_stk s) (w_pos pos1 s))).
Proof. intros H E B. unfold r_counted. rewrite H, E. replace (MAX_ITEMS <? n) with false by (symmetry; apply Z.ltb_ge; exact B). reflexivity. Qed.

Lemma e_begin_len_fields kd n s : s_stk (e_begin_len kd n s) = s_stk s /\ s_pos (e_begin_len kd n s) = s_pos s /\ s_more (e_begin_len kd n s) = s_more s
  /\ s_done (e_begin_len kd n s) = s_done s /\ s_halt (e_begin_len kd n s) = s_halt s /\ s_depth (e_begin_len kd n s) = s_depth s.
Proof.
  unfold e_begin_len, e_put_length. cbv zeta. destruct (MAX_DEPTH <? _); [destruct s; cbn; repeat split; reflexivity|].
  destruct (INT64_MAX <? n); destruct s; cbn; repeat split; reflexivity.
Qed.
Lemma e_begin_indef_fields kd s : s_stk (e_begin_indef kd s) = s_stk s /\ s_pos (e_begin_indef kd s) = s_pos s /\ s_more (e_begin_indef kd s) = s_more s
  /\ s_done (e_begin_indef kd s) = s_done s /\ s_halt (e_begin_indef kd s) = s_halt s /\ s_depth (e_begin_indef kd s) = s_depth s.
Proof. unfold e_begin_indef. cbv zeta. destruct (MAX_DEPTH <? _); destruct s; cbn; repeat split; reflexivity. Qed.
Lemma w_more_e_begin_len kd n s : s_more s = true -> w_more true (e_begin_len kd n s) = e_begin_len kd n s.
Proof. intros H. apply w_more_same. destruct (e_begin_len_fields kd n s) as (_ & _ & -> & _). exact H. Qed.
Lemma w_more_e_begin_indef kd s : s_more s = true -> w_more true (e_begin_indef kd s) = e_begin_indef kd s.
Proof. intros H. apply w_more_same. destruct (e_begin_indef_fields kd s) as (_ & _ & -> & _). exact H. Qed.

Lemma slice_pos_1 p pos : 0 <= pos < blen p -> UbjRef.slice p pos 1 = [bat p pos].
Proof.
  intros H. unfold UbjRef.slice, bat, blen in *.
  remember (Z.to_nat pos) as i. assert (Hi : (i < length p)%nat) by (subst; lia). clear Heqi H.
  revert p Hi. induction i as [|i IH]; intros [|x l] Hl; cbn in *; try lia; [reflexivity|]. apply IH. lia.
Qed.

End PECBD.
