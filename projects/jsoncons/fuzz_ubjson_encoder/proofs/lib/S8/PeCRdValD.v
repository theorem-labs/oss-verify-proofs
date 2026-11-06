(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PeCSink PeCModel PeCSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECRVD.
#[local] Transparent e_end_value.

Definition fin (s : st) : st := if s_ec s then w_more false s else s.

Definition is_num (t : Z) : bool := (t =? 105) || (t =? 85) || (t =? 73) || (t =? 108) || (t =? 76) || (t =? 100) || (t =? 68).
Definition is_marker (t : Z) : bool :=
  (t =? 90) || (t =? 84) || (t =? 70) || (t =? 78) || is_num t || (t =? 67) || (t =? 83) || (t =? 72) || (t =? 91) || (t =? 123).

Lemma rv_ZTF p t X : (t = 90 \/ t = 84 \/ t = 70) -> r_value p t X = fin (w_more true (e_scalar 1 1 X)).
Proof. intros [->|[->| ->]]; reflexivity. Qed.
Lemma rv_N p X : r_value p 78 X = fin X.
Proof. reflexivity. Qed.
Definition num_arm (p : list Z) (k lo hi : Z) (X : st) : st := let s' := r_num p k lo hi X in if s_more s' then fin s' else s'.
Lemma rv_i p X : r_value p 105 X = num_arm p 1 2 2 X. Proof. reflexivity. Qed.
Lemma rv_U p X : r_value p 85 X = num_arm p 1 2 2 X. Proof. reflexivity. Qed.
Lemma rv_I p X : r_value p 73 X = num_arm p 2 2 3 X. Proof. reflexivity. Qed.
Lemma rv_l p X : r_value p 108 X = num_arm p 4 2 5 X. Proof. reflexivity. Qed.
Lemma rv_L p X : r_value p 76 X = num_arm p 8 2 9 X. Proof. reflexivity. Qed.
Lemma rv_d p X : r_value p 100 X = num_arm p 4 5 9 X. Proof. reflexivity. Qed.
Lemma rv_D p X : r_value p 68 X = num_arm p 8 5 9 X. Proof. reflexivity. Qed.
Lemma rv_C p X : r_value p 67 X =
  (if blen p <? s_pos X + 1 then r_fail X
   else if utf8_valid (slice p (s_pos X) 1) then fin (w_more true (e_string true 1 (w_pos (s_pos X + 1) X)))
   else r_fail (w_pos (s_pos X + 1) X)).
Proof. reflexivity. Qed.
Definition str_arm (p : list Z) (t : Z) (X : st) : st :=
  match get_length p (s_pos X) with
  | None => r_fail X
  | Some (n, pos1) =>
      if s_ec X then w_pos pos1 X
      else if blen p <? pos1 + n then r_fail X
      else let v := utf8_valid (slice p pos1 n) in
           if (t =? 83) && negb v then r_fail X else fin (w_more true (e_string v n (w_pos (pos1 + n) X)))
  end.
Lemma rv_S p X : r_value p 83 X = str_arm p 83 X. Proof. reflexivity. Qed.
Lemma rv_H p X : r_value p 72 X = str_arm p 72 X. Proof. reflexivity. Qed.
Lemma rv_A p X : r_value p 91 X = fin (r_begin p false X). Proof. reflexivity. Qed.
Lemma rv_O p X : r_value p 123 X = fin (r_begin p true X). Proof. reflexivity. Qed.
Lemma rv_unknown p t X : is_marker t = false -> r_value p t X = fin (w_ec true X).
Proof.
  intros H. unfold is_marker, is_num in H.
  repeat match goal with G : _ || _ = false |- _ => apply orb_false_elim in G; destruct G as [G ?] end.
  unfold r_value. repeat match goal with G : (t =? ?c) = false |- _ => rewrite G; clear G end. reflexivity.
Qed.

Lemma unknown_cases t : 0 <= t < 256 -> is_marker t = false ->
  In t [69; 71; 74; 75; 77; 79; 80; 81; 82; 86; 87; 88; 89]
  \/ (0 <= t <= 66) \/ (92 <= t <= 99) \/ (101 <= t <= 104) \/ (106 <= t <= 107) \/ (109 <= t <= 122) \/ (124 <= t <= 255).
Proof.
  intros Ht H. unfold is_marker, is_num in H.
  repeat match goal with G : _ || _ = false |- _ => apply orb_false_elim in G; destruct G as [G ?] end.
  repeat match goal with G : (t =? ?c) = false |- _ => apply Z.eqb_neq in G end.
  destruct (Z_le_gt_dec t 66); [right; left; lia|]. destruct (Z_le_gt_dec t 91).
  - left. cbn. lia.
  - right. right. lia.
Qed.
Lemma marker_cases t : is_marker t = true ->
  (t = 90 \/ t = 84 \/ t = 70) \/ t = 78 \/ (t = 105 \/ t = 85 \/ t = 73 \/ t = 108 \/ t = 76 \/ t = 100 \/ t = 68)
  \/ t = 67 \/ (t = 83 \/ t = 72) \/ (t = 91 \/ t = 123).
Proof.
  intros H. unfold is_marker, is_num in H.
  repeat match goal with G : _ || _ = true |- _ => apply orb_true_elim in G; destruct G as [G|G] end;
    match goal with G : (t =? ?c) = true |- _ => apply Z.eqb_eq in G end; lia.
Qed.

Lemma w_more_same s : s_more s = true -> w_more true s = s.
Proof. destruct s; cbn; intros ->; reflexivity. Qed.
Lemma fin_false s : s_ec s = false -> fin s = s.
Proof. unfold fin; intros ->; reflexivity. Qed.
Lemma fin_true s : s_ec s = true -> fin s = w_more false s.
Proof. unfold fin; intros ->; reflexivity. Qed.

Lemma e_scalar_stk lo hi s : s_stk (e_scalar lo hi s) = s_stk s. Proof. unfold e_scalar. rewrite eev_stk. reflexivity. Qed.
Lemma e_scalar_pos lo hi s : s_pos (e_scalar lo hi s) = s_pos s. Proof. unfold e_scalar. rewrite eev_pos. reflexivity. Qed.
Lemma e_scalar_more lo hi s : s_more (e_scalar lo hi s) = s_more s. Proof. unfold e_scalar. rewrite eev_more. reflexivity. Qed.
Lemma e_scalar_done lo hi s : s_done (e_scalar lo hi s) = s_done s. Proof. unfold e_scalar. rewrite eev_done. reflexivity. Qed.
Lemma e_scalar_halt lo hi s : s_halt (e_scalar lo hi s) = s_halt s. Proof. unfold e_scalar. rewrite eev_halt. reflexivity. Qed.
Lemma e_scalar_depth lo hi s : s_depth (e_scalar lo hi s) = s_depth s. Proof. unfold e_scalar. rewrite eev_depth. reflexivity. Qed.
Lemma e_scalar_ec lo hi s : s_ec (e_scalar lo hi s) = s_ec s. Proof. unfold e_scalar. rewrite eev_ec. reflexivity. Qed.
Lemma e_string_stk v n s : s_stk (e_string v n s) = s_stk s.
Proof. unfold e_string, e_put_length. destruct v; [destruct (INT64_MAX <? n); cbn; rewrite eev_stk|]; reflexivity. Qed.
Lemma e_string_pos v n s : s_pos (e_string v n s) = s_pos s.
Proof. unfold e_string, e_put_length. destruct v; [destruct (INT64_MAX <? n); cbn; rewrite eev_pos|]; reflexivity. Qed.
Lemma e_string_more v n s : s_more (e_string v n s) = s_more s.
Proof. unfold e_string, e_put_length. destruct v; [destruct (INT64_MAX <? n); cbn; rewrite eev_more|]; reflexivity. Qed.
Lemma e_string_done v n s : s_done (e_string v n s) = s_done s.
Proof. unfold e_string, e_put_length. destruct v; [destruct (INT64_MAX <? n); cbn; rewrite eev_done|]; reflexivity. Qed.
Lemma e_string_halt v n s : s_halt (e_string v n s) = s_halt s.
Proof. unfold e_string, e_put_length. destruct v; [destruct (INT64_MAX <? n); cbn; rewrite eev_halt|]; reflexivity. Qed.
Lemma e_string_depth v n s : s_depth (e_string v n s) = s_depth s.
Proof. unfold e_string, e_put_length. destruct v; [destruct (INT64_MAX <? n); cbn; rewrite eev_depth|]; reflexivity. Qed.

Definition but_pos (a b : st) : Prop :=
  s_stk a = s_stk b /\ s_more a = s_more b /\ s_done a = s_done b /\ s_halt a = s_halt b /\ s_depth a = s_depth b /\ s_ec a = s_ec b
  /\ s_estk a = s_estk b /\ s_edepth a = s_edepth b /\ s_lo a = s_lo b /\ s_hi a = s_hi b /\ s_bad a = s_bad b.
Lemma but_pos_refl a : but_pos a a.
Proof. repeat split; reflexivity. Qed.
Lemma but_pos_w_pos a v : but_pos (w_pos v a) a.
Proof. destruct a; repeat split; reflexivity. Qed.
Lemma but_pos_sym a b : but_pos a b -> but_pos b a.
Proof. intros H. destruct H as (?&?&?&?&?&?&?&?&?&?&?). repeat split; symmetry; assumption. Qed.
Lemma but_pos_trans a b c : but_pos a b -> but_pos b c -> but_pos a c.
Proof. intros H1 H2. destruct H1 as (?&?&?&?&?&?&?&?&?&?&?). destruct H2 as (?&?&?&?&?&?&?&?&?&?&?). repeat split; congruence. Qed.
Lemma but_pos_r_fail a b : but_pos a b -> but_pos (r_fail a) (r_fail b).
Proof. intros H. destruct H as (?&?&?&?&?&?&?&?&?&?&?). destruct a, b; cbn in *; subst; repeat split; reflexivity. Qed.
Lemma but_pos_w_more a b v : but_pos a b -> but_pos (w_more v a) (w_more v b).
Proof. intros H. destruct H as (?&?&?&?&?&?&?&?&?&?&?). destruct a, b; cbn in *; subst; repeat split; reflexivity. Qed.
Lemma r_fail_more a : s_more (r_fail a) = false. Proof. reflexivity. Qed.
Lemma r_fail_ec a : s_ec (r_fail a) = true. Proof. reflexivity. Qed.

Lemma clink_but_pos p a b s sm en k : s_more b = false -> but_pos a b -> PEC.clink p b s sm en k -> PEC.clink p a s sm en k.
Proof.
  intros Hm H (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). destruct H as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E10&E11).
  unfold PEC.clink. rewrite E1, E2, E3, E5, E7, E8, E9, E10, E11.
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|].
  split; [intros M1 _; exfalso; rewrite Hm in M1; discriminate|].
  split; [exact L6|]. split; [exact L7|]. split; [exact L8| exact L9].
Qed.

Lemma num_arm_short p k lo hi X : blen p < s_pos X + k -> num_arm p k lo hi X = r_fail X.
Proof. intros H. unfold num_arm, r_num. replace (blen p <? s_pos X + k) with true by (symmetry; apply Z.ltb_lt; exact H). reflexivity. Qed.
Lemma num_arm_ok p k lo hi X : s_pos X + k <= blen p ->
  num_arm p k lo hi X = fin (w_more true (e_scalar lo hi (w_pos (s_pos X + k) X))).
Proof.
  intros H. unfold num_arm, r_num. replace (blen p <? s_pos X + k) with false by (symmetry; apply Z.ltb_ge; lia).
  cbn [s_more w_more]. reflexivity.
Qed.

Lemma word_as_signed (w : bv 64) : exists v, - 2 ^ 63 <= v < 2 ^ 63 /\ w = Z_to_bv 64 v.
Proof.
  exists (bv_signed w). split.
  - pose proof (bv_signed_in_range 64 w ltac:(discriminate)) as H. unfold bv_half_modulus in H.
    change (bv_modulus 64 `div` 2) with (2 ^ 63) in H. lia.
  - apply (proj2 (bv_eq_signed 64 _ _)). rewrite Z_to_bv_signed, bv_swrap_bv_signed. reflexivity.
Qed.

Lemma slice_pos_1 p pos : 0 <= pos < blen p -> UbjRef.slice p pos 1 = [bat p pos].
Proof.
  intros H. unfold UbjRef.slice, bat, blen in *.
  remember (Z.to_nat pos) as i. assert (Hi : (i < length p)%nat) by (subst; lia). clear Heqi H.
  revert p Hi. induction i as [|i IH]; intros [|x l] Hl; cbn in *; try lia; [reflexivity|]. apply IH. lia.
Qed.
Lemma slice_length p pos n : 0 <= pos -> 0 <= n -> pos + n <= blen p -> Z.of_nat (length (UbjRef.slice p pos n)) = n.
Proof. intros H1 H2 H3. unfold UbjRef.slice, blen in *. rewrite length_firstn, length_skipn. lia. Qed.
Lemma slice_bytes p pos n : UbjRefFactsS8.bytes_ok p -> Forall (fun b => 0 <= b < 256) (UbjRef.slice p pos n).
Proof. intros H. unfold UbjRef.slice. apply Forall_firstn. apply Forall_skipn. exact H. Qed.
Lemma bat_byte p pos : UbjRefFactsS8.bytes_ok p -> 0 <= pos < blen p -> 0 <= bat p pos < 256.
Proof.
  intros H Hp. unfold bat, blen in *. unfold UbjRefFactsS8.bytes_ok in H.
  apply (Forall_nth (fun b => 0 <= b < 256) p); [exact H|]. lia.
Qed.

Lemma iw8 v : -128 <= v < 128 -> PECS.int64_width v = 2.
Proof.
  intros H. unfold PECS.int64_width, PECS.uint64_width.
  destruct (Z.leb_spec 0 v); [destruct (Z.leb_spec v 255); [reflexivity| lia]|]. destruct (Z.leb_spec (-128) v); [reflexivity| lia].
Qed.
Lemma iw16 v : - 2 ^ 15 <= v < 2 ^ 15 -> 2 <= PECS.int64_width v <= 3.
Proof.
  intros H. unfold PECS.int64_width, PECS.uint64_width.
  destruct (Z.leb_spec 0 v).
  - destruct (Z.leb_spec v 255); [lia|]. destruct (Z.leb_spec v 32767); [lia|]. exfalso. cbn in H. lia.
  - destruct (Z.leb_spec (-128) v); [lia|]. destruct (Z.leb_spec (-32768) v); [lia|]. exfalso. cbn in H. lia.
Qed.
Lemma iw32 v : - 2 ^ 31 <= v < 2 ^ 31 -> 2 <= PECS.int64_width v <= 5.
Proof.
  intros H. unfold PECS.int64_width, PECS.uint64_width.
  destruct (Z.leb_spec 0 v).
  - destruct (Z.leb_spec v 255); [lia|]. destruct (Z.leb_spec v 32767); [lia|]. destruct (Z.leb_spec v 2147483647); [lia|]. exfalso. cbn in H. lia.
  - destruct (Z.leb_spec (-128) v); [lia|]. destruct (Z.leb_spec (-32768) v); [lia|]. destruct (Z.leb_spec (-2147483648) v); [lia|]. exfalso. cbn in H. lia.
Qed.
Lemma iw64 v : 2 <= PECS.int64_width v <= 9.
Proof.
  unfold PECS.int64_width, PECS.uint64_width.
  destruct (Z.leb_spec 0 v).
  - destruct (Z.leb_spec v 255); [lia|]. destruct (Z.leb_spec v 32767); [lia|]. destruct (Z.leb_spec v 2147483647); lia.
  - destruct (Z.leb_spec (-128) v); [lia|]. destruct (Z.leb_spec (-32768) v); [lia|]. destruct (Z.leb_spec (-2147483648) v); lia.
Qed.
Lemma uw8 v : 0 <= v <= 255 -> PECS.uint64_width v = 2.
Proof. intros H. unfold PECS.uint64_width. destruct (Z.leb_spec v 255); [reflexivity| lia]. Qed.

Lemma e_scalar_estk lo hi lo' hi' s : s_estk (e_scalar lo hi s) = s_estk (e_scalar lo' hi' s).
Proof. unfold e_scalar, e_end_value. cbn [s_estk w_out]. destruct (s_estk s); reflexivity. Qed.
Lemma e_scalar_edepth lo hi s : s_edepth (e_scalar lo hi s) = s_edepth s. Proof. unfold e_scalar. rewrite eev_edepth. reflexivity. Qed.
Lemma e_scalar_lo lo hi s : s_lo (e_scalar lo hi s) = s_lo s + lo. Proof. unfold e_scalar. rewrite eev_lo. reflexivity. Qed.
Lemma e_scalar_hi lo hi s : s_hi (e_scalar lo hi s) = s_hi s + hi. Proof. unfold e_scalar. rewrite eev_hi. reflexivity. Qed.
Lemma e_scalar_bad lo hi s : s_bad (e_scalar lo hi s) = s_bad s. Proof. unfold e_scalar. rewrite eev_bad. reflexivity. Qed.
Lemma clink_scalar_widen p lo hi w Y s sm en k :
  lo <= w <= hi -> PEC.clink p (e_scalar w w Y) s sm en k -> PEC.clink p (e_scalar lo hi Y) s sm en k.
Proof.
  intros Hw (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). unfold PEC.clink.
  rewrite !e_scalar_more, !e_scalar_done, !e_scalar_depth, !e_scalar_stk, !e_scalar_pos, !e_scalar_edepth, !e_scalar_lo, !e_scalar_hi, !e_scalar_bad in *.
  rewrite (e_scalar_estk lo hi w w).
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|].
  split; [exact L6|]. split; [exact L7|]. split; [lia| exact L9].
Qed.

End PECRVD.
