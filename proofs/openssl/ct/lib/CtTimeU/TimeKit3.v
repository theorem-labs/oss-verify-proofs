(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Mem Cells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeU Require Import TimeKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma le8_as_le4le4 : forall v, le8 (Z_to_bv 64 v) = le4 (Z_to_bv 64 v) ++ le4 (Z_to_bv 64 (v / 2^32)).
Proof.
  intros v. unfold le8, word_to_le_bytes, le4. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2^64).
  change (Z_to_le_bytes 8 (v mod 2^64)) with (Z_to_le_bytes 4 (v mod 2^64) ++ Z_to_le_bytes 4 (Z.shiftr (Z.shiftr (Z.shiftr (Z.shiftr (v mod 2^64) 8) 8) 8) 8)).
  f_equal. rewrite !Z.shiftr_div_pow2 by lia. rewrite !Z.div_div by lia.
  match goal with |- Z_to_le_bytes 4 ?a = _ => rewrite <- (Z_to_le_bytes_mod 4 a 32) by (cbn; lia) end.
  rewrite <- (Z_to_le_bytes_mod 4 ((v / 2^32) mod 2^64) 32) by (cbn; lia).
  f_equal. change (2^64) with 18446744073709551616. change (2^32) with 4294967296.
  Z.div_mod_to_equations. nia.
Qed.
Lemma C8_as_C4C4 : forall v, cells_bytes [C8 (Z_to_bv 64 v)] = cells_bytes [C4 (Z_to_bv 64 v); C4 (Z_to_bv 64 (v / 2^32))].
Proof. intros v. cbn [cells_bytes cbytes app]. rewrite app_nil_r. apply le8_as_le4le4. Qed.

Section WithSegs. Variable segs : list MemImageType.Segment.
Lemma rw_cells_recast3 : forall m A cs cs', rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
  intros m A cs cs' [[W B] R] W' E. split; [split; [exact W'| rewrite E; exact B]|].
  rewrite <- (cells_bytes_length cs' W'), E, (cells_bytes_length cs W). exact R.
Qed.
Lemma yr_slot_split : forall m A pre yr post,
  rw_cells segs m A (pre ++ C8 (Z_to_bv 64 yr) :: post) -> rw_cells segs m A (pre ++ C4 (Z_to_bv 64 yr) :: C4 (Z_to_bv 64 (yr / 2^32)) :: post).
Proof.
  intros m A pre yr post H. eapply rw_cells_recast3; [exact H| |].
  - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 W2]. apply cells_wf_app. split; [exact W1|]. cbn in W2 |- *. tauto.
  - rewrite !cells_bytes_app. f_equal. change (C8 (Z_to_bv 64 yr) :: post) with ([C8 (Z_to_bv 64 yr)] ++ post).
    change (C4 (Z_to_bv 64 yr) :: C4 (Z_to_bv 64 (yr / 2^32)) :: post) with ([C4 (Z_to_bv 64 yr); C4 (Z_to_bv 64 (yr / 2^32))] ++ post).
    rewrite !cells_bytes_app. f_equal. symmetry. apply C8_as_C4C4.
Qed.
Lemma yr_slot_join : forall m A pre yr post,
  rw_cells segs m A (pre ++ C4 (Z_to_bv 64 yr) :: C4 (Z_to_bv 64 (yr / 2^32)) :: post) -> rw_cells segs m A (pre ++ C8 (Z_to_bv 64 yr) :: post).
Proof.
  intros m A pre yr post H. eapply rw_cells_recast3; [exact H| |].
  - destruct H as [[W _] _]. apply cells_wf_app in W. destruct W as [W1 W2]. apply cells_wf_app. split; [exact W1|]. cbn in W2 |- *. tauto.
  - rewrite !cells_bytes_app. f_equal. change (C8 (Z_to_bv 64 yr) :: post) with ([C8 (Z_to_bv 64 yr)] ++ post).
    change (C4 (Z_to_bv 64 yr) :: C4 (Z_to_bv 64 (yr / 2^32)) :: post) with ([C4 (Z_to_bv 64 yr); C4 (Z_to_bv 64 (yr / 2^32))] ++ post).
    rewrite !cells_bytes_app. f_equal. apply C8_as_C4C4.
Qed.
End WithSegs.

(* [comment removed for export] *)
Ltac yr_split k H :=
  lazymatch type of H with rw_cells ?s ?m ?A ?cs =>
    let pre := eval cbv beta iota zeta delta [firstn] in (firstn k cs) in apply (yr_slot_split s m A pre) in H; cbn [app] in H end.
Ltac yr_join k H :=
  lazymatch type of H with rw_cells ?s ?m ?A ?cs =>
    let pre := eval cbv beta iota zeta delta [firstn] in (firstn k cs) in apply (yr_slot_join s m A pre) in H; cbn [app] in H end.

(* [comment removed for export] *)
Lemma slt_signed_small : forall a b, - 2^63 <= a < 2^63 -> - 2^63 <= b < 2^63 ->
  (Z.lxor (Z.land a 18446744073709551615) 9223372036854775808 <? Z.lxor (Z.land b 18446744073709551615) 9223372036854775808) = (a <? b).
Proof.
  intros a b Ha Hb. rewrite !land64.
  rewrite !(zb_lxor_sign) by (change (2^64) with 18446744073709551616; split; [apply Z.mod_pos_bound| apply Z.mod_pos_bound]; lia).
  change (2^63) with 9223372036854775808 in *. change (2^64) with 18446744073709551616 in *.
  destruct (Z.ltb_spec a b) as [L|L]; [apply Z.ltb_lt| apply Z.ltb_ge]; Z.div_mod_to_equations; lia.
Qed.

Lemma zlit_fold : forall (e v : Z), (bv_unsigned (Z_to_bv 64 e) = v)%Z -> Z_to_bv 64 e = Z_to_bv 64 v.
Proof.
  intros e v H. apply bv_eq. rewrite H. symmetry. rewrite Z_to_bv_unsigned. pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 e)) as R.
  rewrite H in R. unfold bv_wrap. rewrite Z.mod_small; [reflexivity| exact R].
Qed.
