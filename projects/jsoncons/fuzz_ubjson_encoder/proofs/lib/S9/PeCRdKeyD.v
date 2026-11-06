(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PeCSink PeCModel PeCSpecs PeCRdValD.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9.Spec Require Import UbjRefFactsS9.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECRKD.

Lemma e_key_stk n s : s_stk (e_key n s) = s_stk s. Proof. unfold e_key, e_put_length. destruct (INT64_MAX <? n); reflexivity. Qed.
Lemma e_key_pos n s : s_pos (e_key n s) = s_pos s. Proof. unfold e_key, e_put_length. destruct (INT64_MAX <? n); reflexivity. Qed.
Lemma e_key_more n s : s_more (e_key n s) = s_more s. Proof. unfold e_key, e_put_length. destruct (INT64_MAX <? n); reflexivity. Qed.
Lemma e_key_done n s : s_done (e_key n s) = s_done s. Proof. unfold e_key, e_put_length. destruct (INT64_MAX <? n); reflexivity. Qed.
Lemma e_key_halt n s : s_halt (e_key n s) = s_halt s. Proof. unfold e_key, e_put_length. destruct (INT64_MAX <? n); reflexivity. Qed.
Lemma e_key_depth n s : s_depth (e_key n s) = s_depth s. Proof. unfold e_key, e_put_length. destruct (INT64_MAX <? n); reflexivity. Qed.
Lemma e_key_ec n s : s_ec (e_key n s) = s_ec s. Proof. unfold e_key, e_put_length. destruct (INT64_MAX <? n); reflexivity. Qed.
Lemma e_key_estk n s : s_estk (e_key n s) = s_estk s. Proof. unfold e_key, e_put_length. destruct (INT64_MAX <? n); reflexivity. Qed.
Lemma e_key_edepth n s : s_edepth (e_key n s) = s_edepth s. Proof. unfold e_key, e_put_length. destruct (INT64_MAX <? n); reflexivity. Qed.

Lemma r_key_none p X : UbjRef.get_length p (s_pos X) = None -> r_key p X = r_fail X.
Proof. intros H. unfold r_key. rewrite H. reflexivity. Qed.
Lemma r_key_pending p X n pos1 : UbjRef.get_length p (s_pos X) = Some (n, pos1) -> s_ec X = true -> r_key p X = r_fail (w_pos pos1 X).
Proof. intros H E. unfold r_key. rewrite H, E. reflexivity. Qed.
Lemma r_key_short p X n pos1 : UbjRef.get_length p (s_pos X) = Some (n, pos1) -> s_ec X = false -> blen p < pos1 + n -> r_key p X = r_fail X.
Proof. intros H E L. unfold r_key. rewrite H, E. destruct (Z.ltb_spec (blen p) (pos1 + n)); [reflexivity| lia]. Qed.
Lemma r_key_invalid p X n pos1 : UbjRef.get_length p (s_pos X) = Some (n, pos1) -> s_ec X = false -> pos1 + n <= blen p ->
  utf8_valid (UbjRef.slice p pos1 n) = false -> r_key p X = r_fail X.
Proof. intros H E L V. unfold r_key. rewrite H, E, V. destruct (Z.ltb_spec (blen p) (pos1 + n)); [lia| reflexivity]. Qed.
Lemma r_key_valid p X n pos1 : UbjRef.get_length p (s_pos X) = Some (n, pos1) -> s_ec X = false -> pos1 + n <= blen p ->
  utf8_valid (UbjRef.slice p pos1 n) = true -> r_key p X = w_more true (e_key n (w_pos (pos1 + n) X)).
Proof. intros H E L V. unfold r_key. rewrite H, E, V. destruct (Z.ltb_spec (blen p) (pos1 + n)); [lia| reflexivity]. Qed.

Lemma but_pos_fail_any X q : PECRVD.but_pos (r_fail X) (w_more false (w_ec true (w_pos q X))).
Proof. unfold PECRVD.but_pos. destruct X; cbn; repeat split; reflexivity. Qed.
Lemma but_pos_fail_any2 X q q' : PECRVD.but_pos (r_fail (w_pos q' X)) (w_more false (w_ec true (w_pos q X))).
Proof. unfold PECRVD.but_pos. destruct X; cbn; repeat split; reflexivity. Qed.
Lemma but_pos_fail_refail0 X : PECRVD.but_pos (r_fail X) (w_more false (w_ec true (r_fail X))).
Proof. unfold PECRVD.but_pos. destruct X; cbn; repeat split; reflexivity. Qed.
Lemma but_pos_fail_refail X q : PECRVD.but_pos (r_fail X) (w_more false (w_ec true (r_fail (w_pos q X)))).
Proof. unfold PECRVD.but_pos. destruct X; cbn; repeat split; reflexivity. Qed.

End PECRKD.
