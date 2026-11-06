(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanSizeClass.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac leb_false x y := replace (x <=? y) with false by (symmetry; apply Z.leb_gt; lia).
Ltac leb_true x y := replace (x <=? y) with true by (symmetry; apply Z.leb_le; lia).
Ltac ltb_false x y := replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia).
Ltac ltb_true x y := replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma rounded_mult8 : forall n, 16 <= n -> n mod 8 = 0 -> rounded n = n.
Proof.
  intros n H1 H2. unfold rounded, round_up, kChunkHeader2Size. rewrite Z.max_l by lia. Z.div_mod_to_equations. nia.
Qed.

Lemma rz_size_big : forall n, 65536 - 1024 < n -> rz_size n = 2048.
Proof.
  intros n Hn. unfold rz_size, rz_log.
  leb_false n (64 - 16). leb_false n (128 - 32). leb_false n (512 - 64). leb_false n (4096 - 128).
  leb_false n (16384 - 256). leb_false n (32768 - 512). leb_false n (65536 - 1024). reflexivity.
Qed.

Lemma needed_big : forall n, 65536 - 1024 < n -> n mod 8 = 0 -> needed n = n + 4096 /\ from_primary n = false.
Proof.
  intros n Hn H8. unfold needed, from_primary, needed1. rewrite rounded_mult8 by lia. rewrite rz_size_big by lia.
  unfold kMaxSize. leb_false (n + 2048) 65536. split; [lia| reflexivity].
Qed.

Lemma map_size_big : forall n, 65536 - 1024 < n -> n mod 8 = 0 -> map_size n = (n + 4096 + 4095) / 4096 * 4096 + 4096.
Proof.
  intros n Hn H8. unfold map_size, round_up, kPageSize. rewrite (proj1 (needed_big n Hn H8)). f_equal. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma net128_big : forall t, t mod 128 = 0 -> 2^19 <= t -> t + 256 <= 2^40 -> acharge (t + 128) - arefund t <= 7.
Proof.
  intros t H128 Hlo Hhi.
  assert (E1 : (t + 128) mod 8 = 0) by (clear -H128; Z.div_mod_to_equations; lia).
  assert (E0 : t mod 8 = 0) by (clear -H128; Z.div_mod_to_equations; lia).
  unfold acharge, arefund.
  rewrite (proj2 (needed_big (t + 128) ltac:(lia) E1)). rewrite (proj2 (needed_big t ltac:(lia) E0)).
  rewrite (map_size_big (t + 128) ltac:(lia) E1). rewrite (map_size_big t ltac:(lia) E0).
  unfold kBigMapSize.
  replace ((t + 128 + 4096 + 4095) / 4096 * 4096 + 4096 <? 524288) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia).
  replace ((t + 4096 + 4095) / 4096 * 4096 + 4096 <? 524288) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia).
  Z.div_mod_to_equations. nia.
Qed.

Lemma rounded_add256 : forall n, 16 <= n -> rounded (n + 256) = rounded n + 256.
Proof. intros n Hn. unfold rounded, round_up, kChunkHeader2Size. rewrite !Z.max_l by lia. Z.div_mod_to_equations. nia. Qed.

Lemma needed_big' : forall n, 65536 - 1024 < n -> needed n = rounded n + 4096 /\ from_primary n = false.
Proof.
  intros n Hn. unfold needed, from_primary, needed1. rewrite rz_size_big by lia.
  assert (R : n <= rounded n) by (unfold rounded, round_up, kChunkHeader2Size; Z.div_mod_to_equations; nia).
  unfold kMaxSize. leb_false (rounded n + 2048) 65536. split; [lia| reflexivity].
Qed.

(* [comment removed for export] *)
Lemma net256_big : forall t, 2^19 <= t -> acharge (t + 256) - arefund t <= 7.
Proof.
  intros t Hlo.
  assert (R0 : t <= rounded t <= t + 7) by (unfold rounded, round_up, kChunkHeader2Size; Z.div_mod_to_equations; nia).
  pose proof (rounded_add256 t ltac:(lia)) as R1.
  unfold acharge, arefund, map_size, round_up, kPageSize.
  rewrite (proj2 (needed_big' (t + 256) ltac:(lia))), (proj2 (needed_big' t ltac:(lia))).
  rewrite (proj1 (needed_big' (t + 256) ltac:(lia))), (proj1 (needed_big' t ltac:(lia))). rewrite R1.
  unfold kBigMapSize.
  replace ((rounded t + 256 + 4096 + 4096 - 1) / 4096 * 4096 + 4096 <? 524288) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia).
  replace ((rounded t + 4096 + 4096 - 1) / 4096 * 4096 + 4096 <? 524288) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia).
  clear R1. Z.div_mod_to_equations. nia.
Qed.

Lemma acharge_nonneg : forall n, 0 <= acharge n.
Proof.
  intros n. unfold acharge, kCmPrim. destruct (from_primary n); [lia|].
  assert (0 <= map_size n).
  { unfold map_size, round_up, kPageSize, needed, needed1, rounded, round_up, kChunkHeader2Size, rz_size.
    pose proof (Z.pow_nonneg 2 (rz_log n) ltac:(lia)). destruct (from_primary n); Z.div_mod_to_equations; nia. }
  destruct (map_size n <? kBigMapSize); Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma acharge_le_2p28 : forall n, 0 < n <= 2^28 -> acharge n <= 73736.
Proof.
  intros n Hn. unfold acharge.
  destruct (from_primary n); [unfold kCmPrim; lia|].
  assert (MS : map_size n <= 2^28 + 4096 * 3).
  { unfold map_size, round_up, kPageSize, needed, needed1, rounded, round_up, kChunkHeader2Size.
    assert (R : rz_size n <= 2048).
    { unfold rz_size, rz_log. repeat (destruct (_ <=? _)); cbn; lia. }
    destruct (from_primary n); Z.div_mod_to_equations; nia. }
  destruct (map_size n <? kBigMapSize); Z.div_mod_to_equations; lia.
Qed.

Lemma acharge_prim : forall n, from_primary n = true -> acharge n = kCmPrim.
Proof. intros n H. unfold acharge. rewrite H. reflexivity. Qed.
Lemma arefund_prim : forall n, from_primary n = true -> arefund n = 0.
Proof. intros n H. unfold arefund. rewrite H. reflexivity. Qed.
End RC__1.
