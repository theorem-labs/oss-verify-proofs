(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_dview Z_updwin_pure.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface InflateState RefUpdWin1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma isw_window : forall s B, is_window (iset_window s B) = B. Proof. intros s B; destruct s; reflexivity. Qed.
Lemma isw_wsize : forall s B, is_wsize (iset_window s B) = is_wsize s. Proof. intros s B; destruct s; reflexivity. Qed.
Lemma isw_wnext : forall s B, is_wnext (iset_window s B) = is_wnext s. Proof. intros s B; destruct s; reflexivity. Qed.
Lemma isw_whave : forall s B, is_whave (iset_window s B) = is_whave s. Proof. intros s B; destruct s; reflexivity. Qed.
Lemma isn_window : forall s n, is_window (iset_wnext s n) = is_window s. Proof. intros s n; destruct s; reflexivity. Qed.
Lemma isn_wsize : forall s n, is_wsize (iset_wnext s n) = is_wsize s. Proof. intros s n; destruct s; reflexivity. Qed.
Lemma isn_wnext : forall s n, is_wnext (iset_wnext s n) = n. Proof. intros s n; destruct s; reflexivity. Qed.
Lemma isn_whave : forall s n, is_whave (iset_wnext s n) = is_whave s. Proof. intros s n; destruct s; reflexivity. Qed.
Lemma isn_isn : forall s a b, iset_wnext (iset_wnext s a) b = iset_wnext s b. Proof. intros s a b; destruct s; reflexivity. Qed.
Lemma isw_isw : forall s A B, iset_window (iset_window s A) B = iset_window s B. Proof. intros s A B; destruct s; reflexivity. Qed.
Lemma uw_set_of3 : forall s B w n h, is_wsize s = w -> iset_whave (iset_wnext (iset_window s B) n) h = uw_set s B w n h.
Proof. intros s B w n h H; unfold uw_set; destruct s; cbn in H; subst; reflexivity. Qed.
Lemma uw_set_of2 : forall s B w n, is_wsize s = w -> iset_wnext (iset_window s B) n = uw_set s B w n (is_whave s).
Proof. intros s B w n H; unfold uw_set; destruct s; cbn in H; subst; reflexivity. Qed.

Local Ltac isf := repeat first [ rewrite isw_window | rewrite isw_wsize | rewrite isw_wnext | rewrite isw_whave
                                 | rewrite isn_window | rewrite isn_wsize | rewrite isn_wnext | rewrite isn_whave | rewrite isn_isn | rewrite isw_isw ].

Lemma updw_full : forall s src e copy,
  is_wsize s = 32768 -> 32768 <= copy ->
  updw_core s src e copy = uw_set s (arr_blit (is_window s) 0 src (e - 32768) 32768) 32768 0 32768.
Proof.
  intros s src e copy Hws Hc. unfold updw_core, sA. cbv zeta. rewrite Hws. change (32768 =? 0) with false. cbv iota.
  rewrite Hws. replace (32768 <=? copy) with true by (symmetry; apply Z.leb_le; lia).
  isf. rewrite Hws. apply uw_set_of3. exact Hws.
Qed.

Lemma updw_wrap : forall s src e copy,
  is_wsize s = 32768 -> 0 <= is_wnext s < 32768 -> 0 <= copy < 32768 -> 32768 - is_wnext s < copy ->
  updw_core s src e copy
  = uw_set s (arr_blit (arr_blit (is_window s) (is_wnext s) src (e - copy) (32768 - is_wnext s))
                       0 src (e - (copy - (32768 - is_wnext s))) (copy - (32768 - is_wnext s)))
           32768 (copy - (32768 - is_wnext s)) 32768.
Proof.
  intros s src e copy Hws Hwn Hc Hd. unfold updw_core, sA. cbv zeta. rewrite Hws. change (32768 =? 0) with false. cbv iota.
  rewrite Hws. replace (32768 <=? copy) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite (wrap32_id (32768 - is_wnext s)) by lia.
  replace (copy <? 32768 - is_wnext s) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite (wrap32_id (copy - (32768 - is_wnext s))) by lia.
  replace (copy - (32768 - is_wnext s) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
  isf. rewrite Hws. apply uw_set_of3. exact Hws.
Qed.

Lemma updw_app : forall s src e copy,
  is_wsize s = 32768 -> 0 <= is_wnext s < 32768 -> 0 <= is_whave s <= 32768 -> 0 <= copy < 32768 -> copy <= 32768 - is_wnext s ->
  updw_core s src e copy
  = uw_set s (arr_blit (is_window s) (is_wnext s) src (e - copy) copy) 32768
           (if is_wnext s + copy =? 32768 then 0 else is_wnext s + copy)
           (if is_whave s <? 32768 then is_whave s + copy else is_whave s).
Proof.
  intros s src e copy Hws Hwn Hwh Hc Hd. unfold updw_core, sA. cbv zeta. rewrite Hws. change (32768 =? 0) with false. cbv iota.
  rewrite Hws. replace (32768 <=? copy) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite (wrap32_id (32768 - is_wnext s)) by lia.
  assert (ED : (if copy <? 32768 - is_wnext s then copy else 32768 - is_wnext s) = copy).
  { destruct (Z.ltb_spec copy (32768 - is_wnext s)); lia. }
  rewrite ED. rewrite Z.sub_diag. change (wrap32 0) with 0. change (negb (0 =? 0)) with false. cbv iota.
  isf. rewrite ?Hws. rewrite (wrap32_id (is_wnext s + copy)) by lia.
  destruct (is_wnext s + copy =? 32768); isf; rewrite ?Hws;
    (destruct (Z.ltb_spec (is_whave s) 32768); [rewrite (wrap32_id (is_whave s + copy)) by lia|]);
    isf; first [apply uw_set_of3; exact Hws | apply uw_set_of2; exact Hws].
Qed.

Lemma av8_blit2 : forall (w src : arr) k so1 d so2 n N,
  0 <= k -> 0 <= d -> k + d = N -> 0 <= n -> n <= k -> N <= arr_len w ->
  map (Z_to_bv 8) (arr_slice src so2 n) ++ skipn (Z.to_nat n) (firstn (Z.to_nat k) (av8 w N)) ++ map (Z_to_bv 8) (arr_slice src so1 d)
  = av8 (arr_blit (arr_blit w k src so1 d) 0 src so2 n) N.
Proof.
  intros w src k so1 d so2 n N Hk Hd HN Hn Hnk HL.
  assert (LS1 : length (arr_slice src so1 d) = Z.to_nat d) by (unfold arr_slice; apply arr_slice_nat_length).
  assert (LS2 : length (arr_slice src so2 n) = Z.to_nat n) by (unfold arr_slice; apply arr_slice_nat_length).
  pose proof (av8_length w N) as LW.
  rewrite <- (av8_blit (arr_blit w k src so1 d) src 0 so2 n N) by (rewrite ?arr_len_blit; lia).
  rewrite <- (av8_blit w src k so1 d N) by lia.
  change (Z.to_nat 0) with 0%nat. rewrite firstn_O, Nat.add_0_l, app_nil_l.
  f_equal.
  rewrite skipn_app. rewrite length_firstn, LW. replace (Nat.min (Z.to_nat k) (Z.to_nat N)) with (Z.to_nat k) by lia.
  replace (Z.to_nat n - Z.to_nat k)%nat with 0%nat by lia. rewrite skipn_O.
  f_equal. rewrite (skipn_all2 (av8 w N)) by (rewrite LW; lia). rewrite app_nil_r. reflexivity.
Qed.
