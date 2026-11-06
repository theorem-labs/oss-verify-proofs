(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsOps.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nra Cache. Unset Nia Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module L5W.
Definition nth_w (ws : list Z) (i : nat) : Z := nth i ws 0.
Lemma nth_w_eq ws i : nth_w ws i = BigModel.nth_w ws i. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition words_ok (ws : list Z) : Prop := Forall (fun w => 0 <= w < 2 ^ 64) ws.
Lemma words_ok_nth ws j : words_ok ws -> 0 <= nth_w ws j < 2 ^ 64.
Proof.
  intros F. unfold nth_w. destruct (Nat.lt_ge_cases j (length ws)) as [Hl|Hg].
  - apply (Forall_nth (fun w => 0 <= w < 2 ^ 64) ws). exact F. exact Hl.
  - rewrite nth_overflow by lia. lia.
Qed.
Lemma words_ok_app a b : words_ok a -> words_ok b -> words_ok (a ++ b).
Proof. intros; apply Forall_app; auto. Qed.
Lemma words_ok_BF ws : words_ok ws <-> BigFactsBase.words_ok ws.
Proof.
  unfold words_ok, BigFactsBase.words_ok, BigFactsBase.wordZ. rewrite BigFactsBase.M_val.
  split; intros F; eapply Forall_impl; [|exact F| |exact F]; cbn; intros; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rlen (ws : list Z) : nat := length (BigModel.reduce_loop (length ws) ws).

Lemma last_is_nth (ws : list Z) : last ws 0 = nth (length ws - 1) ws 0.
Proof.
  induction ws as [|w ws IH]. reflexivity.
  destruct ws as [|w' ws']. reflexivity.
  cbn [last]. cbn [last] in IH. rewrite IH. cbn [length].
  replace (S (S (length ws')) - 1)%nat with (S (S (length ws') - 1))%nat by lia. reflexivity.
Qed.

Lemma removelast_firstn' (ws : list Z) : removelast ws = firstn (length ws - 1) ws.
Proof. apply BigFactsOps.removelast_firstn. Qed.

Lemma reduce_loop_exact : forall f (ws : list Z) (n' : nat),
  (length ws <= f)%nat -> (n' <= length ws)%nat ->
  (forall i, (n' <= i < length ws)%nat -> nth_w ws i = 0) ->
  (n' = 0%nat \/ nth_w ws (n' - 1) <> 0) ->
  BigModel.reduce_loop f ws = firstn n' ws.
Proof.
  induction f as [|f IH]; intros ws n' Hf Hn Hz Ht.
  - destruct ws. cbn. destruct n'; reflexivity. cbn in Hf. lia.
  - cbn [BigModel.reduce_loop]. destruct ws as [|w ws'] eqn:Ews. { destruct n'; reflexivity. }
    assert (L1: (1 <= length ws)%nat) by (rewrite Ews; cbn; lia). rewrite <- Ews in *. clear Ews w ws'.
    destruct (Nat.eq_dec n' (length ws)) as [->|NE].
    + rewrite firstn_all. rewrite last_is_nth.
      destruct Ht as [H0|Hnz]. lia.
      unfold nth_w in Hnz. destruct (Z.eqb_spec (nth (length ws - 1) ws 0) 0); [contradiction|reflexivity].
    + rewrite last_is_nth. unfold nth_w in Hz. rewrite (Hz (length ws - 1)%nat) by lia. cbn [Z.eqb].
      rewrite removelast_firstn'.
      rewrite (IH (firstn (length ws - 1) ws) n').
      * rewrite firstn_firstn. f_equal. lia.
      * rewrite length_firstn. lia.
      * rewrite length_firstn. lia.
      * intros i Hi. rewrite length_firstn in Hi. unfold nth_w. rewrite nth_firstn. destruct (Nat.ltb_spec i (length ws - 1)). apply Hz. lia. lia.
      * destruct Ht as [H0|Hnz]. left; exact H0. right. unfold nth_w in *. rewrite nth_firstn. destruct (Nat.ltb_spec (n' - 1) (length ws - 1)). exact Hnz. exfalso. apply Hnz. apply Hz. lia.
Qed.

Lemma rlen_charact (ws : list Z) (n' : nat) :
  (n' <= length ws)%nat -> (forall i, (n' <= i < length ws)%nat -> nth_w ws i = 0) -> (n' = 0%nat \/ nth_w ws (n' - 1) <> 0) ->
  rlen ws = n'.
Proof.
  intros Hn Hz Ht. unfold rlen. rewrite (reduce_loop_exact (length ws) ws n' ltac:(lia) Hn Hz Ht). rewrite length_firstn. lia.
Qed.
Lemma rlen_le ws : (rlen ws <= length ws)%nat.
Proof. unfold rlen. apply BigFactsOps.reduce_loop_length. Qed.
Lemma rlen_top ws : (1 <= rlen ws)%nat -> nth_w ws (rlen ws - 1) <> 0.
Proof.
  intros H. unfold rlen in *.
  pose proof (BigFactsOps.reduce_loop_reduced (length ws) ws ltac:(lia)) as RD.
  pose proof (BigFactsOps.reduce_loop_nth (length ws) ws (length (BigModel.reduce_loop (length ws) ws) - 1) ltac:(lia)) as E.
  unfold nth_w. unfold BigModel.nth_w in E. rewrite <- E. apply BigFactsOps.reduced_ws_top. exact RD.
  intros C. rewrite C in H. cbn in H. lia.
Qed.
Lemma reduce_loop_drops_zeros : forall f (l : list Z),
  exists m, BigModel.reduce_loop f l = firstn m l /\ (m <= length l)%nat /\ (forall j, (m <= j < length l)%nat -> nth j l 0 = 0).
Proof.
  induction f as [|f IH]; intros l.
  - exists (length l). cbn. rewrite firstn_all. split. reflexivity. split. lia. intros; lia.
  - cbn [BigModel.reduce_loop]. destruct l as [|w l'] eqn:El. { exists 0%nat. split. reflexivity. split. cbn; lia. intros; cbn in *; lia. }
    rewrite <- El in *. assert (NE: l <> []) by (subst l; discriminate). clear El.
    destruct (Z.eqb_spec (last l 0) 0) as [Z0|NZ].
    + rewrite BigFactsOps.removelast_firstn. destruct (IH (firstn (length l - 1) l)) as (m & E & Hm & Hz).
      rewrite length_firstn in Hm, Hz.
      exists m. split. { rewrite E. rewrite firstn_firstn. f_equal. lia. } split. lia.
      intros j Hj. destruct (Nat.eq_dec j (length l - 1)) as [->|NEj]. { rewrite <- last_is_nth. exact Z0. }
      specialize (Hz j ltac:(lia)). rewrite nth_firstn in Hz. destruct (Nat.ltb_spec j (length l - 1)); [exact Hz|lia].
    + exists (length l). rewrite firstn_all. split. reflexivity. split. lia. intros; lia.
Qed.
Lemma rlen_zeros ws i : (rlen ws <= i < length ws)%nat -> nth_w ws i = 0.
Proof.
  intros Hi. unfold rlen, nth_w in *. destruct (reduce_loop_drops_zeros (length ws) ws) as (m & E & Hm & Hz).
  rewrite E, length_firstn in Hi. apply Hz. lia.
Qed.
(* [comment removed for export] *)
Lemma rlen_ge_of_nonzero ws j : (j < length ws)%nat -> nth_w ws j <> 0 -> (j < rlen ws)%nat.
Proof. intros Hj Hnz. destruct (Nat.lt_ge_cases j (rlen ws)). exact H. exfalso. apply Hnz. apply rlen_zeros. lia. Qed.
Lemma rlen_le_of_zeros ws m : (m <= length ws)%nat -> (forall i, (m <= i < length ws)%nat -> nth_w ws i = 0) -> (rlen ws <= m)%nat.
Proof.
  intros Hm Hz. destruct (Nat.lt_ge_cases m (rlen ws)). 2: exact H. exfalso.
  pose proof (rlen_le ws). apply (rlen_top ws ltac:(lia)). apply Hz. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shl_words (ws : list Z) (k : Z) : list Z :=
  map (BigFactsOps.shlG k (ws ++ [0])) (seq 0 (S (length ws))).
Lemma shl_words_length ws k : length (shl_words ws k) = S (length ws).
Proof. unfold shl_words. rewrite length_map, length_seq. reflexivity. Qed.
Lemma shl_words_nth ws k j : (j <= length ws)%nat -> nth_w (shl_words ws k) j = BigFactsOps.shlG k (ws ++ [0]) j.
Proof.
  intros Hj. unfold shl_words, nth_w. rewrite (nth_indep _ 0 (BigFactsOps.shlG k (ws ++ [0]) 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.
Lemma shl_words_ok ws k : 0 < k < 64 -> words_ok ws -> words_ok (shl_words ws k).
Proof.
  intros Hk W. unfold words_ok, shl_words. apply Forall_map. apply Forall_forall. intros j _.
  pose proof (proj2 (BigFactsOps.shlG_val k Hk (ws ++ [0]) j ltac:(apply (proj1 (words_ok_BF _)); apply words_ok_app; [exact W | constructor; [lia|constructor]]))) as R.
  unfold BigFactsBase.wordZ in R. rewrite BigFactsBase.M_val in R. lia.
Qed.
(* [comment removed for export] *)
Lemma shl_words_val ws k : 0 < k < 64 -> words_ok ws -> BigFactsBase.val (shl_words ws k) = 2 ^ k * BigFactsBase.val ws.
Proof.
  intros Hk W.
  assert (WO: BigFactsBase.words_ok (ws ++ [0])). { apply (proj1 (words_ok_BF _)). apply words_ok_app. exact W. constructor. lia. constructor. }
  pose proof (BigFactsOps.shl_val_prefix k Hk (ws ++ [0]) (shl_words ws k) WO) as VP.
  rewrite shl_words_length, length_app in VP. cbn [length] in VP.
  specialize (VP ltac:(lia)). specialize (VP ltac:(intros j Hj; rewrite <- (shl_words_nth ws k j) by lia; reflexivity)).
  specialize (VP (S (length ws)) ltac:(lia)).
  rewrite firstn_all2 in VP by (rewrite shl_words_length; lia). rewrite firstn_all2 in VP by (rewrite length_app; cbn; lia).
  rewrite VP. replace (S (length ws) - 1)%nat with (length ws) by lia.
  rewrite BigFactsBase.nth_w_app_r by lia. rewrite Nat.sub_diag. cbn [BigModel.nth_w nth].
  rewrite Z.div_0_l by (apply Z.pow_nonzero; lia). rewrite BigFactsBase.val_app, BigFactsBase.val_cons, BigFactsBase.val_nil. lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint mulw_loop (ws : list Z) (y c : Z) : list Z :=
  match ws with
  | [] => [c]
  | w :: ws' => (w * y + c) mod 2 ^ 64 :: mulw_loop ws' y ((w * y + c) / 2 ^ 64)
  end.
Definition mulw_words (ws : list Z) (y : Z) : list Z := mulw_loop ws y 0.
(* [comment removed for export] *)
Fixpoint mulw_c (ws : list Z) (y c : Z) (i : nat) : Z :=
  match i, ws with
  | O, _ => c
  | S i', w :: ws' => mulw_c ws' y ((w * y + c) / 2 ^ 64) i'
  | S _, [] => c
  end.

Lemma mulw_step_bound w y c : 0 <= w < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> 0 <= (w * y + c) / 2 ^ 64 < 2 ^ 64.
Proof.
  intros Hw Hy Hc. split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound. lia.
  assert (w * y <= (2 ^ 64 - 1) * (2 ^ 64 - 1)) by nia. lia.
Qed.
Lemma mulw_loop_length ws : forall y c, length (mulw_loop ws y c) = S (length ws).
Proof. induction ws as [|w ws IH]; intros; cbn [mulw_loop length]. reflexivity. rewrite IH. reflexivity. Qed.
Lemma mulw_loop_ok ws : forall y c, words_ok ws -> 0 <= y < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> words_ok (mulw_loop ws y c).
Proof.
  induction ws as [|w ws IH]; intros y c W Hy Hc; cbn [mulw_loop].
  - constructor. lia. constructor.
  - inversion W; subst. constructor. apply Z.mod_pos_bound; lia. apply IH; auto. apply mulw_step_bound; lia.
Qed.
Lemma mulw_loop_val ws : forall y c, BigFactsBase.val (mulw_loop ws y c) = y * BigFactsBase.val ws + c.
Proof.
  induction ws as [|w ws IH]; intros y c; cbn [mulw_loop].
  - rewrite BigFactsBase.val_cons, !BigFactsBase.val_nil. lia.
  - rewrite !BigFactsBase.val_cons, IH. rewrite BigFactsBase.M_val.
    pose proof (Z.div_mod (w * y + c) (2 ^ 64) ltac:(lia)) as DM. change (2 ^ 64) with 18446744073709551616 in *. nia.
Qed.
Lemma mulw_c_0 ws y c : mulw_c ws y c 0 = c.
Proof. destruct ws; reflexivity. Qed.
Lemma mulw_c_S ws : forall y c i, (i < length ws)%nat -> mulw_c ws y c (S i) = (nth_w ws i * y + mulw_c ws y c i) / 2 ^ 64.
Proof.
  induction ws as [|w ws IH]; intros y c i Hi; cbn [length] in Hi. lia.
  destruct i as [|i]. - cbn [mulw_c nth_w nth]. rewrite mulw_c_0. reflexivity.
  - cbn [mulw_c]. rewrite (IH y _ i) by lia. unfold nth_w. cbn [nth]. reflexivity.
Qed.
Lemma mulw_c_bound ws : forall y c i, words_ok ws -> 0 <= y < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> 0 <= mulw_c ws y c i < 2 ^ 64.
Proof.
  induction ws as [|w ws IH]; intros y c [|i] W Hy Hc; cbn [mulw_c]; try lia.
  inversion W; subst. apply IH; auto. apply mulw_step_bound; lia.
Qed.
Lemma mulw_loop_nth ws : forall y c i, (i < length ws)%nat ->
  nth_w (mulw_loop ws y c) i = (nth_w ws i * y + mulw_c ws y c i) mod 2 ^ 64.
Proof.
  induction ws as [|w ws IH]; intros y c i Hi; cbn [length] in Hi. lia.
  destruct i as [|i]; cbn [mulw_loop mulw_c nth_w nth]. reflexivity.
  unfold nth_w in IH. rewrite IH by lia. reflexivity.
Qed.
Lemma mulw_loop_last ws : forall y c, nth_w (mulw_loop ws y c) (length ws) = mulw_c ws y c (length ws).
Proof.
  induction ws as [|w ws IH]; intros y c; cbn [mulw_loop mulw_c length nth_w nth]. reflexivity.
  unfold nth_w in IH. rewrite IH. reflexivity.
Qed.
Lemma mulw_words_length ws y : length (mulw_words ws y) = S (length ws).
Proof. apply mulw_loop_length. Qed.
Lemma mulw_words_ok ws y : words_ok ws -> 0 <= y < 2 ^ 64 -> words_ok (mulw_words ws y).
Proof. intros; apply mulw_loop_ok; auto; lia. Qed.
(* [comment removed for export] *)
Lemma mulw_words_val ws y : BigFactsBase.val (mulw_words ws y) = y * BigFactsBase.val ws.
Proof. unfold mulw_words. rewrite mulw_loop_val. lia. Qed.
End L5W.
