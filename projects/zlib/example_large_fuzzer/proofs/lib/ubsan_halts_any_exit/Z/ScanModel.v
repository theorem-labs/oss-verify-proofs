(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma sbf_self : forall s, set_bl_tree_fc s (ds_bl_tree_fc s) = s.
Proof. intros s. destruct s; reflexivity. Qed.
Lemma sbf_get : forall s b, ds_bl_tree_fc (set_bl_tree_fc s b) = b.
Proof. intros. reflexivity. Qed.
Lemma sbf_tree_dl : forall s b t, tree_dl (set_bl_tree_fc s b) t = tree_dl s t.
Proof. intros s b [| |]; reflexivity. Qed.
Lemma sbf_Len : forall s b t n, Len (set_bl_tree_fc s b) t n = Len s t n.
Proof. intros. unfold Len. rewrite sbf_tree_dl. reflexivity. Qed.
Lemma sbf_FreqB : forall s b n, Freq (set_bl_tree_fc s b) TB n = arr_get b n.
Proof. intros. reflexivity. Qed.

Lemma sbf_tree_fc : forall s b t, t <> TB -> tree_fc (set_bl_tree_fc s b) t = tree_fc s t.
Proof. intros s b [| |] H; [reflexivity | reflexivity | congruence]. Qed.

Lemma Len_set_Len : forall s t i v n, 0 <= i < arr_len (tree_dl s t) ->
  Len (set_Len s t i v) t n = if i =? n then wrap16 v else Len s t n.
Proof.
  intros s t i v n Hi. unfold Len, set_Len, set_Dad.
  destruct t; cbn [tree_dl set_tree_dl]; dsred; rewrite arr_get_set; unfold arr_inb;
    cbn [tree_dl] in Hi;
    destruct (Z.eqb_spec i n), (Z.leb_spec 0 i); cbn [andb]; try lia;
    [destruct (Z.ltb_spec i (arr_len (ds_dyn_ltree_dl s))) | destruct (Z.ltb_spec i (arr_len (ds_dyn_dtree_dl s)))
    | destruct (Z.ltb_spec i (arr_len (ds_bl_tree_dl s)))]; cbn; try lia; reflexivity.
Qed.

Lemma tree_dl_len_set_Len : forall s t i v t', arr_len (tree_dl (set_Len s t i v) t') = arr_len (tree_dl s t').
Proof. intros s [| |] i v [| |]; cbn [tree_dl set_Len set_Dad set_tree_dl]; dsred; rewrite ?arr_len_set; reflexivity. Qed.
Lemma tree_fc_set_Len : forall s t i v t', tree_fc (set_Len s t i v) t' = tree_fc s t'.
Proof. intros s [| |] i v [| |]; reflexivity. Qed.

Definition st_upd (mn : Z) (b : arr) (curlen prevlen count : Z) : arr :=
  if count <? mn then arr_set b curlen (wrap16 (arr_get b curlen + count))
  else if negb (curlen =? 0) then
    let b := if negb (curlen =? prevlen) then arr_set b curlen (wrap16 (arr_get b curlen + 1)) else b in
    arr_set b REP_3_6 (wrap16 (arr_get b REP_3_6 + 1))
  else if count <=? 10 then arr_set b REPZ_3_10 (wrap16 (arr_get b REPZ_3_10 + 1))
  else arr_set b REPZ_11_138 (wrap16 (arr_get b REPZ_11_138 + 1)).

Lemma st_upd_len : forall mn b c p k, arr_len (st_upd mn b c p k) = arr_len b.
Proof.
  intros. unfold st_upd.
  destruct (k <? mn); [apply arr_len_set|].
  destruct (negb (c =? 0)); [destruct (negb (c =? p)); rewrite ?arr_len_set; reflexivity|].
  destruct (k <=? 10); apply arr_len_set.
Qed.

Lemma st_upd_range : forall mn b c p k,
  (forall i, 0 <= i < arr_len b -> 0 <= arr_get b i < 65536) ->
  forall i, 0 <= i < arr_len b -> 0 <= arr_get (st_upd mn b c p k) i < 65536.
Proof.
  intros mn b c p k Hb i Hi.
  assert (W : forall x, 0 <= wrap16 x < 65536).
  { intros x. rewrite wrap16_mod. change (2 ^ 16) with 65536. apply Z.mod_pos_bound. lia. }
  assert (G : forall a j v q, (forall r, 0 <= r < arr_len a -> 0 <= arr_get a r < 65536) ->
             0 <= q < arr_len a -> 0 <= arr_get (arr_set a j (wrap16 v)) q < 65536).
  { intros a j v q Hr Hq. rewrite arr_get_set. destruct (_ && _); [apply W | apply Hr; exact Hq]. }
  unfold st_upd.
  destruct (k <? mn); [apply G; [exact Hb | exact Hi]|].
  destruct (negb (c =? 0)).
  - destruct (negb (c =? p)).
    + apply G; [| rewrite arr_len_set; exact Hi].
      intros r Hr. rewrite arr_len_set in Hr. apply G; [exact Hb | exact Hr].
    + apply G; [exact Hb | exact Hi].
  - destruct (k <=? 10); apply G; (exact Hb || exact Hi).
Qed.

Lemma scan_loop_S : forall f s0 b t mc n prevlen nextlen count mx mn,
  scan_tree_loop (S f) (set_bl_tree_fc s0 b) t mc n prevlen nextlen count mx mn =
    if n <=? mc then
      let curlen := nextlen in
      let nextlen' := Len s0 t (n + 1) in
      let count' := count + 1 in
      if (count' <? mx) && (curlen =? nextlen') then
        scan_tree_loop f (set_bl_tree_fc s0 b) t mc (n + 1) prevlen nextlen' count' mx mn
      else
        let '(mx', mn') := tree_counts curlen nextlen' in
        scan_tree_loop f (set_bl_tree_fc s0 (st_upd mn b curlen prevlen count')) t mc (n + 1)
                       curlen nextlen' 0 mx' mn'
    else set_bl_tree_fc s0 b.
Proof.
  intros. cbn [scan_tree_loop]. rewrite sbf_Len.
  destruct (n <=? mc); [|reflexivity]. cbv zeta.
  destruct ((count + 1 <? mx) && (nextlen =? Len s0 t (n + 1))); [reflexivity|].
  unfold st_upd. rewrite !sbf_FreqB.
  destruct (count + 1 <? mn); [reflexivity|].
  destruct (negb (nextlen =? 0)).
  - destruct (negb (nextlen =? prevlen)); reflexivity.
  - destruct (count + 1 <=? 10); reflexivity.
Qed.

Lemma scan_loop_0 : forall s t mc n p q c mx mn, scan_tree_loop 0 s t mc n p q c mx mn = s.
Proof. reflexivity. Qed.

Lemma scan_loop_out : forall f s t mc n p q c mx mn, mc < n -> scan_tree_loop f s t mc n p q c mx mn = s.
Proof.
  intros [|f] s t mc n p q c mx mn H; [reflexivity|]. cbn [scan_tree_loop].
  destruct (Z.leb_spec n mc); [lia | reflexivity].
Qed.

Lemma scan_loop_shape : forall f s0 b t mc n p q c mx mn,
  exists b', scan_tree_loop f (set_bl_tree_fc s0 b) t mc n p q c mx mn = set_bl_tree_fc s0 b'
             /\ arr_len b' = arr_len b
             /\ ((forall i, 0 <= i < arr_len b -> 0 <= arr_get b i < 65536) ->
                 forall i, 0 <= i < arr_len b' -> 0 <= arr_get b' i < 65536).
Proof.
  induction f as [|f IH]; intros.
  - exists b. rewrite scan_loop_0. auto.
  - rewrite scan_loop_S. destruct (n <=? mc); [| exists b; auto]. cbv zeta.
    destruct ((c + 1 <? mx) && (q =? Len s0 t (n + 1))); [apply IH|].
    destruct (tree_counts q (Len s0 t (n + 1))) as [mx' mn'].
    destruct (IH s0 (st_upd mn b q p (c + 1)) t mc (n + 1) q (Len s0 t (n + 1)) 0 mx' mn') as (b' & E & L & R).
    exists b'. split; [exact E|]. rewrite st_upd_len in L, R. split; [exact L|].
    intros Hb. apply R. apply st_upd_range. exact Hb.
Qed.

Lemma tree_counts_range : forall a b mx mn, tree_counts a b = (mx, mn) -> (mx = 138 \/ mx = 6 \/ mx = 7) /\ (mn = 3 \/ mn = 4).
Proof.
  intros a b mx mn H. unfold tree_counts in H.
  destruct (b =? 0); [|destruct (a =? b)]; injection H as <- <-; lia.
Qed.
