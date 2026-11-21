(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState Trees DeflateInvKeep OverlayFBS.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import DeflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import TreesTab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Lemma zcount_nil : forall {A} (f : A -> bool), zcount f [] = 0.
Proof. reflexivity. Qed.
Lemma zcount_app1 : forall {A} (f : A -> bool) l x, zcount f (l ++ [x]) = zcount f l + (if f x then 1 else 0).
Proof.
  intros A f l x. unfold zcount. rewrite filter_app, length_app. cbn [filter]. destruct (f x); cbn [length]; lia.
Qed.
Lemma zcount_le : forall {A} (f : A -> bool) l, 0 <= zcount f l <= Z.of_nat (length l).
Proof.
  intros A f l. unfold zcount. induction l as [|x l IH]; cbn [filter length]; [lia|]. destruct (f x); cbn [length]; lia.
Qed.
Lemma zcov_app1 : forall l d lc, zcov (l ++ [(d, lc)]) = zcov l + (if d =? 0 then 1 else lc + MIN_MATCH).
Proof.
  intros l d lc. unfold zcov. induction l as [|[d' lc'] l IH]; cbn [fold_right app]; [lia|]. rewrite IH. lia.
Qed.
Lemma zcov_nil : zcov [] = 0.
Proof. reflexivity. Qed.
Lemma zcov_nonneg : forall l, Forall sym_valid l -> 0 <= zcov l.
Proof.
  intros l H. unfold zcov. induction H as [|[d lc] l Hx H IH]; cbn [fold_right]; [lia|].
  set (X := fold_right _ _ _) in *.
  unfold sym_valid in Hx. cbn in Hx. pose proof (eq_refl : MIN_MATCH = 3). destruct (Z.eqb_spec d 0); lia.
Qed.
Lemma length_app1 : forall {A} (l : list A) x, Z.of_nat (length (l ++ [x])) = Z.of_nat (length l) + 1.
Proof. intros A l x. rewrite length_app. cbn [length]. lia. Qed.
Lemma nth_error_app1_inv : forall {A} (l : list A) x i y,
  nth_error (l ++ [x]) i = Some y -> (nth_error l i = Some y /\ (i < length l)%nat) \/ (i = length l /\ y = x).
Proof.
  intros A l x i y H. destruct (Nat.lt_ge_cases i (length l)) as [L|L].
  - left. rewrite nth_error_app1 in H by exact L. split; [exact H | exact L].
  - right. rewrite nth_error_app2 in H by exact L.
    destruct (i - length l)%nat as [|k] eqn:E; cbn [nth_error] in H; [| destruct k; discriminate H].
    injection H as <-. split; [lia | reflexivity].
Qed.


Lemma Freq_init_block_TL : forall s c, arr_len (ds_dyn_ltree_fc s) = 573 -> 0 <= c < L_CODES ->
  Freq (init_block s) TL c = if c =? END_BLOCK then 1 else 0.
Proof.
  intros s c HL Hc. unfold init_block, Freq, set_Freq. destruct s; cbn -[arr_fill arr_set arr_get Z.eqb L_CODES D_CODES BL_CODES END_BLOCK wrap16].
  cbn -[arr_fill arr_set arr_get Z.eqb wrap16] in HL. unfold L_CODES, END_BLOCK in *.
  rewrite arr_get_set. unfold arr_inb. rewrite arr_len_fill, HL.
  destruct (Z.eqb_spec 256 c) as [<-|Hne]; cbn [andb].
  - replace ((0 <=? 256) && (256 <? 573)) with true by reflexivity. reflexivity.
  - rewrite arr_get_fill. unfold arr_inb. rewrite HL.
    replace ((0 <=? c) && (c <? 0 + Z.max 0 286) && ((0 <=? c) && (c <? 573))) with true
      by (symmetry; rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia).
    destruct (Z.eqb_spec c 256); [lia | reflexivity].
Qed.

Lemma Freq_init_block_TD : forall s j, arr_len (ds_dyn_dtree_fc s) = 61 -> 0 <= j < D_CODES -> Freq (init_block s) TD j = 0.
Proof.
  intros s j HL Hj. unfold init_block, Freq, set_Freq. destruct s; cbn -[arr_fill arr_set arr_get Z.eqb L_CODES D_CODES BL_CODES END_BLOCK wrap16].
  cbn -[arr_fill arr_set arr_get Z.eqb wrap16] in HL. unfold D_CODES in *.
  rewrite arr_get_fill. unfold arr_inb. rewrite HL.
  replace ((0 <=? j) && (j <? 0 + Z.max 0 30) && ((0 <=? j) && (j <? 61))) with true
    by (symmetry; rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma Freq_init_block_TB : forall s j, arr_len (ds_bl_tree_fc s) = 39 -> 0 <= j < BL_CODES -> Freq (init_block s) TB j = 0.
Proof.
  intros s j HL Hj. unfold init_block, Freq, set_Freq. destruct s; cbn -[arr_fill arr_set arr_get Z.eqb L_CODES D_CODES BL_CODES END_BLOCK wrap16].
  cbn -[arr_fill arr_set arr_get Z.eqb wrap16] in HL. unfold BL_CODES in *.
  rewrite arr_get_fill. unfold arr_inb. rewrite HL.
  replace ((0 <=? j) && (j <? 0 + Z.max 0 19) && ((0 <=? j) && (j <? 39))) with true
    by (symmetry; rewrite !Bool.andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia).
  reflexivity.
Qed.

Lemma init_block_scalars : forall s,
  ds_sym_next (init_block s) = 0 /\ ds_opt_len (init_block s) = 0 /\ ds_static_len (init_block s) = 0 /\ ds_matches (init_block s) = 0.
Proof. intros s. destruct s; repeat split; reflexivity. Qed.

Lemma dsyms_init_block : forall s, fbs_tree_lens s -> dsyms [] (init_block s).
Proof.
  intros s HT. pose proof HT as (L1 & _ & L3 & _ & L5 & _).
  pose proof (init_block_scalars s) as (A1 & A2 & A3 & A4).
  constructor; cbn [length Z.of_nat zcount filter]; try assumption.
  - constructor.
  - constructor.
  - intros i d lc H. destruct i; discriminate H.
  - intros c Hc. rewrite (Freq_init_block_TL s c L1 Hc). reflexivity.
  - intros j Hj. exact (Freq_init_block_TD s j L3 Hj).
  - intros j Hj. exact (Freq_init_block_TB s j L5 Hj).
Qed.


Lemma dsyms_keep : forall syms s s', dsyms syms s ->
  ds_sym_next s' = ds_sym_next s -> ds_pending_buf s' = ds_pending_buf s -> ds_lit_bufsize s' = ds_lit_bufsize s ->
  ds_w_size s' = ds_w_size s ->
  ds_dyn_ltree_fc s' = ds_dyn_ltree_fc s -> ds_dyn_dtree_fc s' = ds_dyn_dtree_fc s -> ds_bl_tree_fc s' = ds_bl_tree_fc s ->
  ds_opt_len s' = ds_opt_len s -> ds_static_len s' = ds_static_len s ->
  dsyms syms s'.
Proof.
  intros syms s s' H E1 E2 E3 E4 E5 E6 E7 E8 E9. destruct H; constructor; unfold Freq in *; cbn [tree_fc] in *;
    rewrite ?E1, ?E2, ?E3, ?E4, ?E5, ?E6, ?E7, ?E8, ?E9; assumption.
Qed.

Lemma dsyms_nil_ep : forall s s', dsyms [] s -> eproj s' = eproj s -> dsyms [] s'.
Proof.
  intros s s' H E. destruct H; constructor; try assumption.
  - rewrite (ep_sym_next _ _ E). assumption.
  - constructor.
  - intros i d lc Hi. destruct i; discriminate Hi.
  - intros c Hc. rewrite (ep_Freq _ _ TL c E). auto.
  - intros j Hj. rewrite (ep_Freq _ _ TD j E). auto.
  - intros j Hj. rewrite (ep_Freq _ _ TB j E). auto.
  - rewrite (ep_opt_len _ _ E). assumption.
  - rewrite (ep_static_len _ _ E). assumption.
Qed.



Lemma wrap8_0 : wrap8 0 = 0.
Proof. reflexivity. Qed.

Lemma tally_lit_fields : forall s c,
  let s' := fst (tr_tally_lit s c) in
  let L := ds_lit_bufsize s in let n := ds_sym_next s in let cc := wrap8 c in
  ds_sym_next s' = n + 1 + 1 + 1
  /\ ds_pending_buf s' = arr_set (arr_set (arr_set (ds_pending_buf s) (L + n) (wrap8 0)) (L + (n + 1)) (wrap8 0)) (L + (n + 1 + 1)) (wrap8 cc)
  /\ ds_dyn_ltree_fc s' = arr_set (ds_dyn_ltree_fc s) cc (wrap16 (arr_get (ds_dyn_ltree_fc s) cc + 1))
  /\ ds_dyn_dtree_fc s' = ds_dyn_dtree_fc s /\ ds_bl_tree_fc s' = ds_bl_tree_fc s
  /\ ds_lit_bufsize s' = L /\ ds_w_size s' = ds_w_size s /\ ds_opt_len s' = ds_opt_len s /\ ds_static_len s' = ds_static_len s
  /\ ds_sym_end s' = ds_sym_end s
  /\ snd (tr_tally_lit s c) = (n + 1 + 1 + 1 =? ds_sym_end s).
Proof.
  intros s c. cbv zeta. destruct s; repeat split; reflexivity.
Qed.

Lemma tally_dist_fields : forall s distance length,
  let s' := fst (tr_tally_dist s distance length) in
  let L := ds_lit_bufsize s in let n := ds_sym_next s in
  let len := wrap8 length in let dist := wrap16 distance in
  let lc := arr_get length_code_a len + LITERALS + 1 in let dc := d_code (wrap16 (dist - 1)) in
  ds_sym_next s' = n + 1 + 1 + 1
  /\ ds_pending_buf s' = arr_set (arr_set (arr_set (ds_pending_buf s) (L + n) (wrap8 dist)) (L + (n + 1)) (wrap8 (Z.shiftr dist 8))) (L + (n + 1 + 1)) (wrap8 len)
  /\ ds_dyn_ltree_fc s' = arr_set (ds_dyn_ltree_fc s) lc (wrap16 (arr_get (ds_dyn_ltree_fc s) lc + 1))
  /\ ds_dyn_dtree_fc s' = arr_set (ds_dyn_dtree_fc s) dc (wrap16 (arr_get (ds_dyn_dtree_fc s) dc + 1))
  /\ ds_bl_tree_fc s' = ds_bl_tree_fc s
  /\ ds_lit_bufsize s' = L /\ ds_w_size s' = ds_w_size s /\ ds_opt_len s' = ds_opt_len s /\ ds_static_len s' = ds_static_len s
  /\ ds_sym_end s' = ds_sym_end s
  /\ snd (tr_tally_dist s distance length) = (n + 1 + 1 + 1 =? ds_sym_end s).
Proof.
  intros s distance length. cbv zeta. destruct s; repeat split; reflexivity.
Qed.

Section Tally.
  Variables (syms : list (Z * Z)) (s : deflate_state).
  Hypothesis DS : dsyms syms s.
  Let L := ds_lit_bufsize s.
  Let n := Z.of_nat (length syms).
  Hypothesis HPBL : arr_len (ds_pending_buf s) = L * 4.
  Hypothesis HSE : ds_sym_end s = (L - 1) * 3.
  Hypothesis HL : L <= 32768.
  Hypothesis ROOM : ds_sym_next s + 3 <= ds_sym_end s.
  Hypothesis LT : arr_len (ds_dyn_ltree_fc s) = 573.
  Hypothesis LD : arr_len (ds_dyn_dtree_fc s) = 61.
  Hypothesis WS : MIN_LOOKAHEAD <= ds_w_size s.

  Let Hn : ds_sym_next s = 3 * n := sy_next _ _ DS.

  Lemma tally_n_bound : 0 <= n <= L - 2.
  Proof. pose proof ROOM as R. rewrite Hn, HSE in R. subst n. lia. Qed.


  Lemma dsyms_tally_lit : forall c, 0 <= c < 256 ->
    dsyms (syms ++ [(0, c)]) (fst (tr_tally_lit s c))
    /\ snd (tr_tally_lit s c) = (3 * (n + 1) =? ds_sym_end s).
  Proof.
    intros c Hc. pose proof tally_n_bound as NB.
    destruct (tally_lit_fields s c) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
    rewrite wrap8_0 in F2. rewrite !(wrap8_id c) in F2 by lia. rewrite !(wrap8_id c) in F3 by lia. fold L in F2.
    rewrite Hn in F1, F2, F11.
    split.
    2:{ rewrite F11. f_equal. lia. }
    destruct DS as [Sn Sv Sd Sb Sfl Sfd Sfb Sol Ssl].
    constructor.
    - rewrite F1, length_app1. fold n. lia.
    - apply Forall_app. split; [exact Sv|]. constructor; [| constructor]. unfold sym_valid. left. lia.
    - apply Forall_app. split; [| constructor; [cbn [fst]; lia | constructor]].
      eapply Forall_impl; [| exact Sd]. intros [d lc] H. cbn [fst] in *. rewrite F7. exact H.
    - intros i d lc Hi. rewrite F6, F2. fold L.
      destruct (nth_error_app1_inv _ _ _ _ Hi) as [[Hi' Hlt] | [-> E]].
      + rewrite !arr_get_set_other by lia. exact (Sb i d lc Hi').
      + injection E as E1 E2; subst d lc. fold n. change (0 mod 256) with 0. change (0 / 256) with 0.
        replace (L + 3 * n + 2) with (L + (3 * n + 1 + 1)) by lia.
        replace (L + 3 * n + 1) with (L + (3 * n + 1)) by lia.
        repeat split.
        * rewrite 2 arr_get_set_other by lia. apply arr_get_set_same. lia.
        * rewrite arr_get_set_other by lia. apply arr_get_set_same. rewrite arr_len_set. lia.
        * apply arr_get_set_same. rewrite !arr_len_set. lia.
    - intros c' Hc'. unfold Freq. cbn [tree_fc]. rewrite F3. rewrite zcount_app1. cbn [sym_lcode]. rewrite Z.eqb_refl.
      pose proof (Sfl c' Hc') as E. unfold Freq in E. cbn [tree_fc] in E.
      destruct (Z.eqb_spec c c') as [<-|Hne].
      + rewrite arr_get_set_same by (rewrite LT; unfold L_CODES in Hc'; lia). rewrite E.
        pose proof (zcount_le (fun dl : Z * Z => sym_lcode dl =? c) syms). fold n in H.
        rewrite wrap16_id by (destruct (Z.eqb_spec c END_BLOCK); lia). lia.
      + rewrite arr_get_set_other by exact Hne. rewrite E. lia.
    - intros j Hj. unfold Freq. cbn [tree_fc]. rewrite F4. rewrite zcount_app1. cbn [sym_dcode]. rewrite Z.eqb_refl.
      pose proof (Sfd j Hj) as E. unfold Freq in E. cbn [tree_fc] in E. rewrite E. lia.
    - intros j Hj. unfold Freq. cbn [tree_fc]. rewrite F5. exact (Sfb j Hj).
    - rewrite F8. exact Sol.
    - rewrite F9. exact Ssl.
  Qed.

  Hypothesis WSM : ds_w_size s <= 32768.

  Lemma dsyms_tally_dist : forall d lc, 1 <= d <= ds_w_size s - MIN_LOOKAHEAD -> 0 <= lc <= 255 ->
    dsyms (syms ++ [(d, lc)]) (fst (tr_tally_dist s d lc))
    /\ snd (tr_tally_dist s d lc) = (3 * (n + 1) =? ds_sym_end s).
  Proof.
    intros d lc Hd Hlc. pose proof tally_n_bound as NB.
    assert (Hd' : 1 <= d <= 32506) by (unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hd; lia).
    destruct (tally_dist_fields s d lc) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
    rewrite !(wrap8_id lc) in F2 by lia. rewrite !(wrap8_id lc) in F3 by lia. rewrite !(wrap16_id d) in F2 by lia. rewrite !(wrap16_id d) in F4 by lia.
    rewrite (wrap16_id (d - 1)) in F4 by lia.
    assert (B1 : wrap8 d = d mod 256) by (rewrite wrap8_mod; reflexivity).
    assert (B2 : wrap8 (Z.shiftr d 8) = d / 256).
    { rewrite wrap8_mod, Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256. apply Z.mod_small. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
    rewrite B1, B2 in F2. fold L in F2. rewrite Hn in F1, F2, F11.
    pose proof (length_code_bound lc) as LCB. pose proof (dist_code_bound (d - 1)) as DCB0.
    assert (DCB : 0 <= d_code (d - 1) < 30).
    { unfold d_code. destruct (d - 1 <? 256); apply dist_code_bound. }
    split.
    2:{ rewrite F11. f_equal. lia. }
    destruct DS as [Sn Sv Sd Sb Sfl Sfd Sfb Sol Ssl].
    constructor.
    - rewrite F1, length_app1. fold n. lia.
    - apply Forall_app. split; [exact Sv|]. constructor; [| constructor]. unfold sym_valid. right. lia.
    - apply Forall_app. split; [| constructor; [cbn [fst]; rewrite F7; lia | constructor]].
      eapply Forall_impl; [| exact Sd]. intros [d' lc'] H. cbn [fst] in *. rewrite F7. exact H.
    - intros i d' lc' Hi. rewrite F6, F2. fold L.
      destruct (nth_error_app1_inv _ _ _ _ Hi) as [[Hi' Hlt] | [-> E]].
      + rewrite !arr_get_set_other by lia. exact (Sb i d' lc' Hi').
      + injection E as E1 E2; subst d' lc'. fold n.
        replace (L + 3 * n + 2) with (L + (3 * n + 1 + 1)) by lia.
        replace (L + 3 * n + 1) with (L + (3 * n + 1)) by lia.
        repeat split.
        * rewrite 2 arr_get_set_other by lia. apply arr_get_set_same. lia.
        * rewrite arr_get_set_other by lia. apply arr_get_set_same. rewrite arr_len_set. lia.
        * apply arr_get_set_same. rewrite !arr_len_set. lia.
    - intros c' Hc'. unfold Freq. cbn [tree_fc]. rewrite F3. rewrite zcount_app1. cbn [sym_lcode].
      replace (d =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      pose proof (Sfl c' Hc') as E. unfold Freq in E. cbn [tree_fc] in E.
      destruct (Z.eqb_spec (arr_get length_code_a lc + LITERALS + 1) c') as [<-|Hne].
      + rewrite arr_get_set_same by (rewrite LT; unfold LITERALS; lia). rewrite E.
        pose proof (zcount_le (fun dl : Z * Z => sym_lcode dl =? arr_get length_code_a lc + LITERALS + 1) syms). fold n in H.
        rewrite wrap16_id by (destruct (Z.eqb_spec (arr_get length_code_a lc + LITERALS + 1) END_BLOCK); lia). lia.
      + rewrite arr_get_set_other by exact Hne. rewrite E. lia.
    - intros j Hj. unfold Freq. cbn [tree_fc]. rewrite F4. rewrite zcount_app1. cbn [sym_dcode].
      replace (d =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      pose proof (Sfd j Hj) as E. unfold Freq in E. cbn [tree_fc] in E.
      destruct (Z.eqb_spec (d_code (d - 1)) j) as [<-|Hne].
      + rewrite arr_get_set_same by (rewrite LD; lia). rewrite E.
        pose proof (zcount_le (fun dl : Z * Z => match sym_dcode dl with Some j' => j' =? d_code (d - 1) | None => false end) syms). fold n in H.
        rewrite wrap16_id by lia. lia.
      + rewrite arr_get_set_other by exact Hne. rewrite E. lia.
    - intros j Hj. unfold Freq. cbn [tree_fc]. rewrite F5. exact (Sfb j Hj).
    - rewrite F8. exact Sol.
    - rewrite F9. exact Ssl.
  Qed.
End Tally.


Lemma Forall_nth_error' : forall {A} (P : A -> Prop) l i (x : A), Forall P l -> nth_error l i = Some x -> P x.
Proof.
  intros A P l i x H E. revert i E. induction H as [|y l Hy H IH]; intros [|i] E; cbn in E; try discriminate E.
  - injection E as <-. exact Hy.
  - exact (IH i E).
Qed.

Lemma dsyms_unique : forall a b s, dsyms a s -> dsyms b s -> a = b.
Proof.
  intros a b s Da Db.
  pose proof (sy_next _ _ Da) as Na. pose proof (sy_next _ _ Db) as Nb.
  assert (L : length a = length b) by lia.
  pose proof (sy_bytes _ _ Da) as Ba. pose proof (sy_bytes _ _ Db) as Bb.
  pose proof (sy_valid _ _ Da) as Va. pose proof (sy_valid _ _ Db) as Vb.
  apply nth_error_ext. intros i.
  destruct (nth_error a i) as [[d lc]|] eqn:Ea; destruct (nth_error b i) as [[d' lc']|] eqn:Eb.
  - destruct (Ba i d lc Ea) as (A1 & A2 & A3). destruct (Bb i d' lc' Eb) as (B1 & B2 & B3).
    pose proof (Forall_nth_error' _ _ _ _ Va Ea) as X. pose proof (Forall_nth_error' _ _ _ _ Vb Eb) as Y.
    unfold sym_valid in X, Y. cbn in X, Y.
    f_equal. f_equal; [| congruence].
    rewrite (Z.div_mod d 256) by lia. rewrite (Z.div_mod d' 256) by lia. congruence.
  - exfalso. assert (Hi : (i < length a)%nat) by (apply nth_error_Some; rewrite Ea; discriminate).
    apply nth_error_None in Eb. lia.
  - exfalso. assert (Hi : (i < length b)%nat) by (apply nth_error_Some; rewrite Eb; discriminate).
    apply nth_error_None in Ea. lia.
  - reflexivity.
Qed.
