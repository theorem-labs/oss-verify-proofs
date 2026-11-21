(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState DeflateLz FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation b0 := (Z_to_bv 8 0).

Lemma av8_fill0 : forall a N ofs n, 0 <= ofs -> 0 <= n -> ofs + n <= N -> N <= arr_len a ->
  av8 (arr_fill a ofs n 0) N = firstn (Z.to_nat ofs) (av8 a N) ++ repeat b0 (Z.to_nat n) ++ skipn (Z.to_nat (ofs + n)) (av8 a N).
Proof.
  intros a N ofs n Ho Hn HN HL. apply list_ext_nth.
  - rewrite !length_app, length_firstn, repeat_length, length_skipn, !av8_length. lia.
  - intros k Hk. rewrite av8_length in Hk.
    replace k with (Z.to_nat (Z.of_nat k)) at 1 by lia. rewrite av8_nth by lia. rewrite arr_get_fill. unfold arr_inb.
    destruct (Z_lt_le_dec (Z.of_nat k) ofs) as [C1|C1].
    + replace ((ofs <=? Z.of_nat k) && (Z.of_nat k <? ofs + Z.max 0 n) && ((0 <=? Z.of_nat k) && (Z.of_nat k <? arr_len a))) with false
        by (symmetry; rewrite !andb_false_iff, !Z.leb_gt; lia).
      rewrite nth_error_app1 by (rewrite length_firstn, av8_length; lia).
      rewrite nth_error_firstn. destruct (Nat.ltb_spec k (Z.to_nat ofs)); [|lia].
      replace k with (Z.to_nat (Z.of_nat k)) at 2 by lia. rewrite av8_nth by lia. reflexivity.
    + rewrite nth_error_app2 by (rewrite length_firstn, av8_length; lia).
      rewrite length_firstn, av8_length. replace (Init.Nat.min (Z.to_nat ofs) (Z.to_nat N)) with (Z.to_nat ofs) by lia.
      destruct (Z_lt_le_dec (Z.of_nat k) (ofs + n)) as [C2|C2].
      * replace ((ofs <=? Z.of_nat k) && (Z.of_nat k <? ofs + Z.max 0 n) && ((0 <=? Z.of_nat k) && (Z.of_nat k <? arr_len a))) with true
          by (symmetry; rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia).
        rewrite nth_error_app1 by (rewrite repeat_length; lia).
        rewrite (nth_error_nth' _ b0) by (rewrite repeat_length; lia). rewrite nth_repeat. reflexivity.
      * replace ((ofs <=? Z.of_nat k) && (Z.of_nat k <? ofs + Z.max 0 n) && ((0 <=? Z.of_nat k) && (Z.of_nat k <? arr_len a))) with false
          by (symmetry; rewrite !andb_false_iff, !Z.leb_gt, !Z.ltb_ge; lia).
        rewrite nth_error_app2 by (rewrite repeat_length; lia). rewrite repeat_length, nth_error_skipn.
        replace (Z.to_nat (ofs + n) + (k - Z.to_nat ofs - Z.to_nat n))%nat with (Z.to_nat (Z.of_nat k)) by lia. rewrite av8_nth by lia. reflexivity.
Qed.

Definition fw_more0 (d : deflate_state) : Z := ds_window_size d - ds_lookahead d - ds_strstart d.
Definition slide_cond (d : deflate_state) : bool := 65274 <=? ds_strstart d.
Definition fwA (d : deflate_state) : deflate_state := if slide_cond d then fw_slide d 32768 (fw_more d) else d.
Definition moreA (d : deflate_state) : Z := if slide_cond d then fw_more0 d + 32768 else fw_more0 d.
Definition fwB (s1 : deflate_state) (more : Z) : deflate_state :=
  if cs_avail_in (ds_strm s1) =? 0 then s1
  else let r := read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) more in
       fw_insert (set_lookahead (fst r) (ds_lookahead (fst r) + snd r)).

Definition rb_len (s : deflate_state) (more : Z) : Z :=
  let len := cs_avail_in (ds_strm s) in if more <? len then more else len.

Lemma read_buf_small : forall s off more, let r := read_buf s (RB_window off) more in
  snd r = rb_len s more /\ cs_avail_in (ds_strm (fst r)) = cs_avail_in (ds_strm s) - rb_len s more
  /\ ds_lookahead (fst r) = ds_lookahead s /\ ds_strstart (fst r) = ds_strstart s /\ ds_insert (fst r) = ds_insert s
  /\ ds_high_water (fst r) = ds_high_water s /\ ds_window_size (fst r) = ds_window_size s.
Proof.
  intros s off more. cbv zeta. unfold read_buf, rb_len. cbv zeta.
  destruct ((if more <? cs_avail_in (ds_strm s) then more else cs_avail_in (ds_strm s)) =? 0) eqn:E.
  - apply Z.eqb_eq in E. rewrite E. cbn [fst snd]. repeat split; try reflexivity. lia.
  - dsred. destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]; dsred; repeat split; reflexivity.
Qed.

Definition fw_ins0 (s : deflate_state) : deflate_state :=
  if MIN_MATCH <=? ds_lookahead s + ds_insert s then
    let str := ds_strstart s - ds_insert s in
    set_ins_h (set_ins_h s (arr_get (ds_window s) str)) (update_hash (set_ins_h s (arr_get (ds_window s) str)) (arr_get (ds_window s) str) (arr_get (ds_window s) (str + 1)))
  else s.

Section ONE.
  Variable d : deflate_state.
  Hypothesis FW : fw_wf 32768 32768 d.
  Hypothesis INS : ds_insert d = 0.
  Hypothesis AI : cs_avail_in (ds_strm d) <= 1.

End ONE.

Definition rb1_strm (s : deflate_state) (b : Z) : cstrm :=
  let st := ds_strm s in
  let st1 := cset_avail_in st (cs_avail_in st - 1) in
  let st2 := if ds_wrap s =? 1 then cset_adler st1 (adler32_len1 (cs_adler st) b) else st1 in
  cset_total_in (cset_next_in st2 (cs_next_in st + 1)) (wrap64 (cs_total_in st + 1)).

Lemma fwB_0 : forall s1 more, cs_avail_in (ds_strm s1) = 0 -> fwB s1 more = s1.
Proof. intros s1 more A0. unfold fwB. rewrite A0. reflexivity. Qed.

Definition fwh_init_a (s : deflate_state) : Z :=
  let curr := ds_strstart s + ds_lookahead s in let init := ds_window_size s - curr in if WIN_INIT <? init then WIN_INIT else init.
Definition fwh_init_b (s : deflate_state) : Z :=
  let curr := ds_strstart s + ds_lookahead s in let init := curr + WIN_INIT - ds_high_water s in
  if ds_window_size s - ds_high_water s <? init then ds_window_size s - ds_high_water s else init.

Lemma fwh_none : forall s, ds_window_size s <= ds_high_water s -> fill_window_high s = s.
Proof. intros s H. unfold fill_window_high. replace (ds_high_water s <? ds_window_size s) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. Qed.

Lemma fwh_a : forall s, ds_high_water s < ds_window_size s -> ds_high_water s < ds_strstart s + ds_lookahead s -> 0 <= fwh_init_a s < 2 ^ 32 ->
  fill_window_high s = set_high_water (set_window s (arr_fill (ds_window s) (ds_strstart s + ds_lookahead s) (fwh_init_a s) 0))
                                       (ds_strstart s + ds_lookahead s + fwh_init_a s).
Proof.
  intros s H1 H2 H3. unfold fill_window_high, fwh_init_a in *.
  replace (ds_high_water s <? ds_window_size s) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (ds_high_water s <? ds_strstart s + ds_lookahead s) with true by (symmetry; apply Z.ltb_lt; lia).
  cbv zeta. rewrite wrap32_id by lia. reflexivity.
Qed.

Lemma fwh_b : forall s, ds_high_water s < ds_window_size s -> ds_strstart s + ds_lookahead s <= ds_high_water s ->
  ds_high_water s < ds_strstart s + ds_lookahead s + WIN_INIT -> 0 <= fwh_init_b s < 2 ^ 32 ->
  fill_window_high s = set_high_water (set_window s (arr_fill (ds_window s) (ds_high_water s) (fwh_init_b s) 0)) (ds_high_water s + fwh_init_b s).
Proof.
  intros s H1 H2 H3 H4. unfold fill_window_high, fwh_init_b in *.
  replace (ds_high_water s <? ds_window_size s) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (ds_high_water s <? ds_strstart s + ds_lookahead s) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (ds_high_water s <? ds_strstart s + ds_lookahead s + WIN_INIT) with true by (symmetry; apply Z.ltb_lt; lia).
  cbv zeta. rewrite wrap32_id by lia. reflexivity.
Qed.

Lemma fwh_c : forall s, ds_high_water s < ds_window_size s -> ds_strstart s + ds_lookahead s + WIN_INIT <= ds_high_water s -> fill_window_high s = s.
Proof.
  intros s H1 H2. unfold fill_window_high.
  replace (ds_high_water s <? ds_window_size s) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (ds_high_water s <? ds_strstart s + ds_lookahead s) with false by (symmetry; apply Z.ltb_ge; unfold WIN_INIT, MAX_MATCH in H2; lia).
  replace (ds_high_water s <? ds_strstart s + ds_lookahead s + WIN_INIT) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
