(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.

Module RefDeflSafeW.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition fw_keep (a b : deflate_state) : Prop :=
  ds_pending b = ds_pending a /\ ds_pending_out b = ds_pending_out a /\ ds_bi_valid b = ds_bi_valid a /\ ds_bi_buf b = ds_bi_buf a
  /\ ds_pending_buf b = ds_pending_buf a /\ ds_lit_bufsize b = ds_lit_bufsize a /\ ds_pending_buf_size b = ds_pending_buf_size a
  /\ ds_sym_next b = ds_sym_next a /\ ds_sym_end b = ds_sym_end a /\ ds_level b = ds_level a /\ ds_strategy b = ds_strategy a
  /\ ds_match_length b = ds_match_length a /\ ds_prev_length b = ds_prev_length a /\ ds_match_available b = ds_match_available a
  /\ ds_dyn_ltree_fc b = ds_dyn_ltree_fc a /\ ds_dyn_dtree_fc b = ds_dyn_dtree_fc a /\ ds_status b = ds_status a
  /\ cs_out_rev (ds_strm b) = cs_out_rev (ds_strm a) /\ cs_avail_out (ds_strm b) = cs_avail_out (ds_strm a)
  /\ cs_total_out (ds_strm b) = cs_total_out (ds_strm a)
  /\ ds_lookahead b + cs_avail_in (ds_strm b) = ds_lookahead a + cs_avail_in (ds_strm a).

Lemma fw_keep_refl : forall a, fw_keep a a.
Proof. intros a. repeat split; reflexivity. Qed.

Lemma fw_keep_trans : forall a b c, fw_keep a b -> fw_keep b c -> fw_keep a c.
Proof.
  intros a b c HA HB. unfold fw_keep in *.
  destruct HA as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21).
  destruct HB as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & B18 & B19 & B20 & B21).
  rewrite B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B13, B14, B15, B16, B17, B18, B19, B20, B21.
  repeat split; assumption.
Qed.

Lemma fw_slide_keep : forall s ws more, fw_keep s (fw_slide s ws more).
Proof.
  intros s ws more. unfold fw_keep, fw_slide, slide_hash. destruct (_ <? _); dsred; repeat split; reflexivity.
Qed.

Lemma read_buf_keep : forall s off more,
  let r := read_buf s (RB_window off) more in fw_keep s (set_lookahead (fst r) (ds_lookahead (fst r) + snd r)).
Proof.
  intros s off more r. subst r. unfold read_buf. cbv zeta.
  destruct (_ =? 0); cbv iota beta; unfold fw_keep; dsred; [repeat split; reflexivity || lia|].
  destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]; dsred; repeat split; try reflexivity; lia.
Qed.

Lemma fill_window_insert_keep : forall n s str, fw_keep s (fill_window_insert n s str).
Proof.
  induction n as [|n IH]; intros s str; [apply fw_keep_refl|].
  cbn [fill_window_insert]. destruct (negb (ds_insert s =? 0)); [| apply fw_keep_refl]. cbv zeta.
  match goal with |- fw_keep s (if ?c then ?a else ?b) =>
    assert (K : fw_keep s a) by (unfold fw_keep; dsred; repeat split; reflexivity);
    destruct c; [exact K | exact (fw_keep_trans _ _ _ K (IH _ _))] end.
Qed.

Lemma fw_insert_keep : forall s, fw_keep s (fw_insert s).
Proof.
  intros s. unfold fw_insert. destruct (_ <=? _); [| apply fw_keep_refl]. cbv zeta.
  eapply fw_keep_trans; [| apply fill_window_insert_keep]. unfold fw_keep. dsred. repeat split; reflexivity.
Qed.

Lemma fill_window_body_keep : forall s ws, fw_keep s (fst (fill_window_body s ws)).
Proof.
  intros s ws. rewrite fill_window_body_eq.
  match goal with |- fw_keep s (fst (let '(s1, more1) := ?p in _)) => destruct p as [s1 more1] eqn:Ep end.
  assert (K1 : fw_keep s s1).
  { destruct (_ <=? _); injection Ep as <- <-; [apply fw_slide_keep | apply fw_keep_refl]. }
  destruct (cs_avail_in (ds_strm s1) =? 0); cbn [fst]; [exact K1|].
  pose proof (read_buf_keep s1 (ds_strstart s1 + ds_lookahead s1) more1) as K2. cbv zeta in K2.
  destruct (read_buf s1 _ more1) as [s2 n]. cbn [fst snd] in *.
  exact (fw_keep_trans _ _ _ K1 (fw_keep_trans _ _ _ K2 (fw_insert_keep _))).
Qed.

Lemma fill_window_loop_keep : forall n s ws, fw_keep s (fill_window_loop n s ws).
Proof.
  induction n as [|n IH]; intros s ws; [apply fw_keep_refl|].
  rewrite fill_window_loop_step. pose proof (fill_window_body_keep s ws) as K.
  destruct (fill_window_body s ws) as [s' brk]. cbn [fst] in K.
  destruct brk; [exact K|]. destruct (_ && _); [exact (fw_keep_trans _ _ _ K (IH _ _)) | exact K].
Qed.

Lemma fill_window_high_keep : forall s, fw_keep s (fill_window_high s)
  /\ ds_lookahead (fill_window_high s) = ds_lookahead s /\ ds_strstart (fill_window_high s) = ds_strstart s
  /\ cs_avail_in (ds_strm (fill_window_high s)) = cs_avail_in (ds_strm s) /\ ds_block_start (fill_window_high s) = ds_block_start s.
Proof.
  intros s. unfold fill_window_high, fw_keep.
  destruct (_ <? _); [| repeat split; reflexivity]. cbv zeta.
  destruct (_ <? _); [dsred; repeat split; reflexivity|].
  destruct (_ <? _); dsred; repeat split; reflexivity.
Qed.

Lemma fill_window_keep : forall s, fw_keep s (fill_window s).
Proof.
  intros s. unfold fill_window. eapply fw_keep_trans; [apply fill_window_loop_keep | apply (proj1 (fill_window_high_keep _))].
Qed.


Lemma fill_window_body_break : forall s ws,
  snd (fill_window_body s ws) = true -> ds_lookahead (fst (fill_window_body s ws)) = ds_lookahead s.
Proof.
  intros s ws. rewrite fill_window_body_eq.
  match goal with |- snd (let '(s1, more1) := ?p in _) = true -> _ => destruct p as [s1 more1] eqn:Ep end.
  assert (L1 : ds_lookahead s1 = ds_lookahead s).
  { destruct (_ <=? _); injection Ep as <- <-; [| reflexivity]. unfold fw_slide, slide_hash. destruct (_ <? _); dsred; reflexivity. }
  destruct (cs_avail_in (ds_strm s1) =? 0); cbn [fst snd]; [intros _; exact L1|].
  destruct (read_buf s1 _ more1) as [s2 n]. cbn [snd]. intros H; discriminate H.
Qed.

Lemma fill_window_body_break_avail : forall s ws,
  snd (fill_window_body s ws) = true -> cs_avail_in (ds_strm (fst (fill_window_body s ws))) = 0.
Proof.
  intros s ws. rewrite fill_window_body_eq.
  match goal with |- snd (let '(s1, more1) := ?p in _) = true -> _ => destruct p as [s1 more1] eqn:Ep end.
  destruct (Z.eqb_spec (cs_avail_in (ds_strm s1)) 0) as [A|A]; cbn [fst snd]; [intros _; exact A|].
  destruct (read_buf s1 _ more1) as [s2 n]. cbn [snd]. intros H; discriminate H.
Qed.

Section WF.
  Variables ws hs : Z.

  Lemma fill_window_loop_wf : forall n s,
    fw_wf ws hs s -> ds_lookahead s < MIN_LOOKAHEAD ->
    fw_wf ws hs (fill_window_loop n s ws) /\ fw_const s (fill_window_loop n s ws)
    /\ ds_lookahead s <= ds_lookahead (fill_window_loop n s ws) <= 2 * ws.
  Proof.
    induction n as [|n IH]; intros s HW Hl.
    { cbn [fill_window_loop]. split; [exact HW|]. split; [repeat split; reflexivity|].
      pose proof (wf_sl _ _ _ HW). pose proof (wf_look _ _ _ HW). pose proof (wf_ins _ _ _ HW). lia. }
    rewrite fill_window_loop_step. pose proof (fill_window_body_wf ws hs s HW Hl) as B.
    pose proof (fill_window_body_break s ws) as Bk.
    destruct (fill_window_body s ws) as [s' brk]. destruct B as (HW' & HC' & HL'). cbn [fst snd] in Bk.
    pose proof (wf_sl _ _ _ HW') as Vsl'. pose proof (wf_look _ _ _ HW') as Vl'. pose proof (wf_ins _ _ _ HW') as Vins'.
    pose proof (wf_sl _ _ _ HW) as Vsl. pose proof (wf_look _ _ _ HW) as Vl. pose proof (wf_ins _ _ _ HW) as Vins.
    destruct brk.
    { split; [exact HW'|]. split; [exact HC'|]. rewrite (Bk eq_refl). lia. }
    destruct (HL' eq_refl) as [Hlt Hle].
    destruct (Z.ltb_spec (ds_lookahead s') MIN_LOOKAHEAD) as [Hlo|Hhi]; cbn [andb].
    - destruct (negb (cs_avail_in (ds_strm s') =? 0)).
      + destruct (IH s' HW' Hlo) as (HW2 & HC2 & HL2). split; [exact HW2|].
        split; [| lia]. revert HC' HC2. unfold fw_const. intuition congruence.
      + split; [exact HW'|]. split; [exact HC' | lia].
    - split; [exact HW'|]. split; [exact HC' | lia].
  Qed.

  Lemma fill_window_high_wf' : forall s, fw_wf ws hs s -> fw_wf ws hs (fill_window_high s).
  Proof.
    intros s HW. pose proof (wf_wsr _ _ _ HW) as Lws. pose proof (wf_sl _ _ _ HW) as Vsl. pose proof (wf_look _ _ _ HW) as Vlook.
    pose proof (wf_wsz _ _ _ HW) as Vwsz. pose proof (wf_ins _ _ _ HW) as Vins. pose proof (wf_hw _ _ _ HW) as Vhw.
    unfold fill_window_high, WIN_INIT, MAX_MATCH. rewrite Vwsz. pose proof HW as HW'.
    destruct (Z.ltb_spec (ds_high_water s) (2 * ws)); [|exact HW]. cbv zeta.
    destruct (Z.ltb_spec (ds_high_water s) (ds_strstart s + ds_lookahead s)).
    - destruct HW; constructor; dsred; try assumption.
      + rewrite arr_len_fill. assumption.
      + destruct (Z.ltb_spec 258 (2 * ws - (ds_strstart s + ds_lookahead s))); lia.
      + intros i Hi. rewrite arr_get_fill. destruct (_ && _); [lia | match goal with Hb : forall j, _ -> 0 <= arr_get (ds_window s) j < 256 |- _ => apply Hb; exact Hi end].
    - destruct (Z.ltb_spec (ds_high_water s) (ds_strstart s + ds_lookahead s + 258)); [|exact HW].
      destruct HW; constructor; dsred; try assumption.
      + rewrite arr_len_fill. assumption.
      + destruct (Z.ltb_spec (2 * ws - ds_high_water s) (ds_strstart s + ds_lookahead s + 258 - ds_high_water s)); lia.
      + intros i Hi. rewrite arr_get_fill. destruct (_ && _); [lia | match goal with Hb : forall j, _ -> 0 <= arr_get (ds_window s) j < 256 |- _ => apply Hb; exact Hi end].
  Qed.

  Lemma fill_window_loop_exhausts : forall n s,
    fw_wf ws hs s -> ds_lookahead s < MIN_LOOKAHEAD -> MIN_LOOKAHEAD - ds_lookahead s <= Z.of_nat n ->
    ds_lookahead (fill_window_loop n s ws) < MIN_LOOKAHEAD -> cs_avail_in (ds_strm (fill_window_loop n s ws)) = 0.
  Proof.
    induction n as [|n IH]; intros s HW Hl Hn; [lia|].
    rewrite fill_window_loop_step. pose proof (fill_window_body_wf ws hs s HW Hl) as B.
    pose proof (fill_window_body_break_avail s ws) as Bk.
    destruct (fill_window_body s ws) as [s' brk]. destruct B as (HW' & HC' & HL'). cbn [fst snd] in Bk.
    destruct brk; [intros _; exact (Bk eq_refl)|].
    destruct (HL' eq_refl) as [Hlt Hle].
    destruct (Z.ltb_spec (ds_lookahead s') MIN_LOOKAHEAD) as [Hlo|Hhi]; cbn [andb].
    - destruct (Z.eqb_spec (cs_avail_in (ds_strm s')) 0) as [A|A]; cbn [negb]; [intros _; exact A|].
      apply (IH s' HW' Hlo). lia.
    - intros H. lia.
  Qed.

  Lemma fill_window_facts : forall s,
    fw_wf ws hs s -> ds_lookahead s < MIN_LOOKAHEAD ->
    let s' := fill_window s in
    fw_wf ws hs s' /\ fw_const s s' /\ fw_keep s s'
    /\ ds_lookahead s <= ds_lookahead s' <= 2 * ws
    /\ cs_avail_in (ds_strm s') = cs_avail_in (ds_strm s) - (ds_lookahead s' - ds_lookahead s)
    /\ (ds_lookahead s' < MIN_LOOKAHEAD -> cs_avail_in (ds_strm s') = 0).
  Proof.
    intros s HW Hl s'. subst s'.
    pose proof (fill_window_loop_exhausts 263%nat s HW Hl ltac:(pose proof (wf_look _ _ _ HW); unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in *; lia)) as EX.
    pose proof (fill_window_keep s) as K. pose proof (wf_ws _ _ _ HW) as Ews.
    unfold fill_window in K |- *. rewrite Ews in K |- *.
    destruct (fill_window_loop_wf 263%nat s HW Hl) as (HW1 & HC1 & HL1).
    pose proof (fill_window_high_keep (fill_window_loop 263 s ws)) as (K2 & L2 & S2 & A2 & B2).
    split; [apply fill_window_high_wf'; exact HW1|].
    split. { revert HC1 K2. unfold fw_const, fw_keep. generalize (fill_window_loop 263%nat s ws). intros s1 HC1 K2.
             pose proof (wf_ws _ _ _ HW1) as E1. unfold fill_window_high. destruct (_ <? _); [| exact HC1]. cbv zeta.
             destruct (_ <? _); [| destruct (_ <? _)]; dsred; exact HC1. }
    split; [exact K|].
    rewrite L2, A2. split; [exact HL1|].
    split; [destruct K as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M); rewrite L2, A2 in M; lia|].
    exact EX.
  Qed.
End WF.
End RefDeflSafeW.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Definition fw_rest (s : deflate_state) :=
  (ds_status s, ds_pending_buf s, ds_pending_buf_size s, ds_pending_out s, ds_pending s, ds_wrap s,
   ds_gzhead s, ds_gzindex s, ds_method s, ds_last_flush s, ds_w_size s, ds_w_bits s, ds_w_mask s,
   ds_window_size s, ds_hash_size s, ds_hash_bits s, ds_hash_mask s, ds_hash_shift s,
   ds_match_length s, ds_prev_match s, ds_match_available s, ds_prev_length s,
   (ds_max_chain_length s, ds_max_lazy_match s, ds_level s, ds_strategy s, ds_good_match s, ds_nice_match s,
    ds_dyn_ltree_fc s, ds_dyn_ltree_dl s, ds_dyn_dtree_fc s, ds_dyn_dtree_dl s, ds_bl_tree_fc s, ds_bl_tree_dl s,
    ds_l_max_code s, ds_d_max_code s, ds_bl_max_code s, ds_bl_count s, ds_heap s, ds_heap_len s, ds_heap_max s,
    ds_depth s, ds_lit_bufsize s, ds_sym_next s, ds_sym_end s, ds_opt_len s, ds_static_len s, ds_matches s,
    ds_bi_buf s, ds_bi_valid s),
   (cs_input (ds_strm s), cs_out_rev (ds_strm s), cs_avail_out (ds_strm s), cs_total_out (ds_strm s),
    cs_msg (ds_strm s), cs_data_type (ds_strm s))).

Lemma fw_rest_read_buf : forall s off n, fw_rest (fst (read_buf s (RB_window off) n)) = fw_rest s.
Proof.
  intros s off n. unfold read_buf. cbv beta iota zeta. dsred.
  destruct ((if n <? cs_avail_in (ds_strm s) then n else cs_avail_in (ds_strm s)) =? 0); [reflexivity|].
  destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]; unfold fw_rest; dsred; reflexivity.
Qed.

Lemma fw_rest_insert : forall n s str, fw_rest (fill_window_insert n s str) = fw_rest s.
Proof.
  induction n as [|n IH]; intros s str; [reflexivity|].
  cbn -[fw_rest update_hash Z.ltb Z.eqb Z.add Z.sub Z.land arr_get arr_set wrap16 negb].
  destruct (negb (ds_insert s =? 0)); [|reflexivity].
  destruct (_ <? _); [unfold fw_rest; dsred; reflexivity|].
  rewrite IH. unfold fw_rest; dsred; reflexivity.
Qed.

Lemma fw_rest_slide_hash : forall s, fw_rest (slide_hash s) = fw_rest s.
Proof. intros s. unfold slide_hash, fw_rest. dsred. reflexivity. Qed.

Lemma fw_rest_body : forall s ws, fw_rest (fst (fill_window_body s ws)) = fw_rest s.
Proof.
  intros s ws. rewrite fill_window_body_eq.
  set (s1 := if ws + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s then fw_slide s ws (fw_more s) else s).
  set (m1 := if ws + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s then wrap32 (fw_more s + ws) else fw_more s).
  assert (E1 : fw_rest s1 = fw_rest s).
  { subst s1. destruct (_ <=? _); [|reflexivity]. unfold fw_slide. rewrite fw_rest_slide_hash.
    destruct (_ <? _); unfold fw_rest; dsred; reflexivity. }
  replace (if ws + (ds_w_size s - MIN_LOOKAHEAD) <=? ds_strstart s then (fw_slide s ws (fw_more s), wrap32 (fw_more s + ws)) else (s, fw_more s))
    with (s1, m1) by (subst s1 m1; destruct (_ <=? _); reflexivity).
  cbv beta iota zeta.
  destruct (cs_avail_in (ds_strm s1) =? 0); [exact E1|].
  destruct (read_buf s1 (RB_window (ds_strstart s1 + ds_lookahead s1)) m1) as [s2 n] eqn:E2.
  pose proof (fw_rest_read_buf s1 (ds_strstart s1 + ds_lookahead s1) m1) as E2'. rewrite E2 in E2'. cbn [fst] in E2'.
  cbn [fst]. unfold fw_insert. dsred. destruct (MIN_MATCH <=? _).
  - rewrite fw_rest_insert. rewrite <- E1, <- E2'. unfold fw_rest; dsred; reflexivity.
  - rewrite <- E1, <- E2'. unfold fw_rest; dsred; reflexivity.
Qed.

Lemma fw_rest_loop : forall n s ws, fw_rest (fill_window_loop n s ws) = fw_rest s.
Proof.
  induction n as [|n IH]; intros s ws; [reflexivity|].
  cbn [fill_window_loop]. destruct (fill_window_body s ws) as [s1 b] eqn:E.
  pose proof (fw_rest_body s ws) as E'. rewrite E in E'. cbn [fst] in E'.
  destruct b; [exact E'|]. destruct (_ && _); [rewrite IH; exact E' | exact E'].
Qed.

Lemma fw_rest_high : forall s, fw_rest (fill_window_high s) = fw_rest s.
Proof.
  intros s. unfold fill_window_high.
  destruct (_ <? _); [|reflexivity]. destruct (_ <? _); [unfold fw_rest; dsred; reflexivity|].
  destruct (_ <? _); [unfold fw_rest; dsred; reflexivity | reflexivity].
Qed.

Lemma fw_rest_fill_window : forall s, fw_rest (fill_window s) = fw_rest s.
Proof. intros s. unfold fill_window. rewrite fw_rest_high, fw_rest_loop. reflexivity. Qed.


Lemma longest_match_body_ms : forall s cur cl bl nice lim se1 se,
  exists ms, fst (fst (fst (fst (fst (fst (longest_match_body s cur cl bl nice lim se1 se)))))) = set_match_start s ms.
Proof.
  intros. unfold longest_match_body.
  destruct (_ || _).
  - destruct (_ <? _); [destruct (negb _)|]; exists (ds_match_start s); symmetry; apply set_ms_self.
  - destruct (_ <? _).
    + destruct (_ <=? _); [exists cur; reflexivity|].
      destruct (_ <? _); [destruct (negb _)|]; exists cur; reflexivity.
    + destruct (_ <? _); [destruct (negb _)|]; exists (ds_match_start s); symmetry; apply set_ms_self.
Qed.

Lemma longest_match_loop_ms : forall n s cur cl bl nice lim se1 se,
  exists ms, fst (longest_match_loop n s cur cl bl nice lim se1 se) = set_match_start s ms.
Proof.
  induction n as [|n IH]; intros.
  - exists (ds_match_start s). symmetry. apply set_ms_self.
  - cbn [longest_match_loop].
    destruct (longest_match_body s cur cl bl nice lim se1 se) as [[[[[[s1 bl1] a1] a2] c1] cl1] cont] eqn:E.
    pose proof (longest_match_body_ms s cur cl bl nice lim se1 se) as [ms1 E1]. rewrite E in E1. cbn [fst] in E1.
    destruct cont.
    + destruct (IH s1 c1 cl1 bl1 nice lim a1 a2) as [ms2 E2]. rewrite E2, E1. exists ms2. apply set_ms_twice.
    + exists ms1. exact E1.
Qed.

Lemma longest_match_ms : forall s cur, exists ms, fst (longest_match s cur) = set_match_start s ms.
Proof.
  intros s cur. unfold longest_match.
  destruct (longest_match_loop _ _ _ _ _ _ _ _ _) as [s1 bl] eqn:E.
  match type of E with ?l = _ => pose proof (longest_match_loop_ms (Z.to_nat (if ds_good_match s <=? ds_prev_length s then Z.shiftr (ds_max_chain_length s) 2 else ds_max_chain_length s)) s cur
     (if ds_good_match s <=? ds_prev_length s then Z.shiftr (ds_max_chain_length s) 2 else ds_max_chain_length s)
     (ds_prev_length s) (if ds_lookahead s <? ds_nice_match s then ds_lookahead s else ds_nice_match s)
     (if ds_w_size s - MIN_LOOKAHEAD <? ds_strstart s then ds_strstart s - (ds_w_size s - MIN_LOOKAHEAD) else NIL)
     (arr_get (ds_window s) (ds_strstart s + ds_prev_length s - 1)) (arr_get (ds_window s) (ds_strstart s + ds_prev_length s))) as [ms Hms] end.
  rewrite E in Hms. cbn [fst] in Hms. exists ms. destruct (bl <=? ds_lookahead s1); cbn [fst]; exact Hms.
Qed.


Definition fp_len (s1 : deflate_state) : Z :=
  let len := wrap32 (ds_pending s1) in
  if cs_avail_out (ds_strm s1) <? len then cs_avail_out (ds_strm s1) else len.

Definition fp_tail (s1 : deflate_state) (len : Z) : deflate_state :=
  let st := ds_strm s1 in
  let st1 := cs_emit st (arr_slice (ds_pending_buf s1) (ds_pending_out s1) len) in
  let s2 := set_strm s1 st1 in
  let s3 := set_pending_out s2 (ds_pending_out s1 + len) in
  let s4 := set_strm s3 (cset_avail_out st1 (cs_avail_out st - len)) in
  let s5 := set_strm s4 (cset_total_out (cset_avail_out st1 (cs_avail_out st - len)) (wrap64 (cs_total_out st + len))) in
  let s6 := set_pending s5 (ds_pending s1 - len) in
  if ds_pending s1 - len =? 0 then set_pending_out s6 0 else s6.

Lemma flush_pending_eq : forall s,
  flush_pending s =
  (let s1 := tr_flush_bits s in
   let len := fp_len s1 in
   if len =? 0 then s1 else fp_tail s1 len).
Proof.
  intros s. unfold flush_pending, fp_len, fp_tail. cbv zeta.
  set (s1 := tr_flush_bits s). clearbody s1.
  destruct (_ =? 0) eqn:E0; [reflexivity|].
  destruct s1; cbn -[Z.sub Z.add Z.eqb wrap64 wrap32 arr_slice cs_emit Z.ltb].
  destruct ds_strm; cbn -[Z.sub Z.add Z.eqb wrap64 wrap32 arr_slice Z.ltb].
  destruct (_ =? 0); reflexivity.
Qed.
