(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.RefDeflSafeL1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeG.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflFastM.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflFastM.RefDeflSafeW.

Module RefDeflSafeT.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma arr_set_range16 : forall (a : arr) i v nn,
  (forall j, 0 <= j < nn -> 0 <= arr_get a j < 65536) ->
  forall j, 0 <= j < nn -> 0 <= arr_get (arr_set a i (wrap16 v)) j < 65536.
Proof.
  intros a i v nn H j Hj. rewrite arr_get_set. destruct (_ && _); [apply wrap16_range | apply H; exact Hj].
Qed.

Lemma arr_set_range8 : forall (a : arr) i v nn,
  (forall j, 0 <= j < nn -> 0 <= arr_get a j < 256) ->
  forall j, 0 <= j < nn -> 0 <= arr_get (arr_set a i (wrap8 v)) j < 256.
Proof.
  intros a i v nn H j Hj. rewrite arr_get_set. destruct (_ && _); [apply wrap8_range | apply H; exact Hj].
Qed.

Definition tally_keep (a b : deflate_state) : Prop :=
  ds_strm b = ds_strm a /\ ds_window b = ds_window a /\ ds_prev b = ds_prev a /\ ds_head b = ds_head a
  /\ ds_lookahead b = ds_lookahead a /\ ds_strstart b = ds_strstart a /\ ds_block_start b = ds_block_start a
  /\ ds_match_length b = ds_match_length a /\ ds_match_start b = ds_match_start a /\ ds_prev_length b = ds_prev_length a
  /\ ds_prev_match b = ds_prev_match a /\ ds_match_available b = ds_match_available a
  /\ ds_pending b = ds_pending a /\ ds_pending_out b = ds_pending_out a /\ ds_bi_valid b = ds_bi_valid a /\ ds_bi_buf b = ds_bi_buf a
  /\ ds_lit_bufsize b = ds_lit_bufsize a /\ ds_pending_buf_size b = ds_pending_buf_size a /\ ds_sym_end b = ds_sym_end a
  /\ ds_w_size b = ds_w_size a /\ ds_hash_size b = ds_hash_size a /\ ds_w_mask b = ds_w_mask a /\ ds_hash_mask b = ds_hash_mask a
  /\ ds_hash_shift b = ds_hash_shift a /\ ds_ins_h b = ds_ins_h a /\ ds_insert b = ds_insert a /\ ds_window_size b = ds_window_size a
  /\ ds_level b = ds_level a /\ ds_strategy b = ds_strategy a /\ ds_max_lazy_match b = ds_max_lazy_match a
  /\ ds_good_match b = ds_good_match a /\ ds_nice_match b = ds_nice_match a /\ ds_max_chain_length b = ds_max_chain_length a
  /\ ds_status b = ds_status a /\ ds_wrap b = ds_wrap a /\ ds_high_water b = ds_high_water a /\ ds_matches b = ds_matches a
  /\ arr_len (ds_pending_buf b) = arr_len (ds_pending_buf a).

Lemma tally_lit_facts : forall s c,
  let r := tr_tally_lit s c in
  tally_keep s (fst r)
  /\ ds_sym_next (fst r) = ds_sym_next s + 3
  /\ snd r = (ds_sym_next s + 3 =? ds_sym_end s)
  /\ ds_dyn_dtree_fc (fst r) = ds_dyn_dtree_fc s /\ ds_bl_tree_fc (fst r) = ds_bl_tree_fc s
  /\ ds_dyn_ltree_fc (fst r) = arr_set (ds_dyn_ltree_fc s) (wrap8 c) (wrap16 (arr_get (ds_dyn_ltree_fc s) (wrap8 c) + 1))
  /\ (forall nn, (forall j, 0 <= j < nn -> 0 <= arr_get (ds_dyn_ltree_fc s) j < 65536) ->
               forall j, 0 <= j < nn -> 0 <= arr_get (ds_dyn_ltree_fc (fst r)) j < 65536)
  /\ (forall nn, (forall j, 0 <= j < nn -> 0 <= arr_get (ds_pending_buf s) j < 256) ->
               forall j, 0 <= j < nn -> 0 <= arr_get (ds_pending_buf (fst r)) j < 256).
Proof.
  intros s c r. subst r. unfold tr_tally_lit, sym_buf_set, set_Freq, Freq, tree_fc, set_tree_fc. dsred.
  split. { unfold tally_keep. dsred. rewrite !arr_len_set. repeat split; reflexivity. }
  split; [lia|]. split; [f_equal; lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split. { intros nn H. apply arr_set_range16. exact H. }
  intros nn H. apply arr_set_range8. apply arr_set_range8. apply arr_set_range8. exact H.
Qed.

Lemma tally_dist_facts : forall s distance length,
  let r := tr_tally_dist s distance length in
  tally_keep s (fst r)
  /\ ds_sym_next (fst r) = ds_sym_next s + 3
  /\ snd r = (ds_sym_next s + 3 =? ds_sym_end s)
  /\ ds_bl_tree_fc (fst r) = ds_bl_tree_fc s
  /\ (forall nn, (forall j, 0 <= j < nn -> 0 <= arr_get (ds_dyn_ltree_fc s) j < 65536) ->
               forall j, 0 <= j < nn -> 0 <= arr_get (ds_dyn_ltree_fc (fst r)) j < 65536)
  /\ (forall nn, (forall j, 0 <= j < nn -> 0 <= arr_get (ds_dyn_dtree_fc s) j < 65536) ->
               forall j, 0 <= j < nn -> 0 <= arr_get (ds_dyn_dtree_fc (fst r)) j < 65536)
  /\ (forall nn, (forall j, 0 <= j < nn -> 0 <= arr_get (ds_pending_buf s) j < 256) ->
               forall j, 0 <= j < nn -> 0 <= arr_get (ds_pending_buf (fst r)) j < 256).
Proof.
  intros s distance length r. subst r. unfold tr_tally_dist, sym_buf_set, set_Freq, Freq, tree_fc, set_tree_fc. dsred.
  split. { unfold tally_keep. dsred. rewrite !arr_len_set. repeat split; reflexivity. }
  split; [lia|]. split; [f_equal; lia|]. split; [reflexivity|].
  split. { intros nn H. apply arr_set_range16. exact H. }
  split. { intros nn H. apply arr_set_range16. exact H. }
  intros nn H. apply arr_set_range8. apply arr_set_range8. apply arr_set_range8. exact H.
Qed.

Lemma insert_string_facts : forall s str,
  let r := insert_string s str in
  let h := update_hash s (ds_ins_h s) (arr_get (ds_window s) (str + (MIN_MATCH - 1))) in
  snd r = arr_get (ds_head s) h
  /\ ds_ins_h (fst r) = h
  /\ ds_head (fst r) = arr_set (ds_head s) h (wrap16 str)
  /\ ds_prev (fst r) = arr_set (ds_prev s) (Z.land str (ds_w_mask s)) (arr_get (ds_head s) h)
  /\ ds_strm (fst r) = ds_strm s /\ ds_window (fst r) = ds_window s /\ ds_lookahead (fst r) = ds_lookahead s
  /\ ds_strstart (fst r) = ds_strstart s /\ ds_block_start (fst r) = ds_block_start s
  /\ ds_match_length (fst r) = ds_match_length s /\ ds_sym_next (fst r) = ds_sym_next s
  /\ ds_dyn_ltree_fc (fst r) = ds_dyn_ltree_fc s /\ ds_dyn_dtree_fc (fst r) = ds_dyn_dtree_fc s
  /\ ds_pending (fst r) = ds_pending s /\ ds_pending_buf (fst r) = ds_pending_buf s
  /\ ds_bi_valid (fst r) = ds_bi_valid s /\ ds_bi_buf (fst r) = ds_bi_buf s
  /\ ds_insert (fst r) = ds_insert s /\ ds_prev_length (fst r) = ds_prev_length s /\ ds_match_start (fst r) = ds_match_start s
  /\ (0 <= ds_hash_mask s -> 0 <= h <= ds_hash_mask s).
Proof.
  intros s str r h. subst r h. unfold insert_string. dsred.
  repeat (split; [reflexivity|]).
  intros Hm. exact (update_hash_range s (ds_ins_h s) (arr_get (ds_window s) (str + (MIN_MATCH - 1))) Hm).
Qed.
End RefDeflSafeT.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeT.

Module RefDeflSafeF.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSlow6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefDeflFastM.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflFastM.RefDeflSafeW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition lz_meas (s : deflate_state) : Z := ds_lookahead s + cs_avail_in (ds_strm s).

Lemma lz_fuel_meas : forall s, 0 <= lz_meas s -> lz_meas s < Z.of_nat (lz_fuel s).
Proof. intros s H. unfold lz_fuel, lz_meas in *. rewrite Z2Nat.id; lia. Qed.


Section FastFrame.
  Variable ws : Z.
Variable hs : Z.
Variable flush : Z.
  Variable FTI : deflate_state -> Prop.

  Hypothesis Hmeas : forall s, FTI s -> 0 <= lz_meas s.
  Hypothesis Hstep : forall s, FTI s ->
    trip_ok ws hs s flush
    /\ match snd (st_body s flush) with
       | LCont => FTI (fst (st_body s flush)) /\ lz_meas (fst (st_body s flush)) < lz_meas s
       | LBreak => FTI (fst (st_body s flush))
       | LRet _ => True
       end.

  Lemma loop_ok_FTI : forall fuel s, FTI s -> lz_meas s < Z.of_nat fuel ->
    loop_ok ws hs fuel s flush
    /\ (snd (deflate_fast_loop fuel s flush) = None -> FTI (fst (deflate_fast_loop fuel s flush))).
  Proof.
    induction fuel as [|f IH]; intros s HI Hm.
    { pose proof (Hmeas s HI). lia. }
    rewrite loop_ok_S, loop_step. destruct (Hstep s HI) as [HT HC].
    destruct (snd (st_body s flush)) eqn:E.
    - destruct HC as [HI' Hm'].
      destruct (IH (fst (st_body s flush)) HI' ltac:(lia)) as [HL HF].
      split; [exact (conj HT HL) | exact HF].
    - cbn [fst snd]. split; [exact (conj HT I)|]. intros _. exact HC.
    - cbn [fst snd]. split; [exact (conj HT I)|]. intros H; discriminate H.
  Qed.

  Hypothesis Htail : forall s, FTI s -> tail_ok ws s flush.

  Lemma fast_safe_frame : forall ds, DWF ds -> FTI ds -> ds_w_size ds = ws -> ds_hash_size ds = hs -> fast_safe ds flush.
  Proof.
    intros ds HWF HI Ews Ehs. unfold fast_safe. rewrite Ews, Ehs.
    destruct (loop_ok_FTI (lz_fuel ds) ds HI (lz_fuel_meas ds (Hmeas ds HI))) as [HL HF].
    split; [exact HWF|]. split; [exact HL|].
    destruct (snd (deflate_fast_loop (lz_fuel ds) ds flush)) eqn:E; [exact I|].
    apply Htail. apply HF. reflexivity.
  Qed.
End FastFrame.


Section SlowFrame.
  Variable ws : Z.
Variable hs : Z.
Variable flush : Z.
  Variable STI : deflate_state -> Prop.

  Hypothesis Hmeas : forall s, STI s -> 0 <= lz_meas s.
  Hypothesis Hstep : forall s, STI s ->
    strip_ok ws hs s flush
    /\ match snd (st_sbody s flush) with
       | LCont => STI (fst (st_sbody s flush)) /\ lz_meas (fst (st_sbody s flush)) < lz_meas s
       | LBreak => STI (fst (st_sbody s flush))
       | LRet _ => True
       end.

  Lemma sloop_ok_STI : forall fuel s, STI s -> lz_meas s < Z.of_nat fuel ->
    sloop_ok ws hs fuel s flush
    /\ (snd (deflate_slow_loop fuel s flush) = None -> STI (fst (deflate_slow_loop fuel s flush))).
  Proof.
    induction fuel as [|f IH]; intros s HI Hm.
    { pose proof (Hmeas s HI). lia. }
    rewrite sloop_ok_S, sloop_step'. destruct (Hstep s HI) as [HT HC].
    destruct (snd (st_sbody s flush)) eqn:E.
    - destruct HC as [HI' Hm'].
      destruct (IH (fst (st_sbody s flush)) HI' ltac:(lia)) as [HL HF].
      split; [exact (conj HT HL) | exact HF].
    - cbn [fst snd]. split; [exact (conj HT I)|]. intros _. exact HC.
    - cbn [fst snd]. split; [exact (conj HT I)|]. intros H; discriminate H.
  Qed.

  Hypothesis Htail : forall s, STI s -> stail_ok ws s flush.

  Lemma slow_safe_frame : forall ds, DWF ds -> STI ds -> ds_w_size ds = ws -> ds_hash_size ds = hs -> slow_safe ds flush.
  Proof.
    intros ds HWF HI Ews Ehs. unfold slow_safe. rewrite Ews, Ehs.
    destruct (sloop_ok_STI (lz_fuel ds) ds HI (lz_fuel_meas ds (Hmeas ds HI))) as [HL HF].
    split; [exact HWF|]. split; [exact HL|].
    destruct (snd (deflate_slow_loop (lz_fuel ds) ds flush)) eqn:E; [exact I|].
    apply Htail. apply HF. reflexivity.
  Qed.
End SlowFrame.


Lemma hloop_step : forall f s flush,
  deflate_huff_loop (S f) s flush
  = match snd (hf_body s flush) with
    | LCont => deflate_huff_loop f (fst (hf_body s flush)) flush
    | LBreak => (fst (hf_body s flush), None)
    | LRet bs => (fst (hf_body s flush), Some bs)
    end.
Proof. intros. cbn [deflate_huff_loop]. rewrite hf_body_eq. destruct (hf_body s flush) as [s' o]. reflexivity. Qed.

Lemma rloop_step : forall f s flush,
  deflate_rle_loop (S f) s flush
  = match snd (rl_body s flush) with
    | LCont => deflate_rle_loop f (fst (rl_body s flush)) flush
    | LBreak => (fst (rl_body s flush), None)
    | LRet bs => (fst (rl_body s flush), Some bs)
    end.
Proof. intros. cbn [deflate_rle_loop]. rewrite rl_body_eq. destruct (rl_body s flush) as [s' o]. reflexivity. Qed.

Section HuffFrame.
  Variable FB : deflate_state -> option Z -> Z -> Z -> Prop.
  Variable flush : Z.
  Variable HTI : deflate_state -> Prop.

  Hypothesis Hmeas : forall s, HTI s -> 0 <= lz_meas s.
  Hypothesis Hstep : forall s, HTI s ->
    hf_trip_ok FB s flush
    /\ match snd (hf_body s flush) with
       | LCont => HTI (fst (hf_body s flush)) /\ lz_meas (fst (hf_body s flush)) < lz_meas s
       | LBreak => HTI (fst (hf_body s flush))
       | LRet _ => HTI (fst (hf_body s flush))
       end.

  Lemma hf_loop_ok_HTI : forall fuel s, HTI s -> lz_meas s < Z.of_nat fuel ->
    hf_loop_ok FB fuel s flush /\ HTI (fst (deflate_huff_loop fuel s flush)).
  Proof.
    induction fuel as [|f IH]; intros s HI Hm.
    { pose proof (Hmeas s HI). lia. }
    rewrite hf_loop_ok_S, hloop_step. destruct (Hstep s HI) as [HT HC].
    destruct (snd (hf_body s flush)) eqn:E.
    - destruct HC as [HI' Hm'].
      destruct (IH (fst (hf_body s flush)) HI' ltac:(lia)) as [HL HF].
      split; [exact (conj HT HL) | exact HF].
    - cbn [fst snd]. exact (conj (conj HT I) HC).
    - cbn [fst snd]. exact (conj (conj HT I) HC).
  Qed.
End HuffFrame.

Section RleFrame.
  Variable FB : deflate_state -> option Z -> Z -> Z -> Prop.
  Variable flush : Z.
  Variable RTI : deflate_state -> Prop.

  Hypothesis Hmeas : forall s, RTI s -> 0 <= lz_meas s.
  Hypothesis Hstep : forall s, RTI s ->
    rl_trip_ok FB s flush
    /\ match snd (rl_body s flush) with
       | LCont => RTI (fst (rl_body s flush)) /\ lz_meas (fst (rl_body s flush)) < lz_meas s
       | LBreak => RTI (fst (rl_body s flush))
       | LRet _ => RTI (fst (rl_body s flush))
       end.

  Lemma rl_loop_ok_RTI : forall fuel s, RTI s -> lz_meas s < Z.of_nat fuel ->
    rl_loop_ok FB fuel s flush /\ RTI (fst (deflate_rle_loop fuel s flush)).
  Proof.
    induction fuel as [|f IH]; intros s HI Hm.
    { pose proof (Hmeas s HI). lia. }
    rewrite rl_loop_ok_S, rloop_step. destruct (Hstep s HI) as [HT HC].
    destruct (snd (rl_body s flush)) eqn:E.
    - destruct HC as [HI' Hm'].
      destruct (IH (fst (rl_body s flush)) HI' ltac:(lia)) as [HL HF].
      split; [exact (conj HT HL) | exact HF].
    - cbn [fst snd]. exact (conj (conj HT I) HC).
    - cbn [fst snd]. exact (conj (conj HT I) HC).
  Qed.
End RleFrame.


Lemma st_fill_facts : forall ws hs s flush,
  fw_wf ws hs s ->
  let s1 := fst (st_fill s flush) in
  let o := snd (st_fill s flush) in
  fw_wf ws hs s1 /\ fw_const s s1 /\ fw_keep s s1
  /\ ds_lookahead s <= ds_lookahead s1 <= 2 * ws
  /\ cs_avail_in (ds_strm s1) = cs_avail_in (ds_strm s) - (ds_lookahead s1 - ds_lookahead s)
  /\ (o = None -> 1 <= ds_lookahead s1 /\ (ds_lookahead s1 < MIN_LOOKAHEAD -> flush <> Z_NO_FLUSH /\ cs_avail_in (ds_strm s1) = 0))
  /\ (o = Some LBreak -> ds_lookahead s1 = 0 /\ flush <> Z_NO_FLUSH)
  /\ (forall bs, o = Some (LRet bs) -> bs = need_more /\ flush = Z_NO_FLUSH /\ ds_lookahead s1 < MIN_LOOKAHEAD)
  /\ o <> Some LCont.
Proof.
  intros ws hs s flush HW s1 o. subst s1 o. unfold st_fill.
  pose proof (wf_sl _ _ _ HW) as Vsl. pose proof (wf_look _ _ _ HW) as Vl. pose proof (wf_ins _ _ _ HW) as Vins.
  pose proof (wf_ws _ _ _ HW) as Ews.
  destruct (Z.ltb_spec (ds_lookahead s) MIN_LOOKAHEAD) as [Hlo|Hhi].
  - pose proof (fill_window_facts ws hs s HW Hlo) as F. cbv zeta in F. destruct F as (HW1 & HC1 & HK1 & HL1 & HA1 & HX1).
    pose proof (wf_look _ _ _ HW1) as Vl1.
    destruct (Z.ltb_spec (ds_lookahead (fill_window s)) MIN_LOOKAHEAD) as [L1|L1]; cbn [andb].
    + destruct (Z.eqb_spec flush Z_NO_FLUSH) as [Hf|Hf]; cbn [fst snd].
      { repeat (split; [assumption|]). split; [intros H; discriminate H|]. split; [intros H; discriminate H|].
        split; [intros bs H; injection H as <-; repeat split; assumption | intros H; discriminate H]. }
      destruct (Z.eqb_spec (ds_lookahead (fill_window s)) 0) as [Z0|Z0]; cbn [fst snd].
      { repeat (split; [assumption|]). split; [intros H; discriminate H|]. split; [intros _; split; assumption|].
        split; [intros bs H; discriminate H | intros H; discriminate H]. }
      repeat (split; [assumption|]). split; [intros _; split; [lia | intros Hl1; split; [exact Hf | exact (HX1 Hl1)]]|].
      split; [intros H; discriminate H|]. split; [intros bs H; discriminate H | intros H; discriminate H].
    + destruct (Z.eqb_spec (ds_lookahead (fill_window s)) 0) as [Z0|Z0]; cbn [fst snd].
      { unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in L1. lia. }
      repeat (split; [assumption|]). split; [intros _; split; [lia | intros H; lia]|].
      split; [intros H; discriminate H|]. split; [intros bs H; discriminate H | intros H; discriminate H].
  - cbn [fst snd]. split; [exact HW|]. split; [repeat split; reflexivity|]. split; [apply fw_keep_refl|].
    unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in Hhi.
    split; [lia|]. split; [lia|]. split; [intros _; split; [lia | intros H; unfold MIN_LOOKAHEAD, MAX_MATCH, MIN_MATCH in H; lia]|].
    split; [intros H; discriminate H|]. split; [intros bs H; discriminate H | intros H; discriminate H].
Qed.
End RefDeflSafeF.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeFBT.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI2.

Module RefDeflSafeI3.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.RefDeflSafeL1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeG.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Lemma DX_status_wrap : forall s s',
  dx_core2 s' = dx_core2 (set_wrap (set_status s (ds_status s')) (ds_wrap s')) ->
  ds_pending s' = ds_pending s -> ds_pending_out s' = ds_pending_out s -> ds_bi_valid s' = ds_bi_valid s ->
  ds_pending_buf s' = ds_pending_buf s -> ds_lit_bufsize s' = ds_lit_bufsize s ->
  (ds_wrap s' < 0 -> ds_status s' = FINISH_STATE) ->
  (ds_status s' = FINISH_STATE -> ds_lookahead s = 0) ->
  DX s -> DX s'.
Proof.
  intros s s' E Ep Epo Ebv Epb Elbs Hw Hf X.
  set (t := set_wrap (set_status s (ds_status s')) (ds_wrap s')) in E.
  assert (Xt : DX t).
  { subst t. destruct X; constructor; unfold set_wrap, set_status, dmode, nsym in *; dsred; assumption. }
  apply (DX_core2_same t s' E).
  - intros i Hi. unfold sym_buf_get. subst t; unfold set_wrap, set_status; dsred. rewrite Epb, Elbs. reflexivity.
  - subst t; unfold set_wrap, set_status; dsred. rewrite Ep, Epo. exact (dx_pout0 _ X).
  - subst t; unfold set_wrap, set_status; dsred. rewrite Ebv. exact (dx_biv _ X).
  - exact Xt.
Qed.

Lemma DC_set_status : forall c0 s st,
  DC c0 s -> (st = 42 \/ st = 57 \/ st = 113 \/ st = 666) ->
  (ds_wrap s < 0 -> st = FINISH_STATE) -> (st = FINISH_STATE -> ds_lookahead s = 0) ->
  DC c0 (set_status s st) /\ KV (set_status s st) = KV s /\ ds_strm (set_status s st) = ds_strm s.
Proof.
  intros c0 s st [[D X] V] Hst Hw Hf. split; [| split; reflexivity].
  split; [split|].
  - destruct D; constructor; unfold set_status; dsred; try assumption.
    unfold deflateStateCheck. dsred. unfold INIT_STATE, GZIP_STATE, BUSY_STATE, FINISH_STATE.
    destruct Hst as [-> | [-> | [-> | ->]]]; reflexivity.
  - apply (DX_status_wrap s (set_status s st)); unfold set_status, set_wrap; dsred.
    all: first [exact X | exact Hw | exact Hf | reflexivity | (destruct s; reflexivity)].
  - apply (SV_strm c0 s); [reflexivity | exact V].
Qed.

Lemma DC_set_wrap_neg : forall c0 s w,
  DC c0 s -> - 2 <= w <= 2 -> ds_status s = FINISH_STATE ->
  DC c0 (set_wrap s w) /\ KV (set_wrap s w) = KV s /\ ds_strm (set_wrap s w) = ds_strm s.
Proof.
  intros c0 s w [[D X] V] Hw Hst. split; [| split; reflexivity].
  split; [split|].
  - destruct D; constructor; unfold set_wrap; dsred; try assumption.
  - pose proof (dx_fin _ X) as Hf.
    assert (Hw' : w < 0 -> ds_status s = FINISH_STATE) by (intros _; exact Hst).
    apply (DX_status_wrap s (set_wrap s w)); unfold set_status, set_wrap; dsred.
    all: first [exact X | exact Hw' | exact Hf | reflexivity | (destruct s; reflexivity)].
  - apply (SV_strm c0 s); [reflexivity | exact V].
Qed.

Lemma DC_set_adler : forall c0 s a, DC c0 s -> 0 <= a < 2 ^ 64 ->
  DC c0 (set_strm s (cset_adler (ds_strm s) a)) /\ KV (set_strm s (cset_adler (ds_strm s) a)) = KV s.
Proof.
  intros c0 s a [DDs V] Ha. split; [| reflexivity]. split; [apply DD_set_strm; exact DDs|].
  destruct V; constructor; unfold set_strm, cset_adler; dsred; cbn; assumption.
Qed.


Lemma put_byte_status : forall s b, ds_status (put_byte s b) = ds_status s. Proof. reflexivity. Qed.
Lemma put_byte_wrap : forall s b, ds_wrap (put_byte s b) = ds_wrap s. Proof. reflexivity. Qed.
Lemma put_byte_lookahead : forall s b, ds_lookahead (put_byte s b) = ds_lookahead s. Proof. reflexivity. Qed.
Lemma putShortMSB_status : forall s b, ds_status (putShortMSB s b) = ds_status s. Proof. reflexivity. Qed.
Lemma putShortMSB_wrap : forall s b, ds_wrap (putShortMSB s b) = ds_wrap s. Proof. reflexivity. Qed.
Lemma putShortMSB_lookahead : forall s b, ds_lookahead (putShortMSB s b) = ds_lookahead s. Proof. reflexivity. Qed.

Definition PW (c0 : cstrm) (s : deflate_state) (n : Z) : Prop :=
  DC c0 s /\ ds_pending_out s = 0 /\ 0 <= ds_pending s <= n.

Lemma PW_put_byte : forall c0 s n b, PW c0 s n -> n + 1 <= 128 ->
  PW c0 (put_byte s b) (n + 1) /\ KV (put_byte s b) = KV s /\ ds_strm (put_byte s b) = ds_strm s.
Proof.
  intros c0 s n b (HDC & Hpo & Hp) Hn. pose proof HDC as [[D X] V]. pose proof (dwf_sizes s D) as (_ & _ & Sl & _).
  destruct (DC_put_byte c0 s b HDC ltac:(lia) ltac:(lia)) as (HDC' & E1 & E2 & E3 & E4 & E5).
  split; [| split; [exact E3 | exact E4]]. split; [exact HDC'|]. rewrite E1, E2. lia.
Qed.

Lemma PW_putShortMSB : forall c0 s n b, PW c0 s n -> n + 2 <= 128 ->
  PW c0 (putShortMSB s b) (n + 2) /\ KV (putShortMSB s b) = KV s /\ ds_strm (putShortMSB s b) = ds_strm s.
Proof.
  intros c0 s n b H Hn. unfold putShortMSB.
  destruct (PW_put_byte c0 s n (Z.shiftr b 8) H ltac:(lia)) as (H1 & K1 & S1).
  destruct (PW_put_byte c0 _ (n + 1) (Z.land b 255) H1 ltac:(lia)) as (H2 & K2 & S2).
  replace (n + 2) with (n + 1 + 1) by lia. split; [exact H2|]. rewrite K2, S2, K1, S1. split; reflexivity.
Qed.

Lemma PW_weaken : forall c0 s n m, PW c0 s n -> n <= m -> PW c0 s m.
Proof. intros c0 s n m (A & B & C) H. split; [exact A|]. split; [exact B | lia]. Qed.

Lemma PW_set_adler : forall c0 s n a, PW c0 s n -> 0 <= a < 2 ^ 64 ->
  PW c0 (set_strm s (cset_adler (ds_strm s) a)) n /\ KV (set_strm s (cset_adler (ds_strm s) a)) = KV s.
Proof.
  intros c0 s n a (A & B & C) Ha. destruct (DC_set_adler c0 s a A Ha) as [A' K]. split; [| exact K].
  split; [exact A'|]. unfold set_strm; dsred. split; [exact B | exact C].
Qed.

Lemma PW_set_status_busy : forall c0 s n, PW c0 s n -> ds_status s <> FINISH_STATE ->
  PW c0 (set_status s BUSY_STATE) n /\ KV (set_status s BUSY_STATE) = KV s.
Proof.
  intros c0 s n (A & B & C) Hst. pose proof A as [[D X] V].
  destruct (DC_set_status c0 s BUSY_STATE A ltac:(unfold BUSY_STATE; lia)
              ltac:(intros Hw; exfalso; exact (Hst (dx_wrapneg _ X Hw))) ltac:(unfold BUSY_STATE, FINISH_STATE; intros; lia)) as (A' & K & _).
  split; [| exact K]. split; [exact A'|]. unfold set_status; dsred. split; [exact B | exact C].
Qed.


Lemma adler32_init_range : 0 <= adler32_init < 2 ^ 64. Proof. unfold adler32_init. cbn. lia. Qed.
Lemma crc32_init_range : 0 <= crc32_init < 2 ^ 64. Proof. unfold crc32_init. cbn. lia. Qed.

Lemma zhdr_facts : forall c0 s, DC c0 s -> ds_pending s = 0 -> ds_status s = INIT_STATE ->
  let h := zhdr_st s in
  PW c0 h 6 /\ KV h = KV s /\ OUTLE s h /\ ds_status h = BUSY_STATE
  /\ cs_avail_in (ds_strm h) = cs_avail_in (ds_strm s) /\ ds_lookahead h = ds_lookahead s /\ ds_wrap h = ds_wrap s.
Proof.
  intros c0 s HDC Hp Hst h. subst h. pose proof HDC as [[D X] V].
  assert (P0 : PW c0 s 0) by (split; [exact HDC|]; split; [exact (dx_pout0 _ X Hp) | lia]).
  unfold zhdr_st. cbv zeta.
  match goal with |- context [putShortMSB s ?hd] => set (hdr := hd) end.
  destruct (PW_putShortMSB c0 s 0 hdr P0 ltac:(lia)) as (P1 & K1 & S1).
  set (s1 := putShortMSB s hdr) in *.
  assert (Hst1 : ds_status s1 = INIT_STATE) by (unfold s1; rewrite putShortMSB_status; exact Hst).
  set (s2 := if negb (ds_strstart s1 =? 0) then putShortMSB (putShortMSB s1 (wrap32 (Z.shiftr (cs_adler (ds_strm s1)) 16))) (Z.land (cs_adler (ds_strm s1)) 65535) else s1).
  assert (Hl1 : ds_lookahead s1 = ds_lookahead s /\ ds_wrap s1 = ds_wrap s) by (unfold s1; rewrite putShortMSB_lookahead, putShortMSB_wrap; split; reflexivity).
  assert (H2 : PW c0 s2 6 /\ KV s2 = KV s /\ ds_strm s2 = ds_strm s /\ ds_status s2 = INIT_STATE /\ ds_lookahead s2 = ds_lookahead s /\ ds_wrap s2 = ds_wrap s).
  { subst s2. destruct (negb (ds_strstart s1 =? 0)).
    - destruct (PW_putShortMSB c0 s1 2 (wrap32 (Z.shiftr (cs_adler (ds_strm s1)) 16)) P1 ltac:(lia)) as (P2 & K2 & S2).
      destruct (PW_putShortMSB c0 _ 4 (Z.land (cs_adler (ds_strm s1)) 65535) P2 ltac:(lia)) as (P3 & K3 & S3).
      split; [exact P3|]. rewrite K3, S3, K2, S2, K1, S1. split; [reflexivity|]. split; [reflexivity|].
      rewrite !putShortMSB_status, !putShortMSB_lookahead, !putShortMSB_wrap. split; [exact Hst1 | exact Hl1].
    - split; [apply (PW_weaken c0 s1 2 6 P1); lia|]. rewrite K1, S1. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hst1 | exact Hl1]. }
  clearbody s2. destruct H2 as (P2 & K2 & S2 & Hst2 & Hl2 & Hw2).
  destruct (PW_set_adler c0 s2 6 adler32_init P2 adler32_init_range) as (P3 & K3).
  destruct (PW_set_status_busy c0 _ 6 P3 ltac:(unfold set_strm; dsred; rewrite Hst2; unfold INIT_STATE, FINISH_STATE; lia)) as (P4 & K4).
  split; [exact P4|]. split; [rewrite K4, K3, K2; reflexivity|].
  split; [unfold OUTLE, set_status, set_strm, cset_adler; dsred; cbn [cs_out_rev]; rewrite S2; exists nil; reflexivity|].
  split; [reflexivity|].
  unfold set_status, set_strm, cset_adler; dsred. cbn [cs_avail_in]. rewrite S2. split; [reflexivity|]. split; [exact Hl2 | exact Hw2].
Qed.

Lemma gzhdr_facts : forall c0 s, DC c0 s -> ds_pending s = 0 -> ds_status s = GZIP_STATE ->
  let h := gzhdr_st s in
  PW c0 h 10 /\ KV h = KV s /\ OUTLE s h /\ ds_status h = BUSY_STATE
  /\ cs_avail_in (ds_strm h) = cs_avail_in (ds_strm s) /\ ds_lookahead h = ds_lookahead s /\ ds_wrap h = ds_wrap s.
Proof.
  intros c0 s HDC Hp Hst h. subst h. pose proof HDC as [[D X] V].
  assert (P0 : PW c0 s 0) by (split; [exact HDC|]; split; [exact (dx_pout0 _ X Hp) | lia]).
  unfold gzhdr_st. cbv zeta.
  destruct (PW_set_adler c0 s 0 crc32_init P0 crc32_init_range) as (Q0 & J0).
  set (t0 := set_strm s (cset_adler (ds_strm s) crc32_init)) in *.
  set (t1 := put_byte t0 31). set (t2 := put_byte t1 139). set (t3 := put_byte t2 8). set (t4 := put_byte t3 0).
  set (t5 := put_byte t4 0). set (t6 := put_byte t5 0). set (t7 := put_byte t6 0). set (t8 := put_byte t7 0).
  match goal with |- context [put_byte t8 ?x] => set (xflv := x) end.
  set (t9 := put_byte t8 xflv). set (t10 := put_byte t9 OS_CODE).
  destruct (PW_put_byte c0 t0 0 31 Q0 ltac:(lia)) as (Q1 & J1 & S1). fold t1 in Q1, J1, S1.
  destruct (PW_put_byte c0 t1 1 139 Q1 ltac:(lia)) as (Q2 & J2 & S2). fold t2 in Q2, J2, S2.
  destruct (PW_put_byte c0 t2 2 8 Q2 ltac:(lia)) as (Q3 & J3 & S3). fold t3 in Q3, J3, S3.
  destruct (PW_put_byte c0 t3 3 0 Q3 ltac:(lia)) as (Q4 & J4 & S4). fold t4 in Q4, J4, S4.
  destruct (PW_put_byte c0 t4 4 0 Q4 ltac:(lia)) as (Q5 & J5 & S5). fold t5 in Q5, J5, S5.
  destruct (PW_put_byte c0 t5 5 0 Q5 ltac:(lia)) as (Q6 & J6 & S6). fold t6 in Q6, J6, S6.
  destruct (PW_put_byte c0 t6 6 0 Q6 ltac:(lia)) as (Q7 & J7 & S7). fold t7 in Q7, J7, S7.
  destruct (PW_put_byte c0 t7 7 0 Q7 ltac:(lia)) as (Q8 & J8 & S8). fold t8 in Q8, J8, S8.
  destruct (PW_put_byte c0 t8 8 xflv Q8 ltac:(lia)) as (Q9 & J9 & S9). fold t9 in Q9, J9, S9.
  destruct (PW_put_byte c0 t9 9 OS_CODE Q9 ltac:(lia)) as (Q10 & J10 & S10). fold t10 in Q10, J10, S10.
  assert (St10 : ds_status t10 = GZIP_STATE /\ ds_lookahead t10 = ds_lookahead s /\ ds_wrap t10 = ds_wrap s).
  { unfold t10. rewrite put_byte_status, put_byte_lookahead, put_byte_wrap. unfold t9. rewrite put_byte_status, put_byte_lookahead, put_byte_wrap.
    unfold t8. rewrite put_byte_status, put_byte_lookahead, put_byte_wrap. unfold t7. rewrite put_byte_status, put_byte_lookahead, put_byte_wrap.
    unfold t6. rewrite put_byte_status, put_byte_lookahead, put_byte_wrap. unfold t5. rewrite put_byte_status, put_byte_lookahead, put_byte_wrap.
    unfold t4. rewrite put_byte_status, put_byte_lookahead, put_byte_wrap. unfold t3. rewrite put_byte_status, put_byte_lookahead, put_byte_wrap.
    unfold t2. rewrite put_byte_status, put_byte_lookahead, put_byte_wrap. unfold t1. rewrite put_byte_status, put_byte_lookahead, put_byte_wrap.
    unfold t0. unfold set_strm; dsred. split; [exact Hst | split; reflexivity]. }
  destruct St10 as (St10 & Lk10 & Wr10).
  destruct (PW_set_status_busy c0 t10 10 Q10 ltac:(rewrite St10; unfold GZIP_STATE, FINISH_STATE; lia)) as (Q11 & J11).
  split; [exact Q11|].
  split; [rewrite J11, J10, J9, J8, J7, J6, J5, J4, J3, J2, J1, J0; reflexivity|].
  split; [unfold OUTLE; unfold set_status; dsred; rewrite S10, S9, S8, S7, S6, S5, S4, S3, S2, S1; unfold t0, set_strm, cset_adler; dsred; cbn [cs_out_rev]; exists nil; reflexivity|].
  split; [reflexivity|].
  unfold set_status; dsred. rewrite S10, S9, S8, S7, S6, S5, S4, S3, S2, S1. split; [unfold t0, set_strm, cset_adler; dsred; reflexivity|].
  split; [exact Lk10 | exact Wr10].
Qed.

Lemma trailer_facts : forall c0 s, DC c0 s -> ds_pending s = 0 ->
  let h := trailer_st s in
  PW c0 h 8 /\ KV h = KV s /\ OUTLE s h /\ ds_status h = ds_status s /\ ds_wrap h = ds_wrap s /\ ds_lookahead h = ds_lookahead s.
Proof.
  intros c0 s HDC Hp h. subst h. pose proof HDC as [[D X] V].
  assert (P0 : PW c0 s 0) by (split; [exact HDC|]; split; [exact (dx_pout0 _ X Hp) | lia]).
  unfold trailer_st. cbv zeta.
  destruct (ds_wrap s =? 2).
  - set (a := cs_adler (ds_strm s)). set (t := cs_total_in (ds_strm s)).
    set (t1 := put_byte s (Z.land a 255)). set (t2 := put_byte t1 (Z.land (Z.shiftr a 8) 255)).
    set (t3 := put_byte t2 (Z.land (Z.shiftr a 16) 255)). set (t4 := put_byte t3 (Z.land (Z.shiftr a 24) 255)).
    set (t5 := put_byte t4 (Z.land t 255)). set (t6 := put_byte t5 (Z.land (Z.shiftr t 8) 255)).
    set (t7 := put_byte t6 (Z.land (Z.shiftr t 16) 255)). set (t8 := put_byte t7 (Z.land (Z.shiftr t 24) 255)).
    destruct (PW_put_byte c0 s 0 (Z.land a 255) P0 ltac:(lia)) as (Q1 & J1 & S1). fold t1 in Q1, J1, S1.
    destruct (PW_put_byte c0 t1 1 (Z.land (Z.shiftr a 8) 255) Q1 ltac:(lia)) as (Q2 & J2 & S2). fold t2 in Q2, J2, S2.
    destruct (PW_put_byte c0 t2 2 (Z.land (Z.shiftr a 16) 255) Q2 ltac:(lia)) as (Q3 & J3 & S3). fold t3 in Q3, J3, S3.
    destruct (PW_put_byte c0 t3 3 (Z.land (Z.shiftr a 24) 255) Q3 ltac:(lia)) as (Q4 & J4 & S4). fold t4 in Q4, J4, S4.
    destruct (PW_put_byte c0 t4 4 (Z.land t 255) Q4 ltac:(lia)) as (Q5 & J5 & S5). fold t5 in Q5, J5, S5.
    destruct (PW_put_byte c0 t5 5 (Z.land (Z.shiftr t 8) 255) Q5 ltac:(lia)) as (Q6 & J6 & S6). fold t6 in Q6, J6, S6.
    destruct (PW_put_byte c0 t6 6 (Z.land (Z.shiftr t 16) 255) Q6 ltac:(lia)) as (Q7 & J7 & S7). fold t7 in Q7, J7, S7.
    destruct (PW_put_byte c0 t7 7 (Z.land (Z.shiftr t 24) 255) Q7 ltac:(lia)) as (Q8 & J8 & S8). fold t8 in Q8, J8, S8.
    split; [exact Q8|].
    split; [rewrite J8, J7, J6, J5, J4, J3, J2, J1; reflexivity|].
    split; [unfold OUTLE; rewrite S8, S7, S6, S5, S4, S3, S2, S1; exists nil; reflexivity|].
    unfold t8. rewrite put_byte_status, put_byte_wrap, put_byte_lookahead. unfold t7. rewrite put_byte_status, put_byte_wrap, put_byte_lookahead.
    unfold t6. rewrite put_byte_status, put_byte_wrap, put_byte_lookahead. unfold t5. rewrite put_byte_status, put_byte_wrap, put_byte_lookahead.
    unfold t4. rewrite put_byte_status, put_byte_wrap, put_byte_lookahead. unfold t3. rewrite put_byte_status, put_byte_wrap, put_byte_lookahead.
    unfold t2. rewrite put_byte_status, put_byte_wrap, put_byte_lookahead. unfold t1. rewrite put_byte_status, put_byte_wrap, put_byte_lookahead.
    repeat split; reflexivity.
  - set (a := cs_adler (ds_strm s)).
    set (t1 := putShortMSB s (wrap32 (Z.shiftr a 16))). set (t2 := putShortMSB t1 (Z.land a 65535)).
    destruct (PW_putShortMSB c0 s 0 (wrap32 (Z.shiftr a 16)) P0 ltac:(lia)) as (Q1 & J1 & S1). fold t1 in Q1, J1, S1.
    destruct (PW_putShortMSB c0 t1 2 (Z.land a 65535) Q1 ltac:(lia)) as (Q2 & J2 & S2). fold t2 in Q2, J2, S2.
    split; [apply (PW_weaken _ _ _ 8 Q2); lia|].
    split; [rewrite J2, J1; reflexivity|].
    split; [unfold OUTLE; rewrite S2, S1; exists nil; reflexivity|].
    unfold t2. rewrite putShortMSB_status, putShortMSB_wrap, putShortMSB_lookahead.
    unfold t1. rewrite putShortMSB_status, putShortMSB_wrap, putShortMSB_lookahead. repeat split; reflexivity.
Qed.


Lemma DC_upd4 : forall c0 s A P B V,
  DC c0 s -> ds_pending_out s = 0 ->
  arr_len A = arr_len (ds_pending_buf s) ->
  (forall i, 0 <= i < ds_lit_bufsize s * 4 -> 0 <= arr_get A i < 256) ->
  (forall i, ds_lit_bufsize s <= i -> arr_get A i = arr_get (ds_pending_buf s) i) ->
  0 <= P <= ds_lit_bufsize s -> 0 <= V <= 7 -> 0 <= B < 2 ^ 16 ->
  DC c0 (upd4 s A P B V) /\ KV (upd4 s A P B V) = KV s /\ ds_strm (upd4 s A P B V) = ds_strm s.
Proof.
  intros c0 s A P B V [[D X] Vs] Hpo HlenA HbA HhiA HP HV HB. pose proof (dwf_sizes s D) as (_ & _ & Sl & _).
  split; [| split; reflexivity].
  split; [split|].
  - destruct D; constructor; unfold upd4; dsred; try assumption; try lia.
  - apply (DX_core2_same s); [reflexivity | | | | exact X]; unfold upd4; dsred.
    + intros i Hi. unfold sym_buf_get; dsred. apply HhiA. lia.
    + intros _. exact Hpo.
    + lia.
  - apply (SV_strm c0 s); [reflexivity | exact Vs].
Qed.

Lemma arr_get_set_other' : forall (a : arr) i j v, i <> j -> arr_get (arr_set a i v) j = arr_get a j.
Proof. intros a i j v H. rewrite arr_get_set. destruct (Z.eqb_spec i j); [lia|]. cbn [andb]. reflexivity. Qed.

Local Ltac bytes_tac Hbb :=
  intros i Hi; rewrite !arr_get_set;
  repeat (destruct (_ && _); [apply wrap8_range|]); apply Hbb; exact Hi.

Lemma tr_align_facts : forall c0 s, DC c0 s -> ds_pending s = 0 ->
  let h := tr_align s in
  DC c0 h /\ KV h = KV s /\ ds_strm h = ds_strm s /\ 0 <= ds_pending h <= 3 /\ ds_pending_out h = 0 /\ dx_core2 h = dx_core2 s.
Proof.
  intros c0 s HDC Hp h. subst h. pose proof HDC as [[D X] V]. pose proof (dwf_sizes s D) as (_ & _ & Sl & _).
  pose proof (df_bi _ D) as [Hbv Hbb]. pose proof (dx_biv _ X) as Hbv7. pose proof (dx_pout0 _ X Hp) as Hpo.
  pose proof (df_bb _ D) as Hbytes. pose proof (df_bl _ D) as Hbl.
  pose proof (sb_nb_range s 2) as Hnb.
  assert (Hnb8 : 0 <= Z.shiftr (sb_nb s 2) 8 < 2 ^ 16).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  destruct (Z_lt_le_dec (ds_bi_valid s) 6) as [C1|C1]; [| destruct (Z.eq_dec (ds_bi_valid s) 6) as [C2|C2]].
  - rewrite (tr_align_eq1 s Hbb) by lia.
    destruct (DC_upd4 c0 s (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (sb_nb s 2))) (ds_pending s + 1) (Z.shiftr (sb_nb s 2) 8) (ds_bi_valid s + 2)
                HDC Hpo ltac:(rewrite arr_len_set; reflexivity) ltac:(bytes_tac Hbytes)
                ltac:(intros i Hi; apply arr_get_set_other'; lia) ltac:(lia) ltac:(lia) Hnb8) as (A1 & A2 & A3).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. unfold upd4; dsred. repeat split; try lia; reflexivity.
  - rewrite (tr_align_eq2 s Hbb C2).
    destruct (DC_upd4 c0 s (arr_set (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (Z.land (sb_nb s 2) 255))) (ds_pending s + 1) (wrap8 (Z.shiftr (wrap16 (sb_nb s 2)) 8)))
                (ds_pending s + 1 + 1) 0 0
                HDC Hpo ltac:(rewrite !arr_len_set; reflexivity) ltac:(bytes_tac Hbytes)
                ltac:(intros i Hi; rewrite !arr_get_set_other' by lia; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as (A1 & A2 & A3).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. unfold upd4; dsred. repeat split; try lia; reflexivity.
  - rewrite (tr_align_eq3 s Hbb) by lia.
    destruct (DC_upd4 c0 s (arr_set (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (Z.land (sb_nb s 2) 255))) (ds_pending s + 1) (wrap8 (Z.shiftr (wrap16 (sb_nb s 2)) 8)))
                (ds_pending s + 1 + 1) 0 (ds_bi_valid s - 6)
                HDC Hpo ltac:(rewrite !arr_len_set; reflexivity) ltac:(bytes_tac Hbytes)
                ltac:(intros i Hi; rewrite !arr_get_set_other' by lia; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)) as (A1 & A2 & A3).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. unfold upd4; dsred. repeat split; try lia; reflexivity.
Qed.

Lemma tsb0_facts : forall c0 s, DC c0 s -> ds_pending s = 0 ->
  let h := tr_stored_block s None 0 0 in
  DC c0 h /\ KV h = KV s /\ ds_strm h = ds_strm s /\ 0 <= ds_pending h <= 7 /\ ds_pending_out h = 0 /\ dx_core2 h = dx_core2 s
  /\ ds_bi_valid h = 0.
Proof.
  intros c0 s HDC Hp h. subst h. pose proof HDC as [[D X] V]. pose proof (dwf_sizes s D) as (_ & _ & Sl & _).
  pose proof (df_bi _ D) as [Hbv Hbb]. pose proof (dx_pout0 _ X Hp) as Hpo.
  pose proof (df_bb _ D) as Hbytes.
  rewrite (tr_stored_block_eq s None 0 0 Hbv Hbb). unfold tsb_tail. cbn [negb Z.eqb].
  pose proof (tsb_hP_range s) as HP.
  assert (HA : forall i, ds_pending s + 3 <= i -> arr_get (tsb_hA s 0) i = arr_get (ds_pending_buf s) i).
  { intros i Hi. unfold tsb_hA. destruct (_ <=? 5); [| destruct (_ <=? 13)]; rewrite !arr_get_set_other' by lia; reflexivity. }
  assert (HAb : forall i, 0 <= i < ds_lit_bufsize s * 4 -> 0 <= arr_get (tsb_hA s 0) i < 256).
  { unfold tsb_hA. destruct (_ <=? 5); [| destruct (_ <=? 13)]; bytes_tac Hbytes. }
  destruct (DC_upd4 c0 s (tsb_lenA (tsb_hA s 0) (tsb_hP s) 0) (tsb_hP s + 1 + 1 + 1 + 1 + 0) 0 0 HDC Hpo
              ltac:(unfold tsb_lenA; rewrite !arr_len_set; apply tsb_hA_len)
              ltac:(unfold tsb_lenA; bytes_tac HAb)
              ltac:(intros i Hi; unfold tsb_lenA; rewrite !arr_get_set_other' by lia; apply HA; lia)
              ltac:(lia) ltac:(lia) ltac:(lia)) as (A1 & A2 & A3).
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. unfold upd4; dsred. repeat split; try lia; reflexivity.
Qed.

Lemma clear_hash_eq : forall s,
  clear_hash s = set_head s (arr_fill (arr_set (ds_head s) (ds_hash_size s - 1) NIL) 0 (ds_hash_size s - 1) 0).
Proof. intros s. unfold clear_hash. dsred. reflexivity. Qed.

Lemma DC_clear_hash : forall c0 s, DC c0 s ->
  DC c0 (clear_hash s) /\ KV (clear_hash s) = KV s /\ ds_strm (clear_hash s) = ds_strm s
  /\ (forall h, 0 <= h < ds_hash_size s -> arr_get (ds_head (clear_hash s)) h = 0)
  /\ ds_pending (clear_hash s) = ds_pending s /\ ds_pending_out (clear_hash s) = ds_pending_out s
  /\ ds_lookahead (clear_hash s) = ds_lookahead s /\ ds_bi_valid (clear_hash s) = ds_bi_valid s
  /\ ds_match_available (clear_hash s) = ds_match_available s.
Proof.
  intros c0 s [[D X] V]. pose proof (dwf_sizes s D) as (_ & Sh & _). pose proof (df_hl _ D) as Hhl.
  assert (H0 : forall h, 0 <= h < ds_hash_size s -> arr_get (ds_head (clear_hash s)) h = 0).
  { intros h Hh. rewrite clear_hash_eq. dsred. rewrite arr_get_fill. unfold arr_inb. rewrite arr_len_set, Hhl.
    destruct (Z_lt_le_dec h (ds_hash_size s - 1)).
    - replace ((0 <=? h) && (h <? 0 + Z.max 0 (ds_hash_size s - 1)) && ((0 <=? h) && (h <? ds_hash_size s))) with true
        by (symmetry; rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt; lia). reflexivity.
    - replace ((0 <=? h) && (h <? 0 + Z.max 0 (ds_hash_size s - 1)) && ((0 <=? h) && (h <? ds_hash_size s))) with false
        by (symmetry; apply andb_false_iff; left; apply andb_false_iff; right; apply Z.ltb_ge; lia).
      replace h with (ds_hash_size s - 1) by lia. rewrite arr_get_set_same by (rewrite Hhl; lia). reflexivity. }
  rewrite clear_hash_eq in H0 |- *. unfold set_head in H0. cbn [ds_head] in H0. dsred.
  split; [| repeat split; reflexivity || (intros; apply H0; assumption)].
  split; [split|].
  - destruct D; constructor; dsred; try assumption.
    + rewrite arr_len_fill, arr_len_set. assumption.
    + intros i Hi. rewrite (H0 i Hi). lia.
  - destruct X; constructor; dsred; try assumption.
    intros Hm. apply CHAIN_heads0. dsred. exact H0.
  - apply (SV_strm c0 s); [reflexivity | exact V].
Qed.

Lemma DC_reset0 : forall c0 s, DC c0 s -> ds_lookahead s = 0 -> ds_match_available s = 0 ->
  (forall h, 0 <= h < ds_hash_size s -> arr_get (ds_head s) h = 0) ->
  let s' := set_insert (set_block_start (set_strstart s 0) 0) 0 in
  DC c0 s' /\ KV s' = KV s /\ ds_strm s' = ds_strm s /\ ds_pending s' = ds_pending s /\ ds_pending_out s' = ds_pending_out s
  /\ ds_lookahead s' = 0 /\ ds_bi_valid s' = ds_bi_valid s.
Proof.
  intros c0 s [[D X] V] Hl Hma0 H0 s'. subst s'.
  split; [| dsred; repeat split; try reflexivity; exact Hl].
  split; [split|].
  - destruct D; constructor; dsred; try assumption; try lia.
  - pose proof (dx_nsym _ X) as Xns. pose proof (dx_ma _ X) as Xma. pose proof (dwf_sizes s D) as (Sw & _).
    destruct X as [Xcfg Xinsh Xins Xml Xpl Xma' Xpm Xmatches Xhw Xfast Xnotslow Xslow Xst0 Xwrapneg Xfin Xsn Xnsym Xsyms Xhist Xopt
                   Xstat Xext Xtfc Xtdl Xdepth Xblc Xchain Xpout0 Xbiv];
      constructor; unfold dmode, nsym in *; dsred; try assumption;
      [ first [ solve [ clear - Sw; lia ] | lia ]
      | first [ solve [ clear - Xslow Hl Hma0; lia ] | lia ]
      | first [ solve [ clear - Xst0 Hl; lia ] | lia ]
      | first [ solve [ clear - Xns Xma; lia ] | lia ]
      | intros Hm; apply CHAIN_heads0; dsred; exact H0 ].
  - apply (SV_strm c0 s); [reflexivity | exact V].
Qed.

Lemma bdone_facts : forall c0 s flush, DC c0 s -> ds_pending s = 0 -> ds_match_available s = 0 ->
  let h := bdone_st s flush in
  DC c0 h /\ KV h = KV s /\ ds_strm h = ds_strm s /\ 0 <= ds_pending h <= 7 /\ ds_pending_out h = 0
  /\ (flush = Z_PARTIAL_FLUSH -> ds_pending (tr_align s) <= ds_lit_bufsize s * 4)
  /\ (flush <> Z_PARTIAL_FLUSH -> flush <> Z_BLOCK -> ds_pending (tr_stored_block s None 0 0) <= ds_lit_bufsize s * 4).
Proof.
  intros c0 s flush HDC Hp Hma0 h. subst h. pose proof HDC as [[D X] V]. pose proof (dwf_sizes s D) as (_ & _ & Sl & _).
  pose proof (dx_pout0 _ X Hp) as Hpo.
  destruct (tr_align_facts c0 s HDC Hp) as (A1 & A2 & A3 & A4 & A5 & A6).
  destruct (tsb0_facts c0 s HDC Hp) as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
  assert (R1 : flush = Z_PARTIAL_FLUSH -> ds_pending (tr_align s) <= ds_lit_bufsize s * 4) by (intros; lia).
  assert (R2 : flush <> Z_PARTIAL_FLUSH -> flush <> Z_BLOCK -> ds_pending (tr_stored_block s None 0 0) <= ds_lit_bufsize s * 4) by (intros; lia).
  unfold bdone_st.
  destruct (Z.eqb_spec flush Z_PARTIAL_FLUSH) as [Ef|Ef].
  { split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [lia|]. split; [exact A5|]. split; [exact R1 | exact R2]. }
  destruct (negb (flush =? Z_BLOCK)) eqn:Eb.
  2:{ split; [exact HDC|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact Hpo|]. split; [exact R1 | exact R2]. }
  set (t := tr_stored_block s None 0 0) in *.
  destruct (flush =? Z_FULL_FLUSH).
  2:{ split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|]. split; [exact R1 | exact R2]. }
  destruct (DC_clear_hash c0 t B1) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
  destruct (Z.eqb_spec (ds_lookahead (clear_hash t)) 0) as [El|El].
  - pose proof (KV_fields t (clear_hash t) C2) as (_ & Eh & _).
    pose proof (dx_core2_fields _ _ B6) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ema & _).
    destruct (DC_reset0 c0 (clear_hash t) C1 El ltac:(rewrite C9, Ema; exact Hma0) ltac:(rewrite Eh; exact C4)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
    split; [exact E1|]. split; [rewrite E2, C2; exact B2|]. split; [rewrite E3, C3; exact B3|].
    split; [rewrite E4, C5; exact B4|]. split; [rewrite E5, C6; exact B5|]. split; [exact R1 | exact R2].
  - split; [exact C1|]. split; [rewrite C2; exact B2|]. split; [rewrite C3; exact B3|].
    split; [rewrite C5; exact B4|]. split; [rewrite C6; exact B5|]. split; [exact R1 | exact R2].
Qed.
End RefDeflSafeI3.

Module RefDeflSafeI4.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import CompressModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TrSmallModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateOverlay.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require SendModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.SendModel.RefDeflSafeL1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeZ.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeG.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeS.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflSafeI2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Definition BFPRE (c0 : cstrm) (s : deflate_state) (flush : Z) : Prop :=
  C0OK' c0 /\ DC c0 s /\ ds_pending s = 0 /\ ds_status s <> FINISH_STATE /\ 0 <= flush <= 5.

Definition BFPOST (c0 : cstrm) (s : deflate_state) (flush : Z) (r : deflate_state * block_state) : Prop :=
  let s' := fst r in let b := snd r in
  DC c0 s' /\ KV s' = KV s /\ OUTLE s s'
  /\ (b = block_done -> ds_pending s' = 0 /\ flush <> Z_FINISH /\ ds_match_available s' = 0)
  /\ (b = finish_started \/ b = finish_done -> ds_lookahead s' = 0)
  /\ (b = finish_done -> ds_pending s' = 0).

Definition BF_SPEC (m : Z) (SAFE : deflate_state -> Z -> Prop) (f : deflate_state -> Z -> deflate_state * block_state) : Prop :=
  forall c0 s flush, BFPRE c0 s flush -> dmode s = m -> SAFE s flush /\ BFPOST c0 s flush (f s flush).

Section Integrate.
  Variable SAFEs : deflate_state -> Z -> Prop.
Variable SAFEf : deflate_state -> Z -> Prop.
Variable SAFEw : deflate_state -> Z -> Prop.
  Variable FB : deflate_state -> option Z -> Z -> Z -> Prop.

  Hypothesis Hst : BF_SPEC 0 SAFEs deflate_stored.
  Hypothesis Hhf : BF_SPEC 1 (huff_ok FB) deflate_huff.
  Hypothesis Hrl : BF_SPEC 2 (rle_ok FB) deflate_rle.
  Hypothesis Hfa : BF_SPEC 3 SAFEf deflate_fast.
  Hypothesis Hsl : BF_SPEC 4 SAFEw deflate_slow.

  Local Notation DOK := (@DOK).
  Local Notation dpost_ok := (dpost_ok dwf).

  Section Call.
    Variable c0 : cstrm.
Variable s0 : deflate_state.
    Hypothesis HC0 : C0OK' c0.
    Hypothesis Hs0 : ds_strm s0 = c0.
    Hypothesis D0 : dwf s0.
    Let HC0w : C0OK c0 := c0'_ok _ HC0.

    Definition ST (s : deflate_state) : Prop := DC c0 s /\ KV s = KV s0.

    Lemma ST_DOK : forall s, ST s -> DOK s.
    Proof. intros s [H _]. exact (DC_DOK c0 s HC0w H). Qed.

    Lemma ST_dpost : forall s rc, ST s -> - 2 ^ 31 <= rc < 2 ^ 31 -> dpost_ok s0 s rc.
    Proof. intros s rc [H K] Hrc. exact (DC_dpost c0 s0 s rc HC0 Hs0 D0 H K Hrc). Qed.

    Lemma ST_err_return : forall s e, ST s -> ST (fst (err_return s e)).
    Proof. intros s e [H K]. split; [apply DC_err_return; exact H | rewrite KV_err_return; exact K]. Qed.

    Lemma ST_set_last_flush : forall s v, ST s -> - 2 <= v <= 5 -> ST (set_last_flush s v).
    Proof. intros s v [H K] Hv. split; [apply DC_set_last_flush; [exact Hv | exact H] | rewrite KV_set_last_flush; exact K]. Qed.

    Lemma ST_flush_pending : forall s, ST s ->
      ST (flush_pending s) /\ fp_ok s /\ (ds_pending (flush_pending s) = 0 \/ cs_avail_out (ds_strm (flush_pending s)) = 0)
      /\ 0 <= ds_pending (flush_pending s) <= ds_pending s
      /\ ds_status (flush_pending s) = ds_status s /\ ds_wrap (flush_pending s) = ds_wrap s
      /\ ds_lookahead (flush_pending s) = ds_lookahead s /\ cs_avail_in (ds_strm (flush_pending s)) = cs_avail_in (ds_strm s).
    Proof.
      intros s [H K].
      destruct (DC_flush_pending c0 s HC0w H) as (H' & K' & _ & C2 & Hfp & Hp & Hor & _ & _ & _ & Hai & _).
      pose proof (dx_core2_fields _ _ C2) as F.
      split; [split; [exact H' | rewrite K'; exact K]|]. split; [exact Hfp|]. split; [exact Hor|]. split; [exact Hp|].
      destruct F as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F17 & _ & _ & _ & F21 & F22 & _).
      repeat split; assumption.
    Qed.

    Lemma Z_OK_range : - 2 ^ 31 <= Z_OK < 2 ^ 31. Proof. unfold Z_OK. lia. Qed.
    Lemma Z_BUF_ERROR_range : - 2 ^ 31 <= Z_BUF_ERROR < 2 ^ 31. Proof. unfold Z_BUF_ERROR. lia. Qed.
    Lemma Z_STREAM_ERROR_range : - 2 ^ 31 <= Z_STREAM_ERROR < 2 ^ 31. Proof. unfold Z_STREAM_ERROR. lia. Qed.
    Lemma Z_STREAM_END_range : - 2 ^ 31 <= Z_STREAM_END < 2 ^ 31. Proof. unfold Z_STREAM_END. lia. Qed.

    Lemma hdr_zlib : forall s, ST s -> ds_pending s = 0 -> ds_status s = INIT_STATE ->
      hdr_ok dwf s0 s (zhdr_st s) 6
      /\ ST (flush_pending (zhdr_st s))
      /\ ds_status (flush_pending (zhdr_st s)) = BUSY_STATE
      /\ (ds_pending (flush_pending (zhdr_st s)) = 0 \/ cs_avail_out (ds_strm (flush_pending (zhdr_st s))) = 0)
      /\ cs_avail_in (ds_strm (flush_pending (zhdr_st s))) = cs_avail_in (ds_strm s)
      /\ ds_lookahead (flush_pending (zhdr_st s)) = ds_lookahead s /\ ds_wrap (flush_pending (zhdr_st s)) = ds_wrap s.
    Proof.
      intros s HS Hp Hst0. pose proof HS as [H K]. pose proof H as [[D X] V]. pose proof (dwf_sizes s D) as (_ & _ & Sl & _).
      destruct (zhdr_facts c0 s H Hp Hst0) as ((H1 & Po1 & P1) & K1 & O1 & St1 & Ai1 & Lk1 & Wr1).
      assert (HS1 : ST (zhdr_st s)) by (split; [exact H1 | rewrite K1; exact K]).
      destruct (ST_flush_pending _ HS1) as (HS2 & Hfp & Hor & Hp2 & St2 & Wr2 & Lk2 & Ai2).
      pose proof HS2 as [[[D2 X2] V2] K2]. pose proof (df_pend _ D2).
      split.
      { unfold hdr_ok. split; [exact (ST_DOK s HS)|]. split; [lia|]. split; [exact (ST_DOK _ HS1)|]. split; [exact Hfp|].
        cbv zeta. split; [exact (ST_DOK _ HS2)|]. split; [pose proof (dwf_sizes _ D2); lia|].
        intros _. apply ST_dpost; [apply ST_set_last_flush; [exact HS2 | lia] | apply Z_OK_range]. }
      split; [exact HS2|]. split; [rewrite St2; exact St1|]. split; [exact Hor|].
      rewrite Ai2, Lk2, Wr2. split; [exact Ai1 | split; [exact Lk1 | exact Wr1]].
    Qed.

    Lemma hdr_gzip : forall s, ST s -> ds_pending s = 0 -> ds_status s = GZIP_STATE ->
      hdr_ok dwf s0 s (gzhdr_st s) 10
      /\ ST (flush_pending (gzhdr_st s))
      /\ ds_status (flush_pending (gzhdr_st s)) = BUSY_STATE
      /\ (ds_pending (flush_pending (gzhdr_st s)) = 0 \/ cs_avail_out (ds_strm (flush_pending (gzhdr_st s))) = 0)
      /\ cs_avail_in (ds_strm (flush_pending (gzhdr_st s))) = cs_avail_in (ds_strm s)
      /\ ds_lookahead (flush_pending (gzhdr_st s)) = ds_lookahead s /\ ds_wrap (flush_pending (gzhdr_st s)) = ds_wrap s.
    Proof.
      intros s HS Hp Hst0. pose proof HS as [H K]. pose proof H as [[D X] V]. pose proof (dwf_sizes s D) as (_ & _ & Sl & _).
      destruct (gzhdr_facts c0 s H Hp Hst0) as ((H1 & Po1 & P1) & K1 & O1 & St1 & Ai1 & Lk1 & Wr1).
      assert (HS1 : ST (gzhdr_st s)) by (split; [exact H1 | rewrite K1; exact K]).
      destruct (ST_flush_pending _ HS1) as (HS2 & Hfp & Hor & Hp2 & St2 & Wr2 & Lk2 & Ai2).
      pose proof HS2 as [[[D2 X2] V2] K2]. pose proof (df_pend _ D2).
      split.
      { unfold hdr_ok. split; [exact (ST_DOK s HS)|]. split; [lia|]. split; [exact (ST_DOK _ HS1)|]. split; [exact Hfp|].
        cbv zeta. split; [exact (ST_DOK _ HS2)|]. split; [pose proof (dwf_sizes _ D2); lia|].
        intros _. apply ST_dpost; [apply ST_set_last_flush; [exact HS2 | lia] | apply Z_OK_range]. }
      split; [exact HS2|]. split; [rewrite St2; exact St1|]. split; [exact Hor|].
      rewrite Ai2, Lk2, Wr2. split; [exact Ai1 | split; [exact Lk1 | exact Wr1]].
    Qed.


    Lemma dmode_cases : forall s (P0 P1 P2 P3 P4 : Prop),
      (dmode s = 0 -> P0) -> (dmode s = 1 -> P1) -> (dmode s = 2 -> P2) -> (dmode s = 3 -> P3) -> (dmode s = 4 -> P4) ->
      (if ds_level s =? 0 then P0
       else if ds_strategy s =? Z_HUFFMAN_ONLY then P1
       else if ds_strategy s =? Z_RLE then P2
       else if ds_level s <=? 3 then P3 else P4).
    Proof.
      intros s P0 P1 P2 P3 P4 H0 H1 H2 H3 H4. unfold dmode in *.
      destruct (ds_level s =? 0); [exact (H0 eq_refl)|]. destruct (ds_strategy s =? Z_HUFFMAN_ONLY); [exact (H1 eq_refl)|].
      destruct (ds_strategy s =? Z_RLE); [exact (H2 eq_refl)|]. destruct (ds_level s <=? 3); [exact (H3 eq_refl) | exact (H4 eq_refl)].
    Qed.

    Lemma bf_call : forall s flush, ST s -> ds_pending s = 0 -> ds_status s <> FINISH_STATE -> 0 <= flush <= 5 ->
      (if ds_level s =? 0 then SAFEs s flush
       else if ds_strategy s =? Z_HUFFMAN_ONLY then huff_ok FB s flush
       else if ds_strategy s =? Z_RLE then rle_ok FB s flush
       else if ds_level s <=? 3 then SAFEf s flush else SAFEw s flush)
      /\ BFPOST c0 s flush (run_compress_func s flush).
    Proof.
      intros s flush [H K] Hp Hst0 Hfl.
      assert (PRE : BFPRE c0 s flush) by (split; [exact HC0|]; split; [exact H|]; split; [exact Hp|]; split; [exact Hst0 | exact Hfl]).
      rewrite run_compress_func_dmode.
      pose proof (dmode_range s) as Hm.
      destruct (Z.eq_dec (dmode s) 0) as [E0|E0]; [destruct (Hst c0 s flush PRE E0) as [A B]; rewrite E0; split; [| exact B]; apply dmode_cases; intros; first [exact A | congruence]|].
      destruct (Z.eq_dec (dmode s) 1) as [E1|E1]; [destruct (Hhf c0 s flush PRE E1) as [A B]; rewrite E1; split; [| exact B]; apply dmode_cases; intros; first [exact A | congruence]|].
      destruct (Z.eq_dec (dmode s) 2) as [E2|E2]; [destruct (Hrl c0 s flush PRE E2) as [A B]; rewrite E2; split; [| exact B]; apply dmode_cases; intros; first [exact A | congruence]|].
      destruct (Z.eq_dec (dmode s) 3) as [E3|E3]; [destruct (Hfa c0 s flush PRE E3) as [A B]; rewrite E3; split; [| exact B]; apply dmode_cases; intros; first [exact A | congruence]|].
      assert (E4 : dmode s = 4) by lia.
      destruct (Hsl c0 s flush PRE E4) as [A B]. rewrite E4. split; [| exact B]. apply dmode_cases; intros; first [exact A | congruence].
    Qed.

    Lemma blocks_stage : forall s flush, ST s -> ds_pending s = 0 -> 0 <= flush <= 5 ->
      (ds_status s = FINISH_STATE -> cs_avail_in (ds_strm s) = 0) ->
      blocks_ok SAFEs SAFEf SAFEw FB dwf s0 s flush
      /\ let r := deflate_blocks s flush in
         ST (fst r)
         /\ (snd r = None -> ds_pending (fst r) = 0 /\ (flush = Z_FINISH -> ds_status (fst r) = FINISH_STATE)).
    Proof.
      intros s flush HS Hp Hfl Hfin. pose proof HS as [H K]. pose proof H as [[D X] V].
      unfold blocks_ok, deflate_blocks.
      match goal with |- context [if ?c then _ else (s, None)] => destruct c eqn:Hcond end.
      2:{
          split; [split; [exact (ST_DOK s HS) | intros HH; discriminate HH]|].
          cbn [fst snd]. split; [exact HS|]. intros _. split; [exact Hp|].
          intros Hf. apply orb_false_iff in Hcond as [Hcond C3]. apply orb_false_iff in Hcond as [C1 C2].
          apply andb_false_iff in C3. destruct C3 as [C3|C3].
          - exfalso. rewrite Hf in C3. cbn in C3. discriminate C3.
          - destruct (Z.eqb_spec (ds_status s) FINISH_STATE); [assumption | discriminate C3]. }
      assert (Hst0 : ds_status s <> FINISH_STATE).
      { intros Ef. rewrite (Hfin Ef), (dx_fin _ X Ef), Ef in Hcond. cbn in Hcond.
        rewrite andb_false_r in Hcond. discriminate Hcond. }
      destruct (bf_call s flush HS Hp Hst0 Hfl) as [HSAFE HPOST].
      destruct (run_compress_func s flush) as [s1 bst] eqn:Erun. cbv beta iota zeta.
      unfold BFPOST in HPOST. cbn [fst snd] in HPOST. destruct HPOST as (H1 & K1 & O1 & Pbd & Pfin & Pfd).
      assert (HS1 : ST s1) by (split; [exact H1 | rewrite K1; exact K]).
      pose proof H1 as [[D1 X1] V1].
      set (s2 := if block_state_eqb bst finish_started || block_state_eqb bst finish_done then set_status s1 FINISH_STATE else s1) in *.
      assert (HS2 : ST s2 /\ ds_pending s2 = ds_pending s1 /\ ds_strm s2 = ds_strm s1
                    /\ (block_state_eqb bst finish_started || block_state_eqb bst finish_done = true -> ds_status s2 = FINISH_STATE)
                    /\ (block_state_eqb bst finish_started || block_state_eqb bst finish_done = false -> s2 = s1)).
      { subst s2. destruct (block_state_eqb bst finish_started || block_state_eqb bst finish_done) eqn:Eb.
        - assert (Hl : ds_lookahead s1 = 0).
          { apply Pfin. destruct bst; cbn in Eb; try discriminate Eb; [left | right]; reflexivity. }
          destruct (DC_set_status c0 s1 FINISH_STATE H1 ltac:(unfold FINISH_STATE; lia) ltac:(intros; reflexivity) ltac:(intros _; exact Hl)) as (H2 & K2 & S2).
          split; [split; [exact H2 | rewrite K2, K1; exact K]|].
          split; [reflexivity|]. split; [exact S2|]. split; [intros; reflexivity | intros HH; discriminate HH].
        - split; [exact HS1|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros HH; discriminate HH | intros; reflexivity]. }
      clearbody s2. destruct HS2 as (HS2 & P2 & S2 & Fin2 & NFin2).
      split.
      -
        split; [exact (ST_DOK s HS)|]. intros _.
        split.
        { unfold blocks_call_ok. rewrite Erun. cbn [fst]. split; [| split; [exact (ST_DOK s1 HS1) | exact HSAFE]].
          eapply (lz_keeps_intro c0); [exact D | exact D1 | exact V | exact V1 | exact K1 | exact O1]. }
        split; [exact (ST_DOK s2 HS2)|].
        split.
        { intros _. destruct (cs_avail_out (ds_strm s2) =? 0).
          - apply ST_dpost; [apply ST_set_last_flush; [exact HS2 | lia] | apply Z_OK_range].
          - apply ST_dpost; [exact HS2 | apply Z_OK_range]. }
        intros Ebd. subst bst. destruct (Pbd eq_refl) as (Hp1 & Hnf & Hma1). rewrite (NFin2 eq_refl) in *.
        pose proof HS1 as [H1' _].
        destruct (bdone_facts c0 s1 flush H1 Hp1 Hma1) as (B1 & B2 & B3 & B4 & B5 & R1 & R2).
        assert (HSb : ST (bdone_st s1 flush)) by (split; [exact B1 | rewrite B2, K1; exact K]).
        destruct (ST_flush_pending _ HSb) as (HSf & Hfp & _).
        split.
        { unfold bdone_ok. cbv zeta. pose proof (df_bi _ D1). pose proof (df_pend _ D1). pose proof (dwf_sizes _ D1).
          split; [exact (ST_DOK s1 HS1)|]. split; [unfold BINV; lia|].
          split; [exact R1|]. split; [exact R2|].
          split; [exact (ST_DOK _ HSb)|]. split; [exact Hfp | exact (ST_DOK _ HSf)]. }
        intros _. apply ST_dpost; [apply ST_set_last_flush; [exact HSf | lia] | apply Z_OK_range].
      -
        destruct (block_state_eqb bst need_more || block_state_eqb bst finish_started) eqn:Enm.
        { cbn [fst snd]. split; [| intros HH; discriminate HH].
          destruct (cs_avail_out (ds_strm s2) =? 0); [apply ST_set_last_flush; [exact HS2 | lia] | exact HS2]. }
        destruct (block_state_eqb bst block_done) eqn:Ebd.
        + assert (Eb : bst = block_done) by (destruct bst; cbn in Ebd; try discriminate Ebd; reflexivity). subst bst.
          destruct (Pbd eq_refl) as (Hp1 & Hnf & Hma1). cbn in NFin2. rewrite (NFin2 eq_refl).
          destruct (bdone_facts c0 s1 flush H1 Hp1 Hma1) as (B1 & B2 & B3 & B4 & B5 & R1 & R2).
          assert (HSb : ST (bdone_st s1 flush)) by (split; [exact B1 | rewrite B2, K1; exact K]).
          destruct (ST_flush_pending _ HSb) as (HSf & _ & Hor & _).
          match goal with |- context [flush_pending ?b] => replace b with (bdone_st s1 flush) by (unfold bdone_st; reflexivity) end.
          destruct (Z.eqb_spec (cs_avail_out (ds_strm (flush_pending (bdone_st s1 flush)))) 0) as [Ea|Ea]; cbn [fst snd].
          * split; [apply ST_set_last_flush; [exact HSf | lia] | intros HH; discriminate HH].
          * split; [exact HSf|]. intros _. split; [lia|]. intros Hf. exfalso. exact (Hnf Hf).
        +
          assert (Eb : bst = finish_done) by (destruct bst; cbn in Enm, Ebd; try discriminate Enm; try discriminate Ebd; reflexivity). subst bst.
          cbn [fst snd]. split; [exact HS2|]. intros _. split; [rewrite P2; exact (Pfd eq_refl)|].
          intros _. apply Fin2. reflexivity.
    Qed.


    Lemma finish_stage : forall s flush, ST s -> ds_pending s = 0 -> 0 <= flush <= 5 ->
      (flush = Z_FINISH -> ds_status s = FINISH_STATE) ->
      finish_ok dwf s0 s flush
      /\ (flush = Z_FINISH -> 0 < ds_wrap s -> ST (fst (deflate_trailer s))).
    Proof.
      intros s flush HS Hp Hfl Hfin. pose proof HS as [H K]. pose proof H as [[D X] V]. pose proof (dwf_sizes s D) as (_ & _ & Sl & _).
      destruct (trailer_facts c0 s H Hp) as ((H1 & Po1 & P1) & K1 & O1 & St1 & Wr1 & Lk1).
      assert (HS1 : ST (trailer_st s)) by (split; [exact H1 | rewrite K1; exact K]).
      destruct (ST_flush_pending _ HS1) as (HS2 & Hfp & Hor & Hp2 & St2 & Wr2 & Lk2 & Ai2).
      pose proof HS2 as [[[D2 X2] V2] K2].
      assert (HS3 : flush = Z_FINISH -> ST (set_wrap (flush_pending (trailer_st s)) (- ds_wrap (flush_pending (trailer_st s))))).
      { intros Hf. pose proof HS2 as [H2 _].
        destruct (DC_set_wrap_neg c0 _ (- ds_wrap (flush_pending (trailer_st s))) H2
                    ltac:(pose proof (df_wrap _ D2); lia) ltac:(rewrite St2, St1; exact (Hfin Hf))) as (H3 & K3 & _).
        split; [exact H3 | rewrite K3; exact K2]. }
      split.
      - unfold finish_ok. split; [exact (ST_DOK s HS)|].
        split; [intros _; apply ST_dpost; [exact HS | apply Z_OK_range]|].
        split; [intros _ _; apply ST_dpost; [exact HS | apply Z_STREAM_END_range]|].
        intros Hf Hw. unfold trailer_ok. cbv zeta.
        split; [exact (ST_DOK s HS)|]. split; [exact Hw|].
        split; [destruct (ds_wrap s =? 2); lia|].
        split; [exact (ST_DOK _ HS1)|]. split; [exact Hfp|].
        split; [exact (ST_DOK _ HS2)|]. split; [pose proof (df_pend _ D2); pose proof (dwf_sizes _ D2); lia|].
        split; [rewrite Wr2, Wr1; exact Hw|].
        apply ST_dpost; [exact (HS3 Hf)|]. destruct (negb _); [apply Z_OK_range | apply Z_STREAM_END_range].
      - intros Hf Hw. rewrite deflate_trailer_eq. cbv zeta.
        replace (0 <? ds_wrap (flush_pending (trailer_st s))) with true by (symmetry; apply Z.ltb_lt; rewrite Wr2, Wr1; exact Hw).
        cbn [fst]. exact (HS3 Hf).
    Qed.

    Lemma body_stage : forall s flush, ST s -> ds_pending s = 0 -> 0 <= flush <= 5 ->
      body_ok SAFEs SAFEf SAFEw FB dwf s0 s flush.
    Proof.
      intros s flush HS Hp Hfl. pose proof HS as [H K]. pose proof H as [[D X] V].
      unfold body_ok. split; [exact (ST_DOK s HS)|].
      split; [intros _; apply ST_dpost; [apply ST_err_return; exact HS | apply Z_BUF_ERROR_range]|].
      intros Hnf.
      set (s4 := if (ds_status s =? INIT_STATE) && (ds_wrap s =? 0) then set_status s BUSY_STATE else s).
      assert (HS4 : ST s4 /\ ds_pending s4 = 0 /\ cs_avail_in (ds_strm s4) = cs_avail_in (ds_strm s) /\ ds_lookahead s4 = ds_lookahead s
                    /\ (ds_status s4 = FINISH_STATE -> ds_status s = FINISH_STATE) /\ ds_wrap s4 = ds_wrap s).
      { subst s4. destruct ((ds_status s =? INIT_STATE) && (ds_wrap s =? 0)) eqn:E.
        - apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
          destruct (DC_set_status c0 s BUSY_STATE H ltac:(unfold BUSY_STATE; lia) ltac:(intros; exfalso; lia) ltac:(unfold BUSY_STATE, FINISH_STATE; intros; lia)) as (H4 & K4 & S4).
          split; [split; [exact H4 | rewrite K4; exact K]|]. unfold set_status; dsred. repeat split; try reflexivity; try assumption.
          unfold BUSY_STATE, FINISH_STATE. intros; lia.
        - split; [exact HS|]. repeat split; try reflexivity; try assumption. intros E'; exact E'. }
      clearbody s4. destruct HS4 as (HS4 & Hp4 & Ai4 & Lk4 & Fin4 & Wr4).
      split; [exact (ST_DOK s4 HS4)|].
      split; [intros Hst4; exact (proj1 (hdr_zlib s4 HS4 Hp4 Hst4))|].
      set (s5 := if ds_status s4 =? INIT_STATE then flush_pending (zhdr_st s4) else s4).
      assert (HS5 : ST s5 /\ cs_avail_in (ds_strm s5) = cs_avail_in (ds_strm s) /\ ds_lookahead s5 = ds_lookahead s
                    /\ (ds_status s5 = FINISH_STATE -> ds_status s = FINISH_STATE) /\ (ds_status s4 <> INIT_STATE -> s5 = s4)).
      { subst s5. destruct (Z.eqb_spec (ds_status s4) INIT_STATE) as [E|E].
        - destruct (hdr_zlib s4 HS4 Hp4 E) as (_ & HS5 & St5 & _ & Ai5 & Lk5 & Wr5).
          split; [exact HS5|]. rewrite Ai5, Lk5, St5. split; [exact Ai4|]. split; [exact Lk4|].
          split; [unfold BUSY_STATE, FINISH_STATE; intros; lia | intros NE; exfalso; exact (NE E)].
        - split; [exact HS4|]. split; [exact Ai4|]. split; [exact Lk4|]. split; [exact Fin4 | intros; reflexivity]. }
      clearbody s5. destruct HS5 as (HS5 & Ai5 & Lk5 & Fin5 & Eq5).
      cbv zeta. intros Hp5'.
      assert (Hp5 : ds_pending s5 = 0).
      { destruct (Z.eq_dec (ds_status s4) INIT_STATE) as [E|E]; [exact (Hp5' E) | rewrite (Eq5 E); exact Hp4]. }
      split; [intros Hst5; exact (proj1 (hdr_gzip s5 HS5 Hp5 Hst5))|].
      set (s6 := if ds_status s5 =? GZIP_STATE then flush_pending (gzhdr_st s5) else s5).
      assert (HS6 : ST s6 /\ cs_avail_in (ds_strm s6) = cs_avail_in (ds_strm s) /\ ds_lookahead s6 = ds_lookahead s
                    /\ (ds_status s6 = FINISH_STATE -> ds_status s = FINISH_STATE) /\ (ds_status s5 <> GZIP_STATE -> s6 = s5)).
      { subst s6. destruct (Z.eqb_spec (ds_status s5) GZIP_STATE) as [E|E].
        - destruct (hdr_gzip s5 HS5 Hp5 E) as (_ & HS6 & St6 & _ & Ai6 & Lk6 & Wr6).
          split; [exact HS6|]. rewrite Ai6, Lk6, St6. split; [exact Ai5|]. split; [exact Lk5|].
          split; [unfold BUSY_STATE, FINISH_STATE; intros; lia | intros NE; exfalso; exact (NE E)].
        - split; [exact HS5|]. split; [exact Ai5|]. split; [exact Lk5|]. split; [exact Fin5 | intros; reflexivity]. }
      clearbody s6. destruct HS6 as (HS6 & Ai6 & Lk6 & Fin6 & Eq6).
      intros Hp6'.
      assert (Hp6 : ds_pending s6 = 0).
      { destruct (Z.eq_dec (ds_status s5) GZIP_STATE) as [E|E]; [exact (Hp6' E) | rewrite (Eq6 E); exact Hp5]. }
      assert (Hfin6 : ds_status s6 = FINISH_STATE -> cs_avail_in (ds_strm s6) = 0).
      { intros E. rewrite Ai6. pose proof (Fin6 E) as E0.
        destruct (Z.eq_dec (cs_avail_in (ds_strm s)) 0) as [A|A]; [exact A|]. exfalso. apply Hnf. split; [exact E0 | exact A]. }
      destruct (blocks_stage s6 flush HS6 Hp6 Hfl Hfin6) as (HB & HSr & Hr).
      split; [exact HB|].
      intros Hnone. destruct (Hr Hnone) as [Hpr Hfr].
      exact (proj1 (finish_stage _ flush HSr Hpr Hfl Hfr)).
    Qed.


    Lemma core_result : forall flush, ST s0 -> 0 <= flush < 16 -> ST (fst (deflate_core s0 flush)).
    Proof.
      intros flush HS0 Hfl. pose proof HS0 as [H K]. pose proof H as [[D X] V].
      unfold deflate_core.
      destruct (deflateStateCheck s0 || (Z_BLOCK <? flush) || (flush <? 0)) eqn:Echk; [cbn [fst]; exact HS0|].
      apply orb_false_iff in Echk as [Echk C3]. apply orb_false_iff in Echk as [C1 C2].
      apply Z.ltb_ge in C2. apply Z.ltb_ge in C3. unfold Z_BLOCK in C2.
      destruct ((ds_status s0 =? FINISH_STATE) && negb (flush =? Z_FINISH)); [apply ST_err_return; exact HS0|].
      destruct (cs_avail_out (ds_strm s0) =? 0); [apply ST_err_return; exact HS0|].
      cbv zeta.
      pose proof (ST_set_last_flush s0 flush HS0 ltac:(lia)) as HS1.
      set (s1 := set_last_flush s0 flush) in *.
      match goal with |- ST (fst (let '(s, r) := ?head in _)) => destruct head as [s2 r2] eqn:Ehead end.
      assert (H2 : ST s2 /\ (r2 = None -> ds_pending s2 = 0)).
      { destruct (negb (ds_pending s1 =? 0)) eqn:Ep.
        - destruct (ST_flush_pending s1 HS1) as (HSf & _ & Hor & _).
          destruct (Z.eqb_spec (cs_avail_out (ds_strm (flush_pending s1))) 0) as [Ea|Ea]; inversion Ehead; subst.
          + split; [apply ST_set_last_flush; [exact HSf | lia] | intros HH; discriminate HH].
          + split; [exact HSf | intros _; lia].
        - destruct ((cs_avail_in (ds_strm s1) =? 0) && (RANK flush <=? RANK (ds_last_flush s0)) && negb (flush =? Z_FINISH)).
          + unfold err_return in Ehead. inversion Ehead; subst. split; [| intros HH; discriminate HH].
            exact (ST_err_return s1 Z_BUF_ERROR HS1).
          + inversion Ehead; subst. split; [exact HS1|]. intros _. destruct (Z.eqb_spec (ds_pending s1) 0); [assumption | discriminate Ep]. }
      clear Ehead. destruct H2 as [HS2 Hp2].
      destruct r2 as [rc|]; [cbn [fst]; exact HS2|]. specialize (Hp2 eq_refl).
      destruct ((ds_status s2 =? FINISH_STATE) && negb (cs_avail_in (ds_strm s2) =? 0)) eqn:Efa; [apply ST_err_return; exact HS2|].
      set (s4 := if (ds_status s2 =? INIT_STATE) && (ds_wrap s2 =? 0) then set_status s2 BUSY_STATE else s2).
      assert (HS4 : ST s4 /\ ds_pending s4 = 0 /\ cs_avail_in (ds_strm s4) = cs_avail_in (ds_strm s2)
                    /\ (ds_status s4 = FINISH_STATE -> ds_status s2 = FINISH_STATE)).
      { subst s4. destruct ((ds_status s2 =? INIT_STATE) && (ds_wrap s2 =? 0)) eqn:E.
        - apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. pose proof HS2 as [H2' _].
          destruct (DC_set_status c0 s2 BUSY_STATE H2' ltac:(unfold BUSY_STATE; lia) ltac:(intros; exfalso; lia) ltac:(unfold BUSY_STATE, FINISH_STATE; intros; lia)) as (H4 & K4 & S4).
          split; [split; [exact H4 | rewrite K4; exact (proj2 HS2)]|]. unfold set_status; dsred. split; [exact Hp2|]. split; [reflexivity|].
          unfold BUSY_STATE, FINISH_STATE. intros; lia.
        - split; [exact HS2|]. split; [exact Hp2|]. split; [reflexivity | intros E'; exact E']. }
      clearbody s4. destruct HS4 as (HS4 & Hp4 & Ai4 & Fin4).
      rewrite deflate_zlib_header_eq.
      match goal with |- ST (fst (let '(s, r) := ?head in _)) => destruct head as [s5 r5] eqn:Ehead end.
      assert (H5 : ST s5 /\ (r5 = None -> ds_pending s5 = 0 /\ cs_avail_in (ds_strm s5) = cs_avail_in (ds_strm s2)
                                          /\ (ds_status s5 = FINISH_STATE -> ds_status s2 = FINISH_STATE))).
      { destruct (Z.eqb_spec (ds_status s4) INIT_STATE) as [E|E].
        - destruct (hdr_zlib s4 HS4 Hp4 E) as (_ & HSz & Stz & Horz & Aiz & _).
          cbv zeta in Ehead. destruct (negb (ds_pending (flush_pending (zhdr_st s4)) =? 0)) eqn:Ep; inversion Ehead; subst.
          + split; [apply ST_set_last_flush; [exact HSz | lia] | intros HH; discriminate HH].
          + split; [exact HSz|]. intros _. rewrite Aiz, Stz. split; [destruct (Z.eqb_spec (ds_pending (flush_pending (zhdr_st s4))) 0); [assumption | discriminate Ep]|].
            split; [exact Ai4 | unfold BUSY_STATE, FINISH_STATE; intros; lia].
        - inversion Ehead; subst. split; [exact HS4|]. intros _. split; [exact Hp4|]. split; [exact Ai4 | exact Fin4]. }
      clear Ehead. destruct H5 as [HS5 Hr5].
      destruct r5 as [rc|]; [cbn [fst]; exact HS5|]. destruct (Hr5 eq_refl) as (Hp5 & Ai5 & Fin5).
      rewrite deflate_gzip_header_eq.
      match goal with |- ST (fst (let '(s, r) := ?head in _)) => destruct head as [s6 r6] eqn:Ehead end.
      assert (H6 : ST s6 /\ (r6 = None -> ds_pending s6 = 0 /\ cs_avail_in (ds_strm s6) = cs_avail_in (ds_strm s2)
                                          /\ (ds_status s6 = FINISH_STATE -> ds_status s2 = FINISH_STATE))).
      { destruct (Z.eqb_spec (ds_status s5) GZIP_STATE) as [E|E].
        - destruct (hdr_gzip s5 HS5 Hp5 E) as (_ & HSz & Stz & Horz & Aiz & _).
          cbv zeta in Ehead. destruct (negb (ds_pending (flush_pending (gzhdr_st s5)) =? 0)) eqn:Ep; inversion Ehead; subst.
          + split; [apply ST_set_last_flush; [exact HSz | lia] | intros HH; discriminate HH].
          + split; [exact HSz|]. intros _. rewrite Aiz, Stz. split; [destruct (Z.eqb_spec (ds_pending (flush_pending (gzhdr_st s5))) 0); [assumption | discriminate Ep]|].
            split; [exact Ai5 | unfold BUSY_STATE, FINISH_STATE; intros; lia].
        - inversion Ehead; subst. split; [exact HS5|]. intros _. split; [exact Hp5|]. split; [exact Ai5 | exact Fin5]. }
      clear Ehead. destruct H6 as [HS6 Hr6].
      destruct r6 as [rc|]; [cbn [fst]; exact HS6|]. destruct (Hr6 eq_refl) as (Hp6 & Ai6 & Fin6).
      assert (Hfin6 : ds_status s6 = FINISH_STATE -> cs_avail_in (ds_strm s6) = 0).
      { intros E. rewrite Ai6. pose proof (Fin6 E) as E2. rewrite E2 in Efa. cbn in Efa.
        destruct (Z.eqb_spec (cs_avail_in (ds_strm s2)) 0); [assumption | discriminate Efa]. }
      destruct (blocks_stage s6 flush HS6 Hp6 ltac:(lia) Hfin6) as (_ & HSr & Hr).
      destruct (deflate_blocks s6 flush) as [s7 r7]. cbn [fst snd] in HSr, Hr.
      destruct r7 as [rc|]; [cbn [fst]; exact HSr|]. destruct (Hr eq_refl) as [Hp7 Hfin7].
      destruct (negb (flush =? Z_FINISH)) eqn:Ef; [cbn [fst]; exact HSr|].
      assert (Hf : flush = Z_FINISH) by (destruct (Z.eqb_spec flush Z_FINISH); [assumption | discriminate Ef]).
      destruct (Z.leb_spec (ds_wrap s7) 0); [cbn [fst]; exact HSr|].
      exact (proj2 (finish_stage s7 flush HSr Hp7 ltac:(lia) Hfin7) Hf ltac:(lia)).
    Qed.

  End Call.


  Theorem deflate_safe_DD : forall ds zc flush, DD ds -> dcall_wf zc -> 0 <= flush < 16 ->
    deflate_safe SAFEs SAFEf SAFEw FB dwf ds zc flush.
  Proof.
    intros ds zc flush HDD Hzc Hfl.
    set (c0 := cstrm_of_call zc). set (s0 := set_strm ds c0).
    pose proof (C0OK'_of_call zc Hzc) as HC0. fold c0 in HC0. pose proof (c0'_ok _ HC0) as HC0w.
    assert (H0 : DC c0 s0) by (split; [apply DD_set_strm; exact HDD | subst s0 c0; apply SV_entry; exact Hzc]).
    pose proof H0 as [[D0 X0] V0].
    assert (HS0 : ST c0 s0 s0) by (split; [exact H0 | reflexivity]).
    assert (Es0 : ds_strm s0 = c0) by reflexivity.
    unfold deflate_safe. cbv zeta. fold c0 s0.
    split; [exact (ST_DOK c0 s0 HC0 s0 HS0)|].
    split; [exact (df_status _ D0)|].
    split; [exact (df_lf _ D0)|].
    split; [apply (ST_dpost c0 s0 HC0 Es0 D0); [exact HS0 | unfold Z_STREAM_ERROR; lia]|].
    split; [apply (ST_dpost c0 s0 HC0 Es0 D0); [apply ST_err_return; exact HS0 | unfold Z_STREAM_ERROR; lia]|].
    split; [apply (ST_dpost c0 s0 HC0 Es0 D0); [apply ST_err_return; exact HS0 | unfold Z_BUF_ERROR; lia]|].
    intros Hfl5 Hnf Hao.
    pose proof (ST_set_last_flush c0 s0 s0 flush HS0 ltac:(lia)) as HS1.
    set (s1 := set_last_flush s0 flush) in *.
    split; [exact (ST_DOK c0 s0 HC0 s1 HS1)|].
    split.
    - intros Hp1. destruct (ST_flush_pending c0 s0 HC0 s1 HS1) as (HS2 & Hfp & Hor & _).
      split; [exact Hfp|]. split; [exact (ST_DOK c0 s0 HC0 _ HS2)|].
      split; [intros _; apply (ST_dpost c0 s0 HC0 Es0 D0); [apply ST_set_last_flush; [exact HS2 | lia] | unfold Z_OK; lia]|].
      intros Ha2. apply (body_stage c0 s0 HC0 Es0 D0); [exact HS2 | lia | lia].
    - intros Hp1. split.
      + intros _. apply (ST_dpost c0 s0 HC0 Es0 D0); [apply ST_err_return; exact HS1 | unfold Z_BUF_ERROR; lia].
      + intros _. apply (body_stage c0 s0 HC0 Es0 D0); [exact HS1 | exact Hp1 | lia].
  Qed.

  Theorem deflate_m_DD : forall ds zc flush, DD ds -> dcall_wf zc -> 0 <= flush < 16 -> DD (fst (deflate_m ds zc flush)).
  Proof.
    intros ds zc flush HDD Hzc Hfl.
    set (c0 := cstrm_of_call zc). set (s0 := set_strm ds c0).
    pose proof (C0OK'_of_call zc Hzc) as HC0. fold c0 in HC0.
    assert (H0 : DC c0 s0) by (split; [apply DD_set_strm; exact HDD | subst s0 c0; apply SV_entry; exact Hzc]).
    pose proof H0 as [[D0 X0] V0].
    assert (HS0 : ST c0 s0 s0) by (split; [exact H0 | reflexivity]).
    unfold deflate_m. fold c0 s0.
    pose proof (core_result c0 s0 HC0 eq_refl D0 flush HS0 Hfl) as [[HDD' _] _].
    destruct (deflate_core s0 flush) as [s' rc]. cbn [fst] in HDD' |- *. exact HDD'.
  Qed.

End Integrate.
End RefDeflSafeI4.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).




Record DXX (s : deflate_state) : Prop := {
  xx_cfg : (ds_good_match s, ds_max_lazy_match s, ds_nice_match s, ds_max_chain_length s) = configuration_table (ds_level s);
  xx_insh : 0 <= ds_ins_h s < 65536;
  xx_ins : ds_insert s <= ds_w_size s;
  xx_ml : 0 <= ds_match_length s <= MAX_MATCH;
  xx_pl : 0 <= ds_prev_length s <= MAX_MATCH;
  xx_ma : ds_match_available s = 0 \/ ds_match_available s = 1;
  xx_pm : 0 <= ds_prev_match s < 2 ^ 32;
  xx_hw : ds_high_water s <= ds_window_size s;
  xx_fast : dmode s = 3 -> ds_prev_length s = 2 /\ ds_match_length s < MIN_MATCH;
  xx_notslow : dmode s <> 4 -> ds_match_available s = 0;
  xx_slow : dmode s = 4 -> 2 <= ds_match_length s /\ (ds_match_available s = 1 -> 1 <= ds_strstart s);
  xx_st0 : dmode s = 0 -> ds_lookahead s = 0 /\ 0 <= ds_block_start s <= ds_strstart s /\ ds_sym_next s = 0 /\ ds_matches s <= 2;
  xx_wrapneg : ds_wrap s < 0 -> ds_status s = FINISH_STATE;
  xx_fin : ds_status s = FINISH_STATE -> ds_lookahead s = 0;
  xx_tdl : forall t i, 0 <= arr_get (tree_dl s t) i < 65536;
  xx_depth : forall i, 0 <= arr_get (ds_depth s) i < 256;
  xx_blc : forall i, 0 <= i < 16 -> 0 <= arr_get (ds_bl_count s) i < 65536;
  xx_chain : dmode s <> 0 -> CHAIN s (ds_strstart s) (ds_strstart s) }.

Record DXR (s : deflate_state) : Prop := {
  xr_matches : 0 <= ds_matches s <= nsym s + 2;
  xr_sn : ds_sym_next s = 3 * nsym s;
  xr_nsym : 0 <= nsym s <= ds_lit_bufsize s - 2;
  xr_syms : forall j, 0 <= j < nsym s -> sym_okb s j;
  xr_hist : freq_hist s;
  xr_opt : ds_opt_len s = 0;
  xr_stat : ds_static_len s = 0;
  xr_ext : dmode s <> 0 -> 0 <= ds_strstart s - ds_block_start s <= 258 * nsym s + ds_match_available s;
  xr_tfc : forall t i, 0 <= arr_get (tree_fc s t) i < 65536;
  xr_pout0 : ds_pending s = 0 -> ds_pending_out s = 0;
  xr_biv : ds_bi_valid s <= 7 }.

Definition SLOW3 (s : deflate_state) : Prop :=
  dmode s = 4 -> MIN_MATCH <= ds_match_length s ->
  ds_match_length s <= ds_lookahead s + 1 /\ 1 <= ds_strstart s
  /\ 2 <= wrap32 (ds_strstart s - ds_match_start s) <= ds_w_size s - MIN_LOOKAHEAD + 1.
Definition BND (s : deflate_state) : Prop :=
  (dmode s <> 0 -> CHAIN s (ds_strstart s - 1) (ds_strstart s - 1)) /\ SLOW3 s.

Lemma SLOW3_mode : forall s, dmode s <> 4 -> SLOW3 s.
Proof. intros s Hm H4. exfalso. exact (Hm H4). Qed.
Lemma SLOW3_ml : forall s, ds_match_length s < MIN_MATCH -> SLOW3 s.
Proof. intros s Hml _ H3. exfalso. lia. Qed.

Lemma DX_DXX : forall s, DX s -> DXX s.
Proof.
  intros s X. destruct X; constructor; try assumption.
  - intros Hm. destruct (dx_slow Hm) as (A & B & _). exact (conj A B).
  - intros Hm. eapply CHAIN_mono; [| | exact (dx_chain Hm)]; lia.
Qed.
Lemma DX_DXR : forall s, DX s -> DXR s.
Proof. intros s X. destruct X; constructor; assumption. Qed.
Lemma DX_BND : forall s, DX s -> BND s.
Proof. intros s X. split; [exact (dx_chain _ X)|]. intros Hm H3. destruct (dx_slow _ X Hm) as (_ & _ & C). exact (C H3). Qed.
Lemma DX_SLOW3 : forall s, DX s -> SLOW3 s.
Proof. intros s X. exact (proj2 (DX_BND s X)). Qed.

Lemma DX_join : forall s, DXX s -> DXR s -> BND s -> DX s.
Proof.
  intros s XX XR [BC BS]. destruct XX, XR; constructor; try assumption.
  intros Hm. match goal with Hx : dmode s = 4 -> 2 <= ds_match_length s /\ _ |- _ => destruct (Hx Hm) as [A B] end.
  split; [exact A|]. split; [exact B|]. exact (BS Hm).
Qed.

Lemma DXX_DX : forall s, DXX s -> SLOW3 s ->
  0 <= ds_matches s <= nsym s + 2 -> ds_sym_next s = 3 * nsym s -> 0 <= nsym s <= ds_lit_bufsize s - 2 ->
  (forall j, 0 <= j < nsym s -> sym_okb s j) -> freq_hist s -> ds_opt_len s = 0 -> ds_static_len s = 0 ->
  (dmode s <> 0 -> 0 <= ds_strstart s - ds_block_start s <= 258 * nsym s + ds_match_available s) ->
  (forall t i, 0 <= arr_get (tree_fc s t) i < 65536) ->
  (ds_pending s = 0 -> ds_pending_out s = 0) -> ds_bi_valid s <= 7 ->
  (dmode s <> 0 -> CHAIN s (ds_strstart s - 1) (ds_strstart s - 1)) -> DX s.
Proof. intros s XX SL; intros. apply (DX_join s XX); [constructor; assumption | split; assumption]. Qed.

Definition DCW (c0 : cstrm) (s : deflate_state) : Prop := (dwf s /\ (DXX s /\ DXR s)) /\ SV c0 s.

Lemma DC_DCW : forall c0 s, DC c0 s -> DCW c0 s.
Proof. intros c0 s [[D X] V]. exact (conj (conj D (conj (DX_DXX s X) (DX_DXR s X))) V). Qed.
Lemma DCW_DC : forall c0 s, DCW c0 s -> BND s -> DC c0 s.
Proof. intros c0 s [[D [XX XR]] V] B. exact (conj (conj D (DX_join s XX XR B)) V). Qed.

Lemma DXX_core2_same : forall s s', dx_core2 s' = dx_core2 s -> DXX s -> DXX s'.
Proof.
  intros s s' E X. pose proof (dx_core2_fields s s' E) as F.
  destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20
               & F21 & F22 & F23 & F25 & F26 & F27 & F28 & F29 & F30 & F31 & F32 & F33 & F34 & F35 & F36 & F37 & F38 & F39).
  assert (Em : dmode s' = dmode s) by (unfold dmode; rewrite F5, F6; reflexivity).
  pose proof (xx_tdl _ X) as Xtdl. pose proof (xx_depth _ X) as Xdepth. pose proof (xx_blc _ X) as Xblc. pose proof (xx_chain _ X) as Xchain.
  destruct X; constructor; rewrite ?Em, ?F1, ?F2, ?F3, ?F4, ?F5, ?F6, ?F7, ?F8, ?F9, ?F10, ?F11, ?F12, ?F13, ?F14, ?F15, ?F16,
    ?F17, ?F18, ?F19, ?F20, ?F21, ?F22, ?F23, ?F33, ?F34, ?F39; try assumption.
  - intros t i. destruct t; cbn [tree_dl]; rewrite ?F28, ?F29, ?F30; [apply (Xtdl TL i) | apply (Xtdl TD i) | apply (Xtdl TB i)].
  - intros i. rewrite F31. apply Xdepth.
  - intros i Hi. rewrite F32. apply Xblc. exact Hi.
  - intros Hm. apply (CHAIN_same s s'); [exact F35 | exact F36 | exact F37 | exact F9 | exact F38 |]. apply Xchain. exact Hm.
Qed.

Lemma DXR_core2_same : forall s s', dx_core2 s' = dx_core2 s ->
  (forall i, 0 <= i -> sym_buf_get s' i = sym_buf_get s i) ->
  (ds_pending s' = 0 -> ds_pending_out s' = 0) -> ds_bi_valid s' <= 7 ->
  DXR s -> DXR s'.
Proof.
  intros s s' E Hsym Hp Hbv X. pose proof (dx_core2_fields s s' E) as F.
  destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20
               & F21 & F22 & F23 & F25 & F26 & F27 & F28 & F29 & F30 & F31 & F32 & F33 & F34 & F35 & F36 & F37 & F38 & F39).
  assert (Em : dmode s' = dmode s) by (unfold dmode; rewrite F5, F6; reflexivity).
  assert (En : nsym s' = nsym s) by (apply nsym_same; exact F20).
  destruct (sym_readers_same s s' Hsym) as [La Lb].
  pose proof (xr_syms _ X) as Xsyms. pose proof (xr_hist _ X) as Xhist. pose proof (xr_tfc _ X) as Xtfc.
  destruct X; constructor; rewrite ?Em, ?En, ?F12, ?F14, ?F18, ?F19, ?F20, ?F23, ?F33, ?F34; try assumption.
  - intros j Hj. unfold sym_okb. rewrite La, Lb by lia. apply Xsyms. exact Hj.
  - eapply freq_hist_same2; [exact Hsym | exact F20 | exact F25 | exact F26 | exact F27 | lia | exact Xhist].
  - intros t i. destruct t; cbn [tree_fc]; rewrite ?F25, ?F26, ?F27; [apply (Xtfc TL i) | apply (Xtfc TD i) | apply (Xtfc TB i)].
Qed.

Lemma DCW_flush_pending : forall c0 s, C0OK c0 -> DCW c0 s ->
  let s' := flush_pending s in
  DCW c0 s' /\ KV s' = KV s /\ OUTLE s s' /\ dx_core2 s' = dx_core2 s
  /\ fp_ok s
  /\ 0 <= ds_pending s' <= ds_pending s
  /\ (ds_pending s' = 0 \/ cs_avail_out (ds_strm s') = 0)
  /\ (ds_pending s = 0 -> s' = s)
  /\ ds_bi_valid s' = ds_bi_valid s /\ ds_pending_buf s' = ds_pending_buf s
  /\ cs_avail_in (ds_strm s') = cs_avail_in (ds_strm s) /\ cs_next_in (ds_strm s') = cs_next_in (ds_strm s).
Proof.
  intros c0 s HC0 HDC s'. pose proof HDC as [[D [XX XR]] V]. subst s'.
  pose proof (dwf_sizes s D) as (Sw & Sh & Sl & Spbs & Ssh). pose proof (df_pend _ D) as (P1 & P2 & P3). pose proof (df_bi _ D) as (B1 & B2).
  pose proof (xr_biv _ XR) as B7.
  pose proof (sv_aout _ _ V) as A0. pose proof (sv_out _ _ V) as Ao. pose proof (c0_out _ HC0) as O0. pose proof (c0_aout _ HC0) as Aa.
  rewrite O0 in Ao. unfold zlen in Ao. cbn [length Z.of_nat] in Ao.
  assert (Hfp : fp_ok s).
  { unfold fp_ok. cbv zeta. rewrite (tr_flush_bits_id7 s B7).
    pose proof (fp_len_range s A0 ltac:(lia)) as (R1 & R2 & R3).
    split; [unfold BINV; lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    rewrite (sv_tout _ _ V). apply wrap64_range'. }
  rewrite flush_pending_eq. cbv zeta. rewrite (tr_flush_bits_id7 s B7).
  pose proof (fp_len_range s A0 ltac:(lia)) as (R1 & R2 & R3).
  destruct (Z.eqb_spec (fp_len s) 0) as [E0|E0].
  { split; [exact HDC|]. split; [reflexivity|]. split; [apply OUTLE_refl|]. split; [reflexivity|]. split; [exact Hfp|].
    split; [lia|]. split; [lia|]. split; [reflexivity|]. repeat split; reflexivity. }
  pose proof (fp_tail_facts' s (fp_len s) ltac:(lia)) as
    (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17).
  set (s1 := fp_tail s (fp_len s)) in *.
  assert (D1 : dwf s1).
  { destruct D; constructor; subst s1; unfold fp_tail, cs_emit; destruct (_ =? 0); dsred; try assumption; lia. }
  assert (Hsb : forall i, 0 <= i -> sym_buf_get s1 i = sym_buf_get s i).
  { intros i Hi. unfold sym_buf_get. rewrite F6. destruct (KV_fields s s1 F16) as (_ & _ & E3 & _). rewrite E3. reflexivity. }
  assert (XX1 : DXX s1) by (exact (DXX_core2_same s s1 F17 XX)).
  assert (XR1 : DXR s1) by (apply (DXR_core2_same s s1 F17 Hsb F2); [rewrite F4; exact B7 | exact XR]).
  assert (V1 : SV c0 s1).
  { constructor; rewrite ?F7, ?F8, ?F9, ?F10, ?F11, ?F12, ?F13, ?F14, ?F15.
    - exact (sv_input _ _ V).
    - exact (sv_nin _ _ V).
    - exact (sv_inlen _ _ V).
    - exact (sv_ain _ _ V).
    - unfold zlen. rewrite rev_append_rev, length_app, length_rev. unfold arr_slice. rewrite arr_slice_nat_length.
      rewrite O0. cbn [length]. unfold zlen in Ao. lia.
    - lia.
    - rewrite O0. apply le_0_n.
    - apply Forall_rev_append; [| exact (sv_outb _ _ V)]. apply Forall_arr_slice. intros i Hi.
      apply (df_bb _ D). lia.
    - exact (sv_tin _ _ V).
    - rewrite (sv_tout _ _ V), O0. unfold zlen. rewrite rev_append_rev, length_app, length_rev. unfold arr_slice. rewrite arr_slice_nat_length.
      cbn [length Z.of_nat]. rewrite Z.sub_0_r, Z.sub_0_r. rewrite Nat2Z.inj_add, Z2Nat.id by lia.
      rewrite wrap64_add_l. f_equal. lia.
    - exact (sv_adler _ _ V).
    - exact (sv_dt _ _ V).
    - intros i Hi. apply (sv_ib _ _ V). exact Hi. }
  split; [exact (conj (conj D1 (conj XX1 XR1)) V1)|]. split; [exact F16|].
  split; [apply (OUTLE_emit _ _ (arr_slice (ds_pending_buf s) (ds_pending_out s) (fp_len s))); exact F15|].
  split; [exact F17|]. split; [exact Hfp|]. split; [lia|]. split; [lia|].
  split; [intros Hp0; exfalso; lia|]. repeat split; assumption.
Qed.

Lemma BND_same : forall a b, BND a -> dmode b = dmode a ->
  ds_head b = ds_head a -> ds_prev b = ds_prev a -> ds_hash_size b = ds_hash_size a -> ds_w_size b = ds_w_size a -> ds_w_mask b = ds_w_mask a ->
  ds_strstart b = ds_strstart a -> ds_match_length b = ds_match_length a -> ds_lookahead b = ds_lookahead a -> ds_match_start b = ds_match_start a ->
  BND b.
Proof.
  intros a b [BC BS] Em Ehd Epv Ehs Ews Ewm Estr Eml Elook Ems. split.
  - intros Hm. rewrite Estr. apply (CHAIN_same a b _ _ Ehd Epv Ehs Ews Ewm). apply BC. rewrite <- Em. exact Hm.
  - unfold SLOW3 in *. rewrite Em, Eml, Elook, Estr, Ems, Ews. exact BS.
Qed.


Definition PF (s : deflate_state) :=
  ((ds_good_match s, ds_max_lazy_match s, ds_nice_match s, ds_max_chain_length s, ds_level s, ds_strategy s),
   (ds_ins_h s, ds_insert s, ds_prev_length s, ds_match_available s, ds_prev_match s, ds_high_water s, ds_window_size s, ds_wrap s),
   (ds_status s, ds_lit_bufsize s, ds_head s, ds_prev s, ds_hash_size s, ds_w_mask s, ds_hash_mask s, ds_hash_shift s),
   (ds_w_bits s, ds_hash_bits s, ds_pending_buf_size s, ds_gzhead s, ds_method s, ds_last_flush s, ds_sym_end s, ds_match_start s, KV s)).

Lemma keeps_PF : keeps PF true true.
Proof. constructor; intros; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.

Lemma PF_fields : forall a b, PF b = PF a ->
  (ds_good_match b = ds_good_match a /\ ds_max_lazy_match b = ds_max_lazy_match a /\ ds_nice_match b = ds_nice_match a
   /\ ds_max_chain_length b = ds_max_chain_length a /\ ds_level b = ds_level a /\ ds_strategy b = ds_strategy a)
  /\ (ds_ins_h b = ds_ins_h a /\ ds_insert b = ds_insert a /\ ds_prev_length b = ds_prev_length a /\ ds_match_available b = ds_match_available a
      /\ ds_prev_match b = ds_prev_match a /\ ds_high_water b = ds_high_water a /\ ds_window_size b = ds_window_size a /\ ds_wrap b = ds_wrap a)
  /\ (ds_status b = ds_status a /\ ds_lit_bufsize b = ds_lit_bufsize a /\ ds_head b = ds_head a /\ ds_prev b = ds_prev a
      /\ ds_hash_size b = ds_hash_size a /\ ds_w_mask b = ds_w_mask a /\ ds_hash_mask b = ds_hash_mask a /\ ds_hash_shift b = ds_hash_shift a)
  /\ (ds_w_bits b = ds_w_bits a /\ ds_hash_bits b = ds_hash_bits a /\ ds_pending_buf_size b = ds_pending_buf_size a /\ ds_gzhead b = ds_gzhead a
      /\ ds_method b = ds_method a /\ ds_last_flush b = ds_last_flush a /\ ds_sym_end b = ds_sym_end a /\ ds_match_start b = ds_match_start a /\ KV b = KV a).
Proof.
  intros a b E. unfold PF in E.
  repeat match type of E with (_, _) = (_, _) => apply pair_equal_spec in E; destruct E as [E ?] end.
  repeat match goal with H : (_, _) = (_, _) |- _ => apply pair_equal_spec in H; destruct H as [H ?] end.
  repeat split; assumption.
Qed.

Lemma tr_flush_bits_shape : forall s, 0 <= ds_bi_valid s <= 16 -> 0 <= ds_bi_buf s < 2 ^ 16 ->
  exists A P B V, tr_flush_bits s = upd4 s A P B V
    /\ ds_pending s <= P <= ds_pending s + 2 /\ 0 <= V <= 7 /\ 0 <= B < 2 ^ 16 /\ arr_len A = arr_len (ds_pending_buf s)
    /\ (forall n, (forall i, 0 <= i < n -> 0 <= arr_get (ds_pending_buf s) i < 256) -> forall i, 0 <= i < n -> 0 <= arr_get A i < 256).
Proof.
  intros s Hbv Hbb.
  destruct (tr_flush_bits_cases s) as [E|[E|E]]; rewrite E.
  - exists (ds_pending_buf s), (ds_pending s), (ds_bi_buf s), (ds_bi_valid s).
    split; [destruct s; reflexivity|]. 
    assert (ds_bi_valid s <= 7).
    { unfold tr_flush_bits, bi_flush in E. destruct (Z.eqb_spec (ds_bi_valid s) 16); [exfalso|].
      -
        apply (f_equal ds_pending) in E. unfold put_short, put_byte in E. revert E. dsred. lia.
      - destruct (Z.leb_spec 8 (ds_bi_valid s)); [exfalso | lia].
        apply (f_equal ds_pending) in E. unfold put_byte in E. revert E. dsred. lia. }
    split; [lia|]. split; [lia|]. split; [lia|]. split; [reflexivity|]. intros nn Hn ii Hi. apply Hn. exact Hi.
  - exists (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (ds_bi_buf s))), (ds_pending s + 1), (Z.shiftr (ds_bi_buf s) 8), (ds_bi_valid s - 8).
    assert (8 <= ds_bi_valid s < 16).
    { unfold tr_flush_bits, bi_flush in E. destruct (Z.eqb_spec (ds_bi_valid s) 16).
      - exfalso. apply (f_equal ds_pending) in E. unfold put_short, put_byte in E. revert E. dsred. lia.
      - destruct (Z.leb_spec 8 (ds_bi_valid s)); [lia|]. exfalso. apply (f_equal ds_pending) in E. unfold put_byte in E. revert E. dsred. lia. }
    split; [unfold upd4, put_byte; dsred; reflexivity|].
    split; [lia|]. split; [lia|].
    split; [rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]|].
    split; [rewrite arr_len_set; reflexivity|].
    intros nn Hn ii Hi. rewrite arr_get_set. destruct (_ && _); [apply wrap8_range | apply Hn; exact Hi].
  - exists (arr_set (arr_set (ds_pending_buf s) (ds_pending s) (wrap8 (Z.land (ds_bi_buf s) 255))) (ds_pending s + 1) (wrap8 (Z.shiftr (wrap16 (ds_bi_buf s)) 8))),
           (ds_pending s + 1 + 1), 0, 0.
    split; [unfold upd4, put_byte; dsred; reflexivity|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [rewrite !arr_len_set; reflexivity|].
    intros nn Hn ii Hi. rewrite !arr_get_set. repeat (destruct (_ && _); [apply wrap8_range|]). apply Hn. exact Hi.
Qed.

Lemma flush_pending_bits : forall s, 0 <= ds_bi_valid s <= 16 -> 0 <= ds_bi_buf s < 2 ^ 16 -> flush_pending (tr_flush_bits s) = flush_pending s.
Proof.
  intros s Hbv Hbb. rewrite (flush_pending_eq (tr_flush_bits s)), (flush_pending_eq s). cbv zeta.
  destruct (tr_flush_bits_shape s Hbv Hbb) as (A & P & B & V & E & _ & HV & _).
  rewrite (tr_flush_bits_id7 (tr_flush_bits s)) by (rewrite E; unfold upd4; dsred; lia). reflexivity.
Qed.



Definition TRS (s : deflate_state) :=
  ((ds_dyn_ltree_fc s, ds_dyn_dtree_fc s, ds_bl_tree_fc s, ds_dyn_ltree_dl s, ds_dyn_dtree_dl s, ds_bl_tree_dl s),
   (ds_depth s, ds_bl_count s, ds_heap s, ds_opt_len s, ds_static_len s, ds_matches s, ds_sym_next s)).

Lemma TRS_fields : forall a b, TRS b = TRS a ->
  (ds_dyn_ltree_fc b = ds_dyn_ltree_fc a /\ ds_dyn_dtree_fc b = ds_dyn_dtree_fc a /\ ds_bl_tree_fc b = ds_bl_tree_fc a
   /\ ds_dyn_ltree_dl b = ds_dyn_ltree_dl a /\ ds_dyn_dtree_dl b = ds_dyn_dtree_dl a /\ ds_bl_tree_dl b = ds_bl_tree_dl a)
  /\ (ds_depth b = ds_depth a /\ ds_bl_count b = ds_bl_count a /\ ds_heap b = ds_heap a /\ ds_opt_len b = ds_opt_len a
      /\ ds_static_len b = ds_static_len a /\ ds_matches b = ds_matches a /\ ds_sym_next b = ds_sym_next a).
Proof.
  intros a b E. unfold TRS in E.
  repeat match type of E with (_, _) = (_, _) => apply pair_equal_spec in E; destruct E as [E ?] end.
  repeat match goal with H : (_, _) = (_, _) |- _ => apply pair_equal_spec in H; destruct H as [H ?] end.
  repeat split; assumption.
Qed.

Lemma tree_fc_TRS : forall a b t, TRS b = TRS a -> tree_fc b t = tree_fc a t.
Proof. intros a b t E. pose proof (TRS_fields a b E) as ((E1 & E2 & E3 & _) & _). destruct t; cbn [tree_fc]; congruence. Qed.
Lemma tree_dl_TRS : forall a b t, TRS b = TRS a -> tree_dl b t = tree_dl a t.
Proof. intros a b t E. pose proof (TRS_fields a b E) as ((_ & _ & _ & E1 & E2 & E3) & _). destruct t; cbn [tree_dl]; congruence. Qed.
Lemma tree_lens_TRS : forall a b, TRS b = TRS a -> tree_lens a -> tree_lens b.
Proof.
  intros a b E T. pose proof (TRS_fields a b E) as ((E1 & E2 & E3 & E4 & E5 & E6) & (E7 & E8 & E9 & _)).
  unfold tree_lens in *. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9. exact T.
Qed.

Lemma PF_tfb : forall s buf len last, PF (tr_flush_block s buf len last) = PF s.
Proof. intros. rewrite (k_tr_flush_block PF keeps_PF). unfold tfb_X0. destruct (_ && _); [destruct s|]; reflexivity. Qed.
Lemma PF_set_block_start : forall s v, PF (set_block_start s v) = PF s. Proof. reflexivity. Qed.
Lemma PF_upd4 : forall s a p b v, PF (upd4 s a p b v) = PF s. Proof. reflexivity. Qed.
Lemma PF_tr_flush_bits : forall s, PF (tr_flush_bits s) = PF s.
Proof. intros s. destruct (tr_flush_bits_cases s) as [E|[E|E]]; rewrite E; reflexivity. Qed.
Lemma PF_fp_tail : forall s len, PF (fp_tail s len) = PF s.
Proof. intros s len. unfold fp_tail. destruct (_ =? 0); reflexivity. Qed.
Lemma PF_flush_pending : forall s, PF (flush_pending s) = PF s.
Proof. intros s. rewrite flush_pending_eq. cbv zeta. destruct (_ =? 0); rewrite ?PF_fp_tail; apply PF_tr_flush_bits. Qed.

Lemma TRS_set_block_start : forall s v, TRS (set_block_start s v) = TRS s. Proof. reflexivity. Qed.
Lemma TRS_upd4 : forall s a p b v, TRS (upd4 s a p b v) = TRS s. Proof. reflexivity. Qed.

Lemma window_tr_flush_bits : forall s, ds_window (tr_flush_bits s) = ds_window s.
Proof. intros s. destruct (tr_flush_bits_cases s) as [E|[E|E]]; rewrite E; reflexivity. Qed.
Lemma window_fp_tail : forall s len, ds_window (fp_tail s len) = ds_window s.
Proof. intros s len. unfold fp_tail. destruct (_ =? 0); reflexivity. Qed.
Lemma window_flush_pending : forall s, ds_window (flush_pending s) = ds_window s.
Proof. intros s. rewrite flush_pending_eq. cbv zeta. destruct (_ =? 0); rewrite ?window_fp_tail; apply window_tr_flush_bits. Qed.
Lemma ml_flush_pending : forall s, ds_match_length (flush_pending s) = ds_match_length s.
Proof.
  intros s. rewrite flush_pending_eq. cbv zeta.
  assert (E1 : forall len, ds_match_length (fp_tail (tr_flush_bits s) len) = ds_match_length (tr_flush_bits s)) by (intros len; unfold fp_tail; destruct (_ =? 0); reflexivity).
  assert (E2 : ds_match_length (tr_flush_bits s) = ds_match_length s) by (destruct (tr_flush_bits_cases s) as [E|[E|E]]; rewrite E; reflexivity).
  destruct (_ =? 0); rewrite ?E1; exact E2.
Qed.

Lemma lz_set_block_start : forall s v,
  (ds_strstart (set_block_start s v), ds_lookahead (set_block_start s v), ds_block_start (set_block_start s v),
   ds_match_length (set_block_start s v), ds_window (set_block_start s v), ds_strm (set_block_start s v), ds_pending_out (set_block_start s v))
  = (ds_strstart s, ds_lookahead s, v, ds_match_length s, ds_window s, ds_strm s, ds_pending_out s).
Proof. reflexivity. Qed.
Lemma lz_upd4 : forall s a p b v,
  (ds_strstart (upd4 s a p b v), ds_lookahead (upd4 s a p b v), ds_block_start (upd4 s a p b v),
   ds_match_length (upd4 s a p b v), ds_window (upd4 s a p b v), ds_strm (upd4 s a p b v), ds_pending_out (upd4 s a p b v))
  = (ds_strstart s, ds_lookahead s, ds_block_start s, ds_match_length s, ds_window s, ds_strm s, ds_pending_out s).
Proof. reflexivity. Qed.
Lemma bits_upd4 : forall s a p b v,
  (ds_pending_buf (upd4 s a p b v), ds_pending (upd4 s a p b v), ds_bi_buf (upd4 s a p b v), ds_bi_valid (upd4 s a p b v)) = (a, p, b, v).
Proof. reflexivity. Qed.
Lemma bits_set_block_start : forall s v,
  (ds_pending_buf (set_block_start s v), ds_pending (set_block_start s v), ds_bi_buf (set_block_start s v), ds_bi_valid (set_block_start s v))
  = (ds_pending_buf s, ds_pending s, ds_bi_buf s, ds_bi_valid s).
Proof. reflexivity. Qed.

Lemma lz_view_fields : forall a b, lz_view b = lz_view a ->
  ds_strstart b = ds_strstart a /\ ds_lookahead b = ds_lookahead a /\ ds_block_start b = ds_block_start a
  /\ ds_match_length b = ds_match_length a /\ ds_window b = ds_window a /\ ds_w_size b = ds_w_size a.
Proof.
  intros a b E. unfold lz_view in E.
  repeat match type of E with (_, _) = (_, _) => apply pair_equal_spec in E; destruct E as [E ?] end.
  repeat split; assumption.
Qed.

Lemma SV_cset_data_type : forall c0 s s' dt, SV c0 s -> ds_strm s' = cset_data_type (ds_strm s) dt -> - 2 ^ 31 <= dt < 2 ^ 31 -> SV c0 s'.
Proof.
  intros c0 s s' dt V E Hdt. destruct V; constructor; rewrite E; unfold cset_data_type; cbn; assumption.
Qed.

Lemma dmode_PF : forall a b, PF b = PF a -> dmode b = dmode a.
Proof. intros a b E. pose proof (PF_fields a b E) as ((_ & _ & _ & _ & El & Es) & _). unfold dmode. rewrite El, Es. reflexivity. Qed.

Lemma DXX_transfer : forall a b, DXX a -> PF b = PF a ->
  ds_strstart b = ds_strstart a -> ds_lookahead b = ds_lookahead a -> ds_match_length b = ds_match_length a -> dmode a <> 0 ->
  (forall t i, 0 <= arr_get (tree_dl b t) i < 65536) -> (forall i, 0 <= arr_get (ds_depth b) i < 256) ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get (ds_bl_count b) i < 65536) -> DXX b.
Proof.
  intros a b X E Estr Elook Eml Hm Htdl Hdep Hblc.
  pose proof (PF_fields a b E) as ((Egm & Elz & Enm & Emc & Elv & Esy) & (Eih & Eins & Epl & Ema & Epm & Ehw & Ewsz & Ewr) & (Est & Elbs & Ehd & Epv & Ehs & Ewm & Ehm & Ehsh) & (Ewb & Ehb & Epbs & Egz & Eme & Elf & Ese & Ems & EKV)).
  pose proof (KV_fields _ _ EKV) as (Ews & Ehsz & _ & _).
  assert (Em : dmode b = dmode a) by (unfold dmode; rewrite Elv, Esy; reflexivity).
  pose proof (xx_chain _ X) as XC.
  destruct X; constructor; rewrite ?Em, ?Egm, ?Elz, ?Enm, ?Emc, ?Elv, ?Esy, ?Eih, ?Eins, ?Epl, ?Ema, ?Epm, ?Ehw, ?Ewsz, ?Ewr, ?Est, ?Ews, ?Estr, ?Elook, ?Eml, ?Ems; try assumption.
  - intros H0. exfalso. exact (Hm H0).
  - intros Hm'. apply (CHAIN_same a b); [exact Ehd | exact Epv | exact Ehs | exact Ews | exact Ewm |]. exact (XC Hm').
Qed.

Lemma PF_tfb_X0 : forall s, PF (tfb_X0 s) = PF s.
Proof. intros s. unfold tfb_X0. destruct (_ && _); [destruct s|]; reflexivity. Qed.

Lemma flush_block_only_eq' : forall s last,
  flush_block_only s last
  = flush_pending (set_block_start (tr_flush_block s (fb_buf s) (fb_len s) last) (ds_strstart (tr_flush_block s (fb_buf s) (fb_len s) last))).
Proof. reflexivity. Qed.

Lemma flush_block_eq' : forall s last,
  flush_block s last
  = (flush_block_only s last,
     if cs_avail_out (ds_strm (flush_block_only s last)) =? 0 then Some (if negb (last =? 0) then finish_started else need_more) else None).
Proof. intros s last. unfold flush_block. destruct (_ =? 0); reflexivity. Qed.

Lemma flush_post10 : forall c0 s last s8,
  C0OK c0 -> dwf s -> SV c0 s -> DXX s -> fb_entry s last -> ds_status s <> FINISH_STATE -> dmode s <> 0 ->
  fb_post s last s8 ->
  let s9 := set_block_start s8 (ds_strstart s8) in
  let s10 := tr_flush_bits s9 in
  DCW c0 s10 /\ PF s10 = PF s /\ TRS s10 = TRS s8
  /\ ds_strstart s10 = ds_strstart s /\ ds_lookahead s10 = ds_lookahead s /\ ds_block_start s10 = ds_strstart s
  /\ ds_match_length s10 = ds_match_length s /\ ds_window s10 = ds_window s
  /\ (exists dt, ds_strm s10 = cset_data_type (ds_strm s) dt)
  /\ ds_sym_next s10 = 0 /\ ds_pending_out s10 = 0
  /\ flush_pending s9 = flush_pending s10.
Proof.
  intros c0 s last s8 HC0 D V XX FE Hst Hm FP s9 s10.
  pose proof (fp_keep _ _ _ FP _ PF keeps_PF) as EPF8. rewrite PF_tfb_X0 in EPF8.
  pose proof (lz_view_fields _ _ (fp_lz _ _ _ FP)) as (Estr8 & Elook8 & Ebs8 & Eml8 & Ewin8 & Ews8).
  destruct (fp_strm _ _ _ FP) as (dt & Estrm8 & Hdt).
  pose proof (fp_biv _ _ _ FP) as Bv8. pose proof (fp_bib _ _ _ FP) as Bb8. pose proof (fp_pending _ _ _ FP) as Pd8.
  pose proof (fp_pout _ _ _ FP) as Po8. pose proof (fp_pbl _ _ _ FP) as Pbl8. pose proof (fp_pbb _ _ _ FP) as Pbb8.
  destruct (tr_flush_bits_shape s9 ltac:(exact Bv8) ltac:(exact Bb8)) as (A & P & B & Bv & E10 & HP & HBv & HB & HA & HAb).
  change (ds_pending s9) with (ds_pending s8) in HP. change (ds_pending_buf s9) with (ds_pending_buf s8) in HA, HAb.
  assert (E10' : s10 = upd4 s9 A P B Bv) by exact E10.
  assert (EPF : PF s10 = PF s) by (rewrite E10', PF_upd4; exact EPF8).
  assert (ETRS : TRS s10 = TRS s8) by (rewrite E10', TRS_upd4; reflexivity).
  pose proof (f_equal (fun s => (ds_strstart s, ds_lookahead s, ds_block_start s, ds_match_length s, ds_window s, ds_strm s, ds_pending_out s)) E10') as EL.
  cbv beta in EL. rewrite lz_upd4 in EL. unfold s9 in EL. rewrite lz_set_block_start in EL.
  apply pair_equal_spec in EL; destruct EL as [EL Epo10]. apply pair_equal_spec in EL; destruct EL as [EL Estrm10].
  apply pair_equal_spec in EL; destruct EL as [EL Ewin10]. apply pair_equal_spec in EL; destruct EL as [EL Eml10].
  apply pair_equal_spec in EL; destruct EL as [EL Ebs10]. apply pair_equal_spec in EL; destruct EL as [Estr10 Elook10].
  pose proof (f_equal (fun s => (ds_pending_buf s, ds_pending s, ds_bi_buf s, ds_bi_valid s)) E10') as EB.
  cbv beta in EB. rewrite bits_upd4 in EB.
  apply pair_equal_spec in EB; destruct EB as [EB Ebv10]. apply pair_equal_spec in EB; destruct EB as [EB Ebb10].
  apply pair_equal_spec in EB; destruct EB as [Epb10 Epd10].
  rewrite Estr8 in Estr10, Ebs10. rewrite Elook8 in Elook10. rewrite Eml8 in Eml10. rewrite Ewin8 in Ewin10. rewrite Estrm8 in Estrm10. rewrite Po8 in Epo10.
  pose proof (PF_fields _ _ EPF) as ((Egm & Elz & Enm & Emc & Elv & Esy) & (Eih & Eins & Epl & Ema & Epm & Ehw & Ewsz & Ewr) & (Est & Elbs & Ehd & Epv & Ehs & Ewm & Ehm & Ehsh) & (Ewb & Ehb & Epbs & Egz & Eme & Elf & Ese & Ems & EKV)).
  pose proof (KV_fields _ _ EKV) as (Ews & Ehsz & _ & KB).
  pose proof (TRS_fields _ _ ETRS) as ((Eltf & Edtf & Ebtf & Eltd & Edtd & Ebtd) & (Edep & Eblc & Ehp & Eol & Esl & Emt & Esn)).
  rewrite (fp_sn _ _ _ FP) in Esn. rewrite (fp_matches _ _ _ FP) in Emt. rewrite (fp_optlen _ _ _ FP) in Eol. rewrite (fp_statlen _ _ _ FP) in Esl.
  pose proof (PF_fields _ _ EPF8) as (_ & _ & (_ & Elbs8 & _) & _).
  assert (HAb' : forall i, 0 <= i < ds_lit_bufsize s * 4 -> 0 <= arr_get A i < 256).
  { apply HAb. intros i Hi. apply Pbb8. rewrite Pbl8. exact Hi. }
  assert (D10 : dwf s10).
  { pose proof (df_tl _ D) as TL.
    destruct D; constructor; rewrite ?Est, ?Ewb, ?Ews, ?Ewm, ?Ewsz, ?Ehb, ?Ehsz, ?Ehm, ?Ehsh, ?Elbs, ?Epbs, ?Ese, ?Ewin10, ?Epv, ?Ehd, ?Epb10, ?Egz, ?Eme, ?Elv, ?Esy, ?Ewr, ?Estr10, ?Eins, ?Elook10, ?Ems, ?Eih, ?Ehw, ?Elf, ?Epo10, ?Epd10, ?Ebb10, ?Ebv10; try assumption.
    - unfold deflateStateCheck in *. rewrite Est. assumption.
    - congruence.
    - congruence.
    - congruence.
    - congruence.
    - rewrite HA, Pbl8. reflexivity.
    - apply (tree_lens_TRS s8 s10 ETRS). exact (fp_tl _ _ _ FP).
    - clear - HP Pd8. lia.
    - clear - HBv HB. lia. }
  assert (XX10 : DXX s10).
  { apply (DXX_transfer s s10 XX EPF Estr10 Elook10 Eml10 Hm).
    - intros t i. rewrite (tree_dl_TRS s8 s10 t ETRS). apply (fp_dl _ _ _ FP).
    - intros i. rewrite Edep. apply (fp_depth _ _ _ FP).
    - intros i Hi. rewrite Eblc. apply (fp_blc _ _ _ FP). exact Hi. }
  assert (N10 : nsym s10 = 0) by (unfold nsym; rewrite Esn; reflexivity).
  assert (XR10 : DXR s10).
  { constructor; rewrite ?N10, ?Esn, ?Emt, ?Eol, ?Esl, ?Elbs, ?Epd10, ?Epo10, ?Ebv10, ?Estr10, ?Ebs10, ?Ema.
    - clear. lia.
    - reflexivity.
    - pose proof (fe_lbs _ _ FE). clear - H. lia.
    - intros j Hj. exfalso. clear - Hj. lia.
    - unfold freq_hist. rewrite N10, Eltf, Edtf, Ebtf. cbv beta iota delta [Z.to_nat zsum].
      split; [| split]; [intros c Hc; rewrite (fp_ltree _ _ _ FP c Hc); lia | intros d Hd; exact (fp_dtree _ _ _ FP d Hd) | intros b Hb; exact (fp_bltree _ _ _ FP b Hb)].
    - reflexivity.
    - reflexivity.
    - intros _. pose proof (xx_ma _ XX). clear - H. lia.
    - intros t i. rewrite (tree_fc_TRS s8 s10 t ETRS). apply (fp_fc _ _ _ FP).
    - intros _. reflexivity.
    - clear - HBv. lia. }
  assert (V10 : SV c0 s10) by (apply (SV_cset_data_type c0 s s10 dt V Estrm10 Hdt)).
  split; [exact (conj (conj D10 (conj XX10 XR10)) V10)|]. split; [exact EPF|]. split; [exact ETRS|].
  split; [exact Estr10|]. split; [exact Elook10|]. split; [exact Ebs10|]. split; [exact Eml10|]. split; [exact Ewin10|].
  split; [exists dt; exact Estrm10|]. split; [exact Esn|]. split; [exact Epo10|].
  symmetry. apply flush_pending_bits; [exact Bv8 | exact Bb8].
Qed.

Lemma tr_flush_bits_set_ml : forall s v, tr_flush_bits (set_match_length s v) = set_match_length (tr_flush_bits s) v.
Proof.
  intros s v. unfold tr_flush_bits, bi_flush, put_short, put_byte. dsred.
  destruct (ds_bi_valid s =? 16); [destruct s; reflexivity|].
  destruct (8 <=? ds_bi_valid s); destruct s; reflexivity.
Qed.
Lemma fp_len_set_ml : forall s v, fp_len (set_match_length s v) = fp_len s.
Proof. intros s v. reflexivity. Qed.
Lemma fp_tail_set_ml : forall s v len, fp_tail (set_match_length s v) len = set_match_length (fp_tail s len) v.
Proof.
  intros s v len. unfold fp_tail, cs_emit. dsred. destruct (ds_pending s - len =? 0); destruct s; reflexivity.
Qed.
Lemma flush_pending_set_ml : forall s v, flush_pending (set_match_length s v) = set_match_length (flush_pending s) v.
Proof.
  intros s v. rewrite (flush_pending_eq (set_match_length s v)), (flush_pending_eq s). cbv zeta.
  rewrite tr_flush_bits_set_ml, fp_len_set_ml. destruct (fp_len (tr_flush_bits s) =? 0); [reflexivity|]. apply fp_tail_set_ml.
Qed.

Theorem flush_block_only_factsW : forall c0 s last,
  FB_CALL -> C0OK c0 -> dwf s -> SV c0 s -> DXX s -> fb_entry s last -> ds_status s <> FINISH_STATE -> dmode s <> 0 ->
  let s' := flush_block_only s last in
  flush_ok s last
  /\ DCW c0 s' /\ KV s' = KV s /\ OUTLE s s' /\ PF s' = PF s
  /\ ds_strstart s' = ds_strstart s /\ ds_lookahead s' = ds_lookahead s /\ ds_block_start s' = ds_strstart s
  /\ ds_match_length s' = ds_match_length s /\ ds_window s' = ds_window s
  /\ ds_sym_next s' = 0
  /\ (ds_pending s' = 0 \/ cs_avail_out (ds_strm s') = 0)
  /\ cs_avail_in (ds_strm s') = cs_avail_in (ds_strm s) /\ cs_next_in (ds_strm s') = cs_next_in (ds_strm s).
Proof.
  intros c0 s last HFB HC0 D V XX FE Hst Hm s'.
  destruct (HFB s last FE) as [FO FP].
  subst s'. rewrite flush_block_only_eq'.
  set (s8 := tr_flush_block s (fb_buf s) (fb_len s) last) in *. clearbody s8.
  pose proof (flush_post10 c0 s last s8 HC0 D V XX FE Hst Hm FP) as H10. cbv zeta in H10.
  destruct H10 as (DC10 & EPF & ETRS & Estr10 & Elook10 & Ebs10 & Eml10 & Ewin10 & (dt & Estrm10) & Esn10 & Epo10 & Efp).
  rewrite Efp.
  set (s10 := tr_flush_bits (set_block_start s8 (ds_strstart s8))) in *. clearbody s10.
  pose proof (DCW_flush_pending c0 s10 HC0 DC10) as HF. cbv zeta in HF.
  pose proof (ml_flush_pending s10) as Eml'. pose proof (PF_flush_pending s10) as EPF'. pose proof (window_flush_pending s10) as Ewin'.
  set (s' := flush_pending s10) in *. clearbody s'.
  destruct HF as (DC' & EKV' & Ho' & Ecore & _ & _ & Hpa & _ & _ & _ & Eain & Enin).
  pose proof (dx_core2_fields _ _ Ecore) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Elook' & Ebs' & Estr' & Esn' & _).
  pose proof (PF_fields _ _ EPF) as (_ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & EKV)).
  split; [exact FO|]. split; [exact DC'|]. split; [rewrite EKV'; exact EKV|].
  split; [apply (OUTLE_trans _ s10); [apply OUTLE_out; rewrite Estrm10; reflexivity | exact Ho']|].
  split; [rewrite EPF'; exact EPF|].
  split; [rewrite Estr'; exact Estr10|]. split; [rewrite Elook'; exact Elook10|]. split; [rewrite Ebs'; exact Ebs10|].
  split; [rewrite Eml'; exact Eml10|]. split; [rewrite Ewin'; exact Ewin10|].
  split; [rewrite Esn'; exact Esn10|]. split; [exact Hpa|].
  rewrite Eain, Enin, Estrm10. unfold cset_data_type; cbn. split; reflexivity.
Qed.

Theorem flush_block_only_facts : forall c0 s last,
  FB_CALL -> C0OK c0 -> dwf s -> SV c0 s -> DXX s -> fb_entry s last -> ds_status s <> FINISH_STATE -> dmode s <> 0 -> BND s ->
  let s' := flush_block_only s last in
  flush_ok s last
  /\ DC c0 s' /\ KV s' = KV s /\ OUTLE s s' /\ PF s' = PF s
  /\ ds_strstart s' = ds_strstart s /\ ds_lookahead s' = ds_lookahead s /\ ds_block_start s' = ds_strstart s
  /\ ds_match_length s' = ds_match_length s /\ ds_window s' = ds_window s
  /\ ds_sym_next s' = 0
  /\ (ds_pending s' = 0 \/ cs_avail_out (ds_strm s') = 0)
  /\ cs_avail_in (ds_strm s') = cs_avail_in (ds_strm s) /\ cs_next_in (ds_strm s') = cs_next_in (ds_strm s).
Proof.
  intros c0 s last HFB HC0 D V XX FE Hst Hm B s'.
  pose proof (flush_block_only_factsW c0 s last HFB HC0 D V XX FE Hst Hm) as H. cbv zeta in H. subst s'.
  destruct H as (FO & DC' & HK' & Ho' & EPF & Estr' & Elook' & Ebs' & Eml' & Ewin' & Esn' & Hpa & Eain & Enin).
  split; [exact FO|]. split; [| exact (conj HK' (conj Ho' (conj EPF (conj Estr' (conj Elook' (conj Ebs' (conj Eml' (conj Ewin' (conj Esn' (conj Hpa (conj Eain Enin)))))))))))].
  pose proof (PF_fields _ _ EPF) as (_ & (_ & _ & _ & Ema & _) & (_ & _ & Ehd & Epv & Ehs & Ewm & _) & (_ & _ & _ & _ & _ & _ & _ & Ems & EKV)).
  pose proof (KV_fields _ _ EKV) as (Ews & _).
  apply (DCW_DC c0 _ DC'). apply (BND_same s); try assumption. exact (dmode_PF _ _ EPF).
Qed.

Lemma DC_fb_entry : forall c0 s last, C0OK c0 -> DC c0 s -> ds_pending s = 0 -> dmode s <> 0 -> 0 <= last <= 1 ->
  fb_entry s last.
Proof.
  intros c0 s last HC0 [[D X] V] Hp Hm Hlast.
  pose proof (dwf_sizes s D) as (Sw & Sh & Sl & _).
  pose proof (df_pend _ D) as Pd. pose proof (df_bi _ D) as Bi. pose proof (dx_biv _ X) as Bv. pose proof (dx_pout0 _ X Hp) as Po.
  pose proof (sv_dt _ _ V) as Dt. pose proof (sv_tout _ _ V) as To. pose proof (sv_aout _ _ V) as Ao. pose proof (sv_out _ _ V) as Ou.
  pose proof (c0_out _ HC0) as O0. pose proof (c0_aout _ HC0) as A0. rewrite O0 in Ou. unfold zlen in Ou. cbn [length Z.of_nat] in Ou.
  pose proof (zlen_nonneg (cs_out_rev (ds_strm s))) as Zl. unfold zlen in Zl.
  pose proof (df_level _ D) as Lv. pose proof (df_strategy _ D) as Sy. unfold Z_FIXED in Sy.
  pose proof (dx_ext _ X Hm) as He. pose proof (dx_nsym _ X) as Hn. pose proof (dx_ma _ X) as Hma.
  pose proof (df_strstart _ D) as Hstr. pose proof (df_look _ D) as Hlook. pose proof (df_sl _ D) as Hsl.
  assert (Hl : ds_level s <> 0) by (intros E0; apply Hm; unfold dmode; rewrite E0; reflexivity).
  constructor.
  - exact Hlast.
  - clear - He Hn Hma Sl. lia.
  - clear - He Hn Hma Sl Hstr. lia.
  - clear - Hstr Hlook Hsl. lia.
  - clear - Hstr Hlook Hsl. lia.
  - clear - Sw. lia.
  - exact (df_wl _ D).
  - exact (df_wb _ D).
  - clear - Lv Hl. lia.
  - exact Sy.
  - exact Dt.
  - exact Sl.
  - exact (df_bl _ D).
  - exact (df_symend _ D).
  - exact Hp.
  - exact Po.
  - clear - Bv Bi. lia.
  - clear - Bi. lia.
  - rewrite (df_bl _ D). exact (df_bb _ D).
  - rewrite To. apply wrap64_range'.
  - clear - Ao Ou A0 Zl. lia.
  - exact (dx_sn _ X).
  - clear - Hn. lia.
  - exact (dx_syms _ X).
  - exact (dx_hist _ X).
  - exact (dx_opt _ X).
  - exact (dx_stat _ X).
  - exact (df_tl _ D).
  - exact (dx_tfc _ X).
  - exact (dx_tdl _ X).
  - exact (dx_depth _ X).
  - exact (dx_blc _ X).
  - exists (ds_hash_bits s - 1). exact (df_lbs _ D).
Qed.

Lemma fb_entry_intro : forall c0 s last, C0OK c0 -> dwf s -> SV c0 s ->
  ds_pending s = 0 -> ds_pending_out s = 0 -> ds_bi_valid s <= 7 ->
  BQ s -> nsym s <= ds_lit_bufsize s - 1 -> ds_opt_len s = 0 -> ds_static_len s = 0 ->
  (forall t i, 0 <= arr_get (tree_fc s t) i < 65536) -> (forall t i, 0 <= arr_get (tree_dl s t) i < 65536) ->
  (forall i, 0 <= arr_get (ds_depth s) i < 256) -> (forall i, 0 <= i < 16 -> 0 <= arr_get (ds_bl_count s) i < 65536) ->
  ds_level s <> 0 -> 0 <= ds_strstart s - ds_block_start s <= 258 * nsym s + 1 -> 0 <= last <= 1 ->
  fb_entry s last.
Proof.
  intros c0 s last HC0 D V Hp Po Bv (Q1 & Q2 & Q3 & Q4) Hn Hol Hsl Htfc Htdl Hdep Hblc Hl He Hlast.
  pose proof (dwf_sizes s D) as (Sw & Sh & Sl & _).
  pose proof (df_bi _ D) as Bi.
  pose proof (sv_dt _ _ V) as Dt. pose proof (sv_tout _ _ V) as To. pose proof (sv_aout _ _ V) as Ao. pose proof (sv_out _ _ V) as Ou.
  pose proof (c0_out _ HC0) as O0. pose proof (c0_aout _ HC0) as A0. rewrite O0 in Ou. unfold zlen in Ou. cbn [length Z.of_nat] in Ou.
  pose proof (zlen_nonneg (cs_out_rev (ds_strm s))) as Zl. unfold zlen in Zl.
  pose proof (df_level _ D) as Lv. pose proof (df_strategy _ D) as Sy. unfold Z_FIXED in Sy.
  pose proof (df_strstart _ D) as Hstr. pose proof (df_look _ D) as Hlook. pose proof (df_sl _ D) as Hsl'.
  constructor.
  - exact Hlast.
  - clear - He Hn Q2 Sl. lia.
  - clear - He Hn Q2 Sl Hstr. lia.
  - clear - Hstr Hlook Hsl'. lia.
  - clear - Hstr Hlook Hsl'. lia.
  - clear - Sw. lia.
  - exact (df_wl _ D).
  - exact (df_wb _ D).
  - clear - Lv Hl. lia.
  - exact Sy.
  - exact Dt.
  - exact Sl.
  - exact (df_bl _ D).
  - exact (df_symend _ D).
  - exact Hp.
  - exact Po.
  - clear - Bv Bi. lia.
  - clear - Bi. lia.
  - rewrite (df_bl _ D). exact (df_bb _ D).
  - rewrite To. apply wrap64_range'.
  - clear - Ao Ou A0 Zl. lia.
  - exact Q1.
  - clear - Hn Q2. lia.
  - exact Q3.
  - exact Q4.
  - exact Hol.
  - exact Hsl.
  - exact (df_tl _ D).
  - exact Htfc.
  - exact Htdl.
  - exact Hdep.
  - exact Hblc.
  - exists (ds_hash_bits s - 1). exact (df_lbs _ D).
Qed.
