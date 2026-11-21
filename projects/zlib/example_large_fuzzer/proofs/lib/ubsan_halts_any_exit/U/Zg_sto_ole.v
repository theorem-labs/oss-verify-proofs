(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dkit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Zg_sto_model.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel
     RefDeflFastM RefDeflStored2 RefDeflStored4 RefDeflStored5 RefDeflStored6 RefDeflStored7 RefDeflStored8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Notation OL s := (length (cs_out_rev (ds_strm s))).

Lemma fst_pr : forall {A B} (a : A) (b : B), fst (a, b) = a. Proof. reflexivity. Qed.
Lemma snd_pr : forall {A B} (a : A) (b : B), snd (a, b) = b. Proof. reflexivity. Qed.

Lemma ole_fp_tail : forall s len, (OL s <= OL (fp_tail s len))%nat.
Proof.
  intros s len. unfold fp_tail. cbv zeta.
  destruct (ds_pending s - len =? 0); dsred; rewrite olen_cs_emit; dsred; lia.
Qed.

Lemma ole_fp : forall s, (OL s <= OL (flush_pending s))%nat.
Proof.
  intros s. rewrite flush_pending_eq. cbv zeta. destruct (bits_keep s) as (E & _).
  destruct (fp_len (tr_flush_bits s) =? 0).
  - rewrite E. lia.
  - eapply Nat.le_trans; [| apply ole_fp_tail]. rewrite E. lia.
Qed.

Lemma ole_emit1 : forall s flush, (OL s <= OL (st_emit1 s flush))%nat.
Proof.
  intros s flush. unfold st_emit1.
  eapply Nat.le_trans; [| apply ole_fp].
  destruct (sb_patch_keep (tr_stored_block s None 0 (sb_lastv s flush)) (sb_len s)) as (E2 & _). rewrite E2.
  destruct (sb_keep s None 0 (sb_lastv s flush)) as (E1 & _). rewrite E1. lia.
Qed.

Lemma ole_lcopy : forall s len, (OL s <= OL (st_lcopy s len))%nat.
Proof. intros s len. unfold st_lcopy. dsred. rewrite olen_cs_emit. dsred. lia. Qed.

Lemma ole_copy : forall s left len, (OL s <= OL (fst (st_copy s left len)))%nat.
Proof. intros s left len. unfold st_copy. destruct (negb (left =? 0)); [rewrite ?fst_pr; apply ole_lcopy| rewrite ?fst_pr; lia]. Qed.

Lemma ole_read_buf_out : forall s n, (OL s <= OL (fst (read_buf s RB_next_out n)))%nat.
Proof.
  intros s n. unfold read_buf. cbv beta iota zeta.
  destruct ((if n <? cs_avail_in (ds_strm s) then n else cs_avail_in (ds_strm s)) =? 0); [rewrite ?fst_pr; lia|].
  destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]; rewrite ?fst_pr; dsred; rewrite ?olen_cs_emit; dsred; lia.
Qed.

Lemma ole_read_buf_win : forall s off n, OL (fst (read_buf s (RB_window off) n)) = OL s.
Proof.
  intros s off n. unfold read_buf. cbv beta iota zeta.
  destruct ((if n <? cs_avail_in (ds_strm s) then n else cs_avail_in (ds_strm s)) =? 0); [rewrite ?fst_pr; reflexivity|].
  dsred. destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]; rewrite ?fst_pr; dsred; reflexivity.
Qed.

Lemma ole_rdo : forall s n, (OL s <= OL (st_rdo s n))%nat.
Proof.
  intros s n. unfold st_rdo. destruct (negb (n =? 0)); [| lia].
  destruct (read_buf s RB_next_out n) as [s1 k] eqn:E.
  pose proof (ole_read_buf_out s n) as H. rewrite E, ?fst_pr in H. dsred. exact H.
Qed.

Lemma ole_trip : forall s flush, (OL s <= OL (st_trip s flush))%nat.
Proof.
  intros s flush. unfold st_trip. cbv zeta.
  eapply Nat.le_trans; [apply (ole_emit1 s flush)|].
  eapply Nat.le_trans; [apply (ole_copy _ (sb_left s) (sb_len s))|]. apply ole_rdo.
Qed.

Lemma ole_loop : forall f s flush mb, (OL s <= OL (fst (deflate_stored_loop f s flush mb)))%nat.
Proof.
  induction f as [|f IH]; intros s flush mb; [cbn [deflate_stored_loop]; rewrite ?fst_pr; lia|].
  rewrite sloop_S'. destruct (sb_broke s flush mb); [rewrite ?fst_pr; lia|].
  destruct (sb_lastv s flush =? 0); [| rewrite ?fst_pr; apply ole_trip].
  eapply Nat.le_trans; [apply (ole_trip s flush)| apply IH].
Qed.

Lemma ole_wupd : forall s used, OL (st_wupd s used) = OL s.
Proof.
  intros s used. unfold st_wupd. destruct (negb (used =? 0)); [|reflexivity].
  destruct (ds_w_size s <=? used); [dsred; reflexivity|]. cbv zeta.
  destruct (ds_window_size s - ds_strstart s <=? used); dsred; [|reflexivity].
  destruct (ds_matches _ <? 2); dsred; destruct (_ <? ds_insert _); dsred; reflexivity.
Qed.

Lemma ole_hw : forall s, OL (hw_st s) = OL s.
Proof. intros s. unfold hw_st. destruct (_ <? _); dsred; reflexivity. Qed.

Lemma ole_slide3 : forall s have, OL (fst (st_slide3 s have)) = OL s.
Proof.
  intros s have. unfold st_slide3. destruct (_ && _); [|rewrite ?fst_pr; reflexivity]. cbv zeta.
  destruct (ds_matches _ <? 2); dsred; destruct (_ <? ds_insert _); rewrite ?fst_pr; dsred; reflexivity.
Qed.

Lemma ole_fillw : forall s have, OL (st_fillw s have) = OL s.
Proof.
  intros s have. unfold st_fillw. destruct (negb (have =? 0)); [|reflexivity].
  destruct (read_buf s (RB_window (ds_strstart s)) have) as [s1 k] eqn:E.
  pose proof (ole_read_buf_win s (ds_strstart s) have) as H. rewrite E, ?fst_pr in H. dsred. exact H.
Qed.

Lemma ole_final : forall s flush, (OL s <= OL (fst (st_final s flush)))%nat.
Proof.
  intros s flush. unfold st_final. cbv zeta. destruct (_ || _); rewrite ?fst_pr; [|lia].
  eapply Nat.le_trans; [| apply ole_fp]. dsred.
  match goal with |- (_ <= length (cs_out_rev (ds_strm (tr_stored_block ?a ?b ?c ?d))))%nat => destruct (sb_keep a b c d) as (E & _); rewrite E end.
  lia.
Qed.
