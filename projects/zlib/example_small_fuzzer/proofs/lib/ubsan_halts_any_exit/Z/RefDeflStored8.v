(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCrc32_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefAdler_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefFlushBlk13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefFlushBlk13.RefTrStored_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefSendTree4.RefTrFlushBits_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFast1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflFast6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflStored1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflStored4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflStored5.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflStored5.RefDeflStored2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflStored7.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflStored7.RefDeflStored3.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflStored5.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflStored7.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflStored7.RefDeflStored6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflStored7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
Variable S : Z.
Variable p : ds_ptrs.
Variable zp : zs_ptrs.
Variable ds : deflate_state.
Variable flush : Z.
Variable sp : Z.
Local Notation W := (p_window p).
Local Notation PV := (p_prev p).
Local Notation HD := (p_head p).
Local Notation PB := (p_pending_buf p).
Local Notation strm := (p_strm p).
Local Notation INP := (zp_in zp).
Local Notation OUTB := (zp_out zp).
Local Notation ws := (ds_w_size ds).
Local Notation hs := (ds_hash_size ds).
Local Notation lbs := (ds_lit_bufsize ds).
Local Notation PBL := (ds_lit_bufsize ds * 4).
Local Notation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Notation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Notation AV0 := (cs_avail_out (ds_strm ds)).
Local Notation SP := (sp - 128).
Local Notation MB := (MBv ds).

Local Ltac keeps_tac := constructor; intros; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end.
Lemma keeps_block_start : keeps ds_block_start true true. Proof. keeps_tac. Qed.
Lemma keeps_strstart : keeps ds_strstart true true.       Proof. keeps_tac. Qed.
Lemma keeps_wrap : keeps ds_wrap true true.               Proof. keeps_tac. Qed.
Lemma keeps_pending_buf_size : keeps ds_pending_buf_size true true. Proof. keeps_tac. Qed.
Lemma keeps_insert : keeps ds_insert true true.           Proof. keeps_tac. Qed.
Lemma keeps_matches' : keeps ds_matches true false.
Proof. constructor; intros; try discriminate; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.
Lemma keeps_high_water : keeps ds_high_water true true.   Proof. keeps_tac. Qed.
Lemma keeps_window_size : keeps ds_window_size true true. Proof. keeps_tac. Qed.

Lemma sb_keep : forall s buf len last,
  let s1 := tr_stored_block s buf len last in
  ds_strm s1 = ds_strm s /\ ds_window s1 = ds_window s /\ ds_w_size s1 = ds_w_size s /\ ds_hash_size s1 = ds_hash_size s
  /\ ds_lit_bufsize s1 = ds_lit_bufsize s /\ ds_block_start s1 = ds_block_start s /\ ds_strstart s1 = ds_strstart s.
Proof.
  intros s buf len last s1. subst s1.
  rewrite (k_tr_stored_block _ _ _ keeps_strm eq_refl), (k_tr_stored_block _ _ _ keeps_window eq_refl),
    (k_tr_stored_block _ _ _ keeps_w_size eq_refl), (k_tr_stored_block _ _ _ keeps_hash_size eq_refl),
    (k_tr_stored_block _ _ _ keeps_lit_bufsize eq_refl), (k_tr_stored_block _ _ _ keeps_block_start eq_refl),
    (k_tr_stored_block _ _ _ keeps_strstart eq_refl).
  repeat split; reflexivity.
Qed.

Lemma sb_keep2 : forall s buf len last,
  let s1 := tr_stored_block s buf len last in
  ds_wrap s1 = ds_wrap s /\ ds_pending_buf_size s1 = ds_pending_buf_size s /\ ds_insert s1 = ds_insert s
  /\ ds_high_water s1 = ds_high_water s /\ ds_window_size s1 = ds_window_size s.
Proof.
  intros s buf len last s1. subst s1.
  rewrite (k_tr_stored_block _ _ _ keeps_wrap eq_refl), (k_tr_stored_block _ _ _ keeps_pending_buf_size eq_refl),
    (k_tr_stored_block _ _ _ keeps_insert eq_refl), (k_tr_stored_block _ _ _ keeps_high_water eq_refl),
    (k_tr_stored_block _ _ _ keeps_window_size eq_refl).
  repeat split; reflexivity.
Qed.

Lemma bits_keep : forall s,
  let s1 := tr_flush_bits s in
  ds_strm s1 = ds_strm s /\ ds_window s1 = ds_window s /\ ds_w_size s1 = ds_w_size s /\ ds_hash_size s1 = ds_hash_size s
  /\ ds_lit_bufsize s1 = ds_lit_bufsize s /\ ds_block_start s1 = ds_block_start s /\ ds_strstart s1 = ds_strstart s
  /\ ds_wrap s1 = ds_wrap s /\ ds_pending_out s1 = ds_pending_out s.
Proof.
  intros s s1. subst s1. destruct (tr_flush_bits_cases s) as [E|[E|E]]; rewrite E; unfold put_byte; dsred; repeat split; reflexivity.
Qed.

Lemma fp_tail_keep : forall s len,
  let s1 := fp_tail s len in
  ds_window s1 = ds_window s /\ ds_w_size s1 = ds_w_size s /\ ds_hash_size s1 = ds_hash_size s
  /\ ds_lit_bufsize s1 = ds_lit_bufsize s /\ ds_block_start s1 = ds_block_start s /\ ds_strstart s1 = ds_strstart s
  /\ cs_avail_in (ds_strm s1) = cs_avail_in (ds_strm s) /\ cs_next_in (ds_strm s1) = cs_next_in (ds_strm s)
  /\ cs_input (ds_strm s1) = cs_input (ds_strm s) /\ ds_wrap s1 = ds_wrap s /\ cs_adler (ds_strm s1) = cs_adler (ds_strm s)
  /\ cs_total_in (ds_strm s1) = cs_total_in (ds_strm s) /\ ds_bi_valid s1 = ds_bi_valid s.
Proof. intros s len s1. subst s1. unfold fp_tail. destruct (_ =? 0); dsred; repeat split; reflexivity. Qed.

Lemma sb_patch_keep : forall s len,
  let s1 := sb_patch s len in
  ds_strm s1 = ds_strm s /\ ds_window s1 = ds_window s /\ ds_w_size s1 = ds_w_size s /\ ds_hash_size s1 = ds_hash_size s
  /\ ds_lit_bufsize s1 = ds_lit_bufsize s /\ ds_block_start s1 = ds_block_start s /\ ds_strstart s1 = ds_strstart s
  /\ ds_pending s1 = ds_pending s /\ ds_wrap s1 = ds_wrap s /\ ds_bi_valid s1 = ds_bi_valid s.
Proof. intros s len s1. subst s1. unfold sb_patch. dsred. repeat split; reflexivity. Qed.



Lemma st_emit1_eq : forall X,
  st_emit1 X flush
  = (let X3 := tr_flush_bits (sb_patch (tr_stored_block X None 0 (sb_lastv X flush)) (sb_len X)) in
     if fp_len X3 =? 0 then X3 else fp_tail X3 (fp_len X3)).
Proof. intros X. unfold st_emit1. rewrite flush_pending_eq. reflexivity. Qed.

Lemma rb_mid_facts : forall s n,
  let s7 := rb_mid s n in
  cs_next_in (ds_strm s7) = cs_next_in (ds_strm s) /\ cs_avail_in (ds_strm s7) = cs_avail_in (ds_strm s) - n
  /\ cs_total_in (ds_strm s7) = cs_total_in (ds_strm s) /\ cs_total_out (ds_strm s7) = cs_total_out (ds_strm s)
  /\ cs_avail_out (ds_strm s7) = cs_avail_out (ds_strm s) /\ cs_out_rev (ds_strm s7) = cs_out_rev (ds_strm s)
  /\ ds_bi_valid s7 = ds_bi_valid s /\ cs_input (ds_strm s7) = cs_input (ds_strm s).
Proof.
  intros s n s7. subst s7. unfold rb_mid.
  destruct (ds_wrap s =? 1); [| destruct (ds_wrap s =? 2)]; dsred; repeat split; reflexivity.
Qed.

Lemma st_rdo_0 : forall s, st_rdo s 0 = s.
Proof. intros s. reflexivity. Qed.

Lemma st_copy_snd_range : forall s left len, 0 <= left -> 0 <= len -> 0 <= snd (st_copy s left len) <= len.
Proof.
  intros s left len Hl H. unfold st_copy, lc_len. destruct (negb (left =? 0)); cbn [snd]; [| lia].
  destruct (Z.ltb_spec len left); lia.
Qed.

End Walk.
