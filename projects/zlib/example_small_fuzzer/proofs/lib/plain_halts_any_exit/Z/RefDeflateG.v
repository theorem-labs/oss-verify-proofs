(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.TreeMem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import FlushBlockModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateBlk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefTreesApi.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefTreesApi.RefBitsLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflBlkApi.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefCrc32_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefFillWin4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFillWin4.RefFillWin1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefFillWin4.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefTrFlushBits_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefSendTree4.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefSendTree4.RefTrAlign_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefFlushBlk13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefTrStored_run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require RefFlushBlk13.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFlushBlk13.RefFlushBlk1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefFlushBlk13.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFastM.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflateK.
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
Local Notation SP := (sp - 96).
Local Notation CST := (RefDeflateK.CST ds).



Local Notation LFW X := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.RefFillWin4.RefFillWin1.LF S SP p X).

Lemma cs_output_emit : forall st l, cs_output (cs_emit st l) = cs_output st ++ l.
Proof.
  intros st l. unfold cs_output, cs_emit. destruct st; cbn -[rev_append].
  rewrite !List.rev_append_rev, !app_nil_r, rev_app_distr, rev_involutive. reflexivity.
Qed.

Lemma length_cs_output : forall st, length (cs_output st) = length (cs_out_rev st).
Proof. intros st. unfold cs_output. rewrite List.rev_append_rev, app_nil_r, length_rev. reflexivity. Qed.




Definition ds_lzv (s : deflate_state) := (ds_window s, ds_prev s, ds_head s, ds_strm s, ds_sizes s, ds_pending_out s).

Lemma keeps_lzv : keeps ds_lzv true true.
Proof. constructor; intros; try match goal with tt : tree_id |- _ => destruct tt end; match goal with ss : deflate_state |- _ => destruct ss; reflexivity end. Qed.

Lemma tr_align_lzv : forall s, ds_lzv (tr_align s) = ds_lzv s.
Proof.
  intros s. unfold tr_align, send_code.
  rewrite (k_bi_flush ds_lzv true true keeps_lzv eq_refl), !(k_send_bits ds_lzv true true keeps_lzv eq_refl). reflexivity.
Qed.

Lemma tr_stored_block_lzv : forall s buf len last, ds_lzv (tr_stored_block s buf len last) = ds_lzv s.
Proof. intros. apply (k_tr_stored_block ds_lzv true true keeps_lzv eq_refl). Qed.


Lemma apart_from_mono : forall r r' l l',
  apart_from r l -> Forall2 (fun a b => fst a <= fst b /\ fst b + snd b <= fst a + snd a) l l' ->
  fst r <= fst r' -> fst r' + snd r' <= fst r + snd r ->
  apart_from r' l'.
Proof.
  intros r r' l l' H HF Hr1 Hr2. revert H. induction HF as [|a b l l' Hab HF IH]; intros H; [exact I|].
  destruct H as [H1 H2]. split; [| exact (IH H2)].
  unfold apart in *. destruct Hab as [Hab1 Hab2]. lia.
Qed.

Lemma apart_all_mono : forall l l',
  apart_all l -> Forall2 (fun a b => fst a <= fst b /\ fst b + snd b <= fst a + snd a) l l' -> apart_all l'.
Proof.
  intros l l' H HF. revert H. induction HF as [|a b l l' Hab HF IH]; intros H; [exact I|].
  destruct H as [H1 H2]. split; [| exact (IH H2)].
  destruct Hab as [Hab1 Hab2]. eapply apart_from_mono; [exact H1 | exact HF | lia | lia].
Qed.

Definition LZK (X X' : deflate_state) : Prop :=
  ds_sizes X' = ds_sizes X
  /\ arr_len (ds_window X') = arr_len (ds_window X) /\ arr_len (ds_prev X') = arr_len (ds_prev X)
  /\ arr_len (ds_head X') = arr_len (ds_head X) /\ arr_len (ds_pending_buf X') = arr_len (ds_pending_buf X)
  /\ cs_input (ds_strm X') = cs_input (ds_strm X)
  /\ Z.of_nat (length (cs_out_rev (ds_strm X'))) + cs_avail_out (ds_strm X')
     = Z.of_nat (length (cs_out_rev (ds_strm X))) + cs_avail_out (ds_strm X)
  /\ 0 <= cs_avail_out (ds_strm X')
  /\ (length (cs_out_rev (ds_strm X)) <= length (cs_out_rev (ds_strm X')))%nat.

End Walk.
