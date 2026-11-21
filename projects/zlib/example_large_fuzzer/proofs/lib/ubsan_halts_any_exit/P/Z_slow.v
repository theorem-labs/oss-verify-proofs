(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_defl_iface Z_slow_model Z_slow_frame Z_slow_kit
  Z_slow_fbA Z_slow_fbB Z_slow_fbC Z_slow_fill Z_slow_hash Z_slow_dist2 Z_slow_dist Z_slow_lit Z_slow_litT Z_slow_misc.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk FillWinModel
  RefDeflFast1 RefDeflFastM RefDeflFast6 RefDeflSlow2 RefDeflSlow3 RefDeflSlow5 RefDeflSlow6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma st_bflush_true : forall s,
  st_bflush s true = (flush_block_only s 0, if cs_avail_out (ds_strm (flush_block_only s 0)) =? 0 then LRet need_more else LCont).
Proof. intros s. unfold st_bflush, flush_block. cbv zeta. destruct (_ =? 0); reflexivity. Qed.

Lemma st_bflush_false : forall s, st_bflush s false = (s, LCont).
Proof. reflexivity. Qed.

Lemma fst_pr : forall {A B} (a : A) (b : B), fst (a, b) = a. Proof. reflexivity. Qed.
Lemma snd_pr : forall {A B} (a : A) (b : B), snd (a, b) = b. Proof. reflexivity. Qed.

Lemma deflate_tail_finish_eq : forall t,
  deflate_tail t Z_FINISH = (flush_block_only t 1, if cs_avail_out (ds_strm (flush_block_only t 1)) =? 0 then finish_started else finish_done).
Proof. intros t. unfold deflate_tail, flush_block. change (Z_FINISH =? Z_FINISH) with true. cbv iota zeta. destruct (_ =? 0); reflexivity. Qed.

Section SLOW.
Variables (L : dlay) (flush : Z) (inp : list Z) (rest0 : list byte) (lo : Z) (r : sregs) (F : bvmap 5 word) (fc : bv 32) (me : mem).
Hypothesis CTX : slow_ctx L inp rest0 lo r me.
Hypothesis HFW : fill_window_stmt.
Hypothesis HTFBLK : tr_flush_block_stmt.
Hypothesis HTFB : tr_flush_bits_stmt.
Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH.

Local Notation SKq := (SK L flush rest0 lo r F fc me).
Local Notation SKr := (SKret L flush rest0 lo r F fc me).
Local Notation ROOM s := (Box (OUT s <= length rest0)%nat).




Lemma slow_tail1 : forall (Q : machine_state -> Prop) (X1 : deflate_state),
  0 <= ds_match_available X1 <= 1 ->
  (ds_match_available X1 = 0 -> SKq Q 0x19e9c X1) ->
  (ds_match_available X1 <> 0 -> SKq Q 0x19e20 X1) ->
  SKq Q Z_SLOW_TAIL X1.
Proof.
  intros Q X1 Rma K0 K1. unfold SK. intros until m'. intros SI. pose proof SI as (DR & _).
  destruct DR as [_ ST]. destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. open_A GA. unfold slowR, Z_SLOW_TAIL.
  zs. zstep. if_cases KM; zify_cond KM; rewrite ?unsigned_lit in KM by lia.
  - eapply (K0 KM). exact SI.
  - eapply (K1 KM). exact SI.
Qed.


End SLOW.


