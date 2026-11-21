(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require ZProg ZIface DeflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require DeflateLz DeflateBlk Deflate.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz.Trees OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateLz OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.DeflateBlk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.Deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import RefDeflFast6 RefDeflSlow6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma flush_block_0 : forall s, snd (flush_block s 0) = None \/ snd (flush_block s 0) = Some need_more.
Proof. intros s. unfold flush_block. destruct (_ =? 0); cbn; auto. Qed.

Lemma flush_block_1 : forall s, snd (flush_block s 1) = None \/ snd (flush_block s 1) = Some finish_started.
Proof. intros s. unfold flush_block. destruct (_ =? 0); cbn; auto. Qed.

Lemma st_decide_ret : forall s bs, snd (st_decide s) = LRet bs -> bs = need_more.
Proof.
  intros s bs. unfold st_decide. destruct (dist_cond s).
  - unfold st_bflush. destruct (snd (st_sdist s)); [|cbn; intros H; discriminate H].
    destruct (flush_block_0 (fst (st_sdist s))) as [E|E];
      destruct (flush_block (fst (st_sdist s)) 0) as [s' r]; cbn [snd] in E; subst r; cbn; intros H; inversion H; reflexivity.
  - destruct (negb _).
    + unfold st_slit. destruct (tr_tally_lit _ _) as [s1 b]. cbn [snd]. destruct (_ =? 0); intros H; inversion H; reflexivity.
    + cbn. intros H; discriminate H.
Qed.

Lemma slow_body_ret : forall s flush bs, snd (deflate_slow_body s flush) = LRet bs -> bs = need_more.
Proof.
  intros s flush bs. rewrite st_sbody_eq. unfold st_sbody, st_fill.
  destruct (ds_lookahead s <? MIN_LOOKAHEAD).
  - destruct ((ds_lookahead (fill_window s) <? MIN_LOOKAHEAD) && (flush =? Z_NO_FLUSH)); cbn [fst snd].
    + intros H. inversion H. reflexivity.
    + destruct (ds_lookahead (fill_window s) =? 0); cbn [fst snd]; [intros H; discriminate H|].
      unfold st_srest. apply st_decide_ret.
  - cbn [fst snd]. unfold st_srest. apply st_decide_ret.
Qed.

Lemma slow_loop_ret : forall fuel s flush bs, snd (deflate_slow_loop fuel s flush) = Some bs -> bs = need_more.
Proof.
  induction fuel as [|f IH]; intros s flush bs; cbn [deflate_slow_loop]; [intros H; discriminate H|].
  pose proof (slow_body_ret s flush) as B. destruct (deflate_slow_body s flush) as [s1 o]. cbn [snd] in B.
  destruct o as [| |b]; [apply IH | cbn; intros H; discriminate H | cbn; intros H; inversion H; subst; apply B; reflexivity].
Qed.

Lemma deflate_tail_bs : forall s flush,
  (flush = Z_FINISH -> snd (deflate_tail s flush) = finish_started \/ snd (deflate_tail s flush) = finish_done)
  /\ (flush <> Z_FINISH -> snd (deflate_tail s flush) = need_more \/ snd (deflate_tail s flush) = block_done).
Proof.
  intros s flush. unfold deflate_tail. destruct (Z.eqb_spec flush Z_FINISH) as [E|N]; split; intros H; try contradiction.
  - destruct (flush_block_1 s) as [F|F]; destruct (flush_block s 1) as [s' r]; cbn [snd] in F; subst r; cbn; auto.
  - destruct (negb _); [|cbn; auto].
    destruct (flush_block_0 s) as [F|F]; destruct (flush_block s 0) as [s' r]; cbn [snd] in F; subst r; cbn; auto.
Qed.

Lemma deflate_slow_bs : forall s flush,
  let b := snd (deflate_slow s flush) in
  (flush = Z_FINISH -> b = need_more \/ b = finish_started \/ b = finish_done)
  /\ (flush <> Z_FINISH -> b = need_more \/ b = block_done).
Proof.
  intros s flush. cbv zeta. rewrite deflate_slow_eq.
  pose proof (slow_loop_ret (lz_fuel s) s flush) as L.
  destruct (snd (deflate_slow_loop (lz_fuel s) s flush)) as [bs|].
  - cbn [snd]. rewrite (L bs eq_refl). split; intros _; auto.
  - cbv zeta. match goal with |- context [deflate_tail ?x flush] => pose proof (deflate_tail_bs x flush) as [T1 T2] end.
    split; intros H; [destruct (T1 H); auto | destruct (T2 H); auto].
Qed.
