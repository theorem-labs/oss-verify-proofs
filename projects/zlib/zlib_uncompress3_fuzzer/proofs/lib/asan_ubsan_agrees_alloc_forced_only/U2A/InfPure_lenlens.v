(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees InftreesCoverage ItCovIface InflateInv InflateInvTab.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AArr InfPure InfPure_w7 ItAPure ItBridgeA InfPure_table.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma ll_mode_facts : forall cx st lf cf, sinv cx st lf cf -> t_mode st = LENLENS ->
  4 <= t_ncode st /\ t_ncode st <= 19 /\ 0 <= t_shave st /\ t_shave st <= 19 /\ (forall j, 0 <= j < t_shave st -> lf (order_f j) <= 7)
  /\ (forall i, 0 <= i < 320 -> 0 <= lf i < 65536).
Proof.
  intros cx st lf cf (R & _ & _ & Mo) Hm.
  assert (ML : t_mode st = LENLENS -> 4 <= t_ncode st /\ t_ncode st <= 19 /\ t_shave st <= 19 /\
            257 <= t_nlen st /\ t_nlen st <= 286 /\ 1 <= t_ndist st /\ t_ndist st <= 30 /\
            (forall j0, 0 <= j0 < t_shave st -> lf (arr_get order_a j0) <= 7)) by (unfold MODE in Mo; tauto).
  destruct (ML Hm) as (A1 & A2 & A3 & _ & _ & _ & _ & A8).
  unfold IDefs.RNG in R. cbv zeta in R. destr_conj R.
  match goal with H : forall i, _ -> 0 <= lf i < 65536 |- _ => rename H into Rlf end.
  split; [exact A1|]. split; [exact A2|]. split; [lia|]. split; [exact A3|]. split; [exact A8| exact Rlf].
Qed.

Lemma lens7_upd : forall (lf : Z -> Z) j v, (forall i, 0 <= i < j -> lf (order_f i) <= 7) -> v <= 7 ->
  forall i, 0 <= i < j + 1 -> fupd lf (order_f j) v (order_f i) <= 7.
Proof.
  intros lf j v H Hv i Hi. unfold fupd. destruct (Z.eqb_spec (order_f i) (order_f j)) as [E|NE]; [exact Hv|].
  apply H. assert (i <> j) by (intros ->; apply NE; reflexivity). lia.
Qed.
Lemma lens_rng_upd : forall (lf : Z -> Z) k v, (forall i, 0 <= i < 320 -> 0 <= lf i < 65536) -> 0 <= v < 65536 ->
  forall i, 0 <= i < 320 -> 0 <= fupd lf k v i < 65536.
Proof. intros lf k v H Hv i Hi. unfold fupd. destruct (i =? k); [exact Hv| apply H; exact Hi]. Qed.

Lemma sinv_have : forall cx st lf cf j lf',
  sinv cx st lf cf -> t_mode st = LENLENS -> 0 <= j -> j <= 19 ->
  (forall i, 0 <= i < 320 -> 0 <= lf' i < 65536) -> (forall i, 0 <= i < j -> lf' (order_f i) <= 7) ->
  sinv cx (st_sh st j) lf' cf /\ meas cx (st_sh st j) <= meas cx st.
Proof.
  intros cx st lf cf j lf' SI Hm Hj0 Hj1 Rlf' L7. pose proof SI as (R & _).
  unfold IDefs.RNG in R. cbv zeta in R. destr_conj R.
  exact (sinv_ll cx st lf cf (t_cin st) (t_hold st) (t_bits st) j lf' SI Hm ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
           ltac:(lia) Hj0 Hj1 Rlf' L7).
Qed.
