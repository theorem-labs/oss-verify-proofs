(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import InfPure InfPure_w7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma RNG_len_set : forall cx st lf cf l', IDefs.RNG cx st lf cf -> 0 <= l' <= t_length st ->
  IDefs.RNG cx (st_le st (t_mode st) l' (t_extra st)) lf cf.
Proof.
  intros cx st lf cf l' R HL.
  destruct st as [mode last flags cin cout hold bits out ret length offset extra lc dc lb db ncode nlen ndist shave nx whave wnext].
  unfold IDefs.RNG, st_le in *. icx_cbn. destr_conj R. split_conj; try assumption; lia.
Qed.

Lemma sinv_match_win : forall cx st lf cf, sinv cx st lf cf ->
  (c_w cx = 0 -> t_whave st = 0 /\ t_wnext st = 0) /\ (c_w cx <> 0 -> t_whave st <= 32768 /\ t_wnext st < 32768).
Proof.
  intros cx st lf cf (_ & W & _). unfold WIN in W. destruct W as (W0 & W1). split; [exact W0|].
  intros NZ. destruct (W1 NZ) as (A & B & _). unfold WIN_SIZE in *. lia.
Qed.
