(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz DeflateBlk Deflate DeflateSafe DeflateOverlay.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflateRel RefDeflSafeG RefDeflSafeFB RefDeflSafeLF RefDeflSafeL5.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeI1 RefDeflSafeI2 RefDeflSafeI3 RefDeflSafeI4 RefDeflSafeI6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import BoundFw BoundSlow BoundCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Record PAT (s : deflate_state) : Prop := {
  pt_level : ds_level s = 6;
  pt_strategy : ds_strategy s = 0;
  pt_wrap : ds_wrap s = 1 \/ (ds_wrap s = -1 /\ ds_status s = FINISH_STATE);
  pt_status : ds_status s = INIT_STATE \/ ds_status s = BUSY_STATE \/ ds_status s = FINISH_STATE;
  pt_gz : ds_gzhead s = 0;
  pt_ins : ds_insert s = 0 \/ ds_status s = FINISH_STATE;
  pt_lbs : ds_lit_bufsize s = 16384;
  pt_ws : ds_w_size s = 32768 }.



Lemma PF_zhdr_pre : forall s,
  exists t, zhdr_st s = set_status t BUSY_STATE /\ PF t = PF s.
Proof.
  intros s. unfold zhdr_st. cbv zeta.
  match goal with |- context [putShortMSB s ?hd] => generalize hd end. intros hdr.
  eexists. split; [reflexivity|].
  match goal with |- PF (set_strm ?u _) = _ => assert (E : PF u = PF s) end.
  { destruct (negb (ds_strstart (putShortMSB s hdr) =? 0)); reflexivity. }
  rewrite <- E. reflexivity.
Qed.

Lemma PF_trailer : forall s, PF (trailer_st s) = PF s.
Proof. intros s. unfold trailer_st. cbv zeta. destruct (ds_wrap s =? 2); reflexivity. Qed.

Section CallP.
  Variable c0 : cstrm.
  Variable s0 : deflate_state.
  Hypothesis HC0 : C0OK' c0.
  Hypothesis Hs0 : ds_strm s0 = c0.
  Hypothesis D0 : dwf s0.
  Let HC0w : C0OK c0 := c0'_ok _ HC0.
  Local Abbreviation ST := (RefDeflSafeI4.ST c0 s0).

  Definition P2 (s : deflate_state) : Prop := ST s /\ PAT s.

End CallP.


Lemma pow2_inj_small : forall a b, 0 <= a <= 16 -> 0 <= b <= 16 -> 2 ^ a = 2 ^ b -> a = b.
Proof.
  intros a b Ha Hb E. destruct (Z.lt_trichotomy a b) as [L|[L|L]]; [| exact L |].
  - pose proof (Z.pow_lt_mono_r 2 a b ltac:(lia) ltac:(lia) L). lia.
  - pose proof (Z.pow_lt_mono_r 2 b a ltac:(lia) ltac:(lia) L). lia.
Qed.

