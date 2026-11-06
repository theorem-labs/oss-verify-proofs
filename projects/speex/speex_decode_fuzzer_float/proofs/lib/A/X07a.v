(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bt X1c1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1qy X1r2 X1qz X1nt X1rh X1re X1od X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X05m X0bf X065.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X122 X0wy.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X122 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wy.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Notation DECM := (speex_decode (St := pst) p_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M).
Local Notation DLOOP := (decode_loop (St := pst) p_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M).

Lemma prun_bits_remaining_M : forall (b : bits_st unit) q, prun (bits_remaining_M (St := pst) b) q = Some (speex_bits_remaining b, q).
Proof. intros b q. reflexivity. Qed.

Lemma dloop_step : forall n (st : dec_state unit) (b : bits_st unit) q r q',
prun (DLOOP (S n) st b) q = Some (r, q') ->
exists ret st1 b1 q1, prun (DECM st b 0) q = Some ((ret, st1, b1), q1) /\
( ((ret =? -1) || (ret =? -2) = true /\ r = (st1, b1) /\ q' = q1)
\/ ((ret =? -1) || (ret =? -2) = false /\ speex_bits_remaining b1 < 0 /\ r = (st1, b1) /\ q' = q1)
\/ ((ret =? -1) || (ret =? -2) = false /\ 0 <= speex_bits_remaining b1 /\ prun (DLOOP n st1 b1) q1 = Some (r, q'))).
Proof.
intros n st b q r q' H. cbn [decode_loop] in H. unfold h_decode in H.
rewrite prun_bind in H.
destruct (prun (DECM st b 0) q) as [[[[ret st1] b1] q1]|] eqn:ED; [| discriminate H].
exists ret, st1, b1, q1. split; [reflexivity|]. cbn beta iota in H.
destruct ((ret =? -1) || (ret =? -2)) eqn:ER.
- left. rewrite prun_ret in H. injection H as <- <-. split; [reflexivity| split; reflexivity].
- rewrite prun_bind, prun_bits_remaining_M in H. cbn beta iota in H.
destruct (Z.ltb_spec (speex_bits_remaining b1) 0) as [RN|RP].
+ right; left. rewrite prun_ret in H. injection H as <- <-. split; [reflexivity| split; [exact RN| split; reflexivity]].
+ right; right. split; [reflexivity| split; [exact RP| exact H]].
Qed.

Lemma dloop_appends : forall n (st : dec_state unit) (b : bits_st unit) q r q', prun (DLOOP n st b) q = Some (r, q') -> exists bs, p_err q' = p_err q ++ bs.
Proof.
induction n as [|n IH]; intros st b q r q' H.
- cbn [decode_loop] in H. rewrite prun_ret in H. injection H as _ <-. exists []. rewrite app_nil_r. reflexivity.
- destruct (dloop_step n st b q r q' H) as (ret & st1 & b1 & q1 & ED & CASES).
destruct (dec_appends_all st b q _ q1 ED) as (bs1 & E1).
destruct CASES as [(_ & _ & ->) | [(_ & _ & _ & ->) | (_ & _ & HR)]]; [exists bs1; exact E1| exists bs1; exact E1|].
destruct (IH st1 b1 q1 r q' HR) as (bs2 & E2). exists (bs1 ++ bs2). rewrite E2, E1, app_assoc. reflexivity.
Qed.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Notation DECM := (speex_decode (St := pst) p_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M).
Local Notation DLOOP := (decode_loop (St := pst) p_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M).

Lemma prun_bits_remaining_M : forall (b : bits_st unit) q, prun (bits_remaining_M (St := pst) b) q = Some (speex_bits_remaining b, q).
Proof. intros b q. reflexivity. Qed.

Lemma dloop_step : forall n (st : dec_state unit) (b : bits_st unit) q r q',
prun (DLOOP (S n) st b) q = Some (r, q') ->
exists ret st1 b1 q1, prun (DECM st b 0) q = Some ((ret, st1, b1), q1) /\
( ((ret =? -1) || (ret =? -2) = true /\ r = (st1, b1) /\ q' = q1)
\/ ((ret =? -1) || (ret =? -2) = false /\ speex_bits_remaining b1 < 0 /\ r = (st1, b1) /\ q' = q1)
\/ ((ret =? -1) || (ret =? -2) = false /\ 0 <= speex_bits_remaining b1 /\ prun (DLOOP n st1 b1) q1 = Some (r, q'))).
Proof.
intros n st b q r q' H. cbn [decode_loop] in H. unfold h_decode in H.
rewrite prun_bind in H.
destruct (prun (DECM st b 0) q) as [[[[ret st1] b1] q1]|] eqn:ED; [| discriminate H].
exists ret, st1, b1, q1. split; [reflexivity|]. cbn beta iota in H.
destruct ((ret =? -1) || (ret =? -2)) eqn:ER.
- left. rewrite prun_ret in H. injection H as <- <-. split; [reflexivity| split; reflexivity].
- rewrite prun_bind, prun_bits_remaining_M in H. cbn beta iota in H.
destruct (Z.ltb_spec (speex_bits_remaining b1) 0) as [RN|RP].
+ right; left. rewrite prun_ret in H. injection H as <- <-. split; [reflexivity| split; [exact RN| split; reflexivity]].
+ right; right. split; [reflexivity| split; [exact RP| exact H]].
Qed.

Lemma dloop_appends : forall n (st : dec_state unit) (b : bits_st unit) q r q', prun (DLOOP n st b) q = Some (r, q') -> exists bs, p_err q' = p_err q ++ bs.
Proof.
induction n as [|n IH]; intros st b q r q' H.
- cbn [decode_loop] in H. rewrite prun_ret in H. injection H as _ <-. exists []. rewrite app_nil_r. reflexivity.
- destruct (dloop_step n st b q r q' H) as (ret & st1 & b1 & q1 & ED & CASES).
destruct (dec_appends_all st b q _ q1 ED) as (bs1 & E1).
destruct CASES as [(_ & _ & ->) | [(_ & _ & _ & ->) | (_ & _ & HR)]]; [exists bs1; exact E1| exists bs1; exact E1|].
destruct (IH st1 b1 q1 r q' HR) as (bs2 & E2). exists (bs1 ++ bs2). rewrite E2, E1, app_assoc. reflexivity.
Qed.
