(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode. No check_ function of fuzz/fuzz_decode.c aborts, for any input: fuzz_decode_ok
   (DgnDecHarness.v) is true for every byte string the harness can be given, with the library models of DgnLib.v plugged
   in. The three parts of LLVMFuzzerTestOneInput (fuzz_decode.c:278-344) are the cursor loop (cursor_loop_ok_all,
   DgnAgreeCursor.v), the decoder loop (dgn_events_loop_ok, DgnAgreeDecoder.v) and the refusal
   (check_refusal_ok_all, DgnAgreeCursor.v); each holds for every body of bytes, and the body harness_input hands
   them (fuzz_decode.c:289-302) is bytes of the input, in body mode and in frame mode. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import
  DgnSpec DgnLib DgnDecHarness DgnAgreeCursor DgnAgreeDecoder.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma Forall_skipn_bytes : forall n (l : list Z),
  Forall (fun x => 0 <= x < 256) l -> Forall (fun x => 0 <= x < 256) (skipn n l).
Proof.
  intros n; induction n as [|n IH]; intros l H; [exact H|].
  destruct l as [|x l]; [constructor|]. cbn [skipn]. apply IH. inversion H; assumption.
Qed.

(* the body harness_input hands the loops is bytes of the input: the copy buf of data + 1 in body mode and for a
   refused frame, the list from offset 30 of buf for an accepted frame *)
Lemma harness_input_bytes : forall data sel body len,
  Forall (fun x => 0 <= x < 256) data ->
  harness_input data = Some (sel, body, len) ->
  Forall (fun x => 0 <= x < 256) body.
Proof.
  intros data sel body len Hd H. unfold harness_input in H. cbv beta zeta in H.
  match type of H with (if ?x then _ else _) = _ => destruct x; [discriminate H|] end.
  destruct data as [|s buf]; [discriminate H|].
  pose proof (Forall_inv_tail Hd) as Hbuf.
  match type of H with (if ?x then _ else _) = _ => destruct x end;
    [injection H as _ <- _; exact Hbuf|].
  match type of H with (if ?x then _ else _) = _ => destruct x end;
    injection H as _ <- _; [apply Forall_skipn_bytes|]; exact Hbuf.
Qed.

(* No check of fuzz_decode.c aborts, for any input of bytes. The library enters fuzz_decode_ok as its models:
   diginet_cursor_init, diginet_msg_next, diginet_decoder_init (diginet_personality_of desk) (fuzz_decode.c:324),
   diginet_decoder_next and diginet_body_check. An input harness_input refuses (size 0 or FUZZ_INPUT_MAX and up,
   fuzz_decode.c:289-290) is true at once; every other one, any sel, body mode or frame mode, runs the three
   parts. *)
Theorem fuzz_decode_ok_all : forall data,
  Forall (fun x => 0 <= x < 256) data ->
  fuzz_decode_ok diginet_cursor_init diginet_msg_next
    (fun desk len => diginet_decoder_init (diginet_personality_of desk) len)
    diginet_decoder_next diginet_body_check data = true.
Proof.
  intros data Hd. unfold fuzz_decode_ok.
  destruct (harness_input data) as [[[sel body] len]|] eqn:H; [|reflexivity].
  pose proof (harness_input_bytes data sel body len Hd H) as Hb.
  cbv beta.
  rewrite cursor_loop_ok_all, dgn_events_loop_ok, check_refusal_ok_all by exact Hb.
  reflexivity.
Qed.
