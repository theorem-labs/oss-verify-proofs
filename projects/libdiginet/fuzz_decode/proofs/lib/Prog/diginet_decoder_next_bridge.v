(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* One diginet_msg_next step in the two forms the walk of diginet_decoder_next joins: msg_step (the
   callee contract's result) and DgnLib.diginet_msg_next (the model the contract states its result
   with), read off DgnLib.diginet_msg_next_msg_step for the body map bz bb.
   Written by Theorem Labs. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

(* the message a step that answers 1 writes, whatever the message before *)
Definition dn_msg (r : msg_res) : dgn_msg :=
  {| dm_status := mr_status r; dm_running := mr_running r; dm_d1 := mr_d1 r; dm_d2 := mr_d2 r;
     dm_sysex := if writes_sysex (mr_kind r) then Z.of_nat (mr_sysex r) else 0;
     dm_sysex_len := Z.of_nat (mr_sysex_len r); dm_offset := Z.of_nat (mr_start r);
     dm_len := Z.of_nat (mr_len r) |}.

Lemma dn_msg_next : forall bb pos st m0,
  fst (fst (diginet_msg_next (map bz bb) (cursor_of bb pos st) m0)) = mr_code (msg_step bb pos st) /\
  snd (diginet_msg_next (map bz bb) (cursor_of bb pos st) m0) =
    cursor_of bb (mr_pos (msg_step bb pos st)) (mr_st (msg_step bb pos st)) /\
  (mr_code (msg_step bb pos st) = 1 ->
   snd (fst (diginet_msg_next (map bz bb) (cursor_of bb pos st) m0)) = dn_msg (msg_step bb pos st)).
Proof.
  intros bb pos st m0.
  rewrite (diginet_msg_next_msg_step (map bz bb) bb pos st m0 (holds_body_map bb)).
  cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|].
  intros Hc. unfold msg_after, dn_msg, is_end. unfold mr_code in Hc.
  destruct (mr_kind (msg_step bb pos st)); try discriminate; reflexivity.
Qed.
