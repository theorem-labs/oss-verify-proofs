(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import ClientDecide.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition STATE_SIZE : Z := 7176.
Definition WINDOW_SIZE : Z := 32768.

Definition script (data : list Z) : list Z :=
  STATE_SIZE :: (if window_needed data then [WINDOW_SIZE] else []).

Definition CLIENT_MAX_REQS : nat := 2.
Definition CLIENT_REQ_MAX : Z := 32768.

Lemma script_ok : forall data,
  (length (script data) <= CLIENT_MAX_REQS)%nat /\ Forall (fun n => 0 <= n <= CLIENT_REQ_MAX) (script data).
Proof.
  intros data. unfold script, CLIENT_MAX_REQS, CLIENT_REQ_MAX, STATE_SIZE, WINDOW_SIZE.
  destruct (window_needed data); cbn [length]; (split; [lia|]); repeat constructor; lia.
Qed.

Lemma script_len : forall data, (length (script data) <= CLIENT_MAX_REQS)%nat.
Proof. intros data. apply script_ok. Qed.
Lemma script_sizes : forall data, Forall (fun n => 0 <= n <= CLIENT_REQ_MAX) (script data).
Proof. intros data. apply script_ok. Qed.

Definition CLIENT_PRE : list Z := [STATE_SIZE].
Definition CLIENT_OPT : list Z := [WINDOW_SIZE].

Lemma client_ok :
  (length (CLIENT_PRE ++ CLIENT_OPT) <= CLIENT_MAX_REQS)%nat /\ Forall (fun n => 0 <= n <= CLIENT_REQ_MAX) (CLIENT_PRE ++ CLIENT_OPT).
Proof.
  unfold CLIENT_PRE, CLIENT_OPT, CLIENT_MAX_REQS, CLIENT_REQ_MAX, STATE_SIZE, WINDOW_SIZE. cbn [app length].
  split; [lia|]. repeat constructor; lia.
Qed.
