(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes InitStack.
Import ListNotations.

Definition secret_bytes (rb : list byte) : list byte := firstn 8 (skipn 8 rb).
Definition entry_secret (rnd : EntryDraw) : word := le_bytes_to_word (secret_bytes (at_random_bytes (ed_random rnd))).

Lemma secret_bytes_length : forall rb, (16 <= length rb)%nat -> length (secret_bytes rb) = 8%nat.
Proof. intros rb H. unfold secret_bytes. rewrite length_firstn. rewrite length_skipn. lia. Qed.

Lemma le8_entry_secret : forall rnd, le8 (entry_secret rnd) = secret_bytes (at_random_bytes (ed_random rnd)).
Proof. intros rnd. apply le8_of_bytes. reflexivity. Qed.

Lemma at_random_bytes_split : forall rnd,
  at_random_bytes (ed_random rnd) = firstn 8 (at_random_bytes (ed_random rnd)) ++ secret_bytes (at_random_bytes (ed_random rnd)).
Proof.
  intros rnd. unfold secret_bytes. set (rb := at_random_bytes _).
  rewrite (@firstn_all2 _ 8%nat (skipn 8 rb)) by (rewrite length_skipn; subst rb; rewrite length_at_random_bytes; lia).
  symmetry. apply firstn_skipn.
Qed.
