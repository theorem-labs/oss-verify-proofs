(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* New for libdiginet/fuzz_decode: splitting an rw_cells region at a cell boundary, on the UBSan image.
   A callee whose footprint is part of a bigger object needs that part as an rw_cells of its own, because the kit's
   post_call drops an rw_cells fact whose region meets the callee's footprint: diginet_msg_next over the 25-byte
   cursor of a 40-byte struct diginet_decoder, diginet_cursor_init over the same cursor, the memcpy of a scribble's
   text into the 80-byte struct diginet_event. These two lemmas split such a region before the call and join it
   again after. They are about the kit's cells only and name no image value. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.libdiginet.fuzz_decode.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Lemma rw_cells_split : forall m A cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] (Ha & Hn & Hw)].
  apply cells_wf_app in Hwf as [Hwf1 Hwf2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [Hb1 Hb2].
  rewrite (cells_bytes_length cs1 Hwf1) in Hb2.
  rewrite cells_size_app, Nat2Z.inj_add in Hn, Hw.
  split; (split; [split; assumption|]).
  - split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
    apply Hw. lia.
Qed.

(* Two cell lists that hold the same bytes describe the same region: how a byte block a callee wrote (a CB of the
   memset's zeros, or of the bytes the memcpy copied) becomes the typed cells of a struct. *)
Lemma rw_cells_recast : forall m A cs1 cs2,
  rw_cells rsegs m A cs1 -> cells_wf cs2 ->
  cells_bytes cs2 = cells_bytes cs1 -> cells_size cs2 = cells_size cs1 ->
  rw_cells rsegs m A cs2.
Proof.
  intros m A cs1 cs2 [[Hwf Hb] Hw] Hwf2 Hbs Hsz.
  split; [split; [exact Hwf2|]|]; rewrite ?Hbs, ?Hsz; assumption.
Qed.

Lemma rw_cells_join : forall m A cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A cs1 cs2 [[Hwf1 Hb1] (Ha1 & Hn1 & Hw1)] [[Hwf2 Hb2] (Ha2 & Hn2 & Hw2)].
  split.
  - split; [apply cells_wf_app; split; assumption|].
    rewrite cells_bytes_app. apply bytes_at_app. split; [exact Hb1|].
    rewrite (cells_bytes_length cs1 Hwf1). exact Hb2.
  - rewrite cells_size_app, Nat2Z.inj_add. split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))) as [HL|HL].
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply Hw2. lia.
Qed.
