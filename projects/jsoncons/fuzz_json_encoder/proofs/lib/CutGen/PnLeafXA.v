(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutHeap2.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import ParseNumberChkXA ParseNumberChkXA1 ParseNumberChkXA2 ParseNumberChkXA3 ParseNumberChkXA4 ParseNumberChkXA5 ParseNumberChkXA6 ParseNumberChkXA7 ParseNumberChkXA8 ParseNumberChkXA9 ParseNumberChkXA10.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PNL.
Import PNA.
Lemma LEAFOK_all : forall i c k ps t, CH2.is_leaf G.CPS G.TAGS i c k ps t -> leaf_chk i c k ps t = true.
Proof.
  intros i c k ps t IL. pose proof IL as (tags & Hc & Htg & Hps & Ht).
  assert (Hi : (i < 74)%nat) by (rewrite <- len_cps; apply nth_error_Some; rewrite Hc; discriminate).
  assert (CASES : (0 <= i < 0 + 22)%nat \/ (22 <= i < 22 + 4)%nat \/ (26 <= i < 26 + 4)%nat \/ (30 <= i < 30 + 4)%nat \/ (34 <= i < 34 + 5)%nat \/ (39 <= i < 39 + 4)%nat \/ (43 <= i < 43 + 4)%nat
                  \/ (47 <= i < 47 + 6)%nat \/ (53 <= i < 53 + 12)%nat \/ (65 <= i < 65 + 9)%nat) by (clear - Hi; lia).
  destruct CASES as [H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]].
  - exact (leaves_rng_sound 0 22 leaves_0_22 i c k ps t H IL).
  - exact (leaves_rng_sound 22 4 leaves_22_4 i c k ps t H IL).
  - exact (leaves_rng_sound 26 4 leaves_26_4 i c k ps t H IL).
  - exact (leaves_rng_sound 30 4 leaves_30_4 i c k ps t H IL).
  - exact (leaves_rng_sound 34 5 leaves_34_5 i c k ps t H IL).
  - exact (leaves_rng_sound 39 4 leaves_39_4 i c k ps t H IL).
  - exact (leaves_rng_sound 43 4 leaves_43_4 i c k ps t H IL).
  - exact (leaves_rng_sound 47 6 leaves_47_6 i c k ps t H IL).
  - exact (leaves_rng_sound 53 12 leaves_53_12 i c k ps t H IL).
  - exact (leaves_rng_sound 65 9 leaves_65_9 i c k ps t H IL).
Qed.
End PNL.
