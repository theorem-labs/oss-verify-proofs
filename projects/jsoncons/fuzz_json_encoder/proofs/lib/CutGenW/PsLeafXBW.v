(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutHeap2.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGenW Require Import ParseStringChkXBW ParseStringChkXBW1 ParseStringChkXBW2 ParseStringChkXBW3 ParseStringChkXBW4 ParseStringChkXBW5 ParseStringChkXBW6 ParseStringChkXBW7 ParseStringChkXBW8 ParseStringChkXBW9 ParseStringChkXBW10 ParseStringChkXBW11 ParseStringChkXBW12 ParseStringChkXBW13 ParseStringChkXBW14 ParseStringChkXBW15 ParseStringChkXBW16 ParseStringChkXBW17 ParseStringChkXBW18 ParseStringChkXBW19 ParseStringChkXBW20 ParseStringChkXBW21 ParseStringChkXBW22 ParseStringChkXBW23 ParseStringChkXBW24 ParseStringChkXBW25 ParseStringChkXBW26 ParseStringChkXBW27 ParseStringChkXBW28 ParseStringChkXBW29 ParseStringChkXBW30 ParseStringChkXBW31 ParseStringChkXBW32 ParseStringChkXBW33 ParseStringChkXBW34 ParseStringChkXBW35 ParseStringChkXBW36 ParseStringChkXBW37 ParseStringChkXBW38.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module PSL.
Import PSA.
Lemma tags_len_2 : option_map (@length CC.tag) (nth_error G.TAGS 2) = Some 13%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma tags_len_27 : option_map (@length CC.tag) (nth_error G.TAGS 27) = Some 9%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma LEAFOK_all : forall i c k ps t, CH2.is_leaf G.CPS G.TAGS i c k ps t -> leaf_chk i c k ps t = true.
Proof.
  intros i c k ps t IL. pose proof IL as (tags & Hc & Htg & Hps & Ht).
  assert (Hi : (i < 79)%nat) by (rewrite <- len_cps; apply nth_error_Some; rewrite Hc; discriminate).
  assert (CASES : (0 <= i < 2)%nat \/ i = 2%nat \/ (3 <= i < 5)%nat \/ (5 <= i < 7)%nat \/ (7 <= i < 9)%nat \/ (9 <= i < 11)%nat \/ (11 <= i < 13)%nat \/ (13 <= i < 15)%nat \/ (15 <= i < 17)%nat \/ (17 <= i < 19)%nat \/ (19 <= i < 21)%nat \/ (21 <= i < 23)%nat \/ (23 <= i < 24)%nat \/ (24 <= i < 25)%nat \/ (25 <= i < 26)%nat \/ (26 <= i < 27)%nat \/ i = 27%nat \/ (28 <= i < 30)%nat \/ (30 <= i < 31)%nat \/ (31 <= i < 33)%nat \/ (33 <= i < 34)%nat \/ (34 <= i < 36)%nat \/ (36 <= i < 37)%nat \/ (37 <= i < 39)%nat \/ (39 <= i < 40)%nat \/ (40 <= i < 42)%nat \/ (42 <= i < 52)%nat \/ (52 <= i < 60)%nat \/ (60 <= i < 79)%nat) by (clear - Hi; lia).
  destruct CASES as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]]]]]]]]]]]]]]]]].
  - exact (leaves_rng_sound 0 2 leaves_rng_0_2 i c k ps t H IL).
  - subst i. pose proof tags_len_2 as TL. rewrite Htg in TL. cbn [option_map] in TL. injection TL as TL'.
    assert (Hk : (k < 13)%nat) by (rewrite <- TL'; apply nth_error_Some; rewrite Ht; discriminate).
    destruct k as [|[|[|[|[|[|[|[|[|[|[|[|[|k']]]]]]]]]]]]]; [exact (leaves_ks_sound 2 _ leaves_ks_2_0 0%nat c ps t (or_introl eq_refl) IL) | exact (leaves_ks_sound 2 _ leaves_ks_2_0 1%nat c ps t (or_intror (or_introl eq_refl)) IL) | exact (leaves_ks_sound 2 _ leaves_ks_2_0 2%nat c ps t (or_intror (or_intror (or_introl eq_refl))) IL) | exact (leaves_ks_sound 2 _ leaves_ks_2_3 3%nat c ps t (or_introl eq_refl) IL) | exact (leaves_ks_sound 2 _ leaves_ks_2_3 4%nat c ps t (or_intror (or_introl eq_refl)) IL) | exact (leaves_ks_sound 2 _ leaves_ks_2_3 5%nat c ps t (or_intror (or_intror (or_introl eq_refl))) IL) | exact (leaves_ks_sound 2 _ leaves_ks_2_6 6%nat c ps t (or_introl eq_refl) IL) | exact (leaves_ks_sound 2 _ leaves_ks_2_6 7%nat c ps t (or_intror (or_introl eq_refl)) IL) | exact (leaves_ks_sound 2 _ leaves_ks_2_6 8%nat c ps t (or_intror (or_intror (or_introl eq_refl))) IL) | exact (leaves_ks_sound 2 _ leaves_ks_2_9 9%nat c ps t (or_introl eq_refl) IL) | exact (leaves_ks_sound 2 _ leaves_ks_2_9 10%nat c ps t (or_intror (or_introl eq_refl)) IL) | exact (leaves_ks_sound 2 _ leaves_ks_2_9 11%nat c ps t (or_intror (or_intror (or_introl eq_refl))) IL) | exact (leaves_ks_sound 2 _ leaves_ks_2_12 12%nat c ps t (or_introl eq_refl) IL)| exfalso; clear - Hk; lia].
  - exact (leaves_rng_sound 3 2 leaves_rng_3_2 i c k ps t H IL).
  - exact (leaves_rng_sound 5 2 leaves_rng_5_2 i c k ps t H IL).
  - exact (leaves_rng_sound 7 2 leaves_rng_7_2 i c k ps t H IL).
  - exact (leaves_rng_sound 9 2 leaves_rng_9_2 i c k ps t H IL).
  - exact (leaves_rng_sound 11 2 leaves_rng_11_2 i c k ps t H IL).
  - exact (leaves_rng_sound 13 2 leaves_rng_13_2 i c k ps t H IL).
  - exact (leaves_rng_sound 15 2 leaves_rng_15_2 i c k ps t H IL).
  - exact (leaves_rng_sound 17 2 leaves_rng_17_2 i c k ps t H IL).
  - exact (leaves_rng_sound 19 2 leaves_rng_19_2 i c k ps t H IL).
  - exact (leaves_rng_sound 21 2 leaves_rng_21_2 i c k ps t H IL).
  - exact (leaves_rng_sound 23 1 leaves_rng_23_1 i c k ps t H IL).
  - exact (leaves_rng_sound 24 1 leaves_rng_24_1 i c k ps t H IL).
  - exact (leaves_rng_sound 25 1 leaves_rng_25_1 i c k ps t H IL).
  - exact (leaves_rng_sound 26 1 leaves_rng_26_1 i c k ps t H IL).
  - subst i. pose proof tags_len_27 as TL. rewrite Htg in TL. cbn [option_map] in TL. injection TL as TL'.
    assert (Hk : (k < 9)%nat) by (rewrite <- TL'; apply nth_error_Some; rewrite Ht; discriminate).
    destruct k as [|[|[|[|[|[|[|[|[|k']]]]]]]]]; [exact (leaves_ks_sound 27 _ leaves_ks_27_0 0%nat c ps t (or_introl eq_refl) IL) | exact (leaves_ks_sound 27 _ leaves_ks_27_1 1%nat c ps t (or_introl eq_refl) IL) | exact (leaves_ks_sound 27 _ leaves_ks_27_2 2%nat c ps t (or_introl eq_refl) IL) | exact (leaves_ks_sound 27 _ leaves_ks_27_2 3%nat c ps t (or_intror (or_introl eq_refl)) IL) | exact (leaves_ks_sound 27 _ leaves_ks_27_4 4%nat c ps t (or_introl eq_refl) IL) | exact (leaves_ks_sound 27 _ leaves_ks_27_5 5%nat c ps t (or_introl eq_refl) IL) | exact (leaves_ks_sound 27 _ leaves_ks_27_6 6%nat c ps t (or_introl eq_refl) IL) | exact (leaves_ks_sound 27 _ leaves_ks_27_6 7%nat c ps t (or_intror (or_introl eq_refl)) IL) | exact (leaves_ks_sound 27 _ leaves_ks_27_6 8%nat c ps t (or_intror (or_intror (or_introl eq_refl))) IL)| exfalso; clear - Hk; lia].
  - exact (leaves_rng_sound 28 2 leaves_rng_28_2 i c k ps t H IL).
  - exact (leaves_rng_sound 30 1 leaves_rng_30_1 i c k ps t H IL).
  - exact (leaves_rng_sound 31 2 leaves_rng_31_2 i c k ps t H IL).
  - exact (leaves_rng_sound 33 1 leaves_rng_33_1 i c k ps t H IL).
  - exact (leaves_rng_sound 34 2 leaves_rng_34_2 i c k ps t H IL).
  - exact (leaves_rng_sound 36 1 leaves_rng_36_1 i c k ps t H IL).
  - exact (leaves_rng_sound 37 2 leaves_rng_37_2 i c k ps t H IL).
  - exact (leaves_rng_sound 39 1 leaves_rng_39_1 i c k ps t H IL).
  - exact (leaves_rng_sound 40 2 leaves_rng_40_2 i c k ps t H IL).
  - exact (leaves_rng_sound 42 10 leaves_rng_42_10 i c k ps t H IL).
  - exact (leaves_rng_sound 52 8 leaves_rng_52_8 i c k ps t H IL).
  - exact (leaves_rng_sound 60 19 leaves_rng_60_19 i c k ps t H IL).
Qed.
End PSL.
