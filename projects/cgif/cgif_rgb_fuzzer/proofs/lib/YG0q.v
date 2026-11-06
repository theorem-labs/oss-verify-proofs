(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0n YG0o YG0t YG0p YG0r.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Definition EV_FRAMEV : Z := 1900.
Definition CN_FRAME : Z := 820.
Definition WT_FRAME : Z := 2 ^ 17 * 240.
Definition HL_FRAME : Z := HULL_UNIT * 83.
Definition RGB_COARSE : Z := 166.
Lemma rgb_split :
RGB_COARSE + 16 * EV_FRAMEV <= EV_RLIBV /\ RGB_COARSE + 16 * CN_FRAME <= CN_RLIB /\
2 ^ 17 * RGB_COARSE + 16 * WT_FRAME <= WT_RLIB /\ HULL_UNIT * RGB_COARSE + 16 * HL_FRAME + 2 ^ 24 <= HL_RLIB.
Proof. unfold RGB_COARSE, EV_FRAMEV, CN_FRAME, WT_FRAME, HL_FRAME, EV_RLIBV, CN_RLIB, WT_RLIB, HL_RLIB, HULL_UNIT. lia. Qed.
Lemma rgb_frame_room : forall S Sc j f, bud_ok S EV_RLIBV CN_RLIB WT_RLIB HL_RLIB ->
bud_le S Sc (j + EV_FRAMEV * f) (j + CN_FRAME * f) (2 ^ 17 * j + WT_FRAME * f) (HULL_UNIT * j + HL_FRAME * f) ->
0 <= j <= RGB_COARSE -> 0 <= f < 16 -> bud_ok Sc EV_FRAMEV CN_FRAME WT_FRAME HL_FRAME.
Proof.
intros S Sc j f B D Hj Hf. destruct rgb_split as (R1 & R2 & R3 & R4).
apply (bud_ok_at S Sc _ _ _ _ _ _ _ _ EV_FRAMEV CN_FRAME WT_FRAME HL_FRAME B D);
unfold RGB_COARSE, EV_FRAMEV, CN_FRAME, WT_FRAME, HL_FRAME, EV_RLIBV, CN_RLIB, WT_RLIB, HL_RLIB, HULL_UNIT in *; lia.
Qed.
Lemma rgb_coarse_room : forall S Sc j f k, bud_ok S EV_RLIBV CN_RLIB WT_RLIB HL_RLIB ->
bud_le S Sc (j + EV_FRAMEV * f) (j + CN_FRAME * f) (2 ^ 17 * j + WT_FRAME * f) (HULL_UNIT * j + HL_FRAME * f) ->
0 <= j -> 0 <= k -> j + k <= RGB_COARSE -> 0 <= f <= 16 -> vev Sc + k <= VEV_MAX.
Proof.
intros S Sc j f k B D Hj Hk Hjk Hf. destruct rgb_split as (R1 & R2 & R3 & R4).
apply (vev_room_of_bud S Sc _ _ _ _ _ _ _ _ k B D);
unfold RGB_COARSE, EV_FRAMEV, CN_FRAME, WT_FRAME, HL_FRAME, EV_RLIBV, CN_RLIB, WT_RLIB, HL_RLIB, HULL_UNIT in *; lia.
Qed.
