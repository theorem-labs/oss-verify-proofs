(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG0n YG0o YG0t YG0p YG0r YG0q.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Definition rbv (S S3 : astate) (J F : Z) : Prop :=
exists j f, 0 <= j <= J /\ 0 <= f <= F /\
bud_le S S3 (j + EV_FRAMEV * f) (j + CN_FRAME * f) (2 ^ 17 * j + WT_FRAME * f) (HULL_UNIT * j + HL_FRAME * f).
Lemma rbv_of_jbud : forall S S3 k J F, jbud S S3 k -> 0 <= k <= J -> 0 <= F -> rbv S S3 J F.
Proof.
intros S S3 k J F (_ & D) Hk HF. exists k, 0. split; [exact Hk|]. split; [lia|].
eapply bud_le_mono; [exact D | lia | lia | lia | lia].
Qed.
Lemma rbv_mono : forall S S3 J F J' F', rbv S S3 J F -> J <= J' -> F <= F' -> rbv S S3 J' F'.
Proof. intros S S3 J F J' F' (j & f & Hj & Hf & D) HJ HF. exists j, f. split; [lia|]. split; [lia|]. exact D. Qed.
Lemma rbv_coarse_bud : forall S S3 S4 J F e, rbv S S3 J F -> bud_le S3 S4 e e (2 ^ 17 * e) (HULL_UNIT * e) -> 0 <= e -> rbv S S4 (J + e) F.
Proof.
intros S S3 S4 J F e (j & f & Hj & Hf & D) D2 He. exists (j + e), f. split; [lia|]. split; [lia|].
eapply bud_le_mono; [exact (bud_le_trans _ _ _ _ _ _ _ _ _ _ _ D D2) | lia | lia | lia | lia].
Qed.
Lemma rbv_coarse : forall S S3 S4 J F e, rbv S S3 J F -> jbud S3 S4 e -> 0 <= e -> rbv S S4 (J + e) F.
Proof. intros S S3 S4 J F e H (_ & D) He. exact (rbv_coarse_bud S S3 S4 J F e H D He). Qed.
Lemma rbv_frame : forall S S3 S4 J F, rbv S S3 J F -> bud_le S3 S4 EV_FRAMEV CN_FRAME WT_FRAME HL_FRAME -> rbv S S4 J (F + 1).
Proof.
intros S S3 S4 J F (j & f & Hj & Hf & D) D2. exists j, (f + 1). split; [lia|]. split; [lia|].
eapply bud_le_mono; [exact (bud_le_trans _ _ _ _ _ _ _ _ _ _ _ D D2) | lia | lia | lia | lia].
Qed.
Lemma rbv_same : forall S S3 S4 J F, rbv S S3 J F -> bud_le S3 S4 0 0 0 0 -> rbv S S4 J F.
Proof.
intros S S3 S4 J F (j & f & Hj & Hf & D) D2. exists j, f. split; [lia|]. split; [lia|].
eapply bud_le_mono; [exact (bud_le_trans _ _ _ _ _ _ _ _ _ _ _ D D2) | lia | lia | lia | lia].
Qed.
Lemma rbv_room : forall S S3 J F e, bud_ok S EV_RLIBV CN_RLIB WT_RLIB HL_RLIB -> rbv S S3 J F ->
0 <= e -> J + e <= RGB_COARSE -> F <= 16 -> vev S3 + e <= VEV_MAX.
Proof.
intros S S3 J F e B (j & f & Hj & Hf & D) He HJ HF.
apply (rgb_coarse_room S S3 j f e B D); lia.
Qed.
Lemma rbv_room_lt : forall S S3 J F, bud_ok S EV_RLIBV CN_RLIB WT_RLIB HL_RLIB -> rbv S S3 J F -> J + 1 <= RGB_COARSE -> F <= 16 -> vev S3 < VEV_MAX.
Proof. intros S S3 J F B H HJ HF. pose proof (rbv_room S S3 J F 1 B H ltac:(lia) HJ HF). lia. Qed.
Lemma rbv_room_frame : forall S S3 J F, bud_ok S EV_RLIBV CN_RLIB WT_RLIB HL_RLIB -> rbv S S3 J F ->
J <= RGB_COARSE -> F <= 15 -> bud_ok S3 EV_FRAMEV CN_FRAME WT_FRAME HL_FRAME.
Proof.
intros S S3 J F B (j & f & Hj & Hf & D) HJ HF.
apply (rgb_frame_room S S3 j f B D); lia.
Qed.
Lemma rbv_post : forall S S' J F, rbv S S' J F -> J <= RGB_COARSE -> F <= 16 -> bud_le S S' EV_RLIBV CN_RLIB WT_RLIB HL_RLIB.
Proof.
intros S S' J F (j & f & Hj & Hf & D) HJ HF. destruct rgb_split as (R1 & R2 & R3 & R4).
eapply bud_le_mono; [exact D | | | |];
unfold RGB_COARSE, EV_FRAMEV, CN_FRAME, WT_FRAME, HL_FRAME, EV_RLIBV, CN_RLIB, WT_RLIB, HL_RLIB, HULL_UNIT in *; lia.
Qed.
Lemma jroom : forall S S3 k e, bud_ok S EV_RLIBV CN_RLIB WT_RLIB HL_RLIB -> jbud S S3 k -> 0 <= k -> 0 <= e -> k + e <= RGB_COARSE -> vev S3 + e <= VEV_MAX.
Proof. intros S S3 k e B J Hk He H. apply (rbv_room S S3 k 0 e B (rbv_of_jbud S S3 k k 0 J ltac:(lia) ltac:(lia)) He H). lia. Qed.
