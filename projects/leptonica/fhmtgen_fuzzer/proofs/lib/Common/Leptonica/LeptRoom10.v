(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import AllocIface.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LeptArith LeptRoom LeptRoomPC LeptRoom14.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition RB10_small : Z := 2 ^ 17.
(* [comment removed for export] *)
Definition RB10_pix (n : Z) : Z := 2 ^ 17 + (n + 2 ^ 22).
(* [comment removed for export] *)
Definition RB10_cmapcopy : Z := 2 * 2 ^ 17.
(* [comment removed for export] *)
Definition RB10_pixcopy (n : Z) : Z := RB10_pix n + RB10_cmapcopy.

(* [comment removed for export] *)
Definition rast (w h d : Z) : Z := 4 * (wpl_of w d * h).

(* [comment removed for export] *)
Definition RK10_hmt (d : Z) : Z := if d =? 1 then 3 * RK_pixcopy else 0.
Definition RB10_hmt (d w h : Z) : Z :=
  if d =? 1 then 2 * RB10_pixcopy (rast (w + 64) (h + 64) 1) + RB10_pixcopy (rast w h 1) else 0.

(* [comment removed for export] *)
Definition RK10_sela : Z := 74.       Definition RB10_sela : Z := 74 * RB10_small.

(* [comment removed for export] *)
Definition RK_fhmtgen : Z := RK_deser + RK10_sela + RK_pixcopy + 10 * (3 * RK_pixcopy).
Definition RB_fhmtgen (d w h : Z) : Z := RB_deser + RB10_sela + RB_pixcopy14 + 10 * RB10_hmt d w h.

Ltac room_consts ::=
  unfold RK_fhmtgen, RB_fhmtgen, RK10_sela, RB10_sela, RB10_pixcopy, RB10_cmapcopy, RB10_pix, RB10_small,
         RK_graymorph, RB_graymorph, RK_gm3, RB_gm3, RK_gm4, RB_gm4, RB_pixcopy14, RB_pix14,
         RK_paintcmap, RB_paintcmap, RK_pixcopy, RB_pixcopy, RK_cmapcopy, RB_cmapcopy, RK_box, RB_box,
         RK_hdr, RB_hdr, RK_cmap, RB_cmap, RK_pix, RB_pix, RK_deser, RB_deser in *.

Lemma RK_fhmtgen_val : RK_fhmtgen = 203. Proof. reflexivity. Qed.
Lemma RK10_hmt_le : forall d, 0 <= RK10_hmt d <= 12.
Proof. intros d. unfold RK10_hmt. destruct (d =? 1); [change (3 * RK_pixcopy) with 12|]; lia. Qed.

Lemma wpl_of_1 : forall w, 0 <= w -> wpl_of w 1 = (w + 31) / 32.
Proof. intros w Hw. unfold wpl_of. f_equal. lia. Qed.

(* [comment removed for export] *)
Lemma rast1_le : forall w h, 1 <= w <= 20000 -> 1 <= h <= 20000 -> 0 <= rast w h 1 <= 50000000.
Proof.
  intros w h Hw Hh. unfold rast. rewrite wpl_of_1 by lia.
  assert (0 <= (w + 31) / 32 <= 625) by (split; [apply Z.div_pos; lia | enough ((w + 31) / 32 < 626) by lia; apply Z.div_lt_upper_bound; lia]). nia.
Qed.
Lemma rast1b_le : forall w h, 1 <= w <= 20000 -> 1 <= h <= 20000 -> 0 <= rast (w + 64) (h + 64) 1 <= 50320512.
Proof.
  intros w h Hw Hh. unfold rast. rewrite wpl_of_1 by lia.
  assert (0 <= (w + 64 + 31) / 32 <= 627) by (split; [apply Z.div_pos; lia | enough ((w + 64 + 31) / 32 < 628) by lia; apply Z.div_lt_upper_bound; lia]). nia.
Qed.

Lemma RB10_hmt_le : forall d w h, 1 <= w <= 20000 -> 1 <= h <= 20000 -> 0 <= RB10_hmt d w h <= 164403584.
Proof.
  intros d w h Hw Hh. unfold RB10_hmt. destruct (d =? 1); [| lia].
  pose proof (rast1_le w h Hw Hh). pose proof (rast1b_le w h Hw Hh). room_consts. lia.
Qed.

(* [comment removed for export] *)
Lemma RB_fhmtgen_le : forall d w h, 1 <= w <= 20000 -> 1 <= h <= 20000 -> RB_fhmtgen d w h <= 2 ^ 31 - 2 ^ 26.
Proof. intros d w h Hw Hh. pose proof (RB10_hmt_le d w h Hw Hh). unfold RB_fhmtgen. room_consts. lia. Qed.

(* [comment removed for export] *)
Lemma alloc_margin_small_le : forall n, 0 <= n <= 2028 -> alloc_margin n = RB10_small.
Proof. intros n Hn. unfold RB10_small. exact (alloc_margin_small n Hn). Qed.
