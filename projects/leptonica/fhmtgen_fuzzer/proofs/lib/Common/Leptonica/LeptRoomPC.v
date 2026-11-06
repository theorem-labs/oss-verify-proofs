(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition RK_box : Z := 1.          Definition RB_box : Z := 2 ^ 23.
(* [comment removed for export] *)
Definition RK_cmapcopy : Z := 2.     Definition RB_cmapcopy : Z := 2 ^ 24.
(* [comment removed for export] *)
Definition RK_pixcopy : Z := RK_pix + RK_cmapcopy.
Definition RB_pixcopy : Z := RB_pix + RB_cmapcopy.
(* [comment removed for export] *)
Definition RK_paintcmap : Z := RK_deser + RK_box + 2 * RK_pixcopy.
Definition RB_paintcmap : Z := RB_deser + RB_box + 2 * RB_pixcopy.

Ltac room_consts ::=
  unfold RK_paintcmap, RB_paintcmap, RK_pixcopy, RB_pixcopy, RK_cmapcopy, RB_cmapcopy, RK_box, RB_box,
         RK_hdr, RB_hdr, RK_cmap, RB_cmap, RK_pix, RB_pix, RK_deser, RB_deser in *.

Lemma RK_paintcmap_val : RK_paintcmap = 14. Proof. reflexivity. Qed.
Lemma RB_paintcmap_le : RB_paintcmap <= 2 ^ 30. Proof. room_consts. lia. Qed.
