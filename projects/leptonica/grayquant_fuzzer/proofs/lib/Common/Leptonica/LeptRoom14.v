(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import AllocIface.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition RB_pix14 : Z := 2 ^ 26 + 2 ^ 23 + 2 ^ 22.
(* [comment removed for export] *)
Definition RB_pixcopy14 : Z := RB_pix14 + RB_cmapcopy.

(* [comment removed for export] *)
Definition RK_gm3 : Z := 3 * RK_pixcopy.      Definition RB_gm3 : Z := 3 * RB_pixcopy14.
Definition RK_gm4 : Z := 4 * RK_pixcopy.      Definition RB_gm4 : Z := 4 * RB_pixcopy14.
Definition RK_graymorph : Z := RK_deser + 4 * RK_pixcopy + 2 * RK_gm3 + 2 * RK_gm4.
Definition RB_graymorph : Z := RB_deser + 4 * RB_pixcopy14 + 2 * RB_gm3 + 2 * RB_gm4.

Ltac room_consts ::=
  unfold RK_graymorph, RB_graymorph, RK_gm3, RB_gm3, RK_gm4, RB_gm4, RB_pixcopy14, RB_pix14,
         RK_paintcmap, RB_paintcmap, RK_pixcopy, RB_pixcopy, RK_cmapcopy, RB_cmapcopy, RK_box, RB_box,
         RK_hdr, RB_hdr, RK_cmap, RB_cmap, RK_pix, RB_pix, RK_deser, RB_deser in *.

Lemma RB_pix14_le : RB_pix14 <= RB_pix. Proof. room_consts. lia. Qed.
Lemma RB_pixcopy14_le : RB_pixcopy14 <= RB_pixcopy. Proof. room_consts. lia. Qed.
Lemma RK_graymorph_val : RK_graymorph = 77. Proof. reflexivity. Qed.
Lemma RB_graymorph_le : RB_graymorph <= 2 ^ 31 - 2 ^ 26. Proof. room_consts. lia. Qed.

(* [comment removed for export] *)
Section Weaken.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Lemma roomtr_pix14_pix : forall A vm A' vm', roomtr A vm A' vm' RK_pix RB_pix14 -> roomtr A vm A' vm' RK_pix RB_pix.
Proof. intros A vm A' vm' T. eapply roomtr_weaken; [exact T | lia | exact RB_pix14_le]. Qed.
End Weaken.
