(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import AllocIface.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section RoomCF.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Lemma roomtr_app0 : forall A vm A' vm' k b,
  roomtr A vm A' vm' 0 0 -> aroom A vm k b -> 0 <= k -> 0 <= b -> aroom A' vm' k b.
Proof. intros A vm A' vm' k b T R Hk Hb. pose proof (T k b R Hk Hb) as X. rewrite !Z.sub_0_r in X. exact X. Qed.
Lemma roomtr_app0_wv : forall A vm md A' vm' k b,
  roomtr A (m_vmmaps (with_vmmaps vm md)) A' vm' 0 0 -> aroom A vm k b -> 0 <= k -> 0 <= b -> aroom A' vm' k b.
Proof. intros A vm md A' vm' k b T. exact (roomtr_app0 A vm A' vm' k b (roomtr_wv A vm md A' vm' 0 0 T)). Qed.
End RoomCF.

(* [comment removed for export] *)
Definition RK_boxa : Z := 2.         Definition RB_boxa (n : Z) : Z := 2 ^ 23 + (8 * n + 2 ^ 22).
(* [comment removed for export] *)
Definition RK_naa : Z := 2.          Definition RB_naa (n : Z) : Z := 2 ^ 23 + (8 * n + 2 ^ 22).
(* [comment removed for export] *)
Definition RK_pixa : Z := 2 + RK_boxa.
Definition RB_pixa (n : Z) : Z := 2 ^ 23 + (8 * n + 2 ^ 22) + RB_boxa n.

(* [comment removed for export] *)
Definition RK_cf : Z := RK_boxa + RK_box + 1 + 2 * RK_naa + RK_pixa.
Definition RB_cf : Z := RB_boxa 1 + RB_box + 2 ^ 23 + 2 * RB_naa 1 + RB_pixa 20.
(* [comment removed for export] *)
Definition RK_colorfill : Z := RK_deser + RK_cf.
Definition RB_colorfill : Z := RB_deser + RB_cf.

Ltac room_consts ::=
  unfold RK_colorfill, RB_colorfill, RK_cf, RB_cf, RK_pixa, RB_pixa, RK_naa, RB_naa, RK_boxa, RB_boxa,
         RK_paintcmap, RB_paintcmap, RK_pixcopy, RB_pixcopy, RK_cmapcopy, RB_cmapcopy, RK_box, RB_box,
         RK_hdr, RB_hdr, RK_cmap, RB_cmap, RK_pix, RB_pix, RK_deser, RB_deser in *.

Lemma RK_colorfill_val : RK_colorfill = 17. Proof. reflexivity. Qed.
Lemma RB_colorfill_le : RB_colorfill <= 2 ^ 29. Proof. room_consts. lia. Qed.
