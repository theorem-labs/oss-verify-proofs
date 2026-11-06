(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Written by a Theorem Labs lane, 2026-10: lib/A/AF0m.v states Tfib_zero_shadow with the image bounds as the literals
   (0x10000, 0x5f3000 - 0x10000), because af0m.py emits that list literally. This file does not change AF0m.v:
   it checks, by reflexivity, that those literals ARE lib/Reusable/YImgTop.v's IMG_LO and IMG_TOP, so the
   Theorem Labs rule "no image-end literal outside YImgTop.v" has a machine-checked witness for this unit. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.A Require Import AF0m.
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

Lemma tfib_zero_shadow_img : Tfib_zero_shadow = [(YImgTop.IMG_LO, YImgTop.IMG_TOP - YImgTop.IMG_LO)].
Proof. reflexivity. Qed.
