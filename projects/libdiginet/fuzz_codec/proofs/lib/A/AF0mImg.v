(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/A/AF0m.v states Tfib_zero_shadow with the image bounds as literals, because af0m.py emits that list literally. This file does not change AF0m.v: it checks, by reflexivity, that the first lower bound and the last upper end of that list ARE lib/Reusable/YImgTop.v's IMG_LO and IMG_TOP (libreac/fuzz_knock's lib/A/AF0mImg.v form). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AF0m.
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

Lemma tfib_zero_shadow_img : Tfib_zero_shadow = [(YImgTop.IMG_LO, 0x20f48 - YImgTop.IMG_LO); (0x20f60, 0x20f68 - 0x20f60); (0x20f80, 0x20f88 - 0x20f80); (0x20fa0, 0x20fa8 - 0x20fa0); (0x20fc0, 0x20fc8 - 0x20fc0); (0x21100, 0x21108 - 0x21100); (0x21340, 0x21368 - 0x21340); (0x21380, 0x21388 - 0x21380); (0x213a0, 0x21508 - 0x213a0); (0x21560, 0x9d678 - 0x21560); (0x9d6a0, 0x9d6b0 - 0x9d6a0); (0x9d6c0, 0x9d6d0 - 0x9d6c0); (0x9d6e0, 0x9d8b0 - 0x9d6e0); (0x9d920, 0x9d950 - 0x9d920); (0x9d980, 0xa23c0 - 0x9d980); (0xa2dc0, YImgTop.IMG_TOP - 0xa2dc0)].
Proof. reflexivity. Qed.
