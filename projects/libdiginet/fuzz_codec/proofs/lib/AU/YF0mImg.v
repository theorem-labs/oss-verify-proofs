(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/AU/YF0m.v states Tfib_zero_shadow with the image bounds as literals, because af0m.py emits that list literally. This file does not change YF0m.v: it checks, by reflexivity, that the first lower bound and the last upper end of that list ARE lib/AU/YImgTopU.v's IMG_LO and IMG_TOP (libreac/fuzz_knock's lib/AU/YF0mImg.v form). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import YImgTopU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import YF0m.
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

Lemma tfib_zero_shadow_img : Tfib_zero_shadow = [(YImgTopU.IMG_LO, 0x20fa8 - YImgTopU.IMG_LO); (0x20fc0, 0x20fc8 - 0x20fc0); (0x20fe0, 0x20fe8 - 0x20fe0); (0x21000, 0x21008 - 0x21000); (0x21020, 0x21028 - 0x21020); (0x21160, 0x21168 - 0x21160); (0x213a0, 0x213c8 - 0x213a0); (0x213e0, 0x213e8 - 0x213e0); (0x21400, 0x21568 - 0x21400); (0x215c0, 0x9df98 - 0x215c0); (0x9dfc0, 0x9dfd0 - 0x9dfc0); (0x9dfe0, 0x9dff0 - 0x9dfe0); (0x9e000, 0x9e1d0 - 0x9e000); (0x9e240, 0x9e270 - 0x9e240); (0x9e2a0, 0xa2ce0 - 0x9e2a0); (0xa36e0, YImgTopU.IMG_TOP - 0xa36e0)].
Proof. reflexivity. Qed.
