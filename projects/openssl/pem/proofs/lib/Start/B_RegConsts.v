(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanRegModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition B_RGL : RGM.lay := RGM.L 0x10000 0xbf8000 0x7fff8000 0xbd22a0 0xbd5d6d.
Definition B_RGC : RGM.ctab :=
  RGM.C 0x1a44a4 0x5e2fa0 0x6a0018 0x69cb38 0x69f338 0x69eb9c 0x5dfa70 0x55f010 0x5dfab0 0x721588 0x69cbb0 0x69cc18 0x69bc60 B_RGL.
