(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanRegModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition A_RGL : RGM.lay := RGM.L 0x10000 0xbca000 0x7fff8000 0xba3ae0 0xba7556.
Definition A_RGC : RGM.ctab :=
  RGM.C 0x1a9548 0x5aea40 0x671818 0x66e338 0x670b38 0x67039c 0x5ab7d0 0x52a8ec 0x5ab810 0x6f2d88 0x66e3b0 0x66e418 0x66d480 A_RGL.
