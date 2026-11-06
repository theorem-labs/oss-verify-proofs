(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanRegModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition B_RGL : RGM.lay := RGM.L 0x10000 0xbfd000 0x7fff8000 0xbd6a20 0xbda496.
Definition B_RGC : RGM.ctab :=
  RGM.C 0x1a4458 0x5e76c0 0x6a4758 0x6a1278 0x6a3a78 0x6a32dc 0x5e4190 0x563738 0x5e41d0 0x725cc8 0x6a12f0 0x6a1358 0x6a03c0 B_RGL.
