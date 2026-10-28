(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Start Require Import AsanRegModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition A_RGL : RGM.lay := RGM.L 0x10000 0xbc6000 0x7fff8000 0xb9faa0 0xba356d.
Definition A_RGC : RGM.ctab :=
  RGM.C 0x1a94ec 0x5aaa60 0x66d818 0x66a338 0x66cb38 0x66c39c 0x5a77f0 0x526914 0x5a7830 0x6eed88 0x66a3b0 0x66a418 0x669460 A_RGL.
