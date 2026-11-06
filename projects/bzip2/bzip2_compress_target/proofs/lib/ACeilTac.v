(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Export ACeil.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac bz_ceil :=
  try (lazymatch goal with
       | _ : (0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000)%Z |- _ => fail
       | |- _ => pose proof alloc_ceiling_range as ACR__
       end).

(* [comment removed for export] *)
(* [comment removed for export] *)
