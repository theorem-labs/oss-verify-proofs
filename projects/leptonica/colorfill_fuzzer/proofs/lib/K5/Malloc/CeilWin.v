(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ceil_window {CE : Ceiling} : Prop := (0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000)%Z.

Lemma ceil_window_holds {CE : Ceiling} : ceil_window.
Proof. exact alloc_ceiling_range. Qed.
