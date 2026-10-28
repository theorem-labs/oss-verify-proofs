(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00.
Unset Lia Cache. Unset Nia Cache.
Ltac img_zside := cbn [Z.of_N N.to_nat Pos.to_nat Z.mul Pos.mul Pos.iter_op Nat.add Nat.mul]; img_lia.
Ltac img_eqrefl_t := first [ timeout 30 (exact eq_refl) | (try img_inst; img_case; reflexivity) | (try img_inst; img_case; vm_compute; reflexivity) ].   (* timeout-ok: expiry takes a later img_case arm that proves the same step; conversion on a whole image can run without bound *)
