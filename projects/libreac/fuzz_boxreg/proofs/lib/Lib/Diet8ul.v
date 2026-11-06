(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith Lia.
From Stdlib Require Import Zify PreOmega.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import LiaTwx2 LiaSec DietDL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac dl_first := DietDL3.dl_solve.
Ltac dlia_sec := first [ dl_first | LiaSec.lia_sec ].

Local Open Scope Z_scope.
Goal forall a b c : Z, a + 8 <= b -> b <= c -> a + 4 <= c.
Proof. intros. dlia_sec. Qed.
