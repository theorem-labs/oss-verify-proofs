(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Ceiling.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_CeilWin () := "C69OSSVerify5KrLib2K53Lib7CeilingCalloc_ceiling_rangeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib7Ceiling7Ceiling00C1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ceil_window {CE : Ceiling} : Prop := (0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000)%Z.

Lemma ceil_window_holds {CE : Ceiling} : ceil_window.
Proof.
ltac2:(KReplay.run1 (kr_t_CeilWin ()) [] "h02CEp;1g0000j10Tg0017f0#0W0o"). Qed.
