(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AxSymExec3 AxSymExec3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition ra_t : Type := AX2.expr -> Z -> Z -> AX2.expr -> Z -> Z -> bool.
Definition ra_fast (kn : list AX2.kentry) : ra_t := AX2B.ranges_apartB (AX2B.mkbc kn).
Lemma ra_fast_eq (kn : list AX2.kentry) : ra_fast kn = AX2.ranges_apart kn.
Proof. exact (AX2B.ranges_apartB_eqf kn). Qed.
