(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/YF0q.v (donor image sha256 1c29845fe605), with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK04 YA0n YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.ReusableB Require Import YA00 YB1v YF0m YFfs. From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YF0p.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem afree_realizes_closed : forall B, TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) -> afree_realizes tfibsegs B.
Proof. intros B TS HD. exact (afree_realizes_all B TS HD). Qed.
End a.
