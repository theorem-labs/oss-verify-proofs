(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AF0q.v (donor image sha256 7093581aab04), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from A/AF0q.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA0n_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0f.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w YG0d_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YA00_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AFfs_w.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem afree_realizes_closed : forall B, TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) -> afree_realizes tfibsegs B.
Proof. intros B TS HD. exact (afree_realizes_all B TS HD). Qed.
End a.
