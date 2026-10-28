(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK04 YA0n YG00 YG0f YG0n YG0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YA00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YF0p.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFfs.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem afree_realizes_closed : forall B, TfibSyms B -> (forall t, as_dhash B t = tfib_dhash t) -> afree_realizes tfibsegs B.
Proof. intros B TS HD. exact (afree_realizes_all B TS HD). Qed.
End a.
