(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AF0q.v, with its module paths changed, names TfibSyms -> GrantSyms. *)
(* Relocated from proofs/libreac/fuzz_grant/lib/A/AF0q.v at 25e3d17bdb50 by port_core 83f5203d2a2f onto libdiginet/fuzz_transport (asan). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK04 YA0n YG00 YG0f YG0n YG0d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YA00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YF0p.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AFfs.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem afree_realizes_closed : forall B, TransportSyms B -> (forall t, as_dhash B t = tfib_dhash t) -> afree_realizes tfibsegs B.
Proof. intros B TS HD. exact (afree_realizes_all B TS HD). Qed.
End a.
