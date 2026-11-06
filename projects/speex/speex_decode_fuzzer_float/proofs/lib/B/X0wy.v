(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bt X1c1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1qy X1r2 X1nt X1rh X1re X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X05m.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require X065.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X122.

Theorem dec_appends_all : forall d : dec_state bptr, dec_appends d.
Proof. exact OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X065.dec_appends_all. Qed.
