(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bt X1c1.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1qy X1r2 X1nt X1rh X1re X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X05m.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require X06b.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X0x1.

Theorem dec_isave_pres : forall (d d' : dec_state bptr) b q ret b' q',
prun (speex_decode (St := pst) p_notify bits_unpack_unsigned_M bits_peek_M bits_advance_M bits_remaining_M d b 0) q = Some ((ret, d', b'), q') ->
isave_ok d -> isave_ok d'.
Proof. exact OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A.X06b.dec_isave_pres. Qed.
