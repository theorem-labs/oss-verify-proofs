(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From OSSVerify.Proofs.openssl.punycode.lib.Top Require Import TopBridge PunyTop.
Require OSSVerify.Proofs.openssl.punycode.lib.Top.LaneP.
Require OSSVerify.Proofs.openssl.punycode.lib.P.Fz_closed.
Require OSSVerify.Proofs.openssl.punycode.lib.Top.LaneU.
Require OSSVerify.Proofs.openssl.punycode.lib.U.Fz_closed.
Require OSSVerify.Proofs.openssl.punycode.lib.A.TopA_final.
Require OSSVerify.Proofs.openssl.punycode.lib.B.TopA_final.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem p_realizes : PunyTop.P_realizes.
Proof. exact (OSSVerify.Proofs.openssl.punycode.lib.Top.LaneP.P_realizes_of OSSVerify.Proofs.openssl.punycode.lib.P.Fz_closed.rfuzz_one_closed). Qed.

Theorem p_realizes_san : PunyTop.P_realizes_san.
Proof. exact (OSSVerify.Proofs.openssl.punycode.lib.Top.LaneP.P_realizes_san_of OSSVerify.Proofs.openssl.punycode.lib.P.Fz_closed.rfuzz_one_closed). Qed.

Theorem u_realizes : PunyTop.U_realizes.
Proof. exact (OSSVerify.Proofs.openssl.punycode.lib.Top.LaneU.U_realizes_of OSSVerify.Proofs.openssl.punycode.lib.U.Fz_closed.rfuzz_one_closed). Qed.

Theorem a_realizes : PunyTop.A_realizes.
Proof. exact OSSVerify.Proofs.openssl.punycode.lib.A.TopA_final.A_realizes. Qed.

Theorem b_realizes : PunyTop.B_realizes.
Proof. exact OSSVerify.Proofs.openssl.punycode.lib.B.TopA_final.A_realizes. Qed.

(* [comment removed for export] *)
Definition pinned_ubsan := PunyTop.pinned_ubsan p_realizes u_realizes.
Definition base_ubsan := PunyTop.base_ubsan p_realizes u_realizes.

(* [comment removed for export] *)
Definition pinned_asan := PunyTop.pinned_asan p_realizes a_realizes.
Definition base_asan := PunyTop.base_asan p_realizes_san a_realizes.

(* [comment removed for export] *)
Definition pinned_both := PunyTop.pinned_both p_realizes b_realizes.
Definition base_both := PunyTop.base_both p_realizes_san b_realizes.
