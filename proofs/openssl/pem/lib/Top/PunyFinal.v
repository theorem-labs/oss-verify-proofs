(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Top Require Import TopBridge PemTop.
Require OssFuzzTheorems.Proofs.openssl.pem.lib.Top.LaneP.
Require OssFuzzTheorems.Proofs.openssl.pem.lib.P.Fz_closed.
Require OssFuzzTheorems.Proofs.openssl.pem.lib.Top.LaneU.
Require OssFuzzTheorems.Proofs.openssl.pem.lib.U.Fz_closed.
Require OssFuzzTheorems.Proofs.openssl.pem.lib.B.Fz_clientA.
Require OssFuzzTheorems.Proofs.openssl.pem.lib.A.Fz_clientA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem p_realizes : PemTop.P_realizes.
Proof. exact (OssFuzzTheorems.Proofs.openssl.pem.lib.Top.LaneP.P_realizes_of OssFuzzTheorems.Proofs.openssl.pem.lib.P.Fz_closed.pem_client). Qed.

Theorem p_realizes_san : PemTop.P_realizes_san.
Proof. exact (OssFuzzTheorems.Proofs.openssl.pem.lib.Top.LaneP.P_realizes_san_of OssFuzzTheorems.Proofs.openssl.pem.lib.P.Fz_closed.pem_client). Qed.

Theorem u_realizes : PemTop.U_realizes.
Proof. exact (OssFuzzTheorems.Proofs.openssl.pem.lib.Top.LaneU.U_realizes_of OssFuzzTheorems.Proofs.openssl.pem.lib.U.Fz_closed.pem_client). Qed.

Theorem b_realizes : PemTop.B_realizes.
Proof. exact OssFuzzTheorems.Proofs.openssl.pem.lib.B.Fz_clientA.A_realizes. Qed.

Theorem a_realizes : PemTop.A_realizes.
Proof. exact OssFuzzTheorems.Proofs.openssl.pem.lib.A.Fz_clientA.A_realizes. Qed.

(* [comment removed for export] *)
Definition pinned_both := PemTop.pinned_both p_realizes b_realizes.
Definition base_both := PemTop.base_both p_realizes_san b_realizes.
Definition base_asan := PemTop.base_asan p_realizes_san a_realizes.


