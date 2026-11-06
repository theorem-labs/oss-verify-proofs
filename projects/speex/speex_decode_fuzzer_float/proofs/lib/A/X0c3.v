(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0ec X0fy X0fg X0em X0fd X0g3 X0fz
X0g0 X0g1 X0g2 X0f4 X0c6 X0ep X0e6 X0co X0cl X0cj
X0dh X0cx X0c1.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X14x X16j X161 X157 X15y X16o X16k X16l X16m X16n X15p X12r X15a X14r X139 X136 X134 X142 X13i X12m.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X157 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12r OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14r OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X139 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X136 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X134 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X142 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13i OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem rta_refill_closed : refill_stmt.
Proof. exact (refill_ok fixed_commit_ok). Qed.

Theorem rta_core_sec_closed : core_stmt_sec.
Proof. exact (mal_core_sec grant_node_ok fixed_commit_pab_ok). Qed.

Theorem rta_free_closed : free_contract RTA.
Proof. exact (rta_free (drain_ok fixed_commit_ok (fun p HOK => item_sec_ok p munmap_ok madvise_ok HOK)) fixed_commit_ok). Qed.

Theorem rta_malloc_closed : malloc_contract RTA.
Proof. exact (X158.rta_malloc (X155.core_prim rta_refill_closed) rta_core_sec_closed). Qed.

Theorem rta_calloc_closed : calloc_contract RTA.
Proof. exact (X12m.rta_calloc rta_refill_closed). Qed.

Theorem rta_contracts_closed : rt_contracts RTA.
Proof. exact (rta_contracts rta_refill_closed rta_core_sec_closed rta_free_closed). Qed.
End B_TWIN.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem rta_refill_closed : refill_stmt.
Proof. exact (refill_ok fixed_commit_ok). Qed.

Theorem rta_core_sec_closed : core_stmt_sec.
Proof. exact (mal_core_sec grant_node_ok fixed_commit_pab_ok). Qed.

Theorem rta_free_closed : free_contract RTA.
Proof. exact (rta_free (drain_ok fixed_commit_ok (fun p HOK => item_sec_ok p munmap_ok madvise_ok HOK)) fixed_commit_ok). Qed.

Theorem rta_malloc_closed : malloc_contract RTA.
Proof. exact (X0en.rta_malloc (X0ek.core_prim rta_refill_closed) rta_core_sec_closed). Qed.

Theorem rta_calloc_closed : calloc_contract RTA.
Proof. exact (X0c1.rta_calloc rta_refill_closed). Qed.

Theorem rta_contracts_closed : rt_contracts RTA.
Proof. exact (rta_contracts rta_refill_closed rta_core_sec_closed rta_free_closed). Qed.
