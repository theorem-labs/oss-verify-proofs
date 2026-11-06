(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0ec X0fy X0fg X0em X0fd X0ek X0en
X0e4 X0ea X0fs X0bw X0fv X0c1.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X14x X16j X161 X157 X15y X155 X158 X14p X14v X16d X12h X16g X12m.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X157 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X155 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X158 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16d OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12h OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16g OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12m.

Theorem rta_contracts : refill_stmt -> core_stmt_sec -> free_contract RTA -> rt_contracts RTA.
Proof.
intros RF CS FR.
exact (mkRTC RTA (rta_malloc (core_prim RF) CS) FR rta_free_null (rta_calloc RF)
rta_memcpy rta_asan_memcpy rta_memset rta_asan_memset rta_memchr rta_strlen rta_strnlen
rta_stack_malloc_0 rta_stack_malloc_2 rta_set_shadow rta_art_facts).
Qed.
End B_TWIN.

Theorem rta_contracts : refill_stmt -> core_stmt_sec -> free_contract RTA -> rt_contracts RTA.
Proof.
intros RF CS FR.
exact (mkRTC RTA (rta_malloc (core_prim RF) CS) FR rta_free_null (rta_calloc RF)
rta_memcpy rta_asan_memcpy rta_memset rta_asan_memset rta_memchr rta_strlen rta_strnlen
rta_stack_malloc_0 rta_stack_malloc_2 rta_set_shadow rta_art_facts).
Qed.
