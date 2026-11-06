(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0ec X0fy X0fg X0fw X0fx X0fu X0bt X0f3 X0eb.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X14x X16j X161 X16h X16i X16f X12e X15o X14w.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16h OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16i OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16f OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12e OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X15o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14w.

Theorem rta_contracts_x_of : memmove_icontract RTA e_asan_memmove -> memmove_icontract RTA e_memmove -> bcmp_icontract RTA -> rt_contracts_x RTA.
Proof.
intros X4 X5 X6.
exact (mkRTX RTA rta_realloc rta_stack_malloc_5 rta_stack_malloc_8 rta_stack_free X4 X5 X6 rta_alloca_poison rta_allocas_unpoison rta_allocas_unpoison_nop).
Qed.

Theorem rta_contracts_x_of_bcmp : bcmp_icontract RTA -> rt_contracts_x RTA.
Proof. exact (rta_contracts_x_of rta_asan_memmove rta_memmove). Qed.

Theorem rta_contracts_x : rt_contracts_x RTA.
Proof. exact (rta_contracts_x_of_bcmp rta_bcmp). Qed.
End B_TWIN.

Theorem rta_contracts_x_of : memmove_icontract RTA e_asan_memmove -> memmove_icontract RTA e_memmove -> bcmp_icontract RTA -> rt_contracts_x RTA.
Proof.
intros X4 X5 X6.
exact (mkRTX RTA rta_realloc rta_stack_malloc_5 rta_stack_malloc_8 rta_stack_free X4 X5 X6 rta_alloca_poison rta_allocas_unpoison rta_allocas_unpoison_nop).
Qed.

Theorem rta_contracts_x_of_bcmp : bcmp_icontract RTA -> rt_contracts_x RTA.
Proof. exact (rta_contracts_x_of rta_asan_memmove rta_memmove). Qed.

Theorem rta_contracts_x : rt_contracts_x RTA.
Proof. exact (rta_contracts_x_of_bcmp rta_bcmp). Qed.
