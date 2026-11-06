(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05m.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X12c X14x X161 X16j X0r0 X0yr X0wl X0ys X0zq X0zl
X11k X0yw X0z7 X0z6 X0yb X0zx X12o X12q X153 X0v5 X0wz
X0xm X0y5 X0xb X19u
X0w7 X12f X0yz X0yv X125 X11r.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X19v.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma EH_B : @nbd_EH_cps RTA bptr.
Proof.
pose proof rta_contracts_closed as RC. pose proof rta_contracts_x as RX.
exact (nbd_EH_ok RTA AFB (rc_asan_memcpy RTA RC) (rc_asan_memset RTA RC) (rx_alloca_poison RTA RX) (rx_allocas_unpoison RTA RX) rta_lib_consts
(lsp_to_lpcF_ok RTA AFB (rx_alloca_poison RTA RX) (rx_allocas_unpoison RTA RX))
(multicomb_ok RTA AFB (rx_alloca_poison RTA RX) (rx_allocas_unpoison RTA RX) (rc_stack_malloc_2 RTA RC))
(highpass_ok RTA AFB (rc_stack_malloc_2 RTA RC) (rc_asan_memcpy RTA RC))).
Qed.

Lemma LOOP_B : sb_subframe_cps RTA.
Proof.
pose proof rta_contracts_closed as RC. pose proof rta_contracts_x as RX.
exact (sblB_subframe RTA AFB rta_lib_consts (rx_alloca_poison RTA RX) (rx_allocas_unpoison RTA RX) rta_allocas_unpoison_lo (rc_asan_memset RTA RC)
(lsp_to_lpc8_ok RTA AFB (rx_alloca_poison RTA RX) (rx_allocas_unpoison RTA RX))
(@split_cb_innov RTA bptr AFB (rx_alloca_poison RTA RX) (rx_allocas_unpoison RTA RX) rta_lib_consts)).
Qed.

Theorem MAIN_B : X19v.MAIN_stmt.
Proof. exact (MAIN_closedB EH_B LOOP_B). Qed.
