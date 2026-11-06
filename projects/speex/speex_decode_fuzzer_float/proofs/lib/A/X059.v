(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X0fg X0fy X001 X07z X05s X081 X08y X08u
X05m X085 X08f X08e X098 X0c3 X0c5 X0ei X066 X06j X0jd.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma EH_A : @nbd_EH_cps RTA bptr.
Proof.
pose proof rta_contracts_closed as RC. pose proof rta_contracts_x as RX.
exact (nbd_EH_ok RTA AFA (rc_asan_memcpy RTA RC) (rc_asan_memset RTA RC) (rx_alloca_poison RTA RX) (rx_allocas_unpoison RTA RX) rta_lib_consts
(lsp_to_lpcF_ok RTA AFA (rx_alloca_poison RTA RX) (rx_allocas_unpoison RTA RX) (rc_asan_memset RTA RC))
(multicomb_ok RTA AFA (rx_alloca_poison RTA RX) (rx_allocas_unpoison RTA RX) (rc_stack_malloc_2 RTA RC))).
Qed.

Theorem MAIN_A : X0je.MAIN_stmt.
Proof. exact (MAIN_closedA EH_A). Qed.
