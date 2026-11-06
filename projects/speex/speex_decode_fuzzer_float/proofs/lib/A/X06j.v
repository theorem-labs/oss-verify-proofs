(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X0fg X0fy X001 X07z X05s X081 X05m X06d X069
X068 X08u X0c3 X0c5 X0c4 X0ei X047 X0jd
X05c X05i X06b X06e X09l X09o X09t X09w X0a5
X0a7 X0ac X0aj X063 X07m X06z X07i X06k X066.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require X080 X0je.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma ssv_f8 : In 0xf8 set_shadow_vals.
Proof. unfold set_shadow_vals. cbn [In]. do 12 right. left. reflexivity. Qed.
Lemma ssv_00 : In 0 set_shadow_vals.
Proof. unfold set_shadow_vals. cbn [In]. left. reflexivity. Qed.

Section Closure.
Hypothesis EH : @nbd_EH_cps RTA bptr.

Theorem fuzz_one_closedA : fuzz_one_cpsE RTA OUT_repA ERR_repA IO_FPA X080.LIB_A.
Proof using EH.
pose proof rta_contracts_closed as RC. pose proof rta_contracts_x as RX.
exact (h_fuzz_one_ok RTA AFA OUT_repA ERR_repA IO_FPA X080.LIB_A ERR_locA OUT_locA IO_imgA1 IO_drvA AF_DRVA LIB_locA
(rx_stack_malloc_8 RTA RX) (rc_set_shadow RTA RC 0xf8 ssv_f8) (rc_set_shadow RTA RC 0 ssv_00)
(rx_stack_free RTA RX 8%nat (or_intror (or_intror eq_refl))) (rc_asan_memcpy RTA RC) (rx_bcmp RTA RX)
(speex_bits_init_ok RTA AFA (rc_calloc RTA RC)) (speex_bits_destroy_ok RTA AFA (rc_free RTA RC))
(speex_bits_read_from_ok RTA AFA OUT_repA ERR_repA IO_FPA ERR_locA OUT_locA IO_imgA1 AF_DRVA rta_acc_stderr_var rta_fprintf_lib (rx_realloc RTA RX))
(ogg_sync_buffer_ok RTA AFA (rc_malloc RTA RC) (rx_realloc RTA RX) (rx_memmove RTA RX))
(ogg_sync_pageout_ok RTA AFA (ogg_sync_pageseek_ok RTA AFA (rc_memchr RTA RC)))
(ogg_stream_init_ok RTA AFA (rc_malloc RTA RC) (rc_memset RTA RC))
(ogg_stream_pagein_ok RTA AFA (rx_memmove RTA RX) (rc_memcpy RTA RC)
(os_lacing_expand_ok RTA AFA (rx_realloc RTA RX)) (os_body_expand_ok RTA AFA (rx_realloc RTA RX)))
(ogg_stream_clear_ok RTA AFA (rc_free RTA RC) (rc_memset RTA RC)) (ogg_sync_clear_ok RTA AFA (rc_free RTA RC))
(destroy_cps_all RTA AFA (rc_free RTA RC) rta_lib_consts)
(fun d => proj2 (dec_cps_allA EH d))
dec_isave_pres
rta_lib_consts (rc_free RTA RC)
(speex_packet_to_header_ok RTA AFA OUT_repA ERR_repA IO_FPA ERR_locA OUT_locA IO_imgA1 AF_DRVA rta_acc_stderr_var rta_fprintf_lib
(rc_calloc RTA RC) (rc_asan_memcpy RTA RC) (rc_free RTA RC))
(ctl_cps_all RTA AFA (rc_stack_malloc_0 RTA RC) rta_lib_consts)
(init_cps_all RTA AFA (rc_calloc RTA RC) (rc_asan_memset RTA RC) (rc_stack_malloc_0 RTA RC) rta_lib_consts)).
Qed.

Corollary MAIN_closedA : X0je.MAIN_stmt.
Proof using EH. exact (main_stmt_closed fuzz_one_closedA). Qed.
End Closure.
