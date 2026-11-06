(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0j9 X05m X06d.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require X080.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require Import X12c X14x X161 X16j X0r0 X0yr X0wl X0ys X0x2
X0x1 X0zl X11k X12o X12q X12p X153 X0v5 X19u
X0w9 X0wf X0x4 X0x6 X108 X10b X10t X10y
X114 X0ww X0ye X0xm X0y5 X0xr X0y9 X0xc X0wz
X10g X10i X10r X0xw.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X19v.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma ssv_f8 : In 0xf8 set_shadow_vals.
Proof. unfold set_shadow_vals. cbn [In]. do 12 right. left. reflexivity. Qed.
Lemma ssv_00 : In 0 set_shadow_vals.
Proof. unfold set_shadow_vals. cbn [In]. left. reflexivity. Qed.

Section Closure.
Hypothesis EH : @nbd_EH_cps RTA bptr.
Hypothesis LOOP : sb_subframe_cps RTA.

Theorem fuzz_one_closedB : fuzz_one_cpsE RTA OUT_repA ERR_repA IO_FPA X080.LIB_A.
Proof using EH LOOP.
pose proof rta_contracts_closed as RC. pose proof rta_contracts_x as RX.

assert (PAGEB : forall X F0 fs0, h_clean_cps RTA OUT_repA ERR_repA IO_FPA X F0 fs0 -> h_page_cps RTA OUT_repA ERR_repA IO_FPA X F0 fs0).
{ intros X F0 fs0 CLEAN.
exact (h_page_ok RTA AFB OUT_repA ERR_repA IO_FPA ERR_locA OUT_locA IO_imgB1 AF_DRVB
(ogg_stream_init_ok RTA AFB (rc_malloc RTA RC) (rc_memset RTA RC))
(ogg_stream_pagein_ok RTA AFB (rx_memmove RTA RX) (rc_memcpy RTA RC)
(os_lacing_expand_ok RTA AFB (rx_realloc RTA RX)) (os_body_expand_ok RTA AFB (rx_realloc RTA RX)))
X F0 fs0 CLEAN). }

assert (HDRB : forall X F0 fs0, fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) -> h_hdr_cps RTA OUT_repA ERR_repA IO_FPA X F0 fs0).
{ intros X F0 fs0 FD HX.
exact (h_hdr_ok RTA AFB OUT_repA ERR_repA IO_FPA ERR_locA OUT_locA IO_imgB1 IO_drvB AF_DRVB rta_lib_consts X HX F0 fs0
(speex_bits_destroy_ok RTA AFB (rc_free RTA RC)) (ogg_stream_clear_ok RTA AFB (rc_free RTA RC) (rc_memset RTA RC))
(ogg_sync_clear_ok RTA AFB (rc_free RTA RC)) (rc_free RTA RC) (destroy_cps_all RTA AFB (rc_free RTA RC) rta_lib_consts) FD
(speex_packet_to_header_ok RTA AFB OUT_repA ERR_repA IO_FPA ERR_locA OUT_locA IO_imgB1 AF_DRVB rta_acc_stderr_var rta_fprintf_lib
(rc_calloc RTA RC) (rc_asan_memcpy RTA RC) (rc_free RTA RC))
(ctl_cps_all RTA AFB (rc_stack_malloc_0 RTA RC) rta_lib_consts)
(init_cps_at8_of RTA (init_cps_all RTA AFB (rc_calloc RTA RC) (rc_asan_memset RTA RC) (rc_stack_malloc_0 RTA RC) rta_lib_consts)) HX). }
exact (h_fuzz_one_ok RTA AFB OUT_repA ERR_repA IO_FPA X080.LIB_A ERR_locA OUT_locA IO_imgB1 IO_drvB AF_DRVB LIB_locA
(rx_stack_malloc_8 RTA RX) (rc_set_shadow RTA RC 0xf8 ssv_f8) (rc_set_shadow RTA RC 0 ssv_00)
(rx_stack_free RTA RX 8%nat (or_intror (or_intror eq_refl))) (rc_asan_memcpy RTA RC) (rx_bcmp RTA RX)
(speex_bits_init_ok RTA AFB (rc_calloc RTA RC)) (speex_bits_destroy_ok RTA AFB (rc_free RTA RC))
(speex_bits_read_from_ok RTA AFB OUT_repA ERR_repA IO_FPA ERR_locA OUT_locA IO_imgB1 AF_DRVB rta_acc_stderr_var rta_fprintf_lib (rx_realloc RTA RX))
(ogg_sync_buffer_ok RTA AFB (rc_malloc RTA RC) (rx_realloc RTA RX) (rx_memmove RTA RX))
(ogg_sync_pageout_ok RTA AFB (ogg_sync_pageseek_ok RTA AFB (rc_memchr RTA RC)))
(ogg_stream_clear_ok RTA AFB (rc_free RTA RC) (rc_memset RTA RC)) (ogg_sync_clear_ok RTA AFB (rc_free RTA RC))
(destroy_cps_all RTA AFB (rc_free RTA RC) rta_lib_consts)
(fun d => proj2 (dec_cps_allB EH LOOP d))
dec_isave_pres
HDRB PAGEB).
Qed.

Corollary MAIN_closedB : X19v.MAIN_stmt.
Proof using EH LOOP. exact (main_stmt_closed fuzz_one_closedB). Qed.
End Closure.
