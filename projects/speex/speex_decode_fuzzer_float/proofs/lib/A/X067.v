(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require X00a.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X07z X05s X081 X05l X05m X06d X069
X08y X0b0 X068 X05a X0ay X0ar X065 X06a X0ax X0bd X05v.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0r9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0yr X0wl X0ys X0x2 X0zq X11k X122 X0x1 X0w7 X11i X11c X0wy X0x3 X11h X120 X0wo.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X122 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0w7 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11i OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wy OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x3 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11h OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X120 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wo.
Import ListNotations.
Open Scope Z_scope.

Section DecAll.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis IO_ssp : forall y, in_ranges IO_FP y -> ~ (B.X0r9.SSP_GUARD <= y < B.X0r9.SSP_GUARD + 8).
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis AF_ERRV : forall Σ m, ART RT Σ m -> acc bsegs m STDERR_VAR 8.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.
Hypothesis FPL : fprintf_lib_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis APO : alloca_poison_contract RT.
Hypothesis AUN_lo : allocas_unpoison_lo_contract RT.
Hypothesis AUN_nop : allocas_unpoison_nop_contract RT.
Hypothesis MEMS : memset_icontract RT e_asan_memset.
Hypothesis QMF16 : forall N, N = 320 \/ N = 640 -> qmf_synth_cps16 RT N.
Let LOST : sb_decode_lost_cps RT := sb_decode_lost_ok RT AF QMF16.
Hypothesis LOOP : sb_subframe_cps RT.
Hypothesis NBD : forall st, dec_cps_at RT OUT_rep ERR_rep IO_FP A_nb_decode (DecNB st).
Let CTL2 : forall d : dec_state bptr, ctl2_cps_at RT d := ctl2_cps_all RT AF SM0 AF_LIB.

Theorem dec_cps_all : forall d : dec_state bptr,
dec_cps_at RT OUT_rep ERR_rep IO_FP A_speex_decode_native d /\ dec_cps_at RT OUT_rep ERR_rep IO_FP A_speex_decode d.
Proof.
apply (dec_cps_induction RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_LIB NBD).
intros k IHD s low Hk.
exact (sb_decode_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img IO_ssp AF_DRV AF_ERRV AF_LIB FPL SM0 APO AUN_lo AUN_nop MEMS QMF16 LOST LOOP
k (fun d _ => dec_appends_all d) IHD (fun d _ => CTL2 d) s low Hk).
Qed.
End DecAll.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Section DecAll.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis IO_ssp : forall y, in_ranges IO_FP y -> ~ (X00a.SSP_GUARD <= y < X00a.SSP_GUARD + 8).
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis AF_ERRV : forall Σ m, ART RT Σ m -> acc asegs m STDERR_VAR 8.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.
Hypothesis FPL : fprintf_lib_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis APO : alloca_poison_contract RT.
Hypothesis AUN_lo : allocas_unpoison_lo_contract RT.
Hypothesis AUN_nop : allocas_unpoison_nop_contract RT.
Hypothesis MEMS : memset_icontract RT e_asan_memset.
Hypothesis QMF16 : forall N, N = 320 \/ N = 640 -> qmf_synth_cps16 RT N.
Let LOST : sb_decode_lost_cps RT := sb_decode_lost_ok RT AF QMF16.
Hypothesis LOOP : sb_subframe_cps RT.
Hypothesis NBD : forall st, dec_cps_at RT OUT_rep ERR_rep IO_FP A_nb_decode (DecNB st).
Let CTL2 : forall d : dec_state bptr, ctl2_cps_at RT d := ctl2_cps_all RT AF SM0 AF_LIB.

Theorem dec_cps_all : forall d : dec_state bptr,
dec_cps_at RT OUT_rep ERR_rep IO_FP A_speex_decode_native d /\ dec_cps_at RT OUT_rep ERR_rep IO_FP A_speex_decode d.
Proof.
apply (dec_cps_induction RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_LIB NBD).
intros k IHD s low Hk.
exact (sb_decode_cps RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img IO_ssp AF_DRV AF_ERRV AF_LIB FPL SM0 APO AUN_lo AUN_nop MEMS QMF16 LOST LOOP
k (fun d _ => dec_appends_all d) IHD (fun d _ => CTL2 d) s low Hk).
Qed.
End DecAll.
