(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck X1cu X1cv.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1nu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s X05u X05t
X081 X05l X05m X09f X06d X069 X05w X063 X082 X08y X0b1 X0b0 X068
X0az X09e X06n X091 X08x X08u X090 X08l X08m X094 X08n X092 X08o
X095 X093 X08z.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X08t X08s X08r X08q X08w X08v.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X0wl X0wn X0wm X0ys X0x2 X0yt X0zq X0x1 X0zo X0xf X0xe X0zp X0zl X0zs X0zc X0zd X0zu X0ze X0zt X0zf X0zv X0zr.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X0zk X0zj X0zi X0zh X0zn X0zm.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zo OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xf OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0xe OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zs OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zc OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zd OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zu OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ze OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zf OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zv OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zr.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zk OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zj OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zi OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zh OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zm.

Section NbDecodeCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis AF_ERRV : forall Σ m, ART RT Σ m -> acc bsegs m STDERR_VAR 8.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.
Lemma AF_SMALL : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> n <= 64512 -> SEGTOP_A <= p.
Proof using AF. exact (af_live_small RT AF). Qed.
Hypothesis FPL : fprintf_lib_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis SM5 : stack_malloc_contract RT 5.
Hypothesis SF5 : stack_free_contract RT 5.
Hypothesis MMV : memmove_icontract RT e_asan_memmove.
Hypothesis MST : memset_icontract RT e_asan_memset.
Hypothesis EH : @nbd_EH_cps RT bptr.

Theorem nb_decode_cps : forall st : nb_state bptr, dec_cps_at RT OUT_rep ERR_rep IO_FP A_nb_decode (DecNB st).
Proof using AF ERR_loc OUT_loc IO_img AF_DRV AF_ERRV AF_LIB FPL SM5 SF5 MMV MST EH.
exact (nb_decode_cps_main RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV AF_ERRV AF_LIB FPL SM5 SF5 MMV MST EH (nbd_armB RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV AF_ERRV AF_LIB FPL SM5 SF5 MMV MST EH (nbd_armN RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV AF_ERRV AF_LIB FPL SM5 SF5 MMV MST EH) (nbd_armC RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV AF_ERRV AF_LIB FPL SM5 SF5 MMV MST EH)) (nbd_notify RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV AF_ERRV AF_LIB FPL SM5 SF5 MMV MST EH)).
Qed.

End NbDecodeCPS.
End B_TWIN.

Section NbDecodeCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AF_DRV : forall Σ m, ART RT Σ m -> drv_consts m.
Hypothesis AF_ERRV : forall Σ m, ART RT Σ m -> acc asegs m STDERR_VAR 8.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.
Lemma AF_SMALL : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> n <= 64512 -> SEGTOP_A <= p.
Proof using AF. exact (af_live_small RT AF). Qed.
Hypothesis FPL : fprintf_lib_icontract RT OUT_rep ERR_rep IO_FP.
Hypothesis SM5 : stack_malloc_contract RT 5.
Hypothesis SF5 : stack_free_contract RT 5.
Hypothesis MMV : memmove_icontract RT e_asan_memmove.
Hypothesis MCP : memcpy_icontract RT e_asan_memcpy.
Hypothesis MST : memset_icontract RT e_asan_memset.
Hypothesis EH : @nbd_EH_cps RT bptr.

Theorem nb_decode_cps : forall st : nb_state bptr, dec_cps_at RT OUT_rep ERR_rep IO_FP A_nb_decode (DecNB st).
Proof using AF ERR_loc OUT_loc IO_img AF_DRV AF_ERRV AF_LIB FPL SM5 SF5 MMV MCP MST EH.
exact (nb_decode_cps_main RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV AF_ERRV AF_LIB FPL SM5 SF5 MMV MCP MST EH (nbd_armB RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV AF_ERRV AF_LIB FPL SM5 SF5 MMV MCP MST EH (nbd_armN RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV AF_ERRV AF_LIB FPL SM5 SF5 MMV MCP MST EH) (nbd_armC RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV AF_ERRV AF_LIB FPL SM5 SF5 MMV MCP MST EH)) (nbd_notify RT AF OUT_rep ERR_rep IO_FP ERR_loc OUT_loc IO_img AF_DRV AF_ERRV AF_LIB FPL SM5 SF5 MMV MCP MST EH)).
Qed.

End NbDecodeCPS.
