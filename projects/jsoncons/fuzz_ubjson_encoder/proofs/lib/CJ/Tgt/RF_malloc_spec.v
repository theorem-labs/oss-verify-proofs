(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocTree ASlot_I MallocFacts_AM MallocFacts_AMP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Tgt Require Import RMallocTree RMalloc_iface RAllocSlot_iface RF_malloc_core RF_malloc_top RASlot_I RF_alloc_slot RF_malloc_big RF_am_P RF_alloc_meta.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RF_malloc_spec () := "C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt8RASlot_I8ras_pre2C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt=RF_alloc_slot@ralloc_slot_specC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt=RF_alloc_slot>ras_pre2_introC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent>MallocFacts_AM8am_pre_gC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt=RF_alloc_meta@ralloc_meta_specC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt=RF_malloc_big8ramp_bigC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt=RF_malloc_big9rbig_specC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt=RF_malloc_topBrmalloc_spec_proofC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7ASlot_I7as_inv200C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt:RMallocRep<ref_reservedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Tgt=RF_malloc_topFrmalloc_spec_fit_proofC13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


Theorem rmalloc_spec : rmalloc_stmt.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_malloc_spec ()) ["CEIL_WRAP_1"] "p;1p;2p;4p;6g0000j17Tg001Cj16Tg002cj10Tg004Aj21Tg005\j15Tg007<j12Tg008Tj43Tg009mj64Tp,4RUNpR0%70g00;O%60%00P0g00<d,10%50%20C3E4o"). Qed.

(* [comment removed for export] *)
Theorem rmalloc_spec_fit : rmalloc_stmt_fit.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_malloc_spec ()) ["CEIL_WRAP_1"] "p;1p;2p;4p;6g0000j17Tg001Cj16Tg002cj10Tg004Aj21Tg005\j15Tg007<j12Tg008Tj43Tg00>=j64Tp,4RUNpR0%70g00;O%60%00P0g00<d,10%50%20C3E4o"). Qed.
End CEIL_WRAP_1.


