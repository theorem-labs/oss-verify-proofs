(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocTree ASlot_I MallocFacts_AM MallocFacts_AMP.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RMallocTree RMalloc_iface RAllocSlot_iface RF_malloc_core RF_malloc_top RASlot_I RF_alloc_slot RF_malloc_big RF_am_P RF_alloc_meta.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_malloc_spec () := "C5ARocqVerifyHarness?AgentSubmission5Ubsan8RASlot_I8ras_pre2C5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_alloc_slot@ralloc_slot_specC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_alloc_slot>ras_pre2_introC5ARocqVerifyHarness?AgentSubmission6Malloc>MallocFacts_AM8am_pre_gC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_alloc_meta@ralloc_meta_specC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_malloc_big8ramp_bigC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_malloc_big9rbig_specC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_malloc_topBrmalloc_spec_proofI5ARocqVerifyHarness?AgentSubmission6Malloc7ASlot_I7as_inv200C5ARocqVerifyHarness?AgentSubmission5Ubsan:RMallocRep<ref_reserved".

Section CANSEC1. Context {rc : runConstT}.
Theorem rmalloc_spec : rmalloc_stmt.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_malloc_spec ()) ["CANSEC1"] "p;1p;2p;4p;6g0000j17Tg000lj16Tg0025j10Tg003<j21Tg004?j15Tg005Hj12Tg006Ij43Tg007Kj64Tp,2rcR0%70g008V%60%00P0g009S,10%50%20C3E4o"). Qed.

End CANSEC1.
