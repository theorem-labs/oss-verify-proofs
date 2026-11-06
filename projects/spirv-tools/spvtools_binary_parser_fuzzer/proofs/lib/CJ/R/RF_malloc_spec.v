(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocTree ASlot_I MallocFacts_AM MallocFacts_AMP.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.R Require Import RMallocTree RMalloc_iface RAllocSlot_iface RF_malloc_core RF_malloc_top RASlot_I RF_alloc_slot RF_malloc_big RF_am_P RF_alloc_meta.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import AcLia.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_RF_malloc_spec () := "C69OSSVerify5KrLib2CJ1R8RASlot_I8ras_pre2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1R=RF_alloc_slot@ralloc_slot_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1R=RF_alloc_slot>ras_pre2_introC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1R7RF_am_P6RAMpreC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1R=RF_alloc_meta@ralloc_meta_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1R=RF_malloc_big8ramp_bigC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1R=RF_malloc_big9rbig_specC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1R=RF_malloc_topBrmalloc_spec_proofC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ1A7ASlot_I7as_inv200C1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Section AUXSEC.
Context {AUXM : auxv_mode}.

Theorem rmalloc_spec : rmalloc_stmt.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_malloc_spec ()) ["AC_1"; "AUXSEC"] "p;3p;2p;6p;8g0000j37Tg000kj36Tg0023j30Tg0039j21Tg0041j35Tg0059j32Tg0069j63Tg007:j84Tp,5ACEILR0p,4RRNDR1p,4AUXMR2A7012g008DA6012A0012P0P1P21112A5012A2012E3G4o"). Qed.

End AUXSEC.

End AC_1.
