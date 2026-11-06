(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec AllocIface.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocAllocLayout AllocBase AllocCalloc AllocSure AllocCredit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2MallocLayout O2Pins O2Alloc O2Sure O2Credit O2LeptBl_iface O2LeptBl2_iface O2LeptPbl_iface O2LeptPinsI.
Require OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02.TopA_final.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Top Require Import BaseBilateralAsanPre.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_BaseBilateralAsan () := "C69OSSVerify5KrLib6Common8MallocngAMallocAllocLayoutEmallocng_alloc_layoutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8MallocngAMallocAllocLayoutFmallocng_calloc_layoutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCredit8acr_sureC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2LeptPinsI=s16_fuzz_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3TopDBaseBilateralAsanPreBbilateral_asan_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2>O2MallocLayout4LS16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O28O2Credit:s16_creditC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Pins8s16_pinsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:TopA_final:s3s_closedC1?~~~~~~~~~~~~~~~".

Theorem strong_universal_error_free_bilateral_fuzzer_asan :
  strong_universal_error_free_T_scfg_budgets (Run.alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof.
ltac2:(KReplay.run1 (kr_t_BaseBilateralAsan ()) [] "p;1p;3p;6g0000j14Tg001Lj13Tg002ij30Tg0042j11Tg0053j62Tg006CR0#4R1%30R0g007>R29010g0089%12g0090E2o"). Qed.
