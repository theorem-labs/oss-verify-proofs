(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (recorded (KReplay) proofs re-proved by tactics). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec AllocIface.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocAllocLayout AllocBase AllocCalloc AllocSure AllocCredit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2MallocLayout O2Pins O2Alloc O2Sure O2Credit O2LeptBl_iface O2LeptBl2_iface O2LeptPbl_iface O2LeptPinsI.
Require OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02.TopA_final.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Top Require Import BaseBilateralBothPre.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_BaseBilateralBoth () := "C69OSSVerify5KrLib6Common8MallocngAMallocAllocLayoutEmallocng_alloc_layoutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8MallocngAMallocAllocLayoutFmallocng_calloc_layoutC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCredit8acr_sureC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2;O2LeptPinsI=s16_fuzz_callC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3TopDBaseBilateralBothPreBbilateral_both_preC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2>O2MallocLayout4LS16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O28O2Credit:s16_creditC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O26O2Pins8s16_pinsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:TopA_final:s3s_closedC1?~~~~~~~~~~~~~~~".

Theorem strong_universal_error_free_bilateral_fuzzer_both :
  strong_universal_error_free_T_scfg_budgets (Run.alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof.
  exact (@bilateral_both_pre _ _ (@acr_sure _ _ s16_credit) O2Pins.s16_pins (s16_fuzz_call s16_credit)
           (OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02.TopA_final.s3s_closed OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02.TopA.topA_runseg)).
Qed.
