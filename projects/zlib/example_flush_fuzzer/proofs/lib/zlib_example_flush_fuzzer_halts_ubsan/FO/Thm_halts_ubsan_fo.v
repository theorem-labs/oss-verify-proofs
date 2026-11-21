(** * FO.Thm_halts_ubsan_fo — example_flush_fuzzer UBSan halts, forced-only

    The tree proves the forced-only core directly ([HaltsUFO.zc_halts_ubsan_core]: halting under
    [FOCore.alloc_forced_cfg], no budget premise), closed by the bundle's own instances (as its
    [Proof.v] closes [HaltsFL.zc_halts_ubsan]).  The release shells are the [budget] cells at that
    configuration and, by monotonicity ([FOCore.halts_core_mono]), at the release generator's
    [forced_only_cfg]; the same shape as tier 0's [FO.Thm_halts_fo] for the plain build. *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.World Require Import Tgt_example_flush_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require HaltsUFO.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require FL4Inst.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Spec.MF_Kit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require PlainU0.PlainClosed.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition img_ubsan : Image :=
  mkImage Tgt_example_flush_fuzzer_ubsan.M.loaded_segments Tgt_example_flush_fuzzer_ubsan.M.init_pc
    Tgt_example_flush_fuzzer_ubsan.M.phdrs.

Theorem halts_ubsan_core_af : halts_core alloc_forced_cfg source_alloc_limit AnyExit.codes img_ubsan.
Proof.
  exact (OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.HaltsUFO.zc_halts_ubsan_core OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.FL4Inst.FL4
           OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Spec.MF_Kit.QF_kit
           OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PlainU0.PlainClosed.ubsan_implC_closed).
Qed.

Theorem halts_ubsan_alloc_forced :
  halts_allowed_T_scfg_budgets alloc_forced_cfg ShippedBudgets.lim_source AnyExit.codes img_ubsan.
Proof. apply halts_allowed_T_scfg_budgets_of_core, halts_ubsan_core_af. Qed.

Theorem halts_ubsan_forced_only :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source AnyExit.codes img_ubsan.
Proof.
  apply halts_allowed_T_scfg_budgets_of_core.
  exact (halts_core_mono forced_only_cfg alloc_forced_cfg _ _ _ (forced_only_cfg_least _) halts_ubsan_core_af).
Qed.
