(** * FO.Thm_halts_ubsan_fo — example_small_fuzzer UBSan halts, forced-only

    The UBSan build's tree proves the forced-only core directly ([HaltsUFO.halts_ubsan_core]: halting under
    [FOCore.alloc_forced_cfg], no budget premise).  The release shells are the [budget] cells at that
    configuration and, by monotonicity ([FOCore.halts_core_mono]), at the release generator's
    [forced_only_cfg] (the twin of [FO.Thm_halts_fo] for the plain build). *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_example_small_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit Require HaltsUFO.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition img : Image :=
  mkImage Tgt_example_small_fuzzer_ubsan.M.loaded_segments Tgt_example_small_fuzzer_ubsan.M.init_pc
          Tgt_example_small_fuzzer_ubsan.M.phdrs.

Theorem halts_ubsan_core_af : halts_core alloc_forced_cfg source_alloc_limit AnyExit.codes img.
Proof. exact (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.HaltsUFO.halts_ubsan_core). Qed.

Theorem halts_ubsan_alloc_forced :
  halts_allowed_T_scfg_budgets alloc_forced_cfg ShippedBudgets.lim_source AnyExit.codes img.
Proof. apply halts_allowed_T_scfg_budgets_of_core, halts_ubsan_core_af. Qed.

Theorem halts_ubsan_forced_only :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source AnyExit.codes img.
Proof.
  apply halts_allowed_T_scfg_budgets_of_core.
  exact (halts_core_mono forced_only_cfg alloc_forced_cfg _ _ _ (forced_only_cfg_least _) halts_ubsan_core_af).
Qed.
