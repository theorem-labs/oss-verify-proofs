(* Tier-2b: the forced-only entry's UBSan equivalence row for checksum_fuzzer.  The bundle's
   equivalence proof (Thm_checksum_ubsan_mr.thm_of_fuzz), ported onto the filtered step at memory
   forced-only (patches/checksum_fuzzer-t2b-eq), states the configured shell at alloc_forced_cfg; the spec's
   own bridge strong_universal_error_free_T_scfg_budgets_of_scfg moves it to the shipped budgets. *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_checksum_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Thm_checksum_ubsan_mr S0Fuzz U0Fuzz.

Theorem eq_ubsan_forced_only :
  strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
    ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Src_zlib_checksum_fuzzer_repro.M.loaded_segments Src_zlib_checksum_fuzzer_repro.M.init_pc
             Src_zlib_checksum_fuzzer_repro.M.phdrs)
    (mkImage Tgt_checksum_fuzzer_ubsan.M.loaded_segments Tgt_checksum_fuzzer_ubsan.M.init_pc
             Tgt_checksum_fuzzer_ubsan.M.phdrs).
Proof.
  cbv delta [ShippedBudgets.lim_source ShippedBudgets.lim_target].
  apply strong_universal_error_free_T_scfg_budgets_of_scfg.
  exact (Thm_checksum_ubsan_mr.thm_of_fuzz (@S0Fuzz.s0_fuzz) (@U0Fuzz.u0_fuzz)).  (* for every run *)
Qed.
