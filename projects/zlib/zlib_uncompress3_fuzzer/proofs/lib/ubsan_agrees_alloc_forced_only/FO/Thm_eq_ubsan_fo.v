(* Tier-2b (a worker): the forced-only entry's UBSan equivalence row for zlib_uncompress3_fuzzer.  The bundle's
   equivalence proof (Thm_uncompress3_ubsan_mr.thm_of_lib, over the two zlib library contracts), ported onto
   the filtered step at memory forced-only (patches/zlib_uncompress3_fuzzer-t2b-eq), states the configured
   shell at alloc_forced_cfg; the spec's own bridge strong_universal_error_free_T_scfg_budgets_of_scfg moves it
   to the shipped budgets. *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Src_zlib_zlib_uncompress3_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress3_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Thm_uncompress3_ubsan_mr I8S.S_TopI I8U.T_TopI.

Theorem eq_ubsan_forced_only :
  strong_universal_error_free_T_scfg_budgets (mkSpuriousCfg false true true true true true)
    ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments Src_zlib_zlib_uncompress3_fuzzer_repro.M.init_pc
             Src_zlib_zlib_uncompress3_fuzzer_repro.M.phdrs)
    (mkImage Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments Tgt_zlib_uncompress3_fuzzer_ubsan.M.init_pc
             Tgt_zlib_uncompress3_fuzzer_ubsan.M.phdrs).
Proof.
  cbv delta [ShippedBudgets.lim_source ShippedBudgets.lim_target].
  apply strong_universal_error_free_T_scfg_budgets_of_scfg.
  exact (Thm_uncompress3_ubsan_mr.thm_of_lib (@I8S.S_TopI.zlib_contract_S8) (@I8U.T_TopI.zlib_contract_U8)).  (* the contracts for every run *)
Qed.
