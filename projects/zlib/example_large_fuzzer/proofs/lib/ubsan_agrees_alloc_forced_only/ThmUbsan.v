(* [comment removed for export] *)
(* [comment removed for export] *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import BaseUbsan.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Rnd Zlib_iface Zlib_closed.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Zlib_iface Zlib_closed.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* forced-only port: the equivalence over the filtered run at the zlib re-issue's configuration. *)
Theorem base_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg
    alloc_forced_cfg
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage
       OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.loaded_segments
       OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.init_pc
       OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage
       OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.loaded_segments
       OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.init_pc
       OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.phdrs).
Proof.
  exact (base_ubsan_pinned_of_zlib (fun CE => @P.Zlib_closed.zR CE) (fun CE => @U.Zlib_closed.zR CE)
           P.Zlib_closed.zlib_closed_all U.Zlib_closed.zlib_closed_all).
Qed.

(* forced-only port: the release's [budget] cell at the same configuration. *)
Theorem base_ubsan_budgets :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    alloc_forced_cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage
       OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.loaded_segments
       OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.init_pc
       OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Src_zlib_example_large_fuzzer_repro.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage
       OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.loaded_segments
       OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.init_pc
       OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.Tgt_example_large_fuzzer_ubsan.M.phdrs).
Proof.
  cbv delta [ShippedBudgets.lim_source ShippedBudgets.lim_target].
  apply strong_universal_error_free_T_scfg_budgets_of_scfg. exact base_ubsan.
Qed.
