(** * FO.Thm_equiv_ubsan_fo — example_flush_fuzzer plain/UBSan equivalence, forced-only

    Tier 0's port of [ZTopC] (patches/example_flush_fuzzer-plain/140-ZTopC.patch) already states
    [ZTopC.zc_base_ubsan] over the filtered run: [strong_universal_error_free_T_scfg_budgets] at
    [FOCore.alloc_forced_cfg], from the same program trees as the halts rows ([trees_equivC]).  Closed by
    the bundle's own instances, as its [BaseUbsanFL.base_ubsan_fl] closes it; [alloc_forced_cfg] is the
    entry's [SpuriousCfgM.cfg] (memory forced-only, every other family may-fail). *)

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.World Require Import Src_zlib_example_flush_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.World Require Import Tgt_example_flush_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require ZTopC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require FL4Inst.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Spec.MF_Kit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Plain.PlainClosed.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require PlainU0.PlainClosed.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem equiv_ubsan_alloc_forced :
  strong_universal_error_free_T_scfg_budgets alloc_forced_cfg ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Src_zlib_example_flush_fuzzer_repro.M.loaded_segments Src_zlib_example_flush_fuzzer_repro.M.init_pc
       Src_zlib_example_flush_fuzzer_repro.M.phdrs)
    (mkImage Tgt_example_flush_fuzzer_ubsan.M.loaded_segments Tgt_example_flush_fuzzer_ubsan.M.init_pc
       Tgt_example_flush_fuzzer_ubsan.M.phdrs).
Proof.
  exact (OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.ZTopC.zc_base_ubsan OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.FL4Inst.FL4
           OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Spec.MF_Kit.QF_kit
           OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Plain.PlainClosed.plain_implC_closed
           OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PlainU0.PlainClosed.ubsan_implC_closed).
Qed.
