(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.   (* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ZTopC OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AsanMain.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require Import PImg PlainClosed.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.AImg OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.AMalloc_iface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.AFake_iface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.AHarness_iface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.ADriver_iface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.AInstance OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.AInstanceM OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.AInstanceF OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.AFreeAll OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AsanW.AMain_final OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.AClient_inst OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AsanW.AMain_u3closed.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U3A Require Import U2AIface InfAIface.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Require LinuxProcessSemantics.LinuxProcessSem.State.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Theorem base_asan_u3 :
  strong_universal_error_free_T_scfg_budgets alloc_forced_cfg SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage psegs p_init_pc p_phdrs) (mkImage asegs a_init_pc a_phdrs).
Proof. exact (base_asan plain_implC_closed ASTAGE asan_implC_u3). Qed.

(* [comment removed for export] *)
Theorem base_asan_plain_u3 :
  strong_universal_error_free_T_scfg alloc_forced_cfg (mkImage psegs p_init_pc p_phdrs) (mkImage asegs a_init_pc a_phdrs).
Proof. exact (base_asan_plain plain_implC_closed ASTAGE asan_implC_u3). Qed.

(* [comment removed for export] *)
Theorem halts_asan_u3_core :
  halts_core alloc_forced_cfg LinuxProcessSemantics.LinuxProcessSem.State.source_alloc_limit AnyExit.codes
    (mkImage asegs a_init_pc a_phdrs).
Proof. exact (halts_asanC plain_implC_closed ASTAGE asan_implC_u3). Qed.

(* tier 1 port: the forced-only entry's halts row (every family forced-only, at the shipped budget),
   read off the core by monotonicity in the configuration. *)
Theorem halts_asan_u3 :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source AnyExit.codes (mkImage asegs a_init_pc a_phdrs).
Proof.
  apply halts_allowed_T_scfg_budgets_of_core.
  exact (halts_core_mono forced_only_cfg alloc_forced_cfg _ _ _ (forced_only_cfg_least _) halts_asan_u3_core).
Qed.
