(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.   (* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW Require Import ZTopC AsanMain.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.Plain Require Import PImg PlainClosed.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg AMalloc_iface AFake_iface AHarness_iface ADriver_iface AInstance AInstanceM AInstanceF AFreeAll AMain_final AClient_inst AMain_u1closed.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U1A Require Import U2AIface InfAIface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Require LinuxProcessSemantics.LinuxProcessSem.State.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* the tracker tier 1 port: both runs are the filtered runs at memory forced-only ([FOCore.alloc_forced_cfg], the
   forced-only entry's [SpuriousCfgM.cfg]). *)
Theorem base_asan_u1 :
  strong_universal_error_free_T_scfg_budgets alloc_forced_cfg SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage psegs p_init_pc p_phdrs) (mkImage asegs a_init_pc a_phdrs).
Proof. exact (base_asan plain_implC_closed ASTAGE asan_implC_u1). Qed.

(* [comment removed for export] *)
Theorem base_asan_plain_u1 :
  strong_universal_error_free_T_scfg alloc_forced_cfg (mkImage psegs p_init_pc p_phdrs) (mkImage asegs a_init_pc a_phdrs).
Proof. exact (base_asan_plain plain_implC_closed ASTAGE asan_implC_u1). Qed.

(* the tracker tier 1 port: the halting core at memory forced-only, no budget premise. *)
Theorem halts_asan_u1_core :
  halts_core alloc_forced_cfg LinuxProcessSemantics.LinuxProcessSem.State.source_alloc_limit AnyExit.codes
    (mkImage asegs a_init_pc a_phdrs).
Proof. exact (halts_asanC plain_implC_closed ASTAGE asan_implC_u1). Qed.

(* the tracker tier 1 port: the forced-only entry's halts row (every family forced-only, at the shipped budget), read off
   the core by monotonicity in the configuration. *)
Theorem halts_asan_u1 :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source AnyExit.codes (mkImage asegs a_init_pc a_phdrs).
Proof.
  apply halts_allowed_T_scfg_budgets_of_core.
  exact (halts_core_mono forced_only_cfg alloc_forced_cfg _ _ _ (forced_only_cfg_least _) halts_asan_u1_core).
Qed.
