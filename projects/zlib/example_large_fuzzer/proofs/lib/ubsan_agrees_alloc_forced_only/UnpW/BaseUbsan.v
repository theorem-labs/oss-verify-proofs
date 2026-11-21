(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import ProofBase.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Rnd. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Zlib_iface Zl_iface Impl_closed.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Zlib_iface Zl_iface Impl_closed.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.FO Require FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem base_ubsan_pinned_of_zlib :
  forall (RP : Ceiling -> P.Zl_iface.zrepsL) (RU : Ceiling -> U.Zl_iface.zrepsL),
  (forall (CE__ : Ceiling) (RN__ : P.Rnd.RunRnd), @P.Zl_iface.zlib_okL CE__ RN__ (RP CE__)) ->
  (forall (CE__ : Ceiling) (RN__ : P.Rnd.RunRnd), @U.Zl_iface.zlib_okL CE__ RN__ (RU CE__)) ->
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg
    OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.FO.FOCore.alloc_forced_cfg
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage
       OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.loaded_segments
       OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.init_pc
       OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.SrcO_zlib_example_large_fuzzer_repro.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage
       OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.loaded_segments
       OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.init_pc
       OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World.TgtO_example_large_fuzzer_ubsan.M.phdrs).
Proof.
  intros RP RU ZP ZU. apply base_ubsan_of_impls.
  - exact (P.Impl_closed.impl_P_of_zlib RP ZP).
  - exact (U.Impl_closed.impl_U_of_zlib RU ZU).
Qed.

(* [comment removed for export] *)

