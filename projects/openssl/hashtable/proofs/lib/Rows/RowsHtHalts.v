(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.MustExit.
Require LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.
Require OSSVerify.openssl.hashtable.images.Plain.
Require OSSVerify.openssl.hashtable.images.Ubsan.
Require OSSVerify.openssl.hashtable.images.Asan.
Require OSSVerify.openssl.hashtable.images.AsanUbsan.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType Fs State Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import ShapeAlg Spec SpecGen.
From OSSVerify.Proofs.openssl.hashtable.lib Require ShapeCfg ConeCfg HTSpec HtHaltsLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module HaltsCfgForcedOnly <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg.
End HaltsCfgForcedOnly.

Module OpensslHashtableHaltsPlainExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End OpensslHashtableHaltsPlainExits.

Module OpensslHashtableHaltsUbsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End OpensslHashtableHaltsUbsanExits.

Module OpensslHashtableHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End OpensslHashtableHaltsAsanExits.

Module OpensslHashtableHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End OpensslHashtableHaltsBothExits.

Section HtHalts.
  (* [comment removed for export] *)
  Hypothesis FULLP : HtHaltsLib.full_stmt ConeCfg.CFG
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.hashtable.images.Plain.M.loaded_segments OSSVerify.openssl.hashtable.images.Plain.M.init_pc OSSVerify.openssl.hashtable.images.Plain.M.phdrs)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source HTSpec.t_target_ht.
  Hypothesis FULLU : HtHaltsLib.full_stmt ConeCfg.CFG
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.hashtable.images.Ubsan.M.loaded_segments OSSVerify.openssl.hashtable.images.Ubsan.M.init_pc OSSVerify.openssl.hashtable.images.Ubsan.M.phdrs)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source HTSpec.t_target_ht.
  Hypothesis FULLA : HtHaltsLib.full_stmt ConeCfg.CFG
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.hashtable.images.Asan.M.loaded_segments OSSVerify.openssl.hashtable.images.Asan.M.init_pc OSSVerify.openssl.hashtable.images.Asan.M.phdrs)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source HTSpec.t_target_ht.
  Hypothesis FULLB : HtHaltsLib.full_stmt ConeCfg.CFG
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.hashtable.images.AsanUbsan.M.loaded_segments OSSVerify.openssl.hashtable.images.AsanUbsan.M.init_pc OSSVerify.openssl.hashtable.images.AsanUbsan.M.phdrs)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source HTSpec.t_target_ht.

Theorem halts_allowed_openssl_hashtable_halts_plain :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    OpensslHashtableHaltsPlainExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.hashtable.images.Plain.M.loaded_segments OSSVerify.openssl.hashtable.images.Plain.M.init_pc OSSVerify.openssl.hashtable.images.Plain.M.phdrs).
Proof.
  apply (HtHaltsLib.halts_of_full ConeCfg.CFG _ _ HTSpec.t_target_ht).
  - exact HtHaltsLib.in_codes02_2.
  - exact HtHaltsLib.exits_in_t_target_ht_02.
  - exact FULLP.
Qed.

Theorem halts_allowed_openssl_hashtable_halts_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    OpensslHashtableHaltsUbsanExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.hashtable.images.Ubsan.M.loaded_segments OSSVerify.openssl.hashtable.images.Ubsan.M.init_pc OSSVerify.openssl.hashtable.images.Ubsan.M.phdrs).
Proof.
  apply (HtHaltsLib.halts_of_full ConeCfg.CFG _ _ HTSpec.t_target_ht).
  - exact HtHaltsLib.in_codes02_2.
  - exact HtHaltsLib.exits_in_t_target_ht_02.
  - exact FULLU.
Qed.

Theorem halts_allowed_openssl_hashtable_halts_asan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    OpensslHashtableHaltsAsanExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.hashtable.images.Asan.M.loaded_segments OSSVerify.openssl.hashtable.images.Asan.M.init_pc OSSVerify.openssl.hashtable.images.Asan.M.phdrs).
Proof.
  apply (HtHaltsLib.halts_of_full ConeCfg.CFG _ _ HTSpec.t_target_ht).
  - exact HtHaltsLib.in_codes02_2.
  - exact HtHaltsLib.exits_in_t_target_ht_02.
  - exact FULLA.
Qed.

Theorem halts_allowed_openssl_hashtable_halts_both :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    OpensslHashtableHaltsBothExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.hashtable.images.AsanUbsan.M.loaded_segments OSSVerify.openssl.hashtable.images.AsanUbsan.M.init_pc OSSVerify.openssl.hashtable.images.AsanUbsan.M.phdrs).
Proof.
  apply (HtHaltsLib.halts_of_full ConeCfg.CFG _ _ HTSpec.t_target_ht).
  - exact HtHaltsLib.in_codes02_2.
  - exact HtHaltsLib.exits_in_t_target_ht_02.
  - exact FULLB.
Qed.

End HtHalts.
