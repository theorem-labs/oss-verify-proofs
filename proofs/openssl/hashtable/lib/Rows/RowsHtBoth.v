(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import NArith List.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OssFuzzTheorems.openssl.hashtable.images.Plain.
Require OssFuzzTheorems.openssl.hashtable.images.AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require HTSpec H0FiTail H0LeafTail HBFullDefs HBRefusedClosed HTHfTopB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

Section HtAsan.
  (* [comment removed for export] *)
  Hypothesis L0 : HBFullDefs.file_leaf_stmt HBFullDefs.K0 HBFullDefs.T_file.
  Hypothesis LK : HBFullDefs.file_leaf_stmt HBFullDefs.KGE1 HBFullDefs.T_file.

Theorem strong_universal_error_free_hashtable_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.openssl.hashtable.images.Plain.M.loaded_segments OssFuzzTheorems.openssl.hashtable.images.Plain.M.init_pc OssFuzzTheorems.openssl.hashtable.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.openssl.hashtable.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.openssl.hashtable.images.AsanUbsan.M.init_pc OssFuzzTheorems.openssl.hashtable.images.AsanUbsan.M.phdrs).
Proof.
  exact (HTHfTopB.hf_base HTSpec.t_target_ht H0LeafTail.h0_leaf_tail (HBRefusedClosed.ha_full_r L0 LK)).
Qed.

  (* [comment removed for export] *)
End HtAsan.
