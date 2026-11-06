(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith List.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OSSVerify.openssl.hashtable.images.Plain.
Require OSSVerify.openssl.hashtable.images.Asan.
From OSSVerify.Proofs.openssl.hashtable.lib Require HTSpec H0FiTail H0LeafTail HAFullDefs HARefusedClosed HTHfTopA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

Section HtAsan.
  (* [comment removed for export] *)
  Hypothesis L0 : HAFullDefs.file_leaf_stmt HAFullDefs.K0 HAFullDefs.T_file.
  Hypothesis LK : HAFullDefs.file_leaf_stmt HAFullDefs.KGE1 HAFullDefs.T_file.

Theorem strong_universal_error_free_hashtable_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.hashtable.images.Plain.M.loaded_segments OSSVerify.openssl.hashtable.images.Plain.M.init_pc OSSVerify.openssl.hashtable.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.hashtable.images.Asan.M.loaded_segments OSSVerify.openssl.hashtable.images.Asan.M.init_pc OSSVerify.openssl.hashtable.images.Asan.M.phdrs).
Proof.
  exact (HTHfTopA.hf_base HTSpec.t_target_ht H0LeafTail.h0_leaf_tail (HARefusedClosed.ha_full_r L0 LK)).
Qed.

  (* [comment removed for export] *)
  Theorem full16 : HtHaltsLib.full_stmt ConeCfg.CFG HTHfTopA.X0 LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source HTSpec.t_target_ht.
  Proof. exact (HTHfTopA.full_x16 HTSpec.t_target_ht (HARefusedClosed.ha_full_r L0 LK)). Qed.
End HtAsan.
