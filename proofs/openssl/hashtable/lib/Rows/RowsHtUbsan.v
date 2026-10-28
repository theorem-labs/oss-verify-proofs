(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* The proofs in this file are Anthropic's; the theorem statements were issued by the task authors and are reproduced as issued (see NOTICE). *)
From Stdlib Require Import ZArith NArith List.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OssFuzzTheorems.openssl.hashtable.images.Plain.
Require OssFuzzTheorems.openssl.hashtable.images.Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require HTSpec H0LeafTail HUFull HUFiTail HTHfTopU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HtUbsan.
  Hypothesis LU : HUFiTail.leaf_tail_stmt HTSpec.t_target_ht.

  Lemma hu_full_of_leaves : HTHfTopU.hu_full_stmt.
  Proof.
    intros lim Hlim.
    exact (HUFull.h0_full HTSpec.t_target_ht (HUFiTail.tail_of_leaves HTSpec.t_target_ht LU) lim Hlim).
  Qed.

Theorem strong_universal_error_free_hashtable_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.openssl.hashtable.images.Plain.M.loaded_segments OssFuzzTheorems.openssl.hashtable.images.Plain.M.init_pc OssFuzzTheorems.openssl.hashtable.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.openssl.hashtable.images.Ubsan.M.loaded_segments OssFuzzTheorems.openssl.hashtable.images.Ubsan.M.init_pc OssFuzzTheorems.openssl.hashtable.images.Ubsan.M.phdrs).
Proof.
  exact (HTHfTopU.hu_base H0LeafTail.h0_leaf_tail hu_full_of_leaves).
Qed.
End HtUbsan.
