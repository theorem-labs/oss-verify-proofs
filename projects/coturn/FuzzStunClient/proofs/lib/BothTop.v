(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require OSSVerify.coturn.FuzzStunClient.images.Plain.
Require OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefMain VFC_both.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanMainLib MainGlueDefsB MainGlueB StartupHSMainBoth
  ItabBoth MainTreeBoth AsanTopGlue BothTopE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section T5.
  Variable TREE5 : mtree.
  Hypothesis TREE5_ok : mtree_ok 0%nat 400000%nat 5000%nat IT_both 0%nat 0%nat (HSA HS_mainB 0%nat) (root_class 5) TREE5 = true.

  Theorem both_base_T5 :
    strong_universal_error_free_T_budgets SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage OSSVerify.coturn.FuzzStunClient.images.Plain.M.loaded_segments
               OSSVerify.coturn.FuzzStunClient.images.Plain.M.init_pc
               OSSVerify.coturn.FuzzStunClient.images.Plain.M.phdrs)
      (mkImage OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.loaded_segments
               OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.init_pc
               OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.phdrs).
  Proof.
    exact (both_base_of_specs ref_realizes_spec_san
             (both_spec_E fc_both 0%nat 400000%nat 5000%nat IT_both IT_both_ok (TREE_both TREE5) (TREES_both TREE5 TREE5_ok))).
  Qed.
End T5.
