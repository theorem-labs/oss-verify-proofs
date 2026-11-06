(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require OSSVerify.coturn.FuzzStunClient.images.Plain.
Require OSSVerify.coturn.FuzzStunClient.images.Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefMain VFC_asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanMainLib MainGlueDefs MainGlue StartupHSMainAsan
  ItabAsan MainTreeAsan AsanTopGlue AsanTopE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section T5.
  Variable TREE5 : mtree.
  Hypothesis TREE5_ok : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 0%nat 0%nat (HSA HS_mainA 0%nat) (root_class 5) TREE5 = true.

  Theorem asan_base_T5 :
    strong_universal_error_free_T_budgets SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage OSSVerify.coturn.FuzzStunClient.images.Plain.M.loaded_segments
               OSSVerify.coturn.FuzzStunClient.images.Plain.M.init_pc
               OSSVerify.coturn.FuzzStunClient.images.Plain.M.phdrs)
      (mkImage OSSVerify.coturn.FuzzStunClient.images.Asan.M.loaded_segments
               OSSVerify.coturn.FuzzStunClient.images.Asan.M.init_pc
               OSSVerify.coturn.FuzzStunClient.images.Asan.M.phdrs).
  Proof.
    exact (asan_base_of_specs ref_realizes_spec_san
             (asan_spec_E fc_asan 0%nat 400000%nat 5000%nat IT_asan IT_asan_ok (TREE_asan TREE5) (TREES_asan TREE5 TREE5_ok))).
  Qed.
End T5.
