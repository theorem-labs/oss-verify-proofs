(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From Stdlib Require Import List ZArith.
Require OSSVerify.coturn.FuzzStunClient.images.Plain.
Require OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import BothTop.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanMainLib MainGlueDefsB MainGlueB ItabBoth W0BStates1 Main5Both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section W1.
  Variable TW1 : mtree.
  Hypothesis TW1_ok : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat HG1_s ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) TW1 = true.

  Theorem both_base_W1 :
    strong_universal_error_free_T_budgets SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage OSSVerify.coturn.FuzzStunClient.images.Plain.M.loaded_segments
               OSSVerify.coturn.FuzzStunClient.images.Plain.M.init_pc
               OSSVerify.coturn.FuzzStunClient.images.Plain.M.phdrs)
      (mkImage OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.loaded_segments
               OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.init_pc
               OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.phdrs).
  Proof. exact (both_base_T5 (TREE5 TW1) (TREE5_ok TW1 TW1_ok)). Qed.
End W1.
