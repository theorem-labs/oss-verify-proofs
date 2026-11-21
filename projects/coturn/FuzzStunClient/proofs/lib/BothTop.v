(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the main trees are one per launch rseq layout, and both_halts_T5 gives the halting statement through Corpus/HaltsKitFO.v from the trees' dead-arm checks. *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require OSSVerify.coturn.FuzzStunClient.images.Plain.
Require OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefMain VFC_both.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanMainLib MainGlueDefsB MainGlueB StartupHSMainBoth
  ItabBoth MainTreeBoth AsanTopGlue BothTopE.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import DeadArm.
Require OSSVerify.Core.Shapes.
Require OSSVerify.Proofs.coturn.FuzzStunClient.lib.Corpus.HaltsKitFO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import AP.   (* [rseq_z], as BothTopE reads it *)

Section T5.
  (* one main tree per rseq layout; both_spec_E takes the launch's. *)
  Variable TREE5 : bool -> mtree.
  Hypothesis TREE5_ok : forall rsb, mtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_both 0%nat 0%nat (HSA rsb (HS_mainB (rseq_z rsb)) 0%nat) (root_class 5) (TREE5 rsb) = true.

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
             (both_spec_E fc_both 0%nat 400000%nat 5000%nat IT_both IT_both_ok (fun rsb => TREE_both (rsb := rsb) (TREE5 rsb)) (fun rsb => TREES_both (TREE5 rsb) (TREE5_ok rsb)))).
  Qed.

  (* The halting statement: the same trees at the flag [true], with the fifth tree's
     dead-arm check; the other five are computed in [Asan/MainTreeBoth.TREES_both_dead]. *)
  Hypothesis TREE5_dead : forall rsb, mtree_dead hf26 (TREE5 rsb) = true.

  Theorem both_halts_T5 :
    OSSVerify.Core.Shapes.halts_within_budget OSSVerify.Core.Shapes.Budgets.Standard.lim_source
      OSSVerify.Core.Shapes.Exits.ok_or_refused
      (mkImage OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.loaded_segments
               OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.init_pc
               OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.phdrs).
  Proof.
    exact (HaltsKitFO.both_halts_of_spec
             (both_spec_T fc_both 0%nat 400000%nat 5000%nat IT_both IT_both_ok (fun rsb => TREE_both (rsb := rsb) (TREE5 rsb))
                (fun rsb => TREES_both (TREE5 rsb) (TREE5_ok rsb))
                (fun rsb => TREES_both_dead (rsb := rsb) (TREE5 rsb) (TREE5_ok rsb) (TREE5_dead rsb)))).
  Qed.
End T5.
