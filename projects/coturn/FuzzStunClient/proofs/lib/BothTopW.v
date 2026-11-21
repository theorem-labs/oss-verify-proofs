(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the W1 tree is one per launch rseq layout from the collected template M5TmplRBoth.HG1_r, and both_halts_W1 gives the halting statement from the fifth tree's dead-arm check. *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From Stdlib Require Import List ZArith.
Require OSSVerify.coturn.FuzzStunClient.images.Plain.
Require OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import BothTop.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanMainLib MainGlueDefsB MainGlueB ItabBoth M5TmplRBoth Main5Both.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import DeadArm.
Require OSSVerify.Core.Shapes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Section W1.
  (* one W1 tree per rseq layout, started from that layout's collected hand-off template [HG1_r rsb]
     (M5TmplRBoth); both_base_T5 takes both. *)
  Variable TW1 : bool -> mtree.
  Hypothesis TW1_ok : forall rsb, mtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat (HG1_r rsb) ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) (TW1 rsb) = true.

  Theorem both_base_W1 :
    strong_universal_error_free_T_budgets SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage OSSVerify.coturn.FuzzStunClient.images.Plain.M.loaded_segments
               OSSVerify.coturn.FuzzStunClient.images.Plain.M.init_pc
               OSSVerify.coturn.FuzzStunClient.images.Plain.M.phdrs)
      (mkImage OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.loaded_segments
               OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.init_pc
               OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.phdrs).
  Proof. exact (both_base_T5 (fun rsb => TREE5 (TW1 rsb)) (fun rsb => TREE5_ok (TW1 rsb) (TW1_ok rsb))). Qed.

  (* The halting statement: the fifth tree [TREE5 (TW1 rsb)] passes the dead-arm check. *)
  Hypothesis TW1_dead : forall rsb, mtree_dead hf26 (TREE5 (rsb := rsb) (TW1 rsb)) = true.

  Theorem both_halts_W1 :
    OSSVerify.Core.Shapes.halts_within_budget OSSVerify.Core.Shapes.Budgets.Standard.lim_source
      OSSVerify.Core.Shapes.Exits.ok_or_refused
      (mkImage OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.loaded_segments
               OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.init_pc
               OSSVerify.coturn.FuzzStunClient.images.AsanUbsan.M.phdrs).
  Proof. exact (both_halts_T5 (fun rsb => TREE5 (rsb := rsb) (TW1 rsb)) (fun rsb => TREE5_ok (rsb := rsb) (TW1 rsb) (TW1_ok rsb)) TW1_dead). Qed.
End W1.
