(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv Image Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib Require Import TopLevel Obligations ProofBase TopPlain TopLevelA TopE.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib Require Export TopSidesPU.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prog ModelInv ModelInvN MallocSome Canon CanonNoKill ProgDetIface ProgDet ProgNoEnomem.
From OSSVerify.simdjson.fuzz_dump_raw_tape.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Theorem S_side : forall tsegs tpc tph, S3s_stmt_e tsegs tpc tph ->
  side_canon Tc (mkImage tsegs tpc tph) target_alloc_limit.
Proof. intros tsegs tpc tph HS en inp He Hi. exact (T_canon_e tsegs tpc tph HS en inp He Hi). Qed.

Section Bases.
  Hypothesis HP : impl_P_stmt.

  Section AsanFamily.
    Variables (tsegs : list Segment) (tpc : N) (tph : PhdrInfo).
    Hypothesis HS : S3s_stmt_e tsegs tpc tph.
    Theorem asanfam_off : strong_universal_error_free_T_scfg ACFG
      (mkImage psegs Plain.M.init_pc Plain.M.phdrs) (mkImage tsegs tpc tph).
    Proof. exact (glue_off Tc _ _ (P_side HP) (S_side _ _ _ HS)). Qed.
    Theorem asanfam_base : strong_universal_error_free_T_scfg_budgets_abort ACFG ShippedBudgets.lim_source ShippedBudgets.lim_target
      (mkImage psegs Plain.M.init_pc Plain.M.phdrs) (mkImage tsegs tpc tph).
    Proof. exact (glue_budgets_abort Tc _ _ (P_side HP) (S_side _ _ _ HS) Tc_nokill). Qed.

    Theorem asanfam_base_san : strong_universal_error_free_T_scfg_budgets_abort ACFG SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage psegs Plain.M.init_pc Plain.M.phdrs) (mkImage tsegs tpc tph).
    Proof. exact (glue_budgets_abort_san Tc _ _ (P_side_san HP) (S_side _ _ _ HS) Tc_nokill). Qed.
  End AsanFamily.
End Bases.
