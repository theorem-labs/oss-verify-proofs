(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv Image Ceiling.
From OSSVerify.Proofs.openssl.bndiv.lib Require Import TopLevel Obligations ProofBase TopLevelA TopE.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import Prog ModelInv Canon CanonNoKill ProgDetIface ProgDet ProgNoEnomem.
From OSSVerify.openssl.bndiv.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition Tc (inp : ProcInput) : list event -> Prop := canonT (argv_Z (in_argv inp)) (in_fs inp).

Lemma Tc_nokill : T_nokill Tc.
Proof. intros inp tr sig fs H. exact (canonT_nokill _ _ tr sig fs H). Qed.

(* [comment removed for export] *)
Theorem P_side : impl_P_stmt ->
  side_canon ncfg Tc (mkImage psegs SrcPA.M.init_pc SrcPA.M.phdrs) source_alloc_limit.
Proof. intros HP en inp He Hi. exact (P_canon HP prog_no_enomem_P en inp He Hi). Qed.

(* [comment removed for export] *)
Theorem U_side : impl_U_stmt ->
  side_canon ncfg Tc (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs) target_alloc_limit.
Proof.
  intros HU en inp He Hi.
  destruct (prog_model_ok_U (CE__:=run_ceiling en) en inp He Hi (run_ceiling_eqA _ _ _ _ _ (vie_va_size _ Hi) He)) as [Hl Hs].
  destruct (run_of_tree usegs Ubsan.M.init_pc Ubsan.M.phdrs target_alloc_limit
              (the_prog usegs ustage inp en) (epost the_post) en inp (HU en inp He Hi) Hl Hs)
    as (Htr & Herr & _).
  split; [| exact Herr].
  intros tr. rewrite (Htr tr). exact (prog_det_U prog_no_enomem_U en inp He Hi tr).
Qed.

(* [comment removed for export] *)
Theorem S_side : forall tsegs tpc tph, S3s_stmt tsegs tpc tph ->
  side_canon ncfg Tc (mkImage tsegs tpc tph) target_alloc_limit.
Proof. intros tsegs tpc tph HS en inp He Hi. exact (T_canon tsegs tpc tph HS en inp He Hi). Qed.

(* [comment removed for export] *)
Section Bases.
  Hypothesis HP : impl_P_stmt.

  Section Ubsan.
    Hypothesis HU : impl_U_stmt.
    Theorem ubsan_scfg : strong_universal_error_free_T_scfg ncfg
      (mkImage psegs SrcPA.M.init_pc SrcPA.M.phdrs) (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs).
    Proof. exact (glue_scfg_e ncfg Tc _ _ (P_side HP) (U_side HU)). Qed.
    Theorem ubsan_base : strong_universal_error_free_T_scfg_budgets ncfg ShippedBudgets.lim_source ShippedBudgets.lim_target
      (mkImage psegs SrcPA.M.init_pc SrcPA.M.phdrs) (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs).
    Proof. exact (glue_scfg_budgets_e ncfg Tc _ _ (P_side HP) (U_side HU)). Qed.
  End Ubsan.

  Section AsanFamily.
    Variables (tsegs : list Segment) (tpc : N) (tph : PhdrInfo).
    Hypothesis HS : S3s_stmt tsegs tpc tph.
    Theorem asanfam_scfg : strong_universal_error_free_T_scfg ncfg
      (mkImage psegs SrcPA.M.init_pc SrcPA.M.phdrs) (mkImage tsegs tpc tph).
    Proof. exact (glue_scfg_e ncfg Tc _ _ (P_side HP) (S_side _ _ _ HS)). Qed.
    Theorem asanfam_base : strong_universal_error_free_T_scfg_budgets ncfg ShippedBudgets.lim_source ShippedBudgets.lim_target
      (mkImage psegs SrcPA.M.init_pc SrcPA.M.phdrs) (mkImage tsegs tpc tph).
    Proof. exact (glue_scfg_budgets_e ncfg Tc _ _ (P_side HP) (S_side _ _ _ HS)). Qed.
  End AsanFamily.
End Bases.
