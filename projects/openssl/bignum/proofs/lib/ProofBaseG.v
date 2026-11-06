(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv.
From OSSVerify.Proofs.openssl.bignum.lib Require Import TopLevel Obligations.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prelim Driver Prog ModelInv Unforced LibProg LibSafe LibOps ProgG ProgGSafe ProgGDet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition implG_stmt {LM : LibModel} (segs : list Segment) (pc : N) (ph : PhdrInfo) (rstage : Z) : Prop :=
  forall (en : ExecEntry) (inp : ProcInput),
    valid_entry (mkImage segs pc ph) en inp ->
    valid_input_either inp ->
    impl segs (at_node segs) (the_progG segs rstage inp en) (epost the_post) (ms0 segs pc ph en inp).

Section BaseG.
Context {LM : LibModel}.
Variable P : Z -> Z.
Variable T : list Z.
Variables NBLK BSZ : Z.
Variable linv : LS -> list (bptr * Z) -> Prop.
Hypothesis HP0 : forall c, 0 <= P c.
Hypothesis HC : caps_ok P T NBLK BSZ.
Hypothesis H_init : lwf (okT T) lib_init [] (fun ls Li => linv ls [] /\ subms (map snd Li) T).
Hypothesis H_one : forall ls d X, linv ls X -> zlength d <= MAX_INPUT ->
  lwf (okB NBLK BSZ) (lib_one ls d) X (fun r X' => linv (fst r) X').
Hypothesis H_rc : forall ls d, lleaves (lib_one ls d) (fun r => snd r = 0).

Variables (segsS : list Segment) (pcS : N) (phS : PhdrInfo) (rstageS : Z).
Variables (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (rstageT : Z).
Hypothesis HlowS : image_low segsS.
Hypothesis HlowT : image_low segsT.

Lemma lim_source_ok : KLIM + SMALLREQ <= source_alloc_limit.
Proof. unfold KLIM, SMALLREQ, source_alloc_limit. lia. Qed.
Lemma lim_target_ok : KLIM + SMALLREQ <= target_alloc_limit.
Proof. unfold KLIM, SMALLREQ, target_alloc_limit. lia. Qed.

Lemma tree_okG_S : implG_stmt segsS pcS phS rstageS ->
  tree_ok segsS pcS phS source_alloc_limit (the_progG segsS rstageS) (epost the_post).
Proof.
  intros HI en inp Hve Hvi. split; [exact (HI en inp Hve Hvi)|].
  exact (progG_model_ok_run P T NBLK BSZ linv HP0 HC H_init H_one H_rc segsS rstageS pcS phS source_alloc_limit HlowS lim_source_ok en inp Hve Hvi).
Qed.

Lemma tree_okG_T : implG_stmt segsT pcT phT rstageT ->
  tree_ok segsT pcT phT target_alloc_limit (the_progG segsT rstageT) (epost the_post).
Proof.
  intros HI en inp Hve Hvi. split; [exact (HI en inp Hve Hvi)|].
  exact (progG_model_ok_run P T NBLK BSZ linv HP0 HC H_init H_one H_rc segsT rstageT pcT phT target_alloc_limit HlowT lim_target_ok en inp Hve Hvi).
Qed.

Lemma trees_equivG : trees_equiv segsS pcS phS segsT pcT phT (the_progG segsS rstageS) (the_progG segsT rstageT).
Proof.
  intros enS enT inp HvS HvT Hvi.
  exact (progG_trees_equiv P T NBLK BSZ linv HP0 HC H_init H_one H_rc
           segsS rstageS pcS phS source_alloc_limit segsT rstageT pcT phT target_alloc_limit
           HlowS lim_source_ok HlowT lim_target_ok enS enT inp HvS HvT Hvi).
Qed.

Theorem baseG_scfg :
  implG_stmt segsS pcS phS rstageS -> implG_stmt segsT pcT phT rstageT ->
  strong_universal_error_free_T_scfg ncfg (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros HS HT.
  exact (error_free_from_trees_gen segsS pcS phS segsT pcT phT _ _ _ _ (tree_okG_S HS) (tree_okG_T HT) trees_equivG).
Qed.

Theorem baseG_scfg_budgets :
  implG_stmt segsS pcS phS rstageS -> implG_stmt segsT pcT phT rstageT ->
  strong_universal_error_free_T_scfg_budgets ncfg ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros HS HT.
  exact (error_free_scfg_budgets_from_trees_gen segsS pcS phS segsT pcT phT _ _ _ _ (tree_okG_S HS) (tree_okG_T HT) trees_equivG).
Qed.

End BaseG.
