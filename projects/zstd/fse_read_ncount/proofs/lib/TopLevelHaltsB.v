(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Exec Cfg ITree Nodes RegsEquiv HaltsTree HaltsTreeB.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib Require Import TopLevel.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Theorem must_exit_S_from_tree_gen :
  forall {R : Type} (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z) (S : list word)
         (t : prog_tree R) (Q : R -> machine_state -> Prop),
    tree_ok segs pc ph lim t Q ->
    (forall inp en, texits nexit S (t inp en)) ->
    forall en inp,
      valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
      must_exit_in_scfg ACFG S (mkImage segs pc ph) lim en inp.
Proof.
  intros R segs pc ph lim S t Q HT HX en inp Hve Hvi.
  pose proof (valid_input_either_of_valid_input _ Hvi) as Hei.
  destruct (HT en inp Hve Hei) as (Himpl & Hleaves & Hsafe).
  exact (halts_of_impl_tree_S segs pc ph lim S (t inp en) Q en inp Hve (valid_input_either_va_size _ Hei) (HX inp en)
           Himpl Hleaves Hsafe).
Qed.

(* [comment removed for export] *)
Theorem haltsB_from_tree_gen :
  forall {R : Type} (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z) (S : list word)
         (t : prog_tree R) (Q : R -> machine_state -> Prop) (cfg : SpuriousCfg),
    cfg_le cfg ACFG ->
    tree_ok segs pc ph lim t Q ->
    (forall inp en, texits nexit S (t inp en)) ->
    halts_allowed_T_scfg_budgets cfg lim S (mkImage segs pc ph).
Proof.
  intros R segs pc ph lim S t Q cfg Hle HT HX. apply (haltsB_of_must_exit_may_fail cfg _ _ _ Hle).
  exact (must_exit_S_from_tree_gen segs pc ph lim S t Q HT HX).
Qed.

(* [comment removed for export] *)
Theorem haltsA_S_from_tree_gen :
  forall {R : Type} (segs : list Segment) (pc : N) (ph : PhdrInfo) (S : list word)
         (t : prog_tree R) (Q : R -> machine_state -> Prop) (cfg : SpuriousCfg),
    cfg_le cfg ACFG ->
    tree_ok segs pc ph source_alloc_limit t Q ->
    (forall inp en, texits nexit S (t inp en)) ->
    halts_allowed_T_scfg cfg S (mkImage segs pc ph).
Proof.
  intros R segs pc ph S t Q cfg Hle HT HX en inp Hve Hvi. apply (must_exit_in_scfg_of_may_fail cfg); [exact Hle|].
  exact (must_exit_S_from_tree_gen segs pc ph source_alloc_limit S t Q HT HX en inp Hve Hvi).
Qed.
