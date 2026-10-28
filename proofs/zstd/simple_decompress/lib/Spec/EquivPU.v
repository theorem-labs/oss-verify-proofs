(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState ITree Nodes Decode Image InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad MSafe MPaths STree Malloc Stdio Harness Adapter Driver
  PState Prog StepB KLink KEv ModelInv ImgFacts ModelOK EquivShared EquivProg RSim RSimProg SizeHist PTotal ProgA LB_StmtA LB_Main EquivK_iface
  EquivPA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib Require Import TopLevel.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Lemma tglob_prog_u : forall rs en inp,
  valid_entry (mkImage usegs u_init_pc u_phdrs) en inp -> valid_input_either inp ->
  tglob nstep PhiP (prog usegs rs inp en) (mo0 usegs target_alloc_limit en inp).
Proof.
  intros rs en inp He Hi. apply tglob_PhiP_intro.
  - unfold mo0. apply minv_init. destruct en as [sp ? ? ?]. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hi) in He.
    destruct He as ((Hsp1 & Hsp2 & _) & _). cbn [en_sp]. split; [exact Hsp1| exact Hsp2].
  - destruct en; reflexivity.
  - exact (proj2 (prog_model_ok_ubsan rs en inp He Hi)).
  - exact (never_forced_u rs en inp He Hi).
Qed.

Theorem equiv_PU : forall rs rs' en en' inp,
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_entry (mkImage usegs u_init_pc u_phdrs) en' inp -> valid_input_either inp ->
  trace_equiv (tree_traces (prog psegs rs inp en) (mo0 psegs source_alloc_limit en inp))
              (tree_traces (prog usegs rs' inp en') (mo0 usegs target_alloc_limit en' inp)).
Proof.
  intros rs rs' en en' inp He He' Hi. apply trees_equiv_of_ttrace.
  change (prog usegs rs' inp en') with (treeA PasA rs' startup (ps_init (reservedZ usegs) (entry_atop en')) (argv_Z (in_argv inp))).
  apply (equiv_core_pre PasA nstep PhiP minv rs rs' KP startup startup_startup en inp _ _ He Hi).
  - pose proof He' as He''. destruct en' as [sp brk0 mbase rnd]. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hi) in He''.
    destruct He'' as ((Hsp1 & Hsp2 & _) & Hbrk & _ & _). unfold mo0, entry_atop. cbn [en_brk en_mmap_base en_sp AI KP]. unfold AIP. cbn [map].
    eapply OWN_weakG; [apply (GI_init usegs brk0 mbase sp target_alloc_limit inp _ Hbrk ltac:(rewrite reserved_top_ubsan; lia) ltac:(split; [exact Hsp1| exact Hsp2]) eq_refl ceil_ubsan)|]. intros _; exact I.
  - reflexivity.
  - apply m_fds_mo0.
  - apply m_fs_mo0.
  - change (treeA PasA rs' startup (ps_init (reservedZ usegs) (entry_atop en')) (argv_Z (in_argv inp))) with (prog usegs rs' inp en').
    apply tglob_prog_u; assumption.
Qed.
