(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib Require Import TopLevel.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Cfg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF AcctCore TopLevelGen ITreeA NodesA ModelX SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require TopLevelGenB.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require ImgFacts.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require ShapeAlg SpinAlg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import MainExport MainFactsAsan MainEntryAsan.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prog ProgA EquivPA AsanProgDeps AsanOK AsanHandoff ModelOK.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AProto.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg.
Require OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Plain.PlainAll.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib Require Import AsanMain.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma plain_tree_ok :
  tree_ok psegs p_init_pc p_phdrs source_alloc_limit
          (Prog.prog psegs PREAD_STAGE) (epost (fun (_ : unit) (_ : machine_state) => True)).
Proof.
  intros en inp Hen Hinp. split.
  - exact (Plain.PlainAll.plain_impl_closed en inp Hen Hinp).
  - exact (prog_model_ok_plain PREAD_STAGE en inp Hen Hinp).
Qed.

Lemma plain_side_ok : side_ok psegs p_init_pc p_phdrs source_alloc_limit TP.
Proof. exact (side_ok_of_tree_ok _ _ _ _ _ _ plain_tree_ok). Qed.

Lemma plain_no_kill : tfam_no_kill TP.
Proof. exact (tfam_no_kill_tree psegs source_alloc_limit (Prog.prog psegs PREAD_STAGE)). Qed.

Section Assembly.
  Variable rsA : Z.
  Hypothesis both_impl : both_impl_stmt rsA.

  Lemma both_side : side_ok bsegs b_init_pc b_phdrs target_alloc_limit TB.
  Proof.
    apply both_side_ok. intros en inp Hv Hi. split.
    - (* [comment removed for export] *)
      destruct (plain_side_ok (toP en) inp (toP_valid _ _ _ en inp Hv) Hi) as [Htr _].
      apply Htr. rewrite run_init_config. cbn [bh_traces]. apply CfgRun.obs_trace_cfg_nil.
    - intros ms mo HM.
      apply bmain_at_open in HM as (w & V & m & HM).
      pose proof HM as (_ & _ & _ & _ & HP & _ & _ & _ & _ & HMOD).
      apply Forall_app in HP as [HP _].
      destruct (both_impl en inp w V m ms mo Hv Hi HM) as (NMAX & RNG & A & Q & HT).
      eapply SpinAlg.srz_conseq.
      + exact (implF_srealizes bsegs (at_nodeA bsegs) nstepA nexitA minvA (nsafeA NMAX) fstepS NMAX (nodesA_sound bsegs NMAX) _ RNG A Q ms (MX mo []) mo HT).
      + (* [comment removed for export] *)
        destruct (equiv_PA_both_toP PREAD_STAGE rsA V (en_sp en) _ _ _ en inp mo Hv Hi HMOD HP) as [HEQ _].
        intros tr. unfold TB. symmetry. apply HEQ.
  Qed.

  (* [comment removed for export] *)
  Lemma plain_tree_ok_san :
    tree_ok psegs p_init_pc p_phdrs sanitizer_source_limit
            (Prog.prog psegs PREAD_STAGE) (epost (fun (_ : unit) (_ : machine_state) => True)).
  Proof.
    intros en inp Hen Hinp. split.
    - exact (Plain.PlainAll.plain_impl_closed en inp Hen Hinp).
    - exact (prog_model_ok_plain_lim sanitizer_source_limit PREAD_STAGE en inp ImgFacts.lim_s Hen Hinp).
  Qed.

  Definition TPs : tfam := fun inp en => tree_traces (prog psegs PREAD_STAGE inp en) (mo0 psegs sanitizer_source_limit en inp).

  Lemma plain_side_ok_san : side_ok psegs p_init_pc p_phdrs sanitizer_source_limit TPs.
  Proof. exact (side_ok_of_tree_ok _ _ _ _ _ _ plain_tree_ok_san). Qed.

  Theorem base_both :
    strong_universal_error_free_T_scfg_budgets ACFG SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage psegs p_init_pc p_phdrs)
      (mkImage bsegs b_init_pc b_phdrs).
  Proof.
    eapply (TopLevelGenB.side_ok_equiv_budgets_san _ _ _ _ _ _ TPs TB); [exact plain_side_ok_san | exact both_side |].
    intros enS enT inp HvS HvT Hi. unfold TPs, TB. apply trace_equiv_sym.
    apply (equiv_PP_lim sanitizer_source_limit); [exact ImgFacts.lim_s | exact (toP_valid _ _ _ enT inp HvT) | exact HvS | exact Hi].
  Qed.

  (* [comment removed for export] *)
  Theorem base_both_plain :
    strong_universal_error_free_T_scfg ACFG
      (mkImage psegs p_init_pc p_phdrs)
      (mkImage bsegs b_init_pc b_phdrs).
  Proof.
    eapply (side_ok_equiv _ _ _ _ _ _ TP TB); [exact plain_side_ok | exact both_side |].
    intros enS enT inp HvS HvT Hi. unfold TP, TB. apply equiv_PP; [exact HvS | exact (toP_valid _ _ _ enT inp HvT) | exact Hi].
  Qed.
End Assembly.
