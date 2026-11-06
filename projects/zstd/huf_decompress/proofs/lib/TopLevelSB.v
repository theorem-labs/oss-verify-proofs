(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import TopLevelGen.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_TopLevelSB () := "I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib4LibA;TopLevelGen7side_okC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01C4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_entryC4ELinuxProcessSemantics?LinuxProcessSem3RunBvalid_input_eitherC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence;trace_equivC4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_inputC4ELinuxProcessSemantics?LinuxProcessSem3RunQvalid_input_either_of_valid_inputC4ELinuxProcessSemantics?LinuxProcessSem3Run3runC4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_tracesC4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_errorsC47Corelib4Init5Logic3notI47Corelib4Init5Logic3and00C4ELinuxProcessSemanticsEEquivalenceDefinition;EquivalenceOstrong_equiv_error_free_budgetsC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence:error_freeC49OSSVerify5KrLib8TopLevel?trace_equiv_symC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8TopLevelAtrace_equiv_transC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00C59OSSVerify5KrLib4LibA;TopLevelGen4tfamC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateBtarget_alloc_limitI4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00C4ELinuxProcessSemanticsEEquivalenceDefinition;EquivalenceDsource_within_budgetc49OSSVerify5KrLib:TopLevelSB?side_ok_equiv_LC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemanticsEEquivalenceDefinition;EquivalenceUstrong_universal_error_free_T_budgetsc49OSSVerify5KrLib:TopLevelSBGside_ok_equiv_budgets_LC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemanticsEEquivalenceDefinition;EquivalenceFsanitizer_source_limitC5ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence@SanitizerBudgets:lim_sourceC5ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence@SanitizerBudgets:lim_target".

Theorem side_ok_equiv_L :
  forall (L : Z) (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (TS TT : tfam),
    side_ok segsS pcS phS L TS ->
    side_ok segsT pcT phT target_alloc_limit TT ->
    (forall enS enT inp,
        valid_entry (mkImage segsS pcS phS) enS inp ->
        valid_entry (mkImage segsT pcT phT) enT inp ->
        valid_input_either inp ->
        trace_equiv (TS inp enS) (TT inp enT)) ->
    forall enS enT inp,
      valid_entry (mkImage segsS pcS phS) enS inp ->
      valid_entry (mkImage segsT pcT phT) enT inp ->
      valid_input inp ->
      strong_equiv_error_free_budgets_scfg ACFG L target_alloc_limit (mkImage segsS pcS phS) (mkImage segsT pcT phT) enS enT inp.
Proof.
  intros L segsS pcS phS segsT pcT phT TS TT HS HT HEQ enS enT inp HvS HvT Hvi0.
  pose proof (valid_input_either_of_valid_input _ Hvi0) as Hvi.
  destruct (HS enS inp HvS Hvi) as [HtrS HerrS].
  destruct (HT enT inp HvT Hvi) as [HtrT HerrT].
  split; [exact HerrS|]. split; [exact HerrT|].
  eapply trace_equiv_trans; [exact HtrS|].
  eapply trace_equiv_trans; [exact (HEQ enS enT inp HvS HvT Hvi)|].
  apply trace_equiv_sym. exact HtrT.
Qed.

Theorem side_ok_equiv_budgets_L :
  forall (L : Z) (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (TS TT : tfam),
    side_ok segsS pcS phS L TS ->
    side_ok segsT pcT phT target_alloc_limit TT ->
    (forall enS enT inp,
        valid_entry (mkImage segsS pcS phS) enS inp ->
        valid_entry (mkImage segsT pcT phT) enT inp ->
        valid_input_either inp ->
        trace_equiv (TS inp enS) (TT inp enT)) ->
    strong_universal_error_free_T_scfg_budgets ACFG L target_alloc_limit (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros L segsS pcS phS segsT pcT phT TS TT HS HT HEQ enS enT inp HvS HvT Hvi _.
  exact (side_ok_equiv_L L segsS pcS phS segsT pcT phT TS TT HS HT HEQ enS enT inp HvS HvT Hvi).
Qed.

(* [comment removed for export] *)
Theorem side_ok_equiv_sb :
  forall (segsS : list Segment) (pcS : N) (phS : PhdrInfo)
         (segsT : list Segment) (pcT : N) (phT : PhdrInfo) (TS TT : tfam),
    side_ok segsS pcS phS sanitizer_source_limit TS ->
    side_ok segsT pcT phT target_alloc_limit TT ->
    (forall enS enT inp,
        valid_entry (mkImage segsS pcS phS) enS inp ->
        valid_entry (mkImage segsT pcT phT) enT inp ->
        valid_input_either inp ->
        trace_equiv (TS inp enS) (TT inp enT)) ->
    strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  intros segsS pcS phS segsT pcT phT TS TT HS HT HEQ.
  cbv delta [SanitizerBudgets.lim_source SanitizerBudgets.lim_target].
  exact (side_ok_equiv_budgets_L sanitizer_source_limit segsS pcS phS segsT pcT phT TS TT HS HT HEQ).
Qed.
