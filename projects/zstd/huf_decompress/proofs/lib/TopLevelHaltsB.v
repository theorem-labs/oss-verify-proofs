(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Exec ITree Nodes RegsEquiv HaltsTree HaltsTreeB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_TopLevelHaltsB () := "C49OSSVerify5KrLib8TopLevel9prog_treeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib:HaltsTreeB6texitsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8TopLevel7tree_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib:HaltsTreeBDhalts_of_impl_tree_SC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01C4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_entryC4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_inputC4ELinuxProcessSemantics?LinuxProcessSem3RunQvalid_input_either_of_valid_inputC4ELinuxProcessSemantics?LinuxProcessSem3RunBvalid_input_eitherC59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8TopLevel3ms0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8TopLevel3mo0C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C4ELinuxProcessSemanticsEEquivalenceDefinition8MustExitAmust_exit_in_scfgC49OSSVerify5KrLib8TopLevelJvalid_input_either_va_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITreeDleaves_unreachable_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5tsafeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nsafeC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00C59OSSVerify5KrLib3Lib5Nodes5nexitC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run<may_fail_cfgc49OSSVerify5KrLib>TopLevelHaltsBImust_exit_S_from_tree_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib:HaltsTreeBLhaltsB_of_must_exit_may_failC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00C59OSSVerify5KrLib3Lib:HaltsTreeBMmust_exit_in_scfg_of_may_failC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemanticsEEquivalenceDefinition<HaltsAllowedDhalts_allowed_T_scfgC4ELinuxProcessSemantics?LinuxProcessSem5StateBsource_alloc_limit".
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
  intros R segs pc ph lim S t Q cfg Hle HT HX. apply (haltsB_of_must_exit_may_fail cfg S _ lim Hle).
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
  intros R segs pc ph S t Q cfg Hle HT HX en inp Hve Hvi. apply (must_exit_in_scfg_of_may_fail cfg S _ _ en inp Hle).
  exact (must_exit_S_from_tree_gen segs pc ph source_alloc_limit S t Q HT HX en inp Hve Hvi).
Qed.
