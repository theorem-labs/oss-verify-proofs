(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes HaltsTreeB.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Import TopLevel TopLevelHaltsB PlainTree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prog ProgExits.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_HaltsPlainB () := "I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog4progC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9ProgExits;prog_texitsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>TopLevelHaltsBDhaltsB_from_tree_genC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg9p_init_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg7p_phdrsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateBsource_alloc_limitC59OSSVerify5KrLib4Spec9ProgExits7EXITS02C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib9PlainTree=plain_tree_okC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00I47Corelib4Init9Datatypes4unit00C59OSSVerify5KrLib5Plain4PImg;PREAD_STAGEC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init5Logic4True00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00c49OSSVerify5KrLib;HaltsPlainB<halts_plainBC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run?forced_only_cfg".

Theorem halts_plainB : forall cfg, cfg_le cfg ACFG ->
  halts_allowed_T_scfg_budgets cfg ShippedBudgets.lim_source EXITS02 (mkImage SrcImg.loaded_segments SrcImg.init_pc SrcImg.phdrs).
Proof.
  intros cfg Hle.
  exact (haltsB_from_tree_gen psegs p_init_pc p_phdrs ShippedBudgets.lim_source EXITS02 (Prog.prog psegs PREAD_STAGE)
           (epost (fun (_ : unit) (_ : machine_state) => True)) cfg Hle
           plain_tree_ok (fun inp en => prog_texits psegs PREAD_STAGE inp en)).
Qed.

(* [comment removed for export] *)
Theorem halts_plainB_fo :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source EXITS02 (mkImage SrcImg.loaded_segments SrcImg.init_pc SrcImg.phdrs).
Proof.
  exact (halts_plainB forced_only_cfg (forced_only_cfg_least ACFG)).
Qed.
