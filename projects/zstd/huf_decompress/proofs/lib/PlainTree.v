(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prog ModelInv ModelOK ImgFacts.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
Require OSSVerify.Proofs.zstd.huf_decompress.lib.Plain.PlainClosed.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_PlainTree () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leK4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01C4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_entryC4ELinuxProcessSemantics?LinuxProcessSem3RunBvalid_input_eitherC59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog4progC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5epostC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8TopLevel3ms0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8TopLevel3mo0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITreeDleaves_unreachable_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree5tsafeC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C59OSSVerify5KrLib5Plain;PlainClosedAplain_impl_closedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7ModelOKEprog_model_ok_plain_LC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C49OSSVerify5KrLib8TopLevel7tree_okC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg9p_init_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg7p_phdrsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4unit00C59OSSVerify5KrLib5Plain4PImg;PREAD_STAGEC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init5Logic4True00C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nsafeC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib9PlainTree?plain_tree_ok_LC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateBsource_alloc_limitC59OSSVerify5KrLib4Spec8ImgFacts5lim_pC1?~~~~~~~~~~~~~~~".

(* [comment removed for export] *)
Theorem plain_tree_ok_L : forall L, 2^31 <= L ->
  tree_ok psegs p_init_pc p_phdrs L
          (Prog.prog psegs PREAD_STAGE) (epost (fun (_ : unit) (_ : machine_state) => True)).
Proof.
  intros L HL en inp Hen Hinp. split.
  - exact (Plain.PlainClosed.plain_impl_closed en inp Hen Hinp).
  - exact (prog_model_ok_plain_L L PREAD_STAGE en inp HL Hen Hinp).
Qed.

(* [comment removed for export] *)
Theorem plain_tree_ok :
  tree_ok psegs p_init_pc p_phdrs source_alloc_limit
          (Prog.prog psegs PREAD_STAGE) (epost (fun (_ : unit) (_ : machine_state) => True)).
Proof.
ltac2:(KReplay.run1 (kr_t_PlainTree ()) [] "p;2g00KUj20Tg00LSg00MT'0o"). Qed.
