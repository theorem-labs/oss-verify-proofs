(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the robustness of each node's system call over a larger read-only backing (RomBase.sys_rob), which the walk's nodes now ask, proved at each node; recorded proofs written as text where the node premise changed their terms). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Bcfg BPropExec BShapeAlg BpinAlg BAgentLib BExitSim BAllocSim BNodes BMmapSim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Export BothRefNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Common.Cfg Require RomBase.
Ltac2 kr_t_BothNodesChk () := "K69OSSVerify5KrLib3bpB2HF7BpinAlg9srealizes01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF9BShapeAlg5t_altC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF9BShapeAlg7node_okC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01I69OSSVerify5KrLib3bpB2HF7BpinAlg9srealizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF9BShapeAlg6t_emitC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib3bpB2HF7BpinAlgBsrealizes_nonemptyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF9BShapeAlg=t_emit_nil_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic3and01C47Corelib4Init5Logic3iffC69OSSVerify5KrLib3bpB2HF9BShapeAlg4t_eqC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3bpB2HF7BpinAlg9srealizes03C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3bpB2HF4Bcfg7StepCfg00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C69OSSVerify5KrLib3bpB2HF9BShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00".
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma srz_silent_all {SC : StepCfg} : forall segs c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx ->
  RomBase.sys_rob segs c ->   (* LPS 08b1429: [srz_node] asks it *)
  (forall i, srealizes segs (nx i) T) ->
  srealizes segs c T.
Proof.
  (* LPS 08b1429: text in place of the recorded proof, for [srz_node]'s new premise *)
  intros segs c I nx T i0 Hnode Hrob Hc.
  apply (srz_conseq segs c (t_alt (fun _ : I => t_emit [] T))).
  - apply (srz_node segs c I (fun _ => []) nx (fun _ => T) i0 Hnode Hrob Hc).
  - intros tr. unfold t_alt. split.
    + intros [i H]. exact (proj1 (t_emit_nil_eq T (srealizes_nonempty segs _ _ (Hc i)) tr) H).
    + intros H. exists i0. exact (proj2 (t_emit_nil_eq T (srealizes_nonempty segs _ _ (Hc i0)) tr) H).
Qed.
