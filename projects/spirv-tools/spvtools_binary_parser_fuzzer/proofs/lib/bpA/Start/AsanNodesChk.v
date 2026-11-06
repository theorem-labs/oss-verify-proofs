(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Scfg HPropExec HShapeAlg SpinAlg HAgentLib HExitSim HAllocSim HNodes HMmapSim.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Export AsanRefNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_AsanNodesChk () := "K69OSSVerify5KrLib3bpA2HF7SpinAlg9srealizes01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2HF9HShapeAlg5t_altC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2HF9HShapeAlg7node_okC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01I69OSSVerify5KrLib3bpA2HF7SpinAlg9srealizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2HF9HShapeAlg6t_emitC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib3bpA2HF7SpinAlgBsrealizes_nonemptyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2HF9HShapeAlg=t_emit_nil_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic3and01C47Corelib4Init5Logic3iffC69OSSVerify5KrLib3bpA2HF9HShapeAlg4t_eqC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3bpA2HF7SpinAlg9srealizes03C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3bpA2HF4Scfg7StepCfg00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00C69OSSVerify5KrLib3bpA2HF9HShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00".
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma srz_silent_all {SC : StepCfg} : forall segs c (I : Type) (nx : I -> config) (T : TSet) (i0 : I),
  node_ok segs c I (fun _ => []) nx ->
  (forall i, srealizes segs (nx i) T) ->
  srealizes segs c T.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanNodesChk ()) [] "p'0h01ih11Hh22H0h32Hch45Hnodeh51Ih62SCh71Th81ch92i0h:2nxh;4segsh<2tri001xp;1p;6p;4p;2p;:p;3p;5p;7p200R0g0000R1p4p741110p8P0g000oR2p4p710p8P0g001jR3p4p741110p8g002gj12Tg003Gj1BTP3j67Tg003gj46Tg004fj25j30TP2j2;j3?TP1l::Tg005bR1j21Tg006<j54Tg007Bj33Tg008Ej48Tg008`j49Tg009;j4ATg009Uj4@Tg00:0j2<Tg00:Ij2=Tg00;Cj7>Tg00<Bg00=<#2g00>;R2f0R3P2[g00?0f2R2f5R4f6R5f4R6f3R7g00?jR8#BR9V7P2E7f7R:f8R;P6P3O1R<P7C6^06P:P;P51596V4,;4R=P7P:P;P5P4P9V4P6P6V4P2f1R>P3M::%28A094>R8X05,15R?P4P>O1R@[A0952RAX0:RB,1:\<P1P:PBP5P2O1R1P3f9RCA09;6A09C4f:R;P5O1[PCP4O1A09;5[f=f>P;P>O1PCP5P>O1D4=3C4P3C8W1W0P>P3O2n2001000000120100000X2?P:PBP6P1\8PA\@PCP;P5P6O1P4P2P6O1D4=34>P3C9CAX1<C@1594V5=?53/<<eW<1==7eF>W3W4W9W7W:X50W8W;W6o"). Qed.
