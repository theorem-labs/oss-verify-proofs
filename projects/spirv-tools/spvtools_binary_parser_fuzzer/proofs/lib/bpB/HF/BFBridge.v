(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the robustness of each node's system call over a larger read-only backing (RomBase.sys_rob), which the walk's nodes now ask, proved at each node; recorded proofs written as text where the node premise changed their terms). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require ScfgBase ShapeAlg DivergeSim SRealizes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require S1Spec.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bcfg BShapeAlg BDivergeSim BpinAlg BSpec.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BFBridge () := "C69OSSVerify5KrLib3bpB2HF9BShapeAlg7node_okC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C69OSSVerify5KrLib3bpB2HF4Bcfg=hunspell_scfgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF9BShapeAlg4t_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF9BShapeAlg4TSetC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3bpB2HF7BpinAlg9srealizes01C1?~~~~~~~~~~~~~~~K49OSSVerify5KrLib9SRealizes9srealizes01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF8BFBridge>node_ok_bridgeC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8ShapeAlg7node_okC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3bpB2HF7BpinAlg9srealizes00C1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib9SRealizes9srealizes00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3notK49OSSVerify5KrLib9SRealizes9srealizes02C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib3bpB2HF8BFBridge;t_eq_bridgeC1?~~~~~~~~~~~~~~~K49OSSVerify5KrLib9SRealizes9srealizes03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpB2HF7BpinAlg=srealizes_indC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib3Drv6S1Spec4specC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics?LinuxProcessSem2Fs2Fs".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.

Section Bridge.
  Variable segs : list Segment.

  Lemma node_ok_bridge : forall c I evs nx,
    @BShapeAlg.node_ok segs Bcfg.hunspell_scfg c I evs nx -> ShapeAlg.node_ok segs c I evs nx.
Proof.
ltac2:(KReplay.run1 (kr_t_BFBridge ()) ["Bridge"] "h01Hh11Ih21ch33evsh42nxp;1p;6p200R0g0000R1p4p741110p8g000mj11TP1j60Tg001MR1f0R2g002B#1[f1R3P1[p,4segsg0038f3f2P3P2E0P2W0W4W3X10W2o"). Qed.

  Lemma t_eq_bridge : forall T T', BShapeAlg.t_eq T T' -> ShapeAlg.t_eq T T'.
Proof.
ltac2:(KReplay.run1 (kr_t_BFBridge ()) ["Bridge"] "h01Hh11Th22T'p;2g0046j20Tg0050R0f1f0R1'0P1W0X20W1o"). Qed.

  Theorem srealizes_bridge : forall c T,
    @BpinAlg.srealizes segs Bcfg.hunspell_scfg c T -> SRealizes.srealizes segs c T.
Proof.
  (* LPS 08b1429: text in place of the recorded proof; both [srz_node]s now carry the same
     [RomBase.sys_rob] premise, passed through. *)
  intros c T H.
  induction H as [c I evs nx T i0 Hnode Hrob Hcont IH | c Hh | c T T' H IH Heq].
  - exact (SRealizes.srz_node segs c I evs nx T i0 (node_ok_bridge c I evs nx Hnode) Hrob IH).
  - exact (SRealizes.srz_halt segs c Hh).
  - exact (SRealizes.srz_conseq segs c T T' IH (t_eq_bridge T T' Heq)).
Qed.

End Bridge.

Theorem spec_bridge : forall argv fs, BSpec.spec argv fs = S1Spec.spec argv fs.
Proof.
ltac2:(KReplay.run1 (kr_t_BFBridge ()) [] "h04argvh12fsp;1p;2g00;Tj10Tg00<9j15Tg00<Wj12Tg000mj11Tg00E8j24Tg00Elj23Tg00DS#0#0#0#5#2#1#1g00FFg0050f1f0'4'3W1W0o"). Qed.
