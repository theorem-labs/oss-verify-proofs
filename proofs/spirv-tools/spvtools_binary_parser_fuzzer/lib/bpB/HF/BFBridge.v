(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require ScfgBase ShapeAlg DivergeSim SRealizes.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require S1Spec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bcfg BShapeAlg BDivergeSim BpinAlg BSpec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BFBridge () := "C6ARocqVerifyHarness?AgentSubmission3bpB2HF9BShapeAlg7node_okI47Corelib4Init9Datatypes4list00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C6ARocqVerifyHarness?AgentSubmission3bpB2HF4Bcfg=hunspell_scfgC6ARocqVerifyHarness?AgentSubmission3bpB2HF9BShapeAlg4t_eqC6ARocqVerifyHarness?AgentSubmission3bpB2HF9BShapeAlg4TSetK6ARocqVerifyHarness?AgentSubmission3bpB2HF7BpinAlg9srealizes01K4ARocqVerifyHarness?AgentSubmission9SRealizes9srealizes01c6ARocqVerifyHarness?AgentSubmission3bpB2HF8BFBridge>node_ok_bridgeC4ARocqVerifyHarness?AgentSubmission8ShapeAlg7node_okI6ARocqVerifyHarness?AgentSubmission3bpB2HF7BpinAlg9srealizes00I4ARocqVerifyHarness?AgentSubmission9SRealizes9srealizes00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelC4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3notK4ARocqVerifyHarness?AgentSubmission9SRealizes9srealizes02c6ARocqVerifyHarness?AgentSubmission3bpB2HF8BFBridge;t_eq_bridgeK4ARocqVerifyHarness?AgentSubmission9SRealizes9srealizes03C6ARocqVerifyHarness?AgentSubmission3bpB2HF7BpinAlg=srealizes_indK47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission3Drv6S1Spec4specK47Corelib4Init5Logic2eq01C4ELinuxProcessSemantics?LinuxProcessSem2Fs2Fs".
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
ltac2:(KReplay.run1 (kr_t_BFBridge ()) ["Bridge"] "h01ch11Th21Hh32IHh41ih55Hconth63Heqh72Hhh85Hnodeh91Ih:2T'h;3evsh<2i0h=2nxp;4p;3p;1p;6p;5p;9p;2g005jp4p741110R0g006iR1p4p73110p8P0g007cR2p606311000R3p8P3p1008fp4p73110p8g009[j41Tg00:Zj32Tg000mj14Tg0000j63TP2j5CTP1l9<Tg00;Tj10Tg00<9j15Tg00<Wj16Tg00=:j17Tg00=\j18Tg00>Rj19Tg00?Ij1:Tg00?kj3BTg00@Ej1ATg00@^j3@Tg0046j2=Tg00AXj3>Tg00BXj6?Tg00CRl9;Tg001MR1g0050R2p,4segsR3g0038R4f1R5f0R6C1P3P4A2356X12X01g002B#4\6P1\5f2R7P2[f3R8P3P4f5R9f4R:P8P7E3P3P4P:P6O1R;P8P6O1C1^49f6R<P9P6O1=23;]4P3f8R;f7R=P<P9P:P8P;P=P<P9P7DCP6M9<W3W5W8W<W1W=W;X90X01g00DS#0#0#0#0#0#0#5#6R0#7%86#9%:03B#AA@356W7X01P3P4P7P5C1A23871=87P3P9P:P8P5A>:86E?W6W3W2X:2X12X01P7P5P6M9;W2W1W0o"). Qed.

End Bridge.

Theorem spec_bridge : forall argv fs, BSpec.spec argv fs = S1Spec.spec argv fs.
Proof.
ltac2:(KReplay.run1 (kr_t_BFBridge ()) [] "h04argvh12fsp;1p;2g00;Tj10Tg00<9j15Tg00<Wj12Tg000mj11Tg00E8j24Tg00Elj23Tg00DS#0#0#0#5#2#1#1g00FFg0050f1f0'4'3W1W0o"). Qed.
