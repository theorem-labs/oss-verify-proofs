(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Bcfg BCatSim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BShapeAlg.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAcct BpinAlg.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BothAcctShape () := "I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C6ARocqVerifyHarness?AgentSubmission3bpB5Start8BothAcctErz_msteps_restricted'I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C6ARocqVerifyHarness?AgentSubmission3bpB2HF9BShapeAlg4TSet".
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WithSegs.
Variable segs : list Segment.
Context {SC : StepCfg}.
Variable H : word -> bool.
Hypothesis HH : H_off_segments segs H.
Hypothesis Hwx : wx_segs_nowrap segs.

Let P_of (T : TSet) : config -> Prop := fun c => realizes segs c T.

Let P_of_silent1 (T : TSet) : forall c c',
    BothAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    P_of T c' -> P_of T c :=
  fun c c' Hn Hr => rz_silent1 segs c c' T Hn Hr.

Let SP_of (T : TSet) : config -> Prop := fun c => srealizes segs c T.

Let SP_of_silent1 (T : TSet) : forall c c',
    BothAcct.node_ok segs c unit (fun _ => []) (fun _ => c') ->
    SP_of T c' -> SP_of T c :=
  fun c c' Hn Hr => srz_silent1 segs c c' T Hn Hr.

Theorem srz_msteps_restricted_T : forall A ms msr' model T,
  lazy_cover H (m_vm_lazy model) A -> A_wf A -> MInv A model ->
  m_halted model = None ->
  msteps segs (restrict H ms) msr' ->
  (forall model',
      MInv A model' -> same_but_materialized model model' ->
      hclean H msr' ->
      srealizes segs (mkCfg (unrestrict H (ms_mem ms) msr') model') T) ->
  srealizes segs (mkCfg ms model) T.
Proof.
ltac2:(KReplay.run1 (kr_t_BothAcctShape ()) ["WithSegs"] "h01Ah11Th25modelh32msh44msr'p;2p;1p;;g0000j22Tg000Pj11Tg0010l;0Tg002=R0/20#1g002[R0g003bg004Xp,4segsp,2SCp,1Hp,2HHp,3Hwxp,5SP_off0R1O1p,=SP_of_silent1P1O1f4f3f2f1M;0W1W2X40W3W0o"). Qed.
End WithSegs.
