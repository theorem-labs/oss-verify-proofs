(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from AgentNodes.v for the budget-premise witness: the same statements and proof scripts over BudgetWit.Rzb.realizes; only the name tables change. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  SimInv ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim AllocSim FileSim
  ShapeAlg Nodes StoreOk.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AgentLib Scfg.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16option3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsm2dmachine_state3h5LinuxProcessSemantics5Riscv7Preludeq95bvmapk14Nonek14Somem2h3Build_machine_state69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~vc6fp_csrvc7fp_regs37Corelib4Init5Logichka2eqk14boolk14listk14truehka1I3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehne7Segmentm29MachineOkm2afetch_wordm28is_ecallm2emachine_resultm24step79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAgentNodes4FPX1~~~~~~hva5ependvc4getrvc4mksthf2BVhf4BvWfm26ms_gpr46Stdlib6ZArith6BinInt1Zim83addim86of_nathf7Z_to_bvm2cms_read_byte69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7FileSim~~~~~~iqa3mrbvc7seg_romm2h0ms_writable_bytem25wviewm28set_gpr03h5LinuxProcessSemanticsfLinuxProcessSem3Runjhch0advance_past_svcvc6regupdvc6v_addik13nilk14prodk13natjhccapply_effect3h5LinuxProcessSemanticsfLinuxProcessSem5Statejp27MemCopyjp29mkEffectUjp2cwith_copyins" s.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AgentNodes.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.BudgetWit.Rzb.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.

Lemma rz_sys {SC : StepCfg} : forall segs regs pc mem rom model w T,
  m_halted model = None ->
  m_vm_lazy model = [] ->
  fetch_word segs pc = Some w -> is_ecall w = true ->
  realizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
  realizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
  intros segs regs pc mem rom model w T Hh Hlazy HF HE Hc.
  eapply rz_step; [exact Hh | exact Hlazy | reflexivity | eapply step_ecall_epend; eassumption | exact Hc].
Qed.

End FPX1.
