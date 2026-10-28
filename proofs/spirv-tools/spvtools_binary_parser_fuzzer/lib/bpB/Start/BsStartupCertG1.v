(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BxSymExec3 BothPlanCore BothPlan BsImages BsPlanImages BsStartup BsStartupHS1 BsStartupPlan BsStartupRanges.
From Ltac2 Require Import Ltac2 Constr Std Control.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BsStartupCertG1 () := "K47Corelib4Init5Logic2eq01C6ARocqVerifyHarness?AgentSubmission3bpB5Start9BsStartup:holes_onlyI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c7ARocqVerifyHarness?AgentSubmission3bpB5Start?BsStartupCertG1>AsStartupCert1=startup_shapeK7ARocqVerifyHarness?AgentSubmission3bpB5Start8BothPlan2AP4cres01C7ARocqVerifyHarness?AgentSubmission3bpB5Start8BothPlan2AP>mk_itab_rangesK47Corelib4Init9Datatypes6option02C7ARocqVerifyHarness?AgentSubmission3bpB5Start8BothPlan2AP5checkC6ARocqVerifyHarness?AgentSubmission3bpB5Start<BsPlanImages5ASEGSC6ARocqVerifyHarness?AgentSubmission3bpB5Start8BsImages6ASAN_HC7ARocqVerifyHarness?AgentSubmission3bpB5Start8BothPlan2AP3NX0C6ARocqVerifyHarness?AgentSubmission3bpB5Start8BothInit5LIMITC6ARocqVerifyHarness?AgentSubmission3bpB5Start9BsStartup3XN0C6ARocqVerifyHarness?AgentSubmission3bpB5Start9BsStartup3XE0C6ARocqVerifyHarness?AgentSubmission3bpB5Start9BsStartup3XB0C6ARocqVerifyHarness?AgentSubmission3bpB5Start<BsStartupHS18HS1_asanC6ARocqVerifyHarness?AgentSubmission3bpB5Start=BsStartupPlan8CERT_KC0C6ARocqVerifyHarness?AgentSubmission3bpB5Start=BsStartupPlan:CERT_BFUELC6ARocqVerifyHarness?AgentSubmission3bpB5Start=BsStartupPlan9CERT_FUELC6ARocqVerifyHarness?AgentSubmission3bpB5Start8BsImages5hinitC6ARocqVerifyHarness?AgentSubmission3bpB5Start=BsStartupPlan<startup_planI7ARocqVerifyHarness?AgentSubmission3bpB5Start8BothPlan2AP4cres00C6ARocqVerifyHarness?AgentSubmission3bpB5Start?BsStartupRangesDstartup_plan_xrangesI7ARocqVerifyHarness?AgentSubmission3bpB5Start8BothPlan2AP7loopctx00".
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache.

Ltac2 cert_refl (rhs : constr) :=
  let g := Control.goal () in
  let r := constr:(@eq_refl cres $rhs) in
  Std.exact_no_check (Constr.Unsafe.make (Constr.Unsafe.Cast r Constr.Cast.vm g)).

Module AsStartupCert1.
Definition startup_shape : shape := (SHole 90).
Lemma startup_shape_holes : holes_only startup_shape = true.
Proof.
ltac2:(KReplay.run1 (kr_t_BsStartupCertG1 ()) [] "p;2p;1p;3g0000j22Tg000Jj11Tg001Mj30Tg001gR0g002GR1'2g002g#1=001do"). Qed.
Lemma startup_cert :
  check ASEGS (mk_itab_ranges ASEGS startup_plan_xranges) ASAN_H NX0 BothInit.LIMIT XN0 XE0 XB0 HS1_asan CERT_KC0 CERT_BFUEL CERT_FUEL None hinit startup_plan = COk startup_shape.
Proof.
ltac2:(KReplay.run1 (kr_t_BsStartupCertG1 ()) [] "p;1p;2p;3p;?g004Bj16Tg0000j25Tg005Cj20Tg006Lj11Tg001Mj32Tg006nl?3Tg007nR0f1g008og009mg00:kg00;hg00<dg00=`g00>\g00?`g00@eg00Alf0g00C2g00CoM?3p=4g00E8R1g002g#6R2'5g00F9,00g00GL#1'4=212do"). Qed.
End AsStartupCert1.
