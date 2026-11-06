(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AxSymExec3 AsanPlanCore AsanPlan AsImages AsPlanImages AsStartup AsStartupHS1 AsStartupPlan AsStartupRanges.
From Ltac2 Require Import Ltac2 Constr Std Control.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_AsStartupCertG1 () := "K47Corelib4Init5Logic2eq01C69OSSVerify5KrLib3bpA5Start9AsStartup:holes_onlyC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify5KrLib3bpA5Start?AsStartupCertG1>AsStartupCert1=startup_shapeC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA5Start8AsanPlan2AP4cres01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA5Start8AsanPlan2AP>mk_itab_rangesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02C79OSSVerify5KrLib3bpA5Start8AsanPlan2AP5checkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start<AsPlanImages5ASEGSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start8AsImages6ASAN_HC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA5Start8AsanPlan2AP3NX0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start8AsanInit5LIMITC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start9AsStartup3XN0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start9AsStartup3XE0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start9AsStartup3XB0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start<AsStartupHS18HS1_asanC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start=AsStartupPlan8CERT_KC0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start=AsStartupPlan:CERT_BFUELC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start=AsStartupPlan9CERT_FUELC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start8AsImages5hinitC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start=AsStartupPlan<startup_planC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib3bpA5Start8AsanPlan2AP4cres00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start?AsStartupRangesDstartup_plan_xrangesC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib3bpA5Start8AsanPlan2AP7loopctx00C1?~~~~~~~~~~~~~~~".
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
ltac2:(KReplay.run1 (kr_t_AsStartupCertG1 ()) [] "p;2p;1p;3g0000j22Tg000Jj11Tg001Mj30Tg001gR0g002GR1'2g002g#1=001do"). Qed.
Lemma startup_cert :
  check ASEGS (mk_itab_ranges ASEGS startup_plan_xranges) ASAN_H NX0 AsanInit.LIMIT XN0 XE0 XB0 HS1_asan CERT_KC0 CERT_BFUEL CERT_FUEL None hinit startup_plan = COk startup_shape.
Proof.
ltac2:(KReplay.run1 (kr_t_AsStartupCertG1 ()) [] "p;1p;2p;3p;?g004Bj16Tg0000j25Tg005Cj20Tg006Lj11Tg001Mj32Tg006nl?3Tg007nR0f1g008og009mg00:kg00;hg00<dg00=`g00>\g00?`g00@eg00Alf0g00C2g00CoM?3p=4g00E8R1g002g#6R2'5g00F9,00g00GL#1'4=212do"). Qed.
End AsStartupCert1.
