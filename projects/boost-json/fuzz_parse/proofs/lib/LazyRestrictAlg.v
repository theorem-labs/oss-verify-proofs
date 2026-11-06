(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg CatSim ShapeAlg LazyRestrict LazyRestrictRun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemantics0dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem5Statek65Model37Corelib7Numbers7BinNumsnc4Npos35stdpp9bitvectorbdefinitionspc2bv37Corelib4Init9Datatypesre4unit37Corelib4Init5Logictd2eqre4Nonere6optionre4prod3h5LinuxProcessSemanticsfLinuxProcessSem3Runhgd5mkCfgre3nilre4pair09MachineOk0emachine_result0ems_svc_pendinghgdfmi_account_stepk65eventk68m_halted69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~hq07node_okhgd6confighq08realizes69OSSVerify6Proofsaboost_jsonafuzz_parse3libfLazyRestrictRun~~~~~~hvc6dstepshq04TSetre4list3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeil77Segment" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!il0!ioc@1$0$1").
Context {SC : StepCfg}.   (* [comment removed for export] *)

Lemma node_account : ltac2:(zQ "h30!j7!n4!p5!r9!t6!v1!v6!vd!hg6!hj9!hk2!hk8!hkf!hla!hma!hna!hod!hp5!htb>2ms$0>5model$1>3ms'$0>6model'$1>0@3$5@1$7@1$3@1$2#k0@1$h1^3@1$6@1$3@1$2#k0>0@3$5@1$7@1$3@1$2#k0@1$e^5@1$6@1$3@1$2#k0>0@3$5@1$d@2$8$0$1@3$f?4segs^6^5@2$c@2$8$0$1@4$b$0$1^4^3@6$h2?4segs?2SC@2$9^7^6$4\0$4@1$a$h0\0$4@2$9^6^5").
Proof. intros. apply node_instr_acct; assumption. Qed.

Lemma rz_dsteps : ltac2:(zQ "40!hu6!hv0!ije!ik8>1c$0>2c'$0>1T$3>0@3$2?4segs^3^2>0@4$1?4segs?2SC^3^2@4$1?4segs?2SC^5^3").
Proof.
  intros c c' T H; induction H as [c | ms model ms' model' c3 Hh Hsvc Hacc H IH]; intros Hr; [exact Hr|].
  eapply rz_silent1; [apply node_account; [exact Hh | exact Hsvc | exact Hacc] | apply IH; exact Hr].
Qed.

(* [comment removed for export] *)
Lemma rz_account_step : ltac2:(zQ "h10!j7!n4!p5!r9!v1!v6!vd!hg6!hj9!hv0!hk8!hkf!hla!hma!hna!hp5!ik8>2ms$0>5model$1>3ms'$0>6model'$1>1T$h0>0@3$4@1$6@1$3@1$2#k0@1$f^4@1$5@1$3@1$2#k0>0@3$4@1$6@1$3@1$2#k0@1$d^6@1$5@1$3@1$2#k0>0@3$4@1$c@2$7$0$1@3$e?4segs^7^6@2$b@2$7$0$1@4$a$0$1^5^4>0@4$9?4segs?2SC@2$8^6^5^4@4$9?4segs?2SC@2$8^9^8^5").
Proof.
  intros ms model ms' model' T Hh Hsvc Hacc Hr.
  eapply rz_silent1; [apply node_account; eassumption | exact Hr].
Qed.

Section WithLazy.
Variables L S : list (word * word).
Hypothesis HL : lazy_ranges_okb segs L = true.

(* [comment removed for export] *)

(* [comment removed for export] *)

End WithLazy.
End WithSegs.
(* [comment removed for export] *)
