(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound Scfg.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~0bis_ecall_at79OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlanSound3APS~~~~~~kbanode1_stmtkbanode_mmap10cnode_mmapin10dnode_mprotect0dnode_mmapgapskbanodeL_stmt37Corelib4Init9Datatypesu24list3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehg17Segment06atableu23nat37Corelib7Numbers7BinNumshkf1Zhkf4Npos35stdpp9bitvectorbdefinitionshn52bvu26option79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~hq13envu24bool3h5LinuxProcessSemanticsfLinuxProcessSem2Fshv02Fs" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section Iface.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable SEGS : ltac2:(zQ "20!va!hj6@1$0$1").
Context {SC : StepCfg}.   (* [comment removed for export] *)
Variable A : ltac2:(zQ "10!hk1$0").
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : ltac2:(zQ "40!hmd!hp2!hp8!hu2>0$3>0>0@1$1@1$0#k0@1$2@1$1@1$0#8P").
Variable argH : ltac2:(zQ "40!hu9!hmd!hu2!hp2>0$2>0@1$3@1$1#k0$0").
Variable FS0 : ltac2:(zQ "10!ihb$0").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition OBL_mmap1 : ltac2:(zQ "00P") := ltac2:(zQ "30!je!of!pc@b$1?2fx?4SEGS?2SC?1A?3nx0?5LIMIT?4SINV?4argH?3FS0@1$0?4SEGS@3$2?1A?3nx0?5LIMIT").
Definition OBL_mmapin1 : ltac2:(zQ "00P") := ltac2:(zQ "30!je!q9!of@b$2?2fx?4SEGS?2SC?1A?3nx0?5LIMIT?4SINV?4argH?3FS0@1$0?4SEGS@2$1?1A?5LIMIT").
Definition OBL_mprotect1 : ltac2:(zQ "00P") := ltac2:(zQ "30!je!r7!of@b$2?2fx?4SEGS?2SC?1A?3nx0?5LIMIT?4SINV?4argH?3FS0@1$0?4SEGS@2$1?1A?5LIMIT").
(* [comment removed for export] *)
Definition OBL_mmapgaps : ltac2:(zQ "00P") := ltac2:(zQ "30!je!s6!t5@b$2?2fx?4SEGS?2SC?1A?3nx0?5LIMIT?4SINV?4argH?3FS0@1$0?4SEGS@3$1?1A?3nx0?5LIMIT").

(* [comment removed for export] *)

End Iface.
(* [comment removed for export] *)
