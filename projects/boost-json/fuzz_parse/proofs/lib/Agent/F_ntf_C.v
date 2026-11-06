(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_B F_ntf_A F_ntf_B.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hc4aptrhc6mstate37Corelib4Init5Logicma2eqma3and37Corelib4Init9Datatypeso94Somema3not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~qe9meta_slothc4optrma2exhc6activehccget_meta_rechc6m_prevo94bool79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentbMallocKit_B~~~~~~hj08queue_sthc7LActivehc8optr_eqb" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition qa_facts : ltac2:(zQ "30!h9!la!m1>2st$2>2sc$0>1g$1P") := ltac2:(zQ "d0!la!ne!o3!q1!q8!v0!vc!hg3!h9!hg8!hh1!hi0!m1\2st$c\2sc$8\1g$0>4head$0>0@3$1$6@2$9^4^3@2$3$0^1>0@1$4@3$1$0^2^3@2$2@2$5^6^3@2$7$0\2pv$0@2$2@3$1$6@1$b@2$a^7^4@2$3$0^1@2$2@1$4@3$1$0^1^5@2$5^7^1").

Definition qpath_st : ltac2:(zQ "30!m1!h9!la>2st$0>2sc$1>1g$2$0") := ltac2:(zQ "90!hi9!la!m1!q1!h9!hn4!ho0!hg8!hoa\2st$2\2sc$4\1g$1M0\0$0$2@2$8@2$7^3^2@2$3$1^1^3@3$5@1$6^2^1^3").

(* [comment removed for export] *)
