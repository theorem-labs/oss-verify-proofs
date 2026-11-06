(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt HeapMF_iface.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUcHeapMF_iface~~~~~~03hmf79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~k95block37Corelib4Init9Datatypespc4list08hs_RHEAPk98blk_addrk93mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~t66PState36Stdlib5Lists4Listhhb2In46Stdlib6ZArith6BinInt1Zhj42lt" s.
Open Scope Z_scope.

Section F.
  Context {HCEIL : HeapCeil}.
  Definition heap_floor : ltac2:(zQ "10!k4>1H$0P") := ltac2:(zQ "90!p4!r4!k4!rb!s5!t0!hh2!hie!hkc\1H$2>1s$6>2LB@1$1$0>1m$5>1b$0>0@4$3^5^4^3^2>0@3$7$0^2^4@2$8+hgg0@1$4^3").
End F.
