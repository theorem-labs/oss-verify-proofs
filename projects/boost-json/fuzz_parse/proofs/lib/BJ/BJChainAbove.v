(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require Import BJFrame HeapMF_iface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJcHeapMF_iface~~~~~~03ehk05frame37Corelib4Init9Datatypeske4list08chain_sp0beh_chain_ok05fr_sp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~ob3mem36Stdlib5Lists4Listtb2In46Stdlib6ZArith6BinInt1Zv32le" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CA.
  Context {HCEIL : HeapCeil}.

  Definition eh_chain_above : ltac2:(zQ "10!k2>1E$0P") := ltac2:(zQ "90!k7!m6!md!n7!k2!o4!t5!ue!hgb\1E$4>1G@1$1$0>1m$6>1f$0>0@3$3^4^3^2>0@3$7$0^2^4@2$8@1$2^5@1$5^3").

  (* [comment removed for export] *)

  (* [comment removed for export] *)
End CA.
(* [comment removed for export] *)
