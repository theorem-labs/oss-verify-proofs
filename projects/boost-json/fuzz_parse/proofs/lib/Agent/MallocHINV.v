(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocRep MallocTree.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Export MallocBlocks.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4listhc4prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~k25block79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~of6mstate37Corelib4Init5Logict63andk2bAREACH_fromk28brk_linkhc3nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocHINV~~~~~~hgf9HINV_from69OSSVerify6Proofsaboost_jsonafuzz_parse3libaHeapSecret~~~~~~hlf7hsecretof5minitt63iff79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~hr5bbrk_link_ps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~ig76PStateig76ps_brk" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Definition HINV_from : ltac2:(zQ "50!h9!j4!jb!o7!sd>4resv@1$1@2$2$0$0>2st$4>4pbrk$0>2LB@1$1$3P") := ltac2:(zQ "80!h9!j4!jb!ua!v0!o7!ve!sd\4resv@1$1@2$2$0$0\2st$7\4pbrk$0\2LB@1$1$5@2$3@2$6^3^2@4$4?4HSEC^4^3^1").

End HCW.

Notation HINV := (HINV_from agent_reserved).

Section HCW2.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma HINV_from_init : ltac2:(zQ "80!h9!j4!hg9!jb!o7!hl2!hpc!hq7>4resv@1$1@2$3$0$0>4pbrk$0@5$5?4HSEC^2@2$7@1$6?4HSEC^2^1@1$2$4").
Proof. intros. split; [exact I | apply areach_init]. Qed.

Lemma brk_link_ps_iff : ltac2:(zQ "60!hqf!ve!hv8!sd!ik3!ikd>2st$3>1s$4@2$0@2$2^2^1@2$1^2@1$5^1").
Proof. intros st s. unfold brk_link_ps, brk_link. destruct (c_brk (ctx st)); tauto. Qed.

End HCW2.

