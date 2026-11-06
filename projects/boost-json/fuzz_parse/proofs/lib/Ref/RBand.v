(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMallocRep RMallocTree.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4prod69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~jb5hceil46Stdlib6ZArith6BinInt1Zne2lehc4listhc4pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~q9ddisjoint_from36Stdlib5Lists4Listv52In" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HC.
Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma rdisjoint_high : ltac2:(zQ "80!h9!j4!n6!p6!pb!q2!u5!hg8>1W@1$4@2$1$0$0>1A$0>1n$0>0>2lo$0>2hi$0>0@3$7@2$1$0$0@4$5$0$0^2^1^5@2$3^2@1$2?5HCEIL>0@2$3@1$2?5HCEIL^3@3$6^5^4^3").
Proof. intros W A n.
  induction W as [|[lo hi] W IH]; intros HW HA; cbn; [exact I|].
  split; [pose proof (HW lo hi ltac:(left; reflexivity)); lia|]. apply IH; [|exact HA]. intros lo' hi' Hin. apply (HW lo' hi'). right. exact Hin.
Qed.

End HC.
