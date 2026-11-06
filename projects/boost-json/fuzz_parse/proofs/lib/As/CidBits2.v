(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import CidBits.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04bool04true37Corelib4Init5Logici42eq37Corelib7Numbers7BinNumsjd1Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7CidBits~~~~~~ladforall_rangeZ69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~q78class_id46Stdlib6ZArith6BinInt1Zv33lebv32lei43and" s.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma class_id_chk30 : ltac2:(zQ "70!h8!he!j8!l6!p7!u8!hgb@3$2$0@3$4\1s$3@2$6@1$5^1+he+1+hggg0$1").
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma class_id_le30 : ltac2:(zQ "40!hh1!hh6!u8!l6>4size$3>0@2$1@2$0+1^1@2$0^1+hggg0@2$1@2$0+1@1$2^2@2$0@1$2^2+he").
Proof.
  intros size Hs. pose proof (class_id_range size Hs) as [A _].
  pose proof (forall_rangeZ_spec (fun s => class_id s <=? 30) 1 65536 size class_id_chk30 ltac:(lia) ltac:(lia)) as C.
  cbv beta in C. apply Z.leb_le in C. lia.
Qed.
