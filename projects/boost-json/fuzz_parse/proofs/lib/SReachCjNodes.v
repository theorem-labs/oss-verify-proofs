(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require ITree Nodes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SReach SReachTree.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Nodes~~~~~~04node05nexit05nstep69OSSVerify6Proofsaboost_jsonafuzz_parse3libaSReachTree~~~~~~l0bsilent_node69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~pbdhunspell_scfg37Corelib7Numbers7BinNumsu21Z04NBrk79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSReachCjNodes4FPX1~~~~~~hg5ecj_silent_node05NMmap07NMunmap09NMprotect07NSetTid06NIoctl06NClose37Corelib4Init9Datatypeshp04listu24Npos05NOpen35stdpp9bitvectorbdefinitionshre2bv05NReadhp04boolhp04truehp05false37Corelib4Init5Logicig12eqhg5eis_silent_kind" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition cj_silent_node : ltac2:(zQ "10!jc>1n$0P") := ltac2:(zQ "50!jc!k2!k9!od!t2\1n$0@4$3$0@1$2$4$1^1").

Lemma silent_NBrk : ltac2:(zQ "30!vb!vf!hka>3req$0@1$2@1$1^1").
Proof. intros req. split; [intros mo code mo' H; exact H | intros mo rsp mo' evs [H _]; exact H]. Qed.

Lemma silent_NMmap : ltac2:(zQ "30!vb!hlc!hka>4addr$0>3len$0>4prot$0>5flags$0@1$2@4$1^4^3^2^1").
Proof. intros. split; [intros mo code mo' H; exact H | intros mo rsp mo' evs [H _]; exact H]. Qed.

Lemma silent_NMunmap : ltac2:(zQ "30!vb!hm3!hka>4addr$0>3len$0@1$2@2$1^2^1").
Proof. intros. split; [intros mo code mo' H; exact H | intros mo rsp mo' evs [H _]; exact H]. Qed.

Lemma silent_NMprotect : ltac2:(zQ "30!vb!hmc!hka>4addr$0>3len$0>4prot$0@1$2@3$1^3^2^1").
Proof. intros. split; [intros mo code mo' H; exact H | intros mo rsp mo' evs [H _]; exact H]. Qed.

(* [comment removed for export] *)
Lemma silent_NSetTid : ltac2:(zQ "20!hn7!hka@1$1$0").
Proof. split; [intros mo code mo' H; exact H | intros mo rsp mo' evs [H _]; exact H]. Qed.

Lemma silent_NIoctl : ltac2:(zQ "30!vb!ho0!hka>2fd$0>3req$0@1$2@2$1^2^1").
Proof. intros. split; [intros mo code mo' H; exact H | intros mo rsp mo' evs [H _]; exact H]. Qed.

Lemma silent_NClose : ltac2:(zQ "30!vb!ho8!hka>2fd$0@1$2@1$1^1").
Proof. intros. split; [intros mo code mo' H; exact H | intros mo rsp mo' evs [H _]; exact H]. Qed.

Lemma silent_NOpen : ltac2:(zQ "50!hq8!hr0!hr7!hka!htb>4path@1$0@1$4@1$1#8@1$3@1$2^1").
Proof. intros. split; [intros mo code mo' H; exact H | intros mo rsp mo' evs [H _]; exact H]. Qed.

Lemma silent_NRead : ltac2:(zQ "30!vb!hu1!hka>2fd$0>3buf$0>5count$0@1$2@3$1^3^2^1").
Proof. intros. split; [intros mo code mo' H; exact H | intros mo rsp mo' evs [H _]; exact H]. Qed.

(* [comment removed for export] *)
Definition is_silent_kind : ltac2:(zQ "20!hu8!jc>1n$1$0") := ltac2:(zQ "80!vb!hv0!hq8!hv8!hr0!jc!htb!hu8\1n$5M5\1n$5$7^1\2fd$0\2bs@1$2@1$6@1$4#8$3\2fd$0\4bufs@1$2@1$2@1$6@1$4#8$3\4path@1$2@1$6@1$4#8$1\2fd$0\3buf$0\5count$0$1\2fd$0$1\2fd$0\3req$0$1$1\4code$0$3\3req$0$1\4addr$0\3len$0\4prot$0\5flags$0$1\4addr$0\3len$0$1\4addr$0\3len$0\4prot$0$1").

Lemma is_silent_kind_sound : ltac2:(zQ "60!hu8!hv0!ih5!jc!hka!ihb>1n$3>0@3$2$0@1$5^1$1@1$4^2").
Proof.
  intros n H. destruct n; try discriminate H.
  - apply silent_NOpen.
  - apply silent_NRead.
  - apply silent_NClose.
  - apply silent_NIoctl.
  - apply silent_NSetTid.
  - apply silent_NBrk.
  - apply silent_NMmap.
  - apply silent_NMunmap.
  - apply silent_NMprotect.
Qed.
End FPX1.
