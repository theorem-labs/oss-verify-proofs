(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanHexTree.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat04prod37Corelib7Numbers7BinNumsi98positive04cons04pair03nil69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsanHexTree~~~~~~le4gall69OSSVerify6Proofsaboost_jsonafuzz_parse3libh2BothPlanImagesHexZ~~~~~~q3easan_ia_blocks59OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan~~~~~~vah7AsanUbsan_seg_bytes_003i94Nposle3zptq3fasan_tab_blocks" s.
Unset Lia Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition asan_ia_blocks : ltac2:(zQ "40!h8!he!i3!k2@1$0@2$2$3$1") := ltac2:(zQ "60!he!k2!i3!kd!l3!l9@3$3@2$2$1$0@4$4$1$0#hk7N7@3$3@2$2$1$0@4$4$1$0#i9Na@3$3@2$2$1$0@4$4$1$0#h5Nb@3$3@2$2$1$0@4$4$1$0#bNc@3$3@2$2$1$0@4$4$1$0#3Ne@3$3@2$2$1$0@4$4$1$0#1Nh0@3$3@2$2$1$0@4$4$1$0#1Nh1@3$3@2$2$1$0@4$4$1$0#1Nh2@3$3@2$2$1$0@4$4$1$0#h0Nf@3$3@2$2$1$0@4$4$1$0#k4Nd@3$3@2$2$1$0@4$4$1$0#oaNc@3$3@2$2$1$0@4$4$1$0#kl8N9@3$3@2$2$1$0@4$4$1$0#or2N8@3$3@2$2$1$0@4$4$1$0#hhm6N7@3$3@2$2$1$0@4$4$1$0#klpcN5@3$3@2$2$1$0@4$4$1$0#orjaN4@1$5@2$2$1$0").
Lemma asan_ia_gall : ltac2:(zQ "30!pc!u9!hj2@2$0$2$1").
Proof. unfold asan_ia_blocks. gall_vm. Qed.   (* [comment removed for export] *)
Lemma asan_ia_zero : ltac2:(zQ "30!hkd!hl4!hj2@3$1$2@1$0#qjo0@1$0#ohgj0").
Proof. apply (ztree_scan_sound _ asan_ia_blocks); [exact asan_ia_gall| vm_compute; reflexivity]. Qed.

(* [comment removed for export] *)
Definition asan_tab_blocks : ltac2:(zQ "40!h8!he!i3!k2@1$0@2$2$3$1") := ltac2:(zQ "60!he!k2!i3!kd!l3!l9@3$3@2$2$1$0@4$4$1$0#htmgbN3@3$3@2$2$1$0@4$4$1$0#nlo3N5@3$3@2$2$1$0@4$4$1$0#htm1N7@3$3@2$2$1$0@4$4$1$0#ur1N8@3$3@2$2$1$0@4$4$1$0#nl9N9@3$3@2$2$1$0@4$4$1$0#jqdNa@3$3@2$2$1$0@4$4$1$0#ht7Nb@3$3@2$2$1$0@4$4$1$0#jbNe@3$3@2$2$1$0@4$4$1$0#fNh0@3$3@2$2$1$0@4$4$1$0#1Nh4@3$3@2$2$1$0@4$4$1$0#1Nh5@3$3@2$2$1$0@4$4$1$0#8Nh3@3$3@2$2$1$0@4$4$1$0#h2Nh2@3$3@2$2$1$0@4$4$1$0#i6Nh1@3$3@2$2$1$0@4$4$1$0#pcNf@3$3@2$2$1$0@4$4$1$0#in4Nd@3$3@2$2$1$0@4$4$1$0#kuaNc@3$3@2$2$1$0@4$4$1$0#hjqs0N6@3$3@2$2$1$0@4$4$1$0#kurg4N4@3$3@2$2$1$0@4$4$1$0#ptmgaN3@1$5@2$2$1$0").
Lemma asan_tab_gall : ltac2:(zQ "30!pc!hla!hj2@2$0$2$1").
Proof. unfold asan_tab_blocks. gall_vm. Qed.   (* [comment removed for export] *)
Lemma asan_tab_zero : ltac2:(zQ "30!hkd!hl4!hj2@3$1$2@1$0#urgl8@1$0#kgggg0").
Proof. apply (ztree_scan_sound _ asan_tab_blocks); [exact asan_tab_gall| vm_compute; reflexivity]. Qed.
