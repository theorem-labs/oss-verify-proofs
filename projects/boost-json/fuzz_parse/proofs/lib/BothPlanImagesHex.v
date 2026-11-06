(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanHexScan AsanHexTree.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat04prod37Corelib7Numbers7BinNumsi98positive04cons04pair03nil69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsanHexTree~~~~~~le5gallv69OSSVerify6Proofsaboost_jsonafuzz_parse3libh1BothPlanImagesHex~~~~~~q4h0asan_hex2_blocks59OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan~~~~~~vdh7AsanUbsan_seg_bytes_00204bool04true37Corelib4Init5Logichlc2eqi92N0i94Npos69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsanHexScan~~~~~~ho25scanNle3vpti91N57Corelib7Numbers6Cyclic5Int63cUint63Axiomsht34to_Z37Corelib7StringsaPrimStringig66length46Stdlib6ZArith6BinInt1Ziic3diviic4to_Nvdh7AsanUbsan_seg_bytes_003q4h1asan_hex3a_blocksq4h1asan_hex3b_blocks" s.
Unset Lia Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition asan_hex2_blocks : ltac2:(zQ "40!h8!he!i3!k2@1$0@2$2$3$1") := ltac2:(zQ "60!he!k2!i3!kd!l3!l9@3$3@2$2$1$0@4$4$1$0#1N0@3$3@2$2$1$0@4$4$1$0#1N1@3$3@2$2$1$0@4$4$1$0#1N2@3$3@2$2$1$0@4$4$1$0#1N3@3$3@2$2$1$0@4$4$1$0#1N4@3$3@2$2$1$0@4$4$1$0#1N5@3$3@2$2$1$0@4$4$1$0#1N6@3$3@2$2$1$0@4$4$1$0#1N7@3$3@2$2$1$0@4$4$1$0#1N8@3$3@2$2$1$0@4$4$1$0#1N9@3$3@2$2$1$0@4$4$1$0#1Na@3$3@2$2$1$0@4$4$1$0#1Nb@3$3@2$2$1$0@4$4$1$0#1Nc@3$3@2$2$1$0@4$4$1$0#1Nd@3$3@2$2$1$0@4$4$1$0#1Ne@3$3@2$2$1$0@4$4$1$0#4Nd@1$5@2$2$1$0").
Lemma asan_hex2_gallv : ltac2:(zQ "30!pc!u9!hj5@2$0$2$1").
Proof. unfold asan_hex2_blocks. gallv_vm. Qed.
Lemma asan_hex2_0 : ltac2:(zQ "70!hl0!hl6!hn0!hn6!hnb!hs0!hj5@3$2$0@4$5$6Nk0$3@1$4#1$1").
Proof. vm_compute. reflexivity. Qed.
Lemma asan_hex2 : ltac2:(zQ "40!hn6!hnb!hs9!hj5@3$2$3$0@1$1#qgg0").
Proof.
  change 40960%N with (1 + 40959)%N. apply vpt_app; [exact (scanN_sound _ _ 0 1 asan_hex2_0)|].
  apply (vtree_scan_sound _ asan_hex2_blocks); [exact asan_hex2_gallv| vm_compute; reflexivity].
Qed.

Lemma asan_len2 : ltac2:(zQ "80!hn0!hsf!hnb!hve!ii2!hj5!ik4!ikb@3$0$1@1$7@2$6@1$3@1$4$5+2@1$2#qgg0").
Proof. vm_compute. reflexivity. Qed.
Lemma asan_len3 : ltac2:(zQ "80!hn0!hsf!hnb!hve!ii2!il3!ik4!ikb@3$0$1@1$7@2$6@1$3@1$4$5+2@1$2#llvgg0").
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition asan_hex3a_blocks : ltac2:(zQ "40!h8!he!i3!k2@1$0@2$2$3$1") := ltac2:(zQ "60!he!k2!i3!kd!l3!l9@3$3@2$2$1$0@4$4$1$0#1N0@3$3@2$2$1$0@4$4$1$0#1N1@3$3@2$2$1$0@4$4$1$0#1N2@3$3@2$2$1$0@4$4$1$0#1N3@3$3@2$2$1$0@4$4$1$0#1N4@3$3@2$2$1$0@4$4$1$0#1N5@3$3@2$2$1$0@4$4$1$0#1N6@3$3@2$2$1$0@4$4$1$0#1N7@3$3@2$2$1$0@4$4$1$0#1N8@3$3@2$2$1$0@4$4$1$0#1N9@3$3@2$2$1$0@4$4$1$0#1Na@3$3@2$2$1$0@4$4$1$0#1Nb@3$3@2$2$1$0@4$4$1$0#1Nc@3$3@2$2$1$0@4$4$1$0#1Nd@3$3@2$2$1$0@4$4$1$0#1Ne@3$3@2$2$1$0@4$4$1$0#4Nd@3$3@2$2$1$0@4$4$1$0#l0N9@3$3@2$2$1$0@4$4$1$0#q2N8@3$3@2$2$1$0@4$4$1$0#hk6N7@1$5@2$2$1$0").
Lemma asan_hex3a_gallv : ltac2:(zQ "30!pc!ime!il3@2$0$2$1").
Proof. unfold asan_hex3a_blocks. gallv_vm. Qed.
Lemma asan_hex3a_0 : ltac2:(zQ "70!hl0!hl6!hn0!hn6!hnb!hs0!il3@3$2$0@4$5$6Nk0$3@1$4#1$1").
Proof. vm_compute. reflexivity. Qed.
Lemma asan_hex3a : ltac2:(zQ "40!hn6!hnb!hs9!il3@3$2$3$0@1$1#qjo0").
Proof.
  change 41856%N with (1 + 41855)%N. apply vpt_app; [exact (scanN_sound _ _ 0 1 asan_hex3a_0)|].
  apply (vtree_scan_sound _ asan_hex3a_blocks); [exact asan_hex3a_gallv| vm_compute; reflexivity].
Qed.

(* [comment removed for export] *)
Definition asan_hex3b_blocks : ltac2:(zQ "40!h8!he!i3!k2@1$0@2$2$3$1") := ltac2:(zQ "60!he!k2!i3!kd!l3!l9@3$3@2$2$1$0@4$4$1$0#orjbN4@3$3@2$2$1$0@4$4$1$0#iisfN6@3$3@2$2$1$0@4$4$1$0#iidNa@3$3@2$2$1$0@4$4$1$0#hh7Nb@3$3@2$2$1$0@4$4$1$0#i3Ne@3$3@2$2$1$0@4$4$1$0#9Nh0@3$3@2$2$1$0@4$4$1$0#5Nh1@3$3@2$2$1$0@4$4$1$0#6Nh1@3$3@2$2$1$0@4$4$1$0#hcNf@3$3@2$2$1$0@4$4$1$0#n4Nd@3$3@2$2$1$0@4$4$1$0#uaNc@3$3@2$2$1$0@4$4$1$0#jqs0N6@3$3@2$2$1$0@4$4$1$0#urg4N4@3$3@2$2$1$0@4$4$1$0#htmgaN3@1$5@2$2$1$0").
Lemma asan_hex3b_gallv : ltac2:(zQ "30!pc!io3!il3@2$0$2$1").
Proof. unfold asan_hex3b_blocks. gallv_vm. Qed.
Lemma asan_hex3b : ltac2:(zQ "30!hnb!hs9!il3@3$1$2@1$0#orjr0@1$0#lvsq8").
Proof. apply (vtree_scan_sound _ asan_hex3b_blocks); [exact asan_hex3b_gallv| vm_compute; reflexivity]. Qed.
