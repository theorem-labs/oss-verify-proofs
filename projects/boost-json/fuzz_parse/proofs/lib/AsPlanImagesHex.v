(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Top0Gc4. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanHexScan AsanHexTree.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat04prod37Corelib7Numbers7BinNumsi98positive04cons04pair03nil69OSSVerify6Proofsaboost_jsonafuzz_parse3libfAsPlanImagesHex~~~~~~leh0asan_hex2_blocks69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsanHexTree~~~~~~r45gallv59OSSVerifyaboost_jsonafuzz_parse6images4Asan~~~~~~vah2Asan_seg_bytes_00204bool04true37Corelib4Init5Logichkf2eqi92N0i94Npos69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsanHexScan~~~~~~hn55scanNr43vpti91N57Corelib7Numbers6Cyclic5Int63cUint63Axiomshs64to_Z37Corelib7StringsaPrimStringhv96length46Stdlib6ZArith6BinInt1Zihf3divihf4to_Nvah2Asan_seg_bytes_003leh1asan_hex3a_blocksleh1asan_hex3b_blocks" s.
Unset Lia Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition asan_hex2_blocks : ltac2:(zQ "40!h8!he!i3!k2@1$0@2$2$3$1") := ltac2:(zQ "60!he!k2!i3!kd!l3!l9@3$3@2$2$1$0@4$4$1$0#1N0@3$3@2$2$1$0@4$4$1$0#1N1@3$3@2$2$1$0@4$4$1$0#1N2@3$3@2$2$1$0@4$4$1$0#1N3@3$3@2$2$1$0@4$4$1$0#1N4@3$3@2$2$1$0@4$4$1$0#1N5@3$3@2$2$1$0@4$4$1$0#1N6@3$3@2$2$1$0@4$4$1$0#1N7@3$3@2$2$1$0@4$4$1$0#1N8@3$3@2$2$1$0@4$4$1$0#1N9@3$3@2$2$1$0@4$4$1$0#1Na@3$3@2$2$1$0@4$4$1$0#1Nb@3$3@2$2$1$0@4$4$1$0#1Nc@3$3@2$2$1$0@4$4$1$0#1Nd@3$3@2$2$1$0@4$4$1$0#1Ne@3$3@2$2$1$0@4$4$1$0#4Nd@1$5@2$2$1$0").
Lemma asan_hex2_gallv : ltac2:(zQ "30!q0!v2!hid@2$1$2$0").
Proof. unfold asan_hex2_blocks. gallv_vm. Qed.
Lemma asan_hex2_0 : ltac2:(zQ "70!hk3!hk9!hm3!hm9!hme!hr3!hid@3$2$0@4$5$6Nk0$3@1$4#1$1").
Proof. vm_compute. reflexivity. Qed.
Lemma asan_hex2 : ltac2:(zQ "40!hm9!hme!hrc!hid@3$2$3$0@1$1#qgg0").
Proof.
  change 40960%N with (1 + 40959)%N. apply vpt_app; [exact (scanN_sound _ _ 0 1 asan_hex2_0)|].
  apply (vtree_scan_sound _ asan_hex2_blocks); [exact asan_hex2_gallv| vm_compute; reflexivity].
Qed.

Lemma asan_len2 : ltac2:(zQ "80!hm3!hs2!hme!hv1!ih5!hid!ij7!ije@3$0$1@1$7@2$6@1$3@1$4$5+2@1$2#qgg0").
Proof. vm_compute. reflexivity. Qed.
Lemma asan_len3 : ltac2:(zQ "80!hm3!hs2!hme!hv1!ih5!ik6!ij7!ije@3$0$1@1$7@2$6@1$3@1$4$5+2@1$2#llvgg0").
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition asan_hex3a_blocks : ltac2:(zQ "40!h8!he!i3!k2@1$0@2$2$3$1") := ltac2:(zQ "60!he!k2!i3!kd!l3!l9@3$3@2$2$1$0@4$4$1$0#1N0@3$3@2$2$1$0@4$4$1$0#1N1@3$3@2$2$1$0@4$4$1$0#1N2@3$3@2$2$1$0@4$4$1$0#1N3@3$3@2$2$1$0@4$4$1$0#1N4@3$3@2$2$1$0@4$4$1$0#1N5@3$3@2$2$1$0@4$4$1$0#1N6@3$3@2$2$1$0@4$4$1$0#1N7@3$3@2$2$1$0@4$4$1$0#1N8@3$3@2$2$1$0@4$4$1$0#1N9@3$3@2$2$1$0@4$4$1$0#1Na@3$3@2$2$1$0@4$4$1$0#1Nb@3$3@2$2$1$0@4$4$1$0#1Nc@3$3@2$2$1$0@4$4$1$0#1Nd@3$3@2$2$1$0@4$4$1$0#1Ne@3$3@2$2$1$0@4$4$1$0#4Nd@3$3@2$2$1$0@4$4$1$0#i8Na@3$3@2$2$1$0@4$4$1$0#hk8N7@1$5@2$2$1$0").
Lemma asan_hex3a_gallv : ltac2:(zQ "30!ilc!v2!ik6@2$1$2$0").
Proof. unfold asan_hex3a_blocks. gallv_vm. Qed.
Lemma asan_hex3a_0 : ltac2:(zQ "70!hk3!hk9!hm3!hm9!hme!hr3!ik6@3$2$0@4$5$6Nk0$3@1$4#1$1").
Proof. vm_compute. reflexivity. Qed.
Lemma asan_hex3a : ltac2:(zQ "40!hm9!hme!hrc!ik6@3$2$3$0@1$1#qko0").
Proof.
  change 42112%N with (1 + 42111)%N. apply vpt_app; [exact (scanN_sound _ _ 0 1 asan_hex3a_0)|].
  apply (vtree_scan_sound _ asan_hex3a_blocks); [exact asan_hex3a_gallv| vm_compute; reflexivity].
Qed.

(* [comment removed for export] *)
Definition asan_hex3b_blocks : ltac2:(zQ "40!h8!he!i3!k2@1$0@2$2$3$1") := ltac2:(zQ "60!he!k2!i3!kd!l3!l9@3$3@2$2$1$0@4$4$1$0#orkbN4@3$3@2$2$1$0@4$4$1$0#iit3N6@3$3@2$2$1$0@4$4$1$0#or5N8@3$3@2$2$1$0@4$4$1$0#klbN9@3$3@2$2$1$0@4$4$1$0#hh7Nb@3$3@2$2$1$0@4$4$1$0#i3Ne@3$3@2$2$1$0@4$4$1$0#9Nh0@3$3@2$2$1$0@4$4$1$0#5Nh1@3$3@2$2$1$0@4$4$1$0#6Nh1@3$3@2$2$1$0@4$4$1$0#hcNf@3$3@2$2$1$0@4$4$1$0#n4Nd@3$3@2$2$1$0@4$4$1$0#uaNc@3$3@2$2$1$0@4$4$1$0#ur0N8@3$3@2$2$1$0@4$4$1$0#jqs4N6@3$3@2$2$1$0@4$4$1$0#urh4N4@3$3@2$2$1$0@4$4$1$0#htmiaN3@1$5@2$2$1$0").
Lemma asan_hex3b_gallv : ltac2:(zQ "30!in1!v2!ik6@2$1$2$0").
Proof. unfold asan_hex3b_blocks. gallv_vm. Qed.
Lemma asan_hex3b : ltac2:(zQ "30!hme!hrc!ik6@3$1$2@1$0#orkr0@1$0#lvsq8").
Proof. apply (vtree_scan_sound _ asan_hex3b_blocks); [exact asan_hex3b_gallv| vm_compute; reflexivity]. Qed.
