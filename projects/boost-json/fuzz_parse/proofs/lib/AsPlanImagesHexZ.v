(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Top0Gc4. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanHexTree.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat04prod37Corelib7Numbers7BinNumsi98positive04cons04pair03nil69OSSVerify6Proofsaboost_jsonafuzz_parse3libh0AsPlanImagesHexZ~~~~~~leeasan_ia_blocks69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsanHexTree~~~~~~r34gall59OSSVerifyaboost_jsonafuzz_parse6images4Asan~~~~~~v8h2Asan_seg_bytes_003i94Nposr33zptlefasan_tab_blocks" s.
Unset Lia Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition asan_ia_blocks : ltac2:(zQ "40!h8!he!i3!k2@1$0@2$2$3$1") := ltac2:(zQ "60!he!k2!i3!kd!l3!l9@3$3@2$2$1$0@4$4$1$0#hk9N7@3$3@2$2$1$0@4$4$1$0#q5N8@3$3@2$2$1$0@4$4$1$0#l3N9@3$3@2$2$1$0@4$4$1$0#h5Nb@3$3@2$2$1$0@4$4$1$0#bNc@3$3@2$2$1$0@4$4$1$0#3Ne@3$3@2$2$1$0@4$4$1$0#1Nh0@3$3@2$2$1$0@4$4$1$0#1Nh1@3$3@2$2$1$0@4$4$1$0#1Nh2@3$3@2$2$1$0@4$4$1$0#h0Nf@3$3@2$2$1$0@4$4$1$0#k4Nd@3$3@2$2$1$0@4$4$1$0#oaNc@3$3@2$2$1$0@4$4$1$0#iicNa@3$3@2$2$1$0@4$4$1$0#hhm8N7@3$3@2$2$1$0@4$4$1$0#klq4N5@3$3@2$2$1$0@4$4$1$0#orkaN4@1$5@2$2$1$0").
Lemma asan_ia_gall : ltac2:(zQ "30!q2!v1!hib@2$1$2$0").
Proof. unfold asan_ia_blocks. gall_vm. Qed.   (* [comment removed for export] *)
Lemma asan_ia_zero : ltac2:(zQ "30!hk1!hk8!hib@3$1$2@1$0#qko0@1$0#ohgj0").
Proof. apply (ztree_scan_sound _ asan_ia_blocks); [exact asan_ia_gall| vm_compute; reflexivity]. Qed.

(* [comment removed for export] *)
Definition asan_tab_blocks : ltac2:(zQ "40!h8!he!i3!k2@1$0@2$2$3$1") := ltac2:(zQ "60!he!k2!i3!kd!l3!l9@3$3@2$2$1$0@4$4$1$0#htmibN3@3$3@2$2$1$0@4$4$1$0#nlobN5@3$3@2$2$1$0@4$4$1$0#htm3N7@3$3@2$2$1$0@4$4$1$0#nl9N9@3$3@2$2$1$0@4$4$1$0#jqdNa@3$3@2$2$1$0@4$4$1$0#ht7Nb@3$3@2$2$1$0@4$4$1$0#jbNe@3$3@2$2$1$0@4$4$1$0#fNh0@3$3@2$2$1$0@4$4$1$0#1Nh4@3$3@2$2$1$0@4$4$1$0#1Nh5@3$3@2$2$1$0@4$4$1$0#8Nh3@3$3@2$2$1$0@4$4$1$0#h2Nh2@3$3@2$2$1$0@4$4$1$0#i6Nh1@3$3@2$2$1$0@4$4$1$0#pcNf@3$3@2$2$1$0@4$4$1$0#in4Nd@3$3@2$2$1$0@4$4$1$0#kuaNc@3$3@2$2$1$0@4$4$1$0#kur0N8@3$3@2$2$1$0@4$4$1$0#hjqs4N6@3$3@2$2$1$0@4$4$1$0#kurh4N4@3$3@2$2$1$0@4$4$1$0#ptmiaN3@1$5@2$2$1$0").
Lemma asan_tab_gall : ltac2:(zQ "30!hke!v1!hib@2$1$2$0").
Proof. unfold asan_tab_blocks. gall_vm. Qed.   (* [comment removed for export] *)
Lemma asan_tab_zero : ltac2:(zQ "30!hk1!hk8!hib@3$1$2@1$0#urhl8@1$0#kgggg0").
Proof. apply (ztree_scan_sound _ asan_tab_blocks); [exact asan_tab_gall| vm_compute; reflexivity]. Qed.
