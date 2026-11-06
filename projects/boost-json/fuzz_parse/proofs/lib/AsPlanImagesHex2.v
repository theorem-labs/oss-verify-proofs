(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Top0Gc4. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanHexTree.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat04prod37Corelib7Numbers7BinNumsi98positive04cons04pair03nil69OSSVerify6Proofsaboost_jsonafuzz_parse3libh0AsPlanImagesHex2~~~~~~leh1asan_hex3c_blocks69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsanHexTree~~~~~~r75gallv59OSSVerifyaboost_jsonafuzz_parse6images4Asan~~~~~~vdh2Asan_seg_bytes_003i94Nposr73vpt" s.
Unset Lia Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition asan_hex3c_blocks : ltac2:(zQ "40!h8!he!i3!k2@1$0@2$2$3$1") := ltac2:(zQ "60!he!k2!i3!kd!l3!l9@3$3@2$2$1$0@4$4$1$0#ptmibN3@3$3@2$2$1$0@4$4$1$0#inlobN5@3$3@2$2$1$0@4$4$1$0#ptm3N7@3$3@2$2$1$0@4$4$1$0#inl9N9@3$3@2$2$1$0@4$4$1$0#hjqdNa@3$3@2$2$1$0@4$4$1$0#pt7Nb@3$3@2$2$1$0@4$4$1$0#hjbNe@3$3@2$2$1$0@4$4$1$0#kfNh0@3$3@2$2$1$0@4$4$1$0#i8Nh1@3$3@2$2$1$0@4$4$1$0#l2Nh0@3$3@2$2$1$0@4$4$1$0#q6Nf@3$3@2$2$1$0@4$4$1$0#hkeNe@3$3@2$2$1$0@4$4$1$0#ipeNd@3$3@2$2$1$0@4$4$1$0#ljeNc@1$5@2$2$1$0").
Lemma asan_hex3c_gallv : ltac2:(zQ "30!q2!v5!hj0@2$1$2$0").
Proof. unfold asan_hex3c_blocks. gallv_vm. Qed.
Lemma asan_hex3c : ltac2:(zQ "30!hk6!hkd!hj0@3$1$2@1$0#kurhl8@1$0#ljuq8").
Proof. apply (vtree_scan_sound _ asan_hex3c_blocks); [exact asan_hex3c_gallv| vm_compute; reflexivity]. Qed.
