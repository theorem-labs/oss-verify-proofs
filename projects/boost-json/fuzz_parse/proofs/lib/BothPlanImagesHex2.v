(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanHexTree.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat04prod37Corelib7Numbers7BinNumsi98positive04cons04pair03nil69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsanHexTree~~~~~~le5gallv69OSSVerify6Proofsaboost_jsonafuzz_parse3libh2BothPlanImagesHex2~~~~~~q4h1asan_hex3c_blocks59OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan~~~~~~vfh7AsanUbsan_seg_bytes_003i94Nposle3vpt" s.
Unset Lia Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition asan_hex3c_blocks : ltac2:(zQ "40!h8!he!i3!k2@1$0@2$2$3$1") := ltac2:(zQ "60!he!k2!i3!kd!l3!l9@3$3@2$2$1$0@4$4$1$0#ptmgbN3@3$3@2$2$1$0@4$4$1$0#inlo3N5@3$3@2$2$1$0@4$4$1$0#ptm1N7@3$3@2$2$1$0@4$4$1$0#kur1N8@3$3@2$2$1$0@4$4$1$0#inl9N9@3$3@2$2$1$0@4$4$1$0#hjqdNa@3$3@2$2$1$0@4$4$1$0#pt7Nb@3$3@2$2$1$0@4$4$1$0#hjbNe@3$3@2$2$1$0@4$4$1$0#kfNh0@3$3@2$2$1$0@4$4$1$0#i8Nh1@3$3@2$2$1$0@4$4$1$0#l2Nh0@3$3@2$2$1$0@4$4$1$0#q6Nf@3$3@2$2$1$0@4$4$1$0#hkeNe@3$3@2$2$1$0@4$4$1$0#ipeNd@3$3@2$2$1$0@4$4$1$0#ljeNc@1$5@2$2$1$0").
Lemma asan_hex3c_gallv : ltac2:(zQ "30!pc!ua!hj7@2$0$2$1").
Proof. unfold asan_hex3c_blocks. gallv_vm. Qed.
Lemma asan_hex3c : ltac2:(zQ "30!hl2!hl9!hj7@3$1$2@1$0#kurgl8@1$0#ljvq8").
Proof. apply (vtree_scan_sound _ asan_hex3c_blocks); [exact asan_hex3c_gallv| vm_compute; reflexivity]. Qed.
