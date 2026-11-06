(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1q.v, with its module paths changed and its addresses moved to libreac/fuzz_knock's ASan build; AB1v's tfibsegs is A/AWalkFw0.v's. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/A/AB1q.v (donor image sha256 61768cf4739b), with its module paths changed and its addresses moved to reac-pw/fuzz_qdisc's ASan build. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AB1q.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from reac-pw/fuzz_qdisc's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AB1q.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.AU Require Import AWalkFw0.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x908d8 7%nat (build_table tfibsegs 0x8f824 9%nat (build_table tfibsegs 0x85110 3%nat (build_table tfibsegs 0x7dbb4 6%nat (build_table tfibsegs 0x7169c 70%nat (build_table tfibsegs 0x71038 90%nat (build_table tfibsegs 0x6a44c 8%nat (build_table tfibsegs 0x5e7c4 93%nat (build_table tfibsegs 0x5c570 18%nat (build_table tfibsegs 0x5a1b4 44%nat (build_table tfibsegs 0x59ff0 8%nat (build_table tfibsegs 0x591bc 14%nat (build_table tfibsegs 0x58578 88%nat (build_table tfibsegs 0x577f0 40%nat (build_table tfibsegs 0x568e0 6%nat (build_table tfibsegs 0x52b3c 16%nat (build_table tfibsegs 0x519c0 324%nat (build_table tfibsegs 0x50b30 205%nat (build_table tfibsegs 0x4516c 31%nat (build_table tfibsegs 0x350c4 1016%nat (build_table tfibsegs 0x338e0 96%nat (build_table tfibsegs 0x30bd4 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x70d94 145%nat (build_table tfibsegs 0x706b4 169%nat (build_table tfibsegs 0x703cc 23%nat (build_table tfibsegs 0x6ebc4 45%nat (build_table tfibsegs 0x6e0b8 150%nat (build_table tfibsegs 0x61af0 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6c2bc 87%nat (build_table tfibsegs 0x6c02c 100%nat (build_table tfibsegs 0x6a07c 75%nat (build_table tfibsegs 0x64718 131%nat (build_table tfibsegs 0x64078 111%nat (build_table tfibsegs 0x63b48 128%nat (build_table tfibsegs 0x63a2c 4%nat (build_table tfibsegs 0x63298 2%nat (build_table tfibsegs 0x6234c 27%nat (build_table tfibsegs 0x5e250 26%nat (build_table tfibsegs 0x5dbb8 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6b810 8%nat (build_table tfibsegs 0x847d4 139%nat (build_table tfibsegs 0x64924 756%nat (build_table tfibsegs 0x61b6c 24%nat (build_table tfibsegs 0x6c2bc 87%nat (build_table tfibsegs 0x6c02c 100%nat (build_table tfibsegs 0x6a07c 75%nat (build_table tfibsegs 0x64718 131%nat (build_table tfibsegs 0x64078 111%nat (build_table tfibsegs 0x63b48 128%nat (build_table tfibsegs 0x63a2c 4%nat (build_table tfibsegs 0x63298 2%nat (build_table tfibsegs 0x6234c 27%nat (build_table tfibsegs 0x5e250 26%nat (build_table tfibsegs 0x5dbb8 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
