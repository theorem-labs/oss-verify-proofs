(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AB1q.v, with its module paths changed and its addresses moved to libreac/fuzz_knock's ASan build; AB1v's tfibsegs is A/AWalkFw0.v's. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/libreac/fuzz_knock/proofs/lib/A/AB1q.v (donor image sha256 61768cf4739b), with its module paths changed and its addresses moved to libdiginet/fuzz_codec's ASan build. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AB1q.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from libdiginet/fuzz_codec's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AB1q.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtA_build : ctable := build_table tfibsegs 0x990d8 7%nat (build_table tfibsegs 0x98024 9%nat (build_table tfibsegs 0x8d90c 3%nat (build_table tfibsegs 0x7febc 6%nat (build_table tfibsegs 0x739a4 70%nat (build_table tfibsegs 0x73340 90%nat (build_table tfibsegs 0x6c754 8%nat (build_table tfibsegs 0x60acc 93%nat (build_table tfibsegs 0x5e878 18%nat (build_table tfibsegs 0x5c4bc 44%nat (build_table tfibsegs 0x5c2f8 8%nat (build_table tfibsegs 0x5b4c4 14%nat (build_table tfibsegs 0x5a880 88%nat (build_table tfibsegs 0x59af8 40%nat (build_table tfibsegs 0x58be8 6%nat (build_table tfibsegs 0x54e44 16%nat (build_table tfibsegs 0x53cc8 324%nat (build_table tfibsegs 0x52e38 205%nat (build_table tfibsegs 0x46d98 31%nat (build_table tfibsegs 0x3635c 1016%nat (build_table tfibsegs 0x34b78 96%nat (build_table tfibsegs 0x31e6c 633%nat TEmpty))))))))))))))))))))).
Definition tfibtbl_rtA : ctable := Eval vm_compute in tfibtbl_rtA_build.
Lemma tfibtbl_rtA_eq : tfibtbl_rtA = tfibtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtA). Qed.
Lemma tfibtbl_rtA_ok : table_ok tfibsegs tfibtbl_rtA.
Proof. rewrite tfibtbl_rtA_eq. unfold tfibtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtB_build : ctable := build_table tfibsegs 0x7309c 145%nat (build_table tfibsegs 0x729bc 169%nat (build_table tfibsegs 0x726d4 23%nat (build_table tfibsegs 0x70ecc 45%nat (build_table tfibsegs 0x703c0 150%nat (build_table tfibsegs 0x63df8 9%nat TEmpty))))).
Definition tfibtbl_rtB : ctable := Eval vm_compute in tfibtbl_rtB_build.
Lemma tfibtbl_rtB_eq : tfibtbl_rtB = tfibtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtB). Qed.
Lemma tfibtbl_rtB_ok : table_ok tfibsegs tfibtbl_rtB.
Proof. rewrite tfibtbl_rtB_eq. unfold tfibtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtC_build : ctable := build_table tfibsegs 0x6e5c4 87%nat (build_table tfibsegs 0x6e334 100%nat (build_table tfibsegs 0x6c384 75%nat (build_table tfibsegs 0x66a20 131%nat (build_table tfibsegs 0x66380 111%nat (build_table tfibsegs 0x65e50 128%nat (build_table tfibsegs 0x65d34 4%nat (build_table tfibsegs 0x655a0 2%nat (build_table tfibsegs 0x64654 27%nat (build_table tfibsegs 0x60558 26%nat (build_table tfibsegs 0x5fec0 93%nat TEmpty)))))))))).
Definition tfibtbl_rtC : ctable := Eval vm_compute in tfibtbl_rtC_build.
Lemma tfibtbl_rtC_eq : tfibtbl_rtC = tfibtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtC). Qed.
Lemma tfibtbl_rtC_ok : table_ok tfibsegs tfibtbl_rtC.
Proof. rewrite tfibtbl_rtC_eq. unfold tfibtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tfibtbl_rtD_build : ctable := build_table tfibsegs 0x6db18 8%nat (build_table tfibsegs 0x8cfd0 139%nat (build_table tfibsegs 0x66c2c 756%nat (build_table tfibsegs 0x63e74 24%nat (build_table tfibsegs 0x6e5c4 87%nat (build_table tfibsegs 0x6e334 100%nat (build_table tfibsegs 0x6c384 75%nat (build_table tfibsegs 0x66a20 131%nat (build_table tfibsegs 0x66380 111%nat (build_table tfibsegs 0x65e50 128%nat (build_table tfibsegs 0x65d34 4%nat (build_table tfibsegs 0x655a0 2%nat (build_table tfibsegs 0x64654 27%nat (build_table tfibsegs 0x60558 26%nat (build_table tfibsegs 0x5fec0 93%nat (tfibtbl_rtA))))))))))))))).
Definition tfibtbl_rtD : ctable := Eval vm_compute in tfibtbl_rtD_build.
Lemma tfibtbl_rtD_eq : tfibtbl_rtD = tfibtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtD). Qed.
Lemma tfibtbl_rtD_ok : table_ok tfibsegs tfibtbl_rtD.
Proof. rewrite tfibtbl_rtD_eq. unfold tfibtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
