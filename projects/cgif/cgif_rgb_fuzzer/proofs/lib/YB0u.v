(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ03 YB0z.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tratbl_rtA_build : ctable := build_table trasegs 0x9d138 7%nat (build_table trasegs 0x9c084 9%nat (build_table trasegs 0x914f4 3%nat (build_table trasegs 0x804cc 6%nat (build_table trasegs 0x73fb4 70%nat (build_table trasegs 0x73950 90%nat (build_table trasegs 0x6cd64 8%nat (build_table trasegs 0x610dc 93%nat (build_table trasegs 0x5ee88 18%nat (build_table trasegs 0x5cacc 44%nat (build_table trasegs 0x5c908 8%nat (build_table trasegs 0x5bad4 14%nat (build_table trasegs 0x5ae90 88%nat (build_table trasegs 0x5a108 40%nat (build_table trasegs 0x591f8 6%nat (build_table trasegs 0x55454 16%nat (build_table trasegs 0x542d8 324%nat (build_table trasegs 0x53100 206%nat (build_table trasegs 0x46a48 31%nat (build_table trasegs 0x35fbc 1016%nat (build_table trasegs 0x347d8 96%nat (build_table trasegs 0x318c0 633%nat TEmpty))))))))))))))))))))).
Definition tratbl_rtA : ctable := Eval vm_compute in tratbl_rtA_build.
Lemma tratbl_rtA_eq : tratbl_rtA = tratbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable tratbl_rtA). Qed.
Lemma tratbl_rtA_ok : table_ok trasegs tratbl_rtA.
Proof. rewrite tratbl_rtA_eq. unfold tratbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tratbl_rtB_build : ctable := build_table trasegs 0x736ac 145%nat (build_table trasegs 0x72fcc 169%nat (build_table trasegs 0x72ce4 23%nat (build_table trasegs 0x714dc 45%nat (build_table trasegs 0x709d0 150%nat (build_table trasegs 0x64408 9%nat TEmpty))))).
Definition tratbl_rtB : ctable := Eval vm_compute in tratbl_rtB_build.
Lemma tratbl_rtB_eq : tratbl_rtB = tratbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable tratbl_rtB). Qed.
Lemma tratbl_rtB_ok : table_ok trasegs tratbl_rtB.
Proof. rewrite tratbl_rtB_eq. unfold tratbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tratbl_rtC_build : ctable := build_table trasegs 0x6ebd4 87%nat (build_table trasegs 0x6e944 100%nat (build_table trasegs 0x6c994 75%nat (build_table trasegs 0x67030 131%nat (build_table trasegs 0x66990 111%nat (build_table trasegs 0x66460 128%nat (build_table trasegs 0x66344 4%nat (build_table trasegs 0x65bb0 2%nat (build_table trasegs 0x64c64 27%nat (build_table trasegs 0x60b68 26%nat (build_table trasegs 0x604d0 93%nat TEmpty)))))))))).
Definition tratbl_rtC : ctable := Eval vm_compute in tratbl_rtC_build.
Lemma tratbl_rtC_eq : tratbl_rtC = tratbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable tratbl_rtC). Qed.
Lemma tratbl_rtC_ok : table_ok trasegs tratbl_rtC.
Proof. rewrite tratbl_rtC_eq. unfold tratbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition tratbl_rtD_build : ctable := build_table trasegs 0x6e128 8%nat (build_table trasegs 0x90bb8 139%nat (build_table trasegs 0x6723c 756%nat (build_table trasegs 0x64484 24%nat (build_table trasegs 0x6ebd4 87%nat (build_table trasegs 0x6e944 100%nat (build_table trasegs 0x6c994 75%nat (build_table trasegs 0x67030 131%nat (build_table trasegs 0x66990 111%nat (build_table trasegs 0x66460 128%nat (build_table trasegs 0x66344 4%nat (build_table trasegs 0x65bb0 2%nat (build_table trasegs 0x64c64 27%nat (build_table trasegs 0x60b68 26%nat (build_table trasegs 0x604d0 93%nat (tratbl_rtA))))))))))))))).
Definition tratbl_rtD : ctable := Eval vm_compute in tratbl_rtD_build.
Lemma tratbl_rtD_eq : tratbl_rtD = tratbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable tratbl_rtD). Qed.
Lemma tratbl_rtD_ok : table_ok trasegs tratbl_rtD.
Proof. rewrite tratbl_rtD_eq. unfold tratbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact tratbl_rtA_ok. Qed.
