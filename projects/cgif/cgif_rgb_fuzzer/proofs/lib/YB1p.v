(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ03 YB1u.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition trbtbl_rtA_build : ctable := build_table trbsegs 0x9e224 7%nat (build_table trbsegs 0x9d170 9%nat (build_table trbsegs 0x92540 3%nat (build_table trbsegs 0x80790 6%nat (build_table trbsegs 0x74278 70%nat (build_table trbsegs 0x73c14 90%nat (build_table trbsegs 0x6d028 8%nat (build_table trbsegs 0x613a0 93%nat (build_table trbsegs 0x5f14c 18%nat (build_table trbsegs 0x5cd90 44%nat (build_table trbsegs 0x5cbcc 8%nat (build_table trbsegs 0x5bd98 14%nat (build_table trbsegs 0x5b154 88%nat (build_table trbsegs 0x5a3cc 40%nat (build_table trbsegs 0x594bc 6%nat (build_table trbsegs 0x55718 16%nat (build_table trbsegs 0x5459c 324%nat (build_table trbsegs 0x533c4 206%nat (build_table trbsegs 0x46d0c 31%nat (build_table trbsegs 0x3610c 1016%nat (build_table trbsegs 0x34928 96%nat (build_table trbsegs 0x31a10 633%nat TEmpty))))))))))))))))))))).
Definition trbtbl_rtA : ctable := Eval vm_compute in trbtbl_rtA_build.
Lemma trbtbl_rtA_eq : trbtbl_rtA = trbtbl_rtA_build.
Proof. vm_cast_no_check (@eq_refl ctable trbtbl_rtA). Qed.
Lemma trbtbl_rtA_ok : table_ok trbsegs trbtbl_rtA.
Proof. rewrite trbtbl_rtA_eq. unfold trbtbl_rtA_build. do 21 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition trbtbl_rtB_build : ctable := build_table trbsegs 0x73970 145%nat (build_table trbsegs 0x73290 169%nat (build_table trbsegs 0x72fa8 23%nat (build_table trbsegs 0x717a0 45%nat (build_table trbsegs 0x70c94 150%nat (build_table trbsegs 0x646cc 9%nat TEmpty))))).
Definition trbtbl_rtB : ctable := Eval vm_compute in trbtbl_rtB_build.
Lemma trbtbl_rtB_eq : trbtbl_rtB = trbtbl_rtB_build.
Proof. vm_cast_no_check (@eq_refl ctable trbtbl_rtB). Qed.
Lemma trbtbl_rtB_ok : table_ok trbsegs trbtbl_rtB.
Proof. rewrite trbtbl_rtB_eq. unfold trbtbl_rtB_build. do 5 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition trbtbl_rtC_build : ctable := build_table trbsegs 0x6ee98 87%nat (build_table trbsegs 0x6ec08 100%nat (build_table trbsegs 0x6cc58 75%nat (build_table trbsegs 0x672f4 131%nat (build_table trbsegs 0x66c54 111%nat (build_table trbsegs 0x66724 128%nat (build_table trbsegs 0x66608 4%nat (build_table trbsegs 0x65e74 2%nat (build_table trbsegs 0x64f28 27%nat (build_table trbsegs 0x60e2c 26%nat (build_table trbsegs 0x60794 93%nat TEmpty)))))))))).
Definition trbtbl_rtC : ctable := Eval vm_compute in trbtbl_rtC_build.
Lemma trbtbl_rtC_eq : trbtbl_rtC = trbtbl_rtC_build.
Proof. vm_cast_no_check (@eq_refl ctable trbtbl_rtC). Qed.
Lemma trbtbl_rtC_ok : table_ok trbsegs trbtbl_rtC.
Proof. rewrite trbtbl_rtC_eq. unfold trbtbl_rtC_build. do 10 (apply build_table_ok; [cbv; discriminate|]). apply build_table_ok0. cbv. discriminate. Qed.
Definition trbtbl_rtD_build : ctable := build_table trbsegs 0x6e3ec 8%nat (build_table trbsegs 0x91c04 139%nat (build_table trbsegs 0x67500 756%nat (build_table trbsegs 0x64748 24%nat (build_table trbsegs 0x6ee98 87%nat (build_table trbsegs 0x6ec08 100%nat (build_table trbsegs 0x6cc58 75%nat (build_table trbsegs 0x672f4 131%nat (build_table trbsegs 0x66c54 111%nat (build_table trbsegs 0x66724 128%nat (build_table trbsegs 0x66608 4%nat (build_table trbsegs 0x65e74 2%nat (build_table trbsegs 0x64f28 27%nat (build_table trbsegs 0x60e2c 26%nat (build_table trbsegs 0x60794 93%nat (trbtbl_rtA))))))))))))))).
Definition trbtbl_rtD : ctable := Eval vm_compute in trbtbl_rtD_build.
Lemma trbtbl_rtD_eq : trbtbl_rtD = trbtbl_rtD_build.
Proof. vm_cast_no_check (@eq_refl ctable trbtbl_rtD). Qed.
Lemma trbtbl_rtD_ok : table_ok trbsegs trbtbl_rtD.
Proof. rewrite trbtbl_rtD_eq. unfold trbtbl_rtD_build. do 15 (apply build_table_ok; [cbv; discriminate|]). exact trbtbl_rtA_ok. Qed.
