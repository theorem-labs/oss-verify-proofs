(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB1t.v, with its module paths changed and its addresses moved to omx-clap-core/fuzz_state's ASan+UBSan build (fuzz_state.asan-ubsan). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibtbl_rtF_build : ctable := build_table tfibsegs 0x64464 24%nat (build_table tfibsegs 0x5e964 84%nat (build_table tfibsegs 0x360f8 323%nat (build_table tfibsegs 0x31c28 184%nat (tfibtbl_rtA)))).
Definition tfibtbl_rtF : ctable := Eval vm_compute in tfibtbl_rtF_build.
Lemma tfibtbl_rtF_eq : tfibtbl_rtF = tfibtbl_rtF_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtF). Qed.
Lemma tfibtbl_rtF_ok : table_ok tfibsegs tfibtbl_rtF.
Proof. rewrite tfibtbl_rtF_eq. unfold tfibtbl_rtF_build. do 4 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtA_ok. Qed.
Definition tfibtbl_rtG_build : ctable := build_table tfibsegs 0x34fa0 123%nat (build_table tfibsegs 0x33b78 1194%nat (tfibtbl_rtF)).
Definition tfibtbl_rtG : ctable := Eval vm_compute in tfibtbl_rtG_build.
Lemma tfibtbl_rtG_eq : tfibtbl_rtG = tfibtbl_rtG_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtG). Qed.
Lemma tfibtbl_rtG_ok : table_ok tfibsegs tfibtbl_rtG.
Proof. rewrite tfibtbl_rtG_eq. unfold tfibtbl_rtG_build. do 2 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtF_ok. Qed.
Definition tfibtbl_rtK_build : ctable := build_table tfibsegs 0x664b4 26%nat (tfibtbl_rtG).
Definition tfibtbl_rtK : ctable := Eval vm_compute in tfibtbl_rtK_build.
Lemma tfibtbl_rtK_eq : tfibtbl_rtK = tfibtbl_rtK_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtK). Qed.
Lemma tfibtbl_rtK_ok : table_ok tfibsegs tfibtbl_rtK.
Proof. rewrite tfibtbl_rtK_eq. unfold tfibtbl_rtK_build. do 1 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtG_ok. Qed.
Definition tfibtbl_rtM_build : ctable := build_table tfibsegs 0x60b8c 9%nat (build_table tfibsegs 0x64c44 30%nat (build_table tfibsegs 0x6e064 41%nat (build_table tfibsegs 0x52dec 50%nat (tfibtbl_rtK)))).
Definition tfibtbl_rtM : ctable := Eval vm_compute in tfibtbl_rtM_build.
Lemma tfibtbl_rtM_eq : tfibtbl_rtM = tfibtbl_rtM_build.
Proof. vm_cast_no_check (@eq_refl ctable tfibtbl_rtM). Qed.
Lemma tfibtbl_rtM_ok : table_ok tfibsegs tfibtbl_rtM.
Proof. rewrite tfibtbl_rtM_eq. unfold tfibtbl_rtM_build. do 4 (apply build_table_ok; [cbv; discriminate|]). exact tfibtbl_rtK_ok. Qed.
