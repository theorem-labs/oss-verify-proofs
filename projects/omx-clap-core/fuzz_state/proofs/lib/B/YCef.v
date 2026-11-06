(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCef.v, with its module paths changed and its addresses moved to omx-clap-core/fuzz_state's ASan+UBSan build (fuzz_state.asan-ubsan). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v.
From OSSVerify.omx_clap_core.fuzz_state.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_lib_start : Z := 0x80aec.
Definition tfib_lib_count : nat := 5695.
Definition tfib_memcmp_start : Z := 0x98e3c.
Definition tfib_memcmp_count : nat := 64.
Definition tfibtbl_lib : ctable :=
Eval vm_compute in (build_table tfibsegs tfib_memcmp_start tfib_memcmp_count
(build_table tfibsegs tfib_lib_start tfib_lib_count TEmpty)).
Lemma tfibtbl_lib_eq : tfibtbl_lib = build_table tfibsegs tfib_memcmp_start tfib_memcmp_count
(build_table tfibsegs tfib_lib_start tfib_lib_count TEmpty).
Proof. vm_cast_no_check (eq_refl tfibtbl_lib). Qed.
Lemma tfibtbl_lib_ok : table_ok tfibsegs tfibtbl_lib.
Proof.
rewrite tfibtbl_lib_eq. apply build_table_ok; [cbv; discriminate|].
apply build_table_ok0. cbv. discriminate.
Qed.
