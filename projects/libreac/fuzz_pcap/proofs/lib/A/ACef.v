From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/ACef.v, with its module paths changed and its addresses moved to libreac/fuzz_pcap's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v.
From OSSVerify.libreac.fuzz_pcap.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_lib_start : Z := (symaddr Symbols.Asan.s_main).
(* pcap's lib run: from main to the first compiler-rt function __extenddftf2, in words (1821 on v1.9.0). *)
Definition tfib_lib_count : nat := symwords Symbols.Asan.s_main Symbols.Asan.s___extenddftf2.
Definition tfib_memcmp_start : Z := (symaddr Symbols.Asan.s_bcmp).
Definition tfib_memcmp_count : nat := 13.
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
