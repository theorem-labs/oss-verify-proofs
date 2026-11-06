(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/ACef.v at c8557374ad2e, with its module paths changed (AB1v's tfibsegs is A/AWalkFw0.v's) and its two code ranges relocated to libreac/fuzz_knock's asan image (sha256 61768cf4739b...). Range 1: cgif (0x7fff0, 6907) = main .. __extenddftf2 (the program part: driver, harness, library, __wrap_getenv/getpid); knock's is main 0x7ea30 .. __extenddftf2 0x7f6cc = 807 instructions (knock symtab). Range 2: cgif (0x97194, 13) = the 1-instruction thunk at 0x97194 (REAL(bcmp), `j 0x41900`) and the first 12 instructions of musl memchr 0x97198; knock has no such thunk (no bcmp in its image), and knock's musl memchr 0x8f80c has the same first 48 bytes (and the same 204), so knock's range is (0x8f80c, 12). Range 2's cells, tfib_memcmp_start / tfib_memcmp_count in cgif, are renamed tfib_memchr_start / tfib_memchr_count, after the code at 0x8f850 (musl memchr in this file's asan-ubsan image, YB1w.v:519). *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/ACef.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from libreac/fuzz_knock's asan image to its asan-ubsan image. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import AWalkFw0.
From OSSVerify.libreac.fuzz_knock.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_lib_start : Z := 0x7ea30.
(* main 0x7ea30 .. __extenddftf2 0x7f710 holds 824 instructions in fuzz_knock.asan-ubsan (knock symtab; the asan build
   has 807 in 0x7ea30 .. 0x7f6cc, and main keeps its address while __extenddftf2 moves +0x44). *)
Definition tfib_lib_count : nat := 824.
Definition tfib_memchr_start : Z := 0x8f850.
Definition tfib_memchr_count : nat := 12.
Definition tfibtbl_lib : ctable :=
Eval vm_compute in (build_table tfibsegs tfib_memchr_start tfib_memchr_count
(build_table tfibsegs tfib_lib_start tfib_lib_count TEmpty)).
Lemma tfibtbl_lib_eq : tfibtbl_lib = build_table tfibsegs tfib_memchr_start tfib_memchr_count
(build_table tfibsegs tfib_lib_start tfib_lib_count TEmpty).
Proof. vm_cast_no_check (eq_refl tfibtbl_lib). Qed.
Lemma tfibtbl_lib_ok : table_ok tfibsegs tfibtbl_lib.
Proof.
rewrite tfibtbl_lib_eq. apply build_table_ok; [cbv; discriminate|].
apply build_table_ok0. cbv. discriminate.
Qed.
