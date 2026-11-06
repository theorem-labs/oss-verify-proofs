(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/ACef.v at c8557374ad2e, with its module paths changed (AB1v's tfibsegs is A/AWalkFw0.v's) and its two code ranges relocated to libreac/fuzz_knock's asan image (sha256 61768cf4739b...). Range 1: cgif (0x7fff0, 6907) = main .. __extenddftf2 (the program part: driver, harness, library, __wrap_getenv/getpid); knock's is main 0x7ea30 .. __extenddftf2 0x7f6cc = 807 instructions (knock symtab). Range 2: cgif (0x97194, 13) = the 1-instruction thunk at 0x97194 (REAL(bcmp), `j 0x41900`) and the first 12 instructions of musl memchr 0x97198; knock has no such thunk (no bcmp in its image), and knock's musl memchr 0x8f80c has the same first 48 bytes (and the same 204), so knock's range is (0x8f80c, 12). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/A/ACef.v (donor image sha256 61768cf4739b), with its module paths changed and its addresses moved to reac-pw/fuzz_rate's ASan build. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/ACef.v at 4e3a0a9ad299, derived by derive_y.py: addresses moved from reac-pw/fuzz_rate's asan image (image A) to its asan-ubsan image (image B), the image module Asan -> AsanUbsan; the Modified-by lines above describe how lib/A/ACef.v was made and quote that file's image-A values; the code below carries image B's values. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import AWalkFw0.
From OSSVerify.reac_pw.fuzz_rate.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfib_lib_start : Z := 0x802cc.
(* main 0x802cc .. __extenddftf2 0x84e64 holds 4838 4-byte words in fuzz_rate.asan-ubsan (its symtab; the asan build
   has 4666 in 0x80274 .. 0x84b5c: main moves +0x58, __extenddftf2 +0x308, and pod_write_ent 0x83cc4 (776 bytes) is a
   separate function of this range in the asan-ubsan build only). *)
Definition tfib_lib_count : nat := 4838.
Definition tfib_memcmp_start : Z := 0x95160.
Definition tfib_memcmp_count : nat := 12.
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
