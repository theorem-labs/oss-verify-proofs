(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/A/AB1v.v (donor image sha256 61768cf4739b), with its module paths changed and its addresses moved to reac-pw/fuzz_pin's ASan build. *)
(* Ported to libreac/fuzz_knock by h-rw-kno-5 from proofs/cgif/cgif_file_fuzzer/lib/A/AB1v.v at c8557374ad2: module paths renamed; image values re-derived from fuzz_knock.asan (sha256 61768cf4..), as listed in the commit message. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AB1v.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from reac-pw/fuzz_pin's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AB1v.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP02.
From OSSVerify.reac_pw.fuzz_pin.images Require Import AsanUbsan.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Export AWalkFw0.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibmusl_text_start : Z := 0x86ec0.
Definition tfibmusl_text_count : nat := 16196.
Definition tfibguard_start : Z := 0x8063c.
Definition tfibguard_count : nat := 4.
Definition tfibmusl_tbl : ctable := Eval vm_compute in
(build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty)).
Lemma tfibmusl_tbl_eq : tfibmusl_tbl = build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty).
Proof. vm_cast_no_check (eq_refl tfibmusl_tbl). Qed.
Lemma tfibmusl_tbl_ok : table_ok tfibsegs tfibmusl_tbl.
Proof. rewrite tfibmusl_tbl_eq. apply build_table_ok; [cbv; discriminate|]. apply build_table_ok0. cbv. discriminate. Qed.
