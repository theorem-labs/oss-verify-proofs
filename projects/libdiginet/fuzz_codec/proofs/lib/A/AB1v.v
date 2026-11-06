(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1v.v at origin/ossv/recipes c8557374ad2e, with its module paths changed to libdiginet/fuzz_codec's library and every image numeral recomputed from fuzz_codec.asan by the rule the donor's own numeral follows (the rule reproduces cgif's released text on cgif's image: the control). tfibmusl_text_start = sysconf+0 = 0x8c698 and tfibguard_start = oft_exit_guard+0 = 0x807d4 in fuzz_codec.asan's symbol table; the musl count is cgif's rule ((.text end - sysconf)/4 + 3 = (0x9c230 - 0x8c698)/4 + 3 = 16105, which gives cgif's own 16403); the guard count 4 is cgif's. Knock's layout of record (libreac/fuzz_knock lib/A/AB1v.v, origin/ossv/recipes 4b6f0df50aa7): tfibsegs is defined in lib/A/AWalkFw0.v, and this file re-exports it (Require Export AWalkFw0) instead of defining it. *)
(* Read from: fuzz_codec.asan (libdiginet/fuzz_codec asan) sha256 7d470194ffdbde8b30a9810840f8e81d620ba1c555d510c475daeff37548a422; unstripped twin sha256 b28356da1a6547814e3a3c56e2d9e065e4f5b45715ccb5a236942cda3471fe1d *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP02.
From OSSVerify.libdiginet.fuzz_codec.images Require Import Asan.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Export AWalkFw0.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibmusl_text_start : Z := 0x8c698.
Definition tfibmusl_text_count : nat := 16105.
Definition tfibguard_start : Z := 0x807d4.
Definition tfibguard_count : nat := 4.
Definition tfibmusl_tbl : ctable := Eval vm_compute in
(build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty)).
Lemma tfibmusl_tbl_eq : tfibmusl_tbl = build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty).
Proof. vm_cast_no_check (eq_refl tfibmusl_tbl). Qed.
Lemma tfibmusl_tbl_ok : table_ok tfibsegs tfibmusl_tbl.
Proof. rewrite tfibmusl_tbl_eq. apply build_table_ok; [cbv; discriminate|]. apply build_table_ok0. cbv. discriminate. Qed.
