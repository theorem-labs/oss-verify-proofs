(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated from proofs/cgif/cgif_file_fuzzer/lib/YB1v.v (commit 25e3d17bdb50) by boxb1.py (sha256 0fe1e96732e2) from libdiginet/fuzz_codec's asan-ubsan image: tfibmusl_text_start = sysconf+0 = 0x8cfd0, count (.text end 0x9cb68 - 0x8cfd0)/4 + 3 = 16105 (cgif's rule, its own 16403), tfibguard_start = oft_exit_guard+0 = 0x80924, count 4 (cgif's); module paths changed; tfibsegs is lib/AU/AWalkFw0.v's (Require Export, libreac/fuzz_knock's lib/AU/YB1v.v form). *)
(* Read from: fuzz_codec.asan-ubsan (the libdiginet/fuzz_codec asan-ubsan pin) sha256 73109e32e77beff294d41ae6f16d607479ad1884485781b322645e6f8afa99c3; unstripped twin sha256 43feeaa314a42fe569b4443c710a74561e9077e617f7412cc54fbf4a6557b266 *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP02.
From OSSVerify.libdiginet.fuzz_codec.images Require Import AsanUbsan.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Export AWalkFw0.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibmusl_text_start : Z := 0x8cfd0.
Definition tfibmusl_text_count : nat := 16105.
Definition tfibguard_start : Z := 0x80924.
Definition tfibguard_count : nat := 4.
Definition tfibmusl_tbl : ctable := Eval vm_compute in
(build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty)).
Lemma tfibmusl_tbl_eq : tfibmusl_tbl = build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty).
Proof. vm_cast_no_check (eq_refl tfibmusl_tbl). Qed.
Lemma tfibmusl_tbl_ok : table_ok tfibsegs tfibmusl_tbl.
Proof. rewrite tfibmusl_tbl_eq. apply build_table_ok; [cbv; discriminate|]. apply build_table_ok0. cbv. discriminate. Qed.
