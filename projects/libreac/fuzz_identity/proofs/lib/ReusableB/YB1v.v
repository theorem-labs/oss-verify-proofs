(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10-29: generated for libreac/fuzz_identity image B (fuzz_identity.asan-ubsan baf1a4d065e0): tfibmusl_text_start = sysconf 0x8a4a0 and tfibmusl_text_count = 16105 (= 16102 words from sysconf to the end of .text 0x9a038, + 3, cgif's rule 16400 + 3), tfibguard_start = oft_exit_guard 0x806fc (count 4 as cgif); by symbol from the .debug twin; module paths. The tables are built by vm_compute from the image. *)
(* Modified by Theorem Labs, 2026-10-29: re-emitted at the release's two-image path lib/ReusableB/YB1v.v with the same content as before, only its Require paths mapped to the release layout (lib.B.A* -> lib.ReusableB.Y*, image-specific Reusable modules -> lib.ReusableB). *)
(* tfibguard_count = 4 is the exit walk's FETCH WINDOW at oft_exit_guard 0x806fc: the flag test (auipc / lbu / bnez) and the ret at +0xc, which the exit run takes because the guard flag oft_in_callback 0x5d7914 is 0 at exit (stated in AE23's ex_consts and checked against the exit image by AD1j's ex_consts_chk); it is NOT the guard function's size (0x30, 12 instructions), so do not change it to 12 (cgif's and fuzz_grant's AB1v have 4 too). tfibmusl_text_count = 16105 = 16102 words from sysconf to the end of .text 0x9a038, + 3 (cgif's rule: 16400 + 3). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YP02.
From OSSVerify.libreac.fuzz_identity.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibsegs : list Segment := AsanUbsan.M.loaded_segments.
Definition tfibmusl_text_start : Z := 0x8a4a0.
Definition tfibmusl_text_count : nat := 16105.
Definition tfibguard_start : Z := 0x806fc.
Definition tfibguard_count : nat := 4.
Definition tfibmusl_tbl : ctable := Eval vm_compute in
(build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty)).
Lemma tfibmusl_tbl_eq : tfibmusl_tbl = build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty).
Proof. vm_cast_no_check (eq_refl tfibmusl_tbl). Qed.
Lemma tfibmusl_tbl_ok : table_ok tfibsegs tfibmusl_tbl.
Proof. rewrite tfibmusl_tbl_eq. apply build_table_ok; [cbv; discriminate|]. apply build_table_ok0. cbv. discriminate. Qed.
