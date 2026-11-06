(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1v.v, with its module paths changed; its address literals moved to omx-clap-core/fuzz_preset's ASan build where h-mani-a2's maps/reloc-cgif-preset.A.tsv maps them; the literals it does not map are still cgif_file_fuzzer.asan's (listed in the commit that moved them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP02.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition tfibsegs : list Segment := Asan.M.loaded_segments.
Definition tfibmusl_text_start : Z := 0x8e69c.
Definition tfibmusl_text_count : nat := 18644.
Definition tfibguard_start : Z := 0x81568.
Definition tfibguard_count : nat := 4.
Definition tfibmusl_tbl : ctable := Eval vm_compute in
(build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty)).
Lemma tfibmusl_tbl_eq : tfibmusl_tbl = build_table tfibsegs tfibguard_start tfibguard_count (build_table tfibsegs tfibmusl_text_start tfibmusl_text_count TEmpty).
Proof. vm_cast_no_check (eq_refl tfibmusl_tbl). Qed.
Lemma tfibmusl_tbl_ok : table_ok tfibsegs tfibmusl_tbl.
Proof. rewrite tfibmusl_tbl_eq. apply build_table_ok; [cbv; discriminate|]. apply build_table_ok0. cbv. discriminate. Qed.
