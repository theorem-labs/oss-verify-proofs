(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ03.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition trasegs : list Segment := Asan.M.loaded_segments.
Definition tramusl_text_start : Z := 0x90bb8.
Definition tramusl_text_count : nat := 16388.
Definition traguard_start : Z := 0x80f34.
Definition traguard_count : nat := 4.
Definition tramusl_tbl : ctable := Eval vm_compute in
(build_table trasegs traguard_start traguard_count (build_table trasegs tramusl_text_start tramusl_text_count TEmpty)).
Lemma tramusl_tbl_eq : tramusl_tbl = build_table trasegs traguard_start traguard_count (build_table trasegs tramusl_text_start tramusl_text_count TEmpty).
Proof. vm_cast_no_check (eq_refl tramusl_tbl). Qed.
Lemma tramusl_tbl_ok : table_ok trasegs tramusl_tbl.
Proof. rewrite tramusl_tbl_eq. apply build_table_ok; [cbv; discriminate|]. apply build_table_ok0. cbv. discriminate. Qed.
