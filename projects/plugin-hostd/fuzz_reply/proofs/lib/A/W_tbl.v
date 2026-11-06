(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the code table of fuzz_reply.asan's program text, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACef.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP02.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition frsegs : list Segment := Asan.M.loaded_segments.
Definition fr_prog_start : Z := 0x822ec.
Definition fr_prog_count : nat := 4042.
Definition frtbl_prog : ctable :=
Eval vm_compute in (build_table frsegs fr_prog_start fr_prog_count TEmpty).
Lemma frtbl_prog_eq : frtbl_prog = build_table frsegs fr_prog_start fr_prog_count TEmpty.
Proof. vm_cast_no_check (eq_refl frtbl_prog). Qed.
Lemma frtbl_prog_ok : table_ok frsegs frtbl_prog.
Proof. rewrite frtbl_prog_eq. apply build_table_ok0. cbv. discriminate. Qed.
