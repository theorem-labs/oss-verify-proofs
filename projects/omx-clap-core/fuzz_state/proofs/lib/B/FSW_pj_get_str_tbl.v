(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the table pattern of proofs/omx-clap-core/fuzz_state/lib/A/AB1k.v (RELOC's port of
   proofs/cgif/cgif_file_fuzzer/lib/A/AB1k.v), as in lane CRT's FSW_crt_tbl.v and the image-A twin
   lib/A/FSW_pj_get_str_tbl.v (a working branch b3097a2a998), for pj_get_str's text range in IMAGE B. *)
(* fs program part, READER lane (a Theorem Labs lane), image B (fs.asan-ubsan, sha256 5ac5ce0954f8...): the decode table of
   pj_get_str's own text, for the walk's symbolic runs (lib/B/FSW_K.v fsw_run_AJU / fsw_run_to_AJU take
   `table_ok tfibsegs tbl`). The range is lib/B/YB1w.v's names: tfib_A_pj_get_str = 0x83a54 .. tfib_E_pj_get_str =
   0x83adc, 136 bytes. build_table steps pc + 4 (Reusable/YP02.v:19-22), so the count is in 32-bit words: 34. MEASURED
   on the pinned fs.asan-ubsan (listing (internal path)):
   pj_get_str has 34 instructions, every one 4 bytes (objdump word widths), so it has no compressed instruction and
   every instruction it executes is a table entry. Its calls (pj_get 0x83a6c, __asan_report_load4 0x83ad4,
   __asan_report_load8 0x83ad8) leave the range; the walk runs each segment up to its call, and the call step takes over
   there. Image-closure content rule: this file names only image B's segments and addresses. rule 24: no function
   proved (a decode table). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1a YK1e.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope Z_scope.

Definition pj_get_str_text_start : Z := tfib_A_pj_get_str.
Definition pj_get_str_text_count : nat := Z.to_nat ((tfib_E_pj_get_str - tfib_A_pj_get_str) / 4).
(* the range is a whole number of words, so the table covers it exactly *)
Lemma pj_get_str_text_exact : Z.of_nat pj_get_str_text_count * 4 = tfib_E_pj_get_str - tfib_A_pj_get_str.
Proof. vm_compute. reflexivity. Qed.
Lemma pj_get_str_text_count_34 : pj_get_str_text_count = 34%nat.
Proof. vm_compute. reflexivity. Qed.

Definition pj_get_str_tbl : ctable := Eval vm_compute in (build_table tfibsegs pj_get_str_text_start pj_get_str_text_count TEmpty).
Lemma pj_get_str_tbl_eq : pj_get_str_tbl = build_table tfibsegs pj_get_str_text_start pj_get_str_text_count TEmpty.
Proof. vm_cast_no_check (eq_refl pj_get_str_tbl). Qed.
Lemma pj_get_str_tbl_ok : table_ok tfibsegs pj_get_str_tbl.
Proof. rewrite pj_get_str_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
