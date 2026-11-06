(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/omx-clap-core/fuzz_state/lib/A/AB1k.v (RELOC's port of
   proofs/cgif/cgif_file_fuzzer/lib/A/AB1k.v), keeping only its table pattern (lane CRT's FSW_crt_tbl.v), for
   parse_value's text range. *)
(* fs program part, READER lane: the decode table of parse_value's own text (A 0x82f9c), for the walk's symbolic runs
   (FSW_K.v fsw_run_AJU / fsw_run_to_AJU / fsw_run_tok_AJU take `table_ok tfibsegs tbl`). The range is RELOC's AB1w.v
   names: tfib_A_parse_value = 0x82f9c .. tfib_E_parse_value = 0x83570, 1,492 bytes. build_table steps pc + 4
   (Reusable/YP02.v:19-22), so the count is in 32-bit words: 373. MEASURED on the pinned fs.asan (sha256
   64b53ff86172bb07f93f146e67b81a0354bca88e0a580e93fb1da01406fb76e0, capstone 5.0.7, RISCV64 + C): those 1,492 bytes
   decode to exactly 373 instructions, every one 4 bytes, so parse_value has no compressed instruction and every
   instruction it executes is a table entry. Its calls (__asan_stack_malloc_0 0x8300c, parse_string 0x831cc,
   parse_items 0x832f4, and the dead ones) leave the range; the walk runs each segment up to its call. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1a YK1e.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1w.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope Z_scope.

Definition pv_text_start : Z := tfib_A_parse_value.
Definition pv_text_count : nat := Z.to_nat ((tfib_E_parse_value - tfib_A_parse_value) / 4).
(* the range is a whole number of words (373), so the table covers it exactly *)
Lemma pv_text_exact : Z.of_nat pv_text_count * 4 = tfib_E_parse_value - tfib_A_parse_value.
Proof. vm_compute. reflexivity. Qed.
Lemma pv_text_count_val : pv_text_count = 373%nat.
Proof. vm_compute. reflexivity. Qed.

Definition pv_tbl : ctable := Eval vm_compute in (build_table tfibsegs pv_text_start pv_text_count TEmpty).
Lemma pv_tbl_eq : pv_tbl = build_table tfibsegs pv_text_start pv_text_count TEmpty.
Proof. vm_cast_no_check (eq_refl pv_tbl). Qed.
Lemma pv_tbl_ok : table_ok tfibsegs pv_tbl.
Proof. rewrite pv_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
