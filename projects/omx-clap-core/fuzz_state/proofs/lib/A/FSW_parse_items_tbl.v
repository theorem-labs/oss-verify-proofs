(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* A Theorem Labs lane / a Theorem Labs lane; built on S0 946ad86dc9f and re-targeted on the CTX-free statements
   (a working branch faa7e2570e5). This file takes no spec, so the CTX drop does not touch it. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/omx-clap-core/fuzz_state/lib/A/FSW_crt_tbl.v (lane CRT,
   a working branch 0c8f540c787), keeping only its table pattern, for parse_items' text range. *)
(* fs program part, READER lane (a Theorem Labs lane, walk of parse_items): the decode table of parse_items' own text, for the
   walk's symbolic runs (FSW_K.v fsw_run_AJU / fsw_run_to_AJU / fsw_run_tok_AJU take `table_ok tfibsegs tbl`). The
   range is RELOC's AB1w.v names: tfib_A_parse_items = 0x84a04 .. tfib_E_parse_items = 0x850b8, 1,716 bytes (nm:
   st_size 0x6b4). build_table steps pc + 4 (Reusable/YP02.v:19-22), so the count is in 32-bit words: 429. MEASURED on
   the pinned fs.asan (sha256 64b53ff86172bb07f93f146e67b81a0354bca88e0a580e93fb1da01406fb76e0; objdump of its .debug
   twin 7c4afaee248b): those 1,716 bytes are exactly 429 four-byte instructions, no compressed instruction, so every
   instruction parse_items executes is a table entry. Its calls (grow, parse_string, __asan_memset, parse_value,
   fuzz_free and the __asan_report_* traps) leave the range; the walk runs each segment up to its call, and the call
   step takes over there. *)
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

Definition pitems_text_start : Z := tfib_A_parse_items.
Definition pitems_text_count : nat := Z.to_nat ((tfib_E_parse_items - tfib_A_parse_items) / 4).
(* the range is a whole number of words, so the table covers it exactly *)
Lemma pitems_text_exact : Z.of_nat pitems_text_count * 4 = tfib_E_parse_items - tfib_A_parse_items.
Proof. vm_compute. reflexivity. Qed.
Lemma pitems_text_count_eq : pitems_text_count = 429%nat.
Proof. vm_compute. reflexivity. Qed.

Definition pitems_tbl : ctable := Eval vm_compute in (build_table tfibsegs pitems_text_start pitems_text_count TEmpty).
Lemma pitems_tbl_eq : pitems_tbl = build_table tfibsegs pitems_text_start pitems_text_count TEmpty.
Proof. vm_cast_no_check (eq_refl pitems_tbl). Qed.
Lemma pitems_tbl_ok : table_ok tfibsegs pitems_tbl.
Proof. rewrite pitems_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
