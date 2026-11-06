(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the table pattern of proofs/omx-clap-core/fuzz_state/lib/A/AB1k.v (RELOC's port of
   proofs/cgif/cgif_file_fuzzer/lib/A/AB1k.v), as in lane CRT's FSW_crt_tbl.v and READER's FSW_pj_object_tbl.v, for
   pj_parse's text range. *)
(* fs program part, READER lane (a Theorem Labs lane): the decode table of pj_parse's own text, for the walk's
   symbolic runs (FSW_K.v fsw_run_AJU / fsw_run_to_AJU / fsw_run_tok_AJU take `table_ok tfibsegs tbl`). The range is
   RELOC's AB1w.v names: tfib_A_pj_parse = 0x82eac .. tfib_E_pj_parse = 0x82f9c, 240 bytes. build_table steps pc + 4
   (Reusable/YP02.v:19-22), so the count is in 32-bit words: 60. MEASURED on the pinned fs.asan (sha256 64b53ff86172bb07...;
   (internal path) over the unstripped twin, PT_LOAD bytes identical): pj_parse has st_size 240 and 60 instructions,
   every one 4 bytes (no compressed instruction, ELF RVC flag clear), so every instruction it executes is a table entry.
   Its calls (__asan_memset 0x82ee8, parse_value 0x82ef4, __asan_report_load1 0x82f60, pj_free 0x82f78) leave the range;
   the walk runs each segment up to its call, and the call step takes over there. rule 24: no function proved (a decode
   table). *)
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

Definition pj_parse_text_start : Z := tfib_A_pj_parse.
Definition pj_parse_text_count : nat := Z.to_nat ((tfib_E_pj_parse - tfib_A_pj_parse) / 4).
(* the range is a whole number of words, so the table covers it exactly *)
Lemma pj_parse_text_exact : Z.of_nat pj_parse_text_count * 4 = tfib_E_pj_parse - tfib_A_pj_parse.
Proof. vm_compute. reflexivity. Qed.
Lemma pj_parse_text_count_60 : pj_parse_text_count = 60%nat.
Proof. vm_compute. reflexivity. Qed.

Definition pj_parse_tbl : ctable := Eval vm_compute in (build_table tfibsegs pj_parse_text_start pj_parse_text_count TEmpty).
Lemma pj_parse_tbl_eq : pj_parse_tbl = build_table tfibsegs pj_parse_text_start pj_parse_text_count TEmpty.
Proof. vm_cast_no_check (eq_refl pj_parse_tbl). Qed.
Lemma pj_parse_tbl_ok : table_ok tfibsegs pj_parse_tbl.
Proof. rewrite pj_parse_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
