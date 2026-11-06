(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the table pattern of lane CRT's lib/A/FSW_crt_tbl.v (0c8f540c787, itself from
   proofs/omx-clap-core/fuzz_state/lib/A/AB1k.v), for parse_string's text range. *)
(* fs program part, READER group: the decode table of parse_string's own text (A_parse_string 0x850b8, pf.c:117-181), for
   the walk's symbolic runs (FSW_K.v fsw_run_AJU / fsw_run_to_AJU and their tok twins take `table_ok tfibsegs tbl`).
   The range is RELOC's A/AB1w.v:474 names: tfib_A_parse_string = 0x850b8 .. tfib_E_parse_string = 0x856cc, 1,556 bytes.
   build_table steps pc + 4 (Reusable/YP02.v), so the count is in 32-bit words: 389. MEASURED (capstone over the
   unstripped twin, same loadable bytes as the pinned fs.asan): those 1,556 bytes
   decode to exactly 389 four-byte instructions, so parse_string has no compressed instruction and every instruction it
   executes is a table entry. Its calls (fuzz_malloc 0x85180, hex4 0x85494, put_utf8 0x854cc, fuzz_free 0x855b8, the
   __asan_report_* calls) leave the range; a run stops at the callee's entry, and the call step takes over there.
   rule 24: no function proved here. *)
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

Definition pstr_text_start : Z := tfib_A_parse_string.
Definition pstr_text_count : nat := Z.to_nat ((tfib_E_parse_string - tfib_A_parse_string) / 4).
(* the range is a whole number of words, so the table covers it exactly *)
Lemma pstr_text_exact : Z.of_nat pstr_text_count * 4 = tfib_E_parse_string - tfib_A_parse_string.
Proof. vm_compute. reflexivity. Qed.
Lemma pstr_text_count_389 : pstr_text_count = 389%nat.
Proof. vm_compute. reflexivity. Qed.

Definition parse_string_tbl : ctable :=
  Eval vm_compute in (build_table tfibsegs pstr_text_start pstr_text_count TEmpty).
Lemma parse_string_tbl_eq : parse_string_tbl = build_table tfibsegs pstr_text_start pstr_text_count TEmpty.
Proof. vm_cast_no_check (eq_refl parse_string_tbl). Qed.
Lemma parse_string_tbl_ok : table_ok tfibsegs parse_string_tbl.
Proof. rewrite parse_string_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
(* the first word (addi sp, sp, -0x90), the call words (jal fuzz_malloc 0x85180, ret 0x855fc), the last word
   (jal __asan_report_store8 0x856c8) and nothing past the range, as the listing gives them *)
Lemma parse_string_tbl_probe :
  clookup parse_string_tbl 0x850b8 = Some 0xf7010113 /\ clookup parse_string_tbl 0x85180 = Some 0xf2cfd0ef /\
  clookup parse_string_tbl 0x855fc = Some 0x00008067 /\ clookup parse_string_tbl 0x856c8 = Some 0xfb9d30ef /\
  clookup parse_string_tbl 0x856cc = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
