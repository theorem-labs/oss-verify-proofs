(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the table pattern of proofs/omx-clap-core/fuzz_state/lib/A/AB1k.v (RELOC's port of
   proofs/cgif/cgif_file_fuzzer/lib/A/AB1k.v), as in lib/A/FSW_pj_free_tbl.v and lib/B/FSW_parse_string_tbl.v, for
   pj_free's text range on image B. *)
(* fs program part, READER lane (a Theorem Labs lane), image B (fs.asan-ubsan): the decode table of pj_free's own text, for the
   walk's symbolic runs (lib/B FSW_K.v fsw_run_AJU / fsw_run_to_AJU and their tok twins take `table_ok tfibsegs tbl`).
   The range is RELOC-B's B/YB1w.v:463 names: tfib_A_pj_free = 0x83674 .. tfib_E_pj_free = 0x83894, 544 bytes.
   build_table steps pc + 4 (Reusable/YP02.v), so the count is in 32-bit words: 136. MEASURED on the listing
   (internal path) (lines 86558-86694): 136 instructions at 0x83674 .. 0x83890,
   each an 8-hex-digit (4-byte) word at a pc 4 past the last, so pj_free has no compressed instruction and every
   instruction it executes is a table entry. Its calls (pj_free 0x83760, fuzz_free 0x837a0 / 0x837d4 / 0x837ec /
   0x83808, __asan_memset 0x83818, the eight __asan_report_load8 calls 0x83860 .. 0x83890) leave the range; a run stops
   at the callee's entry, and the call step takes over there. rule 24: no function proved (a decode table).
   Base: the fs core of a working branch cb01f65c0f3 (image B's YB1v / YB1w names). *)
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

Definition pj_free_text_start : Z := tfib_A_pj_free.
Definition pj_free_text_count : nat := Z.to_nat ((tfib_E_pj_free - tfib_A_pj_free) / 4).
(* the range is a whole number of words, so the table covers it exactly *)
Lemma pj_free_text_exact : Z.of_nat pj_free_text_count * 4 = tfib_E_pj_free - tfib_A_pj_free.
Proof. vm_compute. reflexivity. Qed.
Lemma pj_free_text_count_136 : pj_free_text_count = 136%nat.
Proof. vm_compute. reflexivity. Qed.

Definition pj_free_tbl : ctable := Eval vm_compute in (build_table tfibsegs pj_free_text_start pj_free_text_count TEmpty).
Lemma pj_free_tbl_eq : pj_free_tbl = build_table tfibsegs pj_free_text_start pj_free_text_count TEmpty.
Proof. vm_cast_no_check (eq_refl pj_free_tbl). Qed.
Lemma pj_free_tbl_ok : table_ok tfibsegs pj_free_tbl.
Proof. rewrite pj_free_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
(* the first word, the self call (jal pj_free 0x83760), the first fuzz_free call 0x837a0, the __asan_memset call
   0x83818, the ret 0x83854, the last word 0x83890 and nothing past the range, as the listing gives them *)
Lemma pj_free_tbl_probe :
  clookup pj_free_tbl 0x83674 = Some 0xf8010113 /\ clookup pj_free_tbl 0x83760 = Some 0xf15ff0ef /\
  clookup pj_free_tbl 0x837a0 = Some 0xe1cff0ef /\ clookup pj_free_tbl 0x83818 = Some 0xa15ce0ef /\
  clookup pj_free_tbl 0x83854 = Some 0x00008067 /\ clookup pj_free_tbl 0x83890 = Some 0xb41d50ef /\
  clookup pj_free_tbl 0x83894 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
