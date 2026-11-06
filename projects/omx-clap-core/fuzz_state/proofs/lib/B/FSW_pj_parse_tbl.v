(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the table pattern of lane CRT's lib/A/FSW_crt_tbl.v (0c8f540c787, itself from
   proofs/omx-clap-core/fuzz_state/lib/A/AB1k.v), for pj_parse's text range; lib/B (fs.asan-ubsan) twin of
   lib/A/FSW_pj_parse_tbl.v (a working branch 7583bdfb8e8). *)
(* fs program part, READER group, image B (fs.asan-ubsan): the decode table of pj_parse's own text (A_pj_parse 0x82f3c,
   pf.c:296-309), for the walk's symbolic runs (lib/B FSW_K.v fsw_run_AJU / fsw_run_to_AJU take `table_ok tfibsegs
   tbl`). The range is RELOC-B's B/YB1w.v:460 names: tfib_A_pj_parse = 0x82f3c .. tfib_E_pj_parse = 0x82fcc, 144 bytes.
   build_table steps pc + 4 (Reusable/YP02.v), so the count is in 32-bit words: 36. MEASURED on
   (internal path) (objdump of the pinned fs.asan-ubsan): 0x82f3c .. 0x82fc8
   are 36 instructions, each a 4-byte word (eight hex digits, no compressed instruction), the last the UBSan trap
   `unimp` 0x82fc8; so every instruction pj_parse executes is a table entry. Its calls (__asan_memset 0x82f7c,
   parse_value 0x82f88, skip_ws 0x82f94, pj_free 0x82fa8) leave the range; a run stops at the callee's entry, and the
   call step takes over there. rule 24: proves no function (kind: segment lemma). *)
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

Definition pj_parse_text_start : Z := tfib_A_pj_parse.
Definition pj_parse_text_count : nat := Z.to_nat ((tfib_E_pj_parse - tfib_A_pj_parse) / 4).
(* the range is a whole number of words, so the table covers it exactly *)
Lemma pj_parse_text_exact : Z.of_nat pj_parse_text_count * 4 = tfib_E_pj_parse - tfib_A_pj_parse.
Proof. vm_compute. reflexivity. Qed.
Lemma pj_parse_text_count_36 : pj_parse_text_count = 36%nat.
Proof. vm_compute. reflexivity. Qed.

Definition pj_parse_tbl : ctable :=
  Eval vm_compute in (build_table tfibsegs pj_parse_text_start pj_parse_text_count TEmpty).
Lemma pj_parse_tbl_eq : pj_parse_tbl = build_table tfibsegs pj_parse_text_start pj_parse_text_count TEmpty.
Proof. vm_cast_no_check (eq_refl pj_parse_tbl). Qed.
Lemma pj_parse_tbl_ok : table_ok tfibsegs pj_parse_tbl.
Proof. rewrite pj_parse_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
(* the first word, the three call words (jal __asan_memset 0x82f7c, jal parse_value 0x82f88, jal skip_ws 0x82f94),
   the ret 0x82fbc, the trap word 0x82fc8 and nothing past the range, as the listing gives them *)
Lemma pj_parse_tbl_probe :
  clookup pj_parse_tbl 0x82f3c = Some 0xfd010113 /\ clookup pj_parse_tbl 0x82f7c = Some 0xab0cf0ef /\
  clookup pj_parse_tbl 0x82f88 = Some 0x044000ef /\ clookup pj_parse_tbl 0x82f94 = Some 0x604000ef /\
  clookup pj_parse_tbl 0x82fbc = Some 0x00008067 /\ clookup pj_parse_tbl 0x82fc8 = Some 0xc0001073 /\
  clookup pj_parse_tbl 0x82fcc = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
