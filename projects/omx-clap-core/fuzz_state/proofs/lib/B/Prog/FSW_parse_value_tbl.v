(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the table pattern of lib/B/FSW_parse_string_tbl.v (itself lane CRT's
   lib/A/FSW_crt_tbl.v pattern) and of image A's lib/A/FSW_parse_value_tbl.v (a working branch
   c4ac4207dc3), for image B's parse_value text range. *)
(* fs program part, READER group, image B (fs.asan-ubsan): the decode table of parse_value's own text (A_parse_value
   0x82fcc, pf.c:277-294), for the walk's symbolic runs (lib/B FSW_K.v fsw_run_AJU / fsw_run_to_AJU / fsw_run_tok_AJU
   and their tactics take `table_ok tfibsegs tbl`). The range is RELOC-B's B/YB1w.v:461 names: tfib_A_parse_value =
   0x82fcc .. tfib_E_parse_value = 0x83598, 1,484 bytes. build_table steps pc + 4 (Reusable/YP02.v), so the count is
   in 32-bit words: 371. MEASURED (capstone 5.0.7, CS_ARCH_RISCV, CS_MODE_RISCV64 | CS_MODE_RISCVC, over the pinned
   fuzz_state.asan-ubsan sha256 5ac5ce0954f87e2d050c481b7b0599cfd55ef554eadc008e51491f44c053d204, file offset =
   vaddr - p_vaddr + p_offset of its PT_LOAD): those 1,484 bytes decode to exactly 371 four-byte instructions, so
   parse_value has no compressed instruction and every instruction it executes is a table entry. Its calls
   (__asan_stack_malloc_0 0x8303c, skip_ws 0x830d0, parse_string 0x831ac, parse_items 0x83278, and the dead ones:
   literal 0x83294, parse_number's fuzz_malloc 0x833c4 / __asan_memcpy 0x8340c, strtod 0x83468, the __asan_report_*
   calls) leave the range; the walk runs each segment up to its call. UBSan trap mode: the one trap site is the
   unimp 0x834e8.
   rule 24: proves no function (kind: segment lemma). *)
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

Definition pv_text_start : Z := tfib_A_parse_value.
Definition pv_text_count : nat := Z.to_nat ((tfib_E_parse_value - tfib_A_parse_value) / 4).
(* the range is a whole number of words, so the table covers it exactly *)
Lemma pv_text_exact : Z.of_nat pv_text_count * 4 = tfib_E_parse_value - tfib_A_parse_value.
Proof. vm_compute. reflexivity. Qed.
Lemma pv_text_count_371 : pv_text_count = 371%nat.
Proof. vm_compute. reflexivity. Qed.

Definition pv_tbl : ctable :=
  Eval vm_compute in (build_table tfibsegs pv_text_start pv_text_count TEmpty).
Lemma pv_tbl_eq : pv_tbl = build_table tfibsegs pv_text_start pv_text_count TEmpty.
Proof. vm_cast_no_check (eq_refl pv_tbl). Qed.
Lemma pv_tbl_ok : table_ok tfibsegs pv_tbl.
Proof. rewrite pv_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
(* the words the listing gives at the entry, the __asan_stack_malloc_0 call 0x8303c, the skip_ws call 0x830d0, the
   parse_string call 0x831ac, the parse_items call 0x83278, the epilogue 0x8329c, the `ret` 0x8333c, the trap
   0x834e8 and the last word 0x83594, and nothing past the range *)
Lemma pv_tbl_probe :
  clookup pv_tbl 0x82fcc = Some 0xf6010113 /\ clookup pv_tbl 0x8303c = Some 0xcb8ba0ef /\
  clookup pv_tbl 0x830d0 = Some 0x4c8000ef /\ clookup pv_tbl 0x831ac = Some 0x388020ef /\
  clookup pv_tbl 0x83278 = Some 0x3f9010ef /\ clookup pv_tbl 0x8329c = Some 0x45e03537 /\
  clookup pv_tbl 0x8333c = Some 0x00008067 /\ clookup pv_tbl 0x834e8 = Some 0xc0001073 /\
  clookup pv_tbl 0x83594 = Some 0x95cd60ef /\ clookup pv_tbl 0x83598 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
