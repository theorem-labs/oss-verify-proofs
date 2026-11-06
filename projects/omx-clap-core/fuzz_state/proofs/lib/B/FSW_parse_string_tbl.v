(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the table pattern of lane CRT's lib/A/FSW_crt_tbl.v (0c8f540c787, itself from
   proofs/omx-clap-core/fuzz_state/lib/A/AB1k.v), for parse_string's text range; lib/B (fs.asan-ubsan) twin of
   lib/A/FSW_parse_string_tbl.v (a Theorem Labs lane). *)
(* fs program part, READER group, image B (fs.asan-ubsan): the decode table of parse_string's own text (A_parse_string
   0x85534, pf.c:117-181), for the walk's symbolic runs (lib/B FSW_K.v fsw_run_AJU / fsw_run_to_AJU and their tok twins
   take `table_ok tfibsegs tbl`). The range is RELOC-B's B/YB1w.v:476 names: tfib_A_parse_string = 0x85534 ..
   tfib_E_parse_string = 0x85b3c, 1,544 bytes. build_table steps pc + 4 (Reusable/YP02.v), so the count is in 32-bit
   words: 386. MEASURED (capstone over the unstripped twin, whose .text bytes in this range equal the pinned
   fs.asan-ubsan's): those 1,544 bytes decode to exactly 386 four-byte instructions,
   so parse_string has no compressed instruction and every instruction it executes is a table entry. Its calls
   (fuzz_malloc 0x85614, hex4 0x856fc and 0x858fc, put_utf8 0x85944, fuzz_free 0x85a18, the __asan_report_* calls;
   no __ubsan_handle_* call is in the range) leave the range; a run stops at the callee's entry, and the call step takes over there.
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

Definition pstr_text_start : Z := tfib_A_parse_string.
Definition pstr_text_count : nat := Z.to_nat ((tfib_E_parse_string - tfib_A_parse_string) / 4).
(* the range is a whole number of words, so the table covers it exactly *)
Lemma pstr_text_exact : Z.of_nat pstr_text_count * 4 = tfib_E_parse_string - tfib_A_parse_string.
Proof. vm_compute. reflexivity. Qed.
Lemma pstr_text_count_386 : pstr_text_count = 386%nat.
Proof. vm_compute. reflexivity. Qed.

Definition parse_string_tbl : ctable :=
  Eval vm_compute in (build_table tfibsegs pstr_text_start pstr_text_count TEmpty).
Lemma parse_string_tbl_eq : parse_string_tbl = build_table tfibsegs pstr_text_start pstr_text_count TEmpty.
Proof. vm_cast_no_check (eq_refl parse_string_tbl). Qed.
Lemma parse_string_tbl_ok : table_ok tfibsegs parse_string_tbl.
Proof. rewrite parse_string_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
(* the first word, the call word (jal fuzz_malloc 0x85614), the ret 0x85a5c, the last word 0x85b38 and nothing past
   the range, as the listing gives them *)
Lemma parse_string_tbl_probe :
  clookup parse_string_tbl 0x85534 = Some 0xf7010113 /\ clookup parse_string_tbl 0x85614 = Some 0xc44fd0ef /\
  clookup parse_string_tbl 0x85a5c = Some 0x00008067 /\ clookup parse_string_tbl 0x85b38 = Some 0xbb9d30ef /\
  clookup parse_string_tbl 0x85b3c = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
