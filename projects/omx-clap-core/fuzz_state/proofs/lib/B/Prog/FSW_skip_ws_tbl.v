(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the table pattern of lib/B/FSW_parse_string_tbl.v (itself lane CRT's
   lib/A/FSW_crt_tbl.v pattern), for skip_ws's text range. *)
(* fs program part, READER group, image B (fs.asan-ubsan): the decode table of skip_ws's own text (A_skip_ws 0x83598,
   pf.c:36-40, out of line in B only), for the walk's symbolic runs (lib/B FSW_K.v fsw_run_tok_AJU /
   fsw_run_to_tok_AJU and their tactics take `table_ok tfibsegs tbl`). The range is RELOC-B's B/YB1w.v:462 names:
   tfib_A_skip_ws = 0x83598 .. tfib_E_skip_ws = 0x83674, 220 bytes. build_table steps pc + 4 (Reusable/YP02.v), so
   the count is in 32-bit words: 55. MEASURED (capstone 5.0.7, CS_ARCH_RISCV, CS_MODE_RISCV64 | CS_MODE_RISCVC, over
   the pinned fuzz_state.asan-ubsan sha256 5ac5ce0954f8..., file offset = vaddr - p_vaddr + p_offset of its PT_LOAD):
   those 220 bytes decode to exactly 55 four-byte instructions, so skip_ws has no compressed instruction and every
   instruction it executes is a table entry. Its only calls are the __asan_report_* calls 0x83650, 0x83664, 0x83668,
   0x83670 (all unreached under skip_ws_spec's premises); no __ubsan_handle_* call is in the range (UBSan trap mode:
   the one trap site is the unimp 0x83660).
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

Definition skw_text_start : Z := tfib_A_skip_ws.
Definition skw_text_count : nat := Z.to_nat ((tfib_E_skip_ws - tfib_A_skip_ws) / 4).
(* the range is a whole number of words, so the table covers it exactly *)
Lemma skw_text_exact : Z.of_nat skw_text_count * 4 = tfib_E_skip_ws - tfib_A_skip_ws.
Proof. vm_compute. reflexivity. Qed.
Lemma skw_text_count_55 : skw_text_count = 55%nat.
Proof. vm_compute. reflexivity. Qed.

Definition skip_ws_tbl : ctable :=
  Eval vm_compute in (build_table tfibsegs skw_text_start skw_text_count TEmpty).
Lemma skip_ws_tbl_eq : skip_ws_tbl = build_table tfibsegs skw_text_start skw_text_count TEmpty.
Proof. vm_cast_no_check (eq_refl skip_ws_tbl). Qed.
Lemma skip_ws_tbl_ok : table_ok tfibsegs skip_ws_tbl.
Proof. rewrite skip_ws_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
(* the words the listing gives at the entry, the loop head 0x835fc, the in->p store 0x83638, the exit 0x83654, the
   `ret` 0x8365c, the trap 0x83660 and the last word 0x83670, and nothing past the range *)
Lemma skip_ws_tbl_probe :
  clookup skip_ws_tbl 0x83598 = Some 0xff010113 /\ clookup skip_ws_tbl 0x835fc = Some 0x06078263 /\
  clookup skip_ws_tbl 0x83638 = Some 0x00f53023 /\ clookup skip_ws_tbl 0x83654 = Some 0x00813083 /\
  clookup skip_ws_tbl 0x8365c = Some 0x00008067 /\ clookup skip_ws_tbl 0x83660 = Some 0xc0001073 /\
  clookup skip_ws_tbl 0x83670 = Some 0xd61d50ef /\ clookup skip_ws_tbl 0x83674 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
