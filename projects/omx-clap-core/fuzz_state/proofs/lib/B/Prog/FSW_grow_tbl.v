(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/Prog/FSW_grow_tbl.v (a working branch
   f9ccbd8f565, a Theorem Labs lane), at B's range. *)
(* fs program part, READER group, image B (fs.asan-ubsan): the decode table of grow's own text (A_grow 0x83ca8, pf.c:42-63),
   for the walk's symbolic runs (lib/B FSW_K.v fsw_run_AJU / fsw_run_tok_AJU and their run-to twins take
   `table_ok tfibsegs tbl`). The range is RELOC-B's B/YB1w.v:467 names: tfib_A_grow = 0x83ca8 .. tfib_E_grow = 0x83e58,
   432 bytes. build_table steps pc + 4 (Reusable/YP02.v), so the count is in 32-bit words: 108. MEASURED (capstone 5.0.7,
   CS_MODE_RISCV64 | CS_MODE_RISCVC, over the pinned fuzz_state.asan-ubsan sha256 5ac5ce0954f8..., PT_LOAD vaddr 0x30d20 at
   file offset 0x1fd20, so 0x83ca8 is file offset 0x72ca8: `python3 gdis.py fuzz_state.asan-ubsan 0x83ca8 0x83e58`, the
   script reading the PT_LOAD bytes and decoding with capstone): those 432 bytes decode to exactly 108 four-byte
   instructions, so grow has no compressed instruction and every instruction it executes is a table entry. Its calls
   (fuzz_realloc 0x83d64 and 0x83db4, the __asan_report_* calls 0x83e20 .. 0x83e54) leave the range; a run stops at the
   callee's entry, and the call step takes over there. Its one UBSan trap is the unimp 0x83e10.
   rule 24: proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1a YK1e.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w FSH_Base.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Open Scope Z_scope.

(* the YB1w range, in instructions *)
Definition grow_ninsn : nat := Z.to_nat ((tfib_E_grow - tfib_A_grow) / 4).
Lemma grow_range : A_grow = tfib_A_grow /\ tfib_E_grow - tfib_A_grow = 432 /\ grow_ninsn = 108%nat.
Proof. split; [|split]; reflexivity. Qed.

Definition grow_tbl : ctable := Eval vm_compute in build_table tfibsegs tfib_A_grow grow_ninsn TEmpty.
Lemma grow_tbl_eq : grow_tbl = build_table tfibsegs tfib_A_grow grow_ninsn TEmpty.
Proof. vm_cast_no_check (eq_refl grow_tbl). Qed.
Lemma grow_tbl_ok : table_ok tfibsegs grow_tbl.
Proof. rewrite grow_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
(* the entry word, the two UBSan guards (0x83cd8 beqz a0 / 0x83ce4 bnez s8 -> unimp 0x83e10), the two call words
   (jal fuzz_realloc 0x83d64 / 0x83db4), the ret 0x83e0c, the trap 0x83e10, the last word 0x83e54 and nothing past
   the range, as the listing gives them *)
Lemma grow_tbl_probe :
  clookup grow_tbl 0x83ca8 = Some 0xfa010113 /\ clookup grow_tbl 0x83cd8 = Some 0x12050c63 /\
  clookup grow_tbl 0x83ce4 = Some 0x120c1663 /\ clookup grow_tbl 0x83d64 = Some 0xe61fe0ef /\
  clookup grow_tbl 0x83db4 = Some 0xe11fe0ef /\ clookup grow_tbl 0x83e0c = Some 0x00008067 /\
  clookup grow_tbl 0x83e10 = Some 0xc0001073 /\ clookup grow_tbl 0x83e54 = Some 0x89dd50ef /\
  clookup grow_tbl 0x83e58 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
