(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_parse_items_tbl.v,
   in the form of lib/B/Prog/FSW_grow_tbl.v; every image
   value is read from image B: the range is B/YB1w.v:475 (tfib_A_parse_items = 0x84e70 .. tfib_E_parse_items =
   0x85534), A_parse_items is B/FSH_Base.v:70. *)
(* fs program part, READER group, image B (fs.asan-ubsan): the decode table of parse_items' own text (A_parse_items
   0x84e70, pf.c:211-264), for the walk's symbolic runs (lib/B FSW_K.v fsw_run_AJU / fsw_run_tok_AJU and their run-to
   twins take `table_ok tfibsegs tbl`). The range [0x84e70, 0x85534) is 1,732 bytes; build_table steps pc + 4
   (Reusable/YP02.v), so the count is in 32-bit words: 433. MEASURED (capstone over the unstripped twin of image B,
   (internal path) sha256 b1566a1ca816...; nm: parse_items st_value 0x84e70, st_size 1732): those 1,732 bytes
   decode to exactly 433 four-byte instructions, so parse_items has no compressed instruction and every instruction it
   executes is a table entry. Its calls leave the range: skip_ws 0x83598 (0x84f58, 0x84ffc, 0x850b8, 0x851f0), grow
   0x83ca8 (0x84fac, 0x8524c), parse_string 0x85534 (0x85044), __asan_memset 0x5222c (0x8516c), parse_value 0x82fcc
   (0x851cc), fuzz_free 0x82dbc (0x85368, dead) and the 38 __asan_report_* calls / the UBSan trap of
   report-sites-B.tsv rows 166-203 (0x85278 .. 0x85530; the one trap is the unimp 0x853d8). A run stops at the
   callee's entry, and the call step takes over there.
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
Definition pitems_ninsn : nat := Z.to_nat ((tfib_E_parse_items - tfib_A_parse_items) / 4).
Lemma pitems_range : A_parse_items = tfib_A_parse_items /\ tfib_E_parse_items - tfib_A_parse_items = 1732 /\
  pitems_ninsn = 433%nat.
Proof. split; [|split]; reflexivity. Qed.

Definition pitems_tbl : ctable := Eval vm_compute in build_table tfibsegs tfib_A_parse_items pitems_ninsn TEmpty.
Lemma pitems_tbl_eq : pitems_tbl = build_table tfibsegs tfib_A_parse_items pitems_ninsn TEmpty.
Proof. vm_cast_no_check (eq_refl pitems_tbl). Qed.
Lemma pitems_tbl_ok : table_ok tfibsegs pitems_tbl.
Proof. rewrite pitems_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
(* the entry word (addi sp, sp, -0x90), the ten call words of the brief's table (skip_ws x4, grow x2, parse_string,
   __asan_memset, parse_value, fuzz_free), the ret 0x852fc, the UBSan trap 0x853d8 (unimp), the last word 0x85530
   (jal __asan_report_store8) and nothing past the range, as image B's bytes give them (MEASURED, elfx over the
   unstripped twin) *)
Lemma pitems_tbl_probe :
  clookup pitems_tbl 0x84e70 = Some 0xf7010113 /\
  clookup pitems_tbl 0x84f58 = Some 0xe40fe0ef /\ clookup pitems_tbl 0x84fac = Some 0xcfdfe0ef /\
  clookup pitems_tbl 0x84ffc = Some 0xd9cfe0ef /\ clookup pitems_tbl 0x85044 = Some 0x4f0000ef /\
  clookup pitems_tbl 0x850b8 = Some 0xce0fe0ef /\ clookup pitems_tbl 0x8516c = Some 0x8c0cd0ef /\
  clookup pitems_tbl 0x851cc = Some 0xe01fd0ef /\ clookup pitems_tbl 0x851f0 = Some 0xba8fe0ef /\
  clookup pitems_tbl 0x8524c = Some 0xa5dfe0ef /\ clookup pitems_tbl 0x85368 = Some 0xa55fd0ef /\
  clookup pitems_tbl 0x852fc = Some 0x00008067 /\ clookup pitems_tbl 0x853d8 = Some 0xc0001073 /\
  clookup pitems_tbl 0x85530 = Some 0x9c0d40ef /\ clookup pitems_tbl 0x85534 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.
