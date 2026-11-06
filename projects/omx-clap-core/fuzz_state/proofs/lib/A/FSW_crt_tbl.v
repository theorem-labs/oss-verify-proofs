(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/omx-clap-core/fuzz_state/lib/A/AB1k.v (RELOC's port of
   proofs/cgif/cgif_file_fuzzer/lib/A/AB1k.v), keeping only its table pattern, for check_round_trip's text range. *)
(* fs program part, lane CRT: the decode table of check_round_trip's own text, for the walk's symbolic runs
   (FSW_K.v fsw_run_AJU / fsw_run_to_AJU take `table_ok tfibsegs tbl`). The range is RELOC's AB1w.v names:
   tfib_A_check_round_trip = 0x81a9c .. tfib_E_check_round_trip = 0x82508, 2,668 bytes. build_table steps pc + 4
   (Reusable/YP02.v:19-22), so the count is in 32-bit words: 667. MEASURED on the pinned fs.asan: those 2,668 bytes
   decode to exactly 667 instructions (capstone, RISCV64 + C), so check_round_trip has no compressed instruction and
   every instruction it executes is a table entry. Its calls leave the range; the walk runs each segment up to its
   call, and the call step takes over there. *)
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

Definition crt_text_start : Z := tfib_A_check_round_trip.
Definition crt_text_count : nat := Z.to_nat ((tfib_E_check_round_trip - tfib_A_check_round_trip) / 4).
(* the range is a whole number of words, so the table covers it exactly *)
Lemma crt_text_exact : Z.of_nat crt_text_count * 4 = tfib_E_check_round_trip - tfib_A_check_round_trip.
Proof. vm_compute. reflexivity. Qed.

Definition crt_tbl : ctable := Eval vm_compute in (build_table tfibsegs crt_text_start crt_text_count TEmpty).
Lemma crt_tbl_eq : crt_tbl = build_table tfibsegs crt_text_start crt_text_count TEmpty.
Proof. vm_cast_no_check (eq_refl crt_tbl). Qed.
Lemma crt_tbl_ok : table_ok tfibsegs crt_tbl.
Proof. rewrite crt_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.
