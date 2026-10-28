(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec SeqExec StepTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import RefStep.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc RelocBlocks RelocCode RelocImg RelocKit.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require Import R23Code.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23Reloc V23RelocImg.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope bv_scope.

Definition v23_cc23_sites : list cchunk := [mkChunk 3004%positive 0x157c8 1 [Some 0x0004a517%Z]; mkChunk 3004%positive 0x157cc 1 [Some 0xf0450913%Z]; mkChunk 3004%positive 0x157d8 1 [Some 0x1b5100ef%Z]; mkChunk 3004%positive 0x15824 1 [Some 0x3f1100ef%Z]; mkChunk 3004%positive 0x15834 1 [Some 0x159100ef%Z]; mkChunk 3004%positive 0x15874 1 [Some 0x3a11006f%Z]; mkChunk 3004%positive 0x15898 1 [Some 0x0004a517%Z]; mkChunk 3004%positive 0x1589c 1 [Some 0xe3450993%Z]; mkChunk 3004%positive 0x158a8 1 [Some 0x0e5100ef%Z]; mkChunk 3004%positive 0x1591c 1 [Some 0x2f9100ef%Z]; mkChunk 3003%positive 0x135f8 1 [Some 0x000d5517%Z]; mkChunk 3003%positive 0x135fc 1 [Some 0x9ac54503%Z]].
Lemma v23_sites23_ok : code_check (@rl_segs v23_reloc) (@rl_delta v23_reloc) v23_cc23_sites = true.
Proof. vm_refl. Qed.
Lemma S23_157c8 : fetch_word (@rl_segs v23_reloc) (rl (@rl_delta v23_reloc B_E___funcs_on_exit) 0x157c8) = Some (0x0004a517 : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_157c8 : decode_any (0x0004a517 : bv 32) = Some (Auipc 10 74, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_157cc : fetch_word (@rl_segs v23_reloc) (rl (@rl_delta v23_reloc B_E___funcs_on_exit) 0x157cc) = Some (0xf0450913 : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_157cc : decode_any (0xf0450913 : bv 32) = Some (OpImm ALU_ADD 18 10 3844, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_157d8 : fetch_word (@rl_segs v23_reloc) (rl (@rl_delta v23_reloc B_E___funcs_on_exit) 0x157d8) = Some (0x1b5100ef : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_157d8 : decode_any (0x1b5100ef : bv 32) = Some (Jal 1 68020, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_15824 : fetch_word (@rl_segs v23_reloc) (rl (@rl_delta v23_reloc B_E___funcs_on_exit) 0x15824) = Some (0x3f1100ef : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_15824 : decode_any (0x3f1100ef : bv 32) = Some (Jal 1 68592, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_15834 : fetch_word (@rl_segs v23_reloc) (rl (@rl_delta v23_reloc B_E___funcs_on_exit) 0x15834) = Some (0x159100ef : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_15834 : decode_any (0x159100ef : bv 32) = Some (Jal 1 67928, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_15874 : fetch_word (@rl_segs v23_reloc) (rl (@rl_delta v23_reloc B_E___funcs_on_exit) 0x15874) = Some (0x3a11006f : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_15874 : decode_any (0x3a11006f : bv 32) = Some (Jal 0 68512, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_15898 : fetch_word (@rl_segs v23_reloc) (rl (@rl_delta v23_reloc B_E___funcs_on_exit) 0x15898) = Some (0x0004a517 : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_15898 : decode_any (0x0004a517 : bv 32) = Some (Auipc 10 74, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_1589c : fetch_word (@rl_segs v23_reloc) (rl (@rl_delta v23_reloc B_E___funcs_on_exit) 0x1589c) = Some (0xe3450993 : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_1589c : decode_any (0xe3450993 : bv 32) = Some (OpImm ALU_ADD 19 10 3636, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_158a8 : fetch_word (@rl_segs v23_reloc) (rl (@rl_delta v23_reloc B_E___funcs_on_exit) 0x158a8) = Some (0x0e5100ef : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_158a8 : decode_any (0x0e5100ef : bv 32) = Some (Jal 1 67812, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_1591c : fetch_word (@rl_segs v23_reloc) (rl (@rl_delta v23_reloc B_E___funcs_on_exit) 0x1591c) = Some (0x2f9100ef : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_1591c : decode_any (0x2f9100ef : bv 32) = Some (Jal 1 68344, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_135f8 : fetch_word (@rl_segs v23_reloc) (rl (@rl_delta v23_reloc B_E_target_run) 0x135f8) = Some (0x000d5517 : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_135f8 : decode_any (0x000d5517 : bv 32) = Some (Auipc 10 213, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_135fc : fetch_word (@rl_segs v23_reloc) (rl (@rl_delta v23_reloc B_E_target_run) 0x135fc) = Some (0x9ac54503 : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_135fc : decode_any (0x9ac54503 : bv 32) = Some (Load SZ1 false 10 10 2476, 4%Z).
Proof. vm_refl. Qed.

Lemma v23_ax_foe_la : @ax_foe_la_stmt v23_reloc (Z_to_bv 64 0x158314).
Proof. r23_la S23_157c8 DS23_157c8 S23_157cc DS23_157cc. Qed.
Lemma v23_ax_foe_j1 : @ax_foe_j1_stmt v23_reloc.
Proof. r23_jal_link S23_157d8 DS23_157d8. Qed.
Lemma v23_ax_foe_j2 : @ax_foe_j2_stmt v23_reloc.
Proof. r23_jal_link S23_15824 DS23_15824. Qed.
Lemma v23_ax_foe_j3 : @ax_foe_j3_stmt v23_reloc.
Proof. r23_jal_link S23_15834 DS23_15834. Qed.
Lemma v23_ax_foe_j4 : @ax_foe_j4_stmt v23_reloc.
Proof. r23_jal_x0 S23_15874 DS23_15874. Qed.
Lemma v23_ax_at_la : @ax_at_la_stmt v23_reloc (Z_to_bv 64 0x1583e4).
Proof. r23_la S23_15898 DS23_15898 S23_1589c DS23_1589c. Qed.
Lemma v23_ax_at_j1 : @ax_at_j1_stmt v23_reloc.
Proof. r23_jal_link S23_158a8 DS23_158a8. Qed.
Lemma v23_ax_at_j2 : @ax_at_j2_stmt v23_reloc.
Proof. r23_jal_link S23_1591c DS23_1591c. Qed.
Lemma v23_ax_guard_lb : @ax_guard_lb_stmt v23_reloc (Z_to_bv 64 0x138568).
Proof. r23_lb S23_135f8 DS23_135f8 S23_135fc DS23_135fc. Qed.
Lemma v23_r23_code_ok : code_check (@rl_segs v23_reloc) (@rl_delta v23_reloc) r23_code = true.
Proof. vm_refl. Qed.
Lemma v23_ax_statics_lo : (@rl_data_lo v23_reloc v23_data <= 0x2f620 + @rl_delta v23_reloc B_A_2f840)%Z.
Proof. vm_compute; intro H; discriminate H. Qed.
Lemma v23_ax_statics_gap : (0x2f840 + @rl_delta v23_reloc B_A_2f6b0 <= 0x2f620 + @rl_delta v23_reloc B_A_2f840)%Z.
Proof. vm_compute; intro H; discriminate H. Qed.

#[export] Instance v23_r23code : @R23Code v23_reloc v23_data :=
  {| r23_code_ok := v23_r23_code_ok; ax_statics_lo := v23_ax_statics_lo; ax_statics_gap := v23_ax_statics_gap;
     r23_foe_hi := Z_to_bv 64 0x158314; r23_at_hi := Z_to_bv 64 0x1583e4; r23_guard_hi := Z_to_bv 64 0x138568;
     ax_foe_la := v23_ax_foe_la; ax_foe_j1 := v23_ax_foe_j1; ax_foe_j2 := v23_ax_foe_j2; ax_foe_j3 := v23_ax_foe_j3; ax_foe_j4 := v23_ax_foe_j4;
     ax_at_la := v23_ax_at_la; ax_at_j1 := v23_ax_at_j1; ax_at_j2 := v23_ax_at_j2; ax_guard_lb := v23_ax_guard_lb |}.
