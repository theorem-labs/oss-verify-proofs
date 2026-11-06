(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec SeqExec StepTac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import RefStep.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc RelocBlocks RelocCode RelocImg RelocKit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require Import R23Code.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2Reloc O2RelocImg.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope bv_scope.

Definition o2_cc23_sites : list cchunk := [mkChunk 3004%positive 0x157c8 1 [Some 0x0003a517%Z]; mkChunk 3004%positive 0x157cc 1 [Some 0x57850913%Z]; mkChunk 3004%positive 0x157d8 1 [Some 0x511070ef%Z]; mkChunk 3004%positive 0x15824 1 [Some 0x74d070ef%Z]; mkChunk 3004%positive 0x15834 1 [Some 0x4b5070ef%Z]; mkChunk 3004%positive 0x15874 1 [Some 0x6fd0706f%Z]; mkChunk 3004%positive 0x15898 1 [Some 0x0003a517%Z]; mkChunk 3004%positive 0x1589c 1 [Some 0x4a850993%Z]; mkChunk 3004%positive 0x158a8 1 [Some 0x441070ef%Z]; mkChunk 3004%positive 0x1591c 1 [Some 0x655070ef%Z]; mkChunk 3003%positive 0x135f8 1 [Some 0x00032517%Z]; mkChunk 3003%positive 0x135fc 1 [Some 0xd0454503%Z]].
Lemma o2_sites23_ok : code_check (@rl_segs o2_reloc) (@rl_delta o2_reloc) o2_cc23_sites = true.
Proof. vm_refl. Qed.
Lemma S23_157c8 : fetch_word (@rl_segs o2_reloc) (rl (@rl_delta o2_reloc B_E___funcs_on_exit) 0x157c8) = Some (0x0003a517 : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_157c8 : decode_any (0x0003a517 : bv 32) = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_157cc : fetch_word (@rl_segs o2_reloc) (rl (@rl_delta o2_reloc B_E___funcs_on_exit) 0x157cc) = Some (0x57850913 : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_157cc : decode_any (0x57850913 : bv 32) = Some (OpImm ALU_ADD 18 10 1400, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_157d8 : fetch_word (@rl_segs o2_reloc) (rl (@rl_delta o2_reloc B_E___funcs_on_exit) 0x157d8) = Some (0x511070ef : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_157d8 : decode_any (0x511070ef : bv 32) = Some (Jal 1 32016, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_15824 : fetch_word (@rl_segs o2_reloc) (rl (@rl_delta o2_reloc B_E___funcs_on_exit) 0x15824) = Some (0x74d070ef : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_15824 : decode_any (0x74d070ef : bv 32) = Some (Jal 1 32588, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_15834 : fetch_word (@rl_segs o2_reloc) (rl (@rl_delta o2_reloc B_E___funcs_on_exit) 0x15834) = Some (0x4b5070ef : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_15834 : decode_any (0x4b5070ef : bv 32) = Some (Jal 1 31924, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_15874 : fetch_word (@rl_segs o2_reloc) (rl (@rl_delta o2_reloc B_E___funcs_on_exit) 0x15874) = Some (0x6fd0706f : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_15874 : decode_any (0x6fd0706f : bv 32) = Some (Jal 0 32508, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_15898 : fetch_word (@rl_segs o2_reloc) (rl (@rl_delta o2_reloc B_E___funcs_on_exit) 0x15898) = Some (0x0003a517 : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_15898 : decode_any (0x0003a517 : bv 32) = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_1589c : fetch_word (@rl_segs o2_reloc) (rl (@rl_delta o2_reloc B_E___funcs_on_exit) 0x1589c) = Some (0x4a850993 : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_1589c : decode_any (0x4a850993 : bv 32) = Some (OpImm ALU_ADD 19 10 1192, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_158a8 : fetch_word (@rl_segs o2_reloc) (rl (@rl_delta o2_reloc B_E___funcs_on_exit) 0x158a8) = Some (0x441070ef : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_158a8 : decode_any (0x441070ef : bv 32) = Some (Jal 1 31808, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_1591c : fetch_word (@rl_segs o2_reloc) (rl (@rl_delta o2_reloc B_E___funcs_on_exit) 0x1591c) = Some (0x655070ef : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_1591c : decode_any (0x655070ef : bv 32) = Some (Jal 1 32340, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_135f8 : fetch_word (@rl_segs o2_reloc) (rl (@rl_delta o2_reloc B_E_target_run) 0x135f8) = Some (0x00032517 : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_135f8 : decode_any (0x00032517 : bv 32) = Some (Auipc 10 50, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_135fc : fetch_word (@rl_segs o2_reloc) (rl (@rl_delta o2_reloc B_E_target_run) 0x135fc) = Some (0xd0454503 : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_135fc : decode_any (0xd0454503 : bv 32) = Some (Load SZ1 false 10 10 3332, 4%Z).
Proof. vm_refl. Qed.

Lemma o2_ax_foe_la : @ax_foe_la_stmt o2_reloc (Z_to_bv 64 0x69308).
Proof. r23_la S23_157c8 DS23_157c8 S23_157cc DS23_157cc. Qed.
Lemma o2_ax_foe_j1 : @ax_foe_j1_stmt o2_reloc.
Proof. r23_jal_link S23_157d8 DS23_157d8. Qed.
Lemma o2_ax_foe_j2 : @ax_foe_j2_stmt o2_reloc.
Proof. r23_jal_link S23_15824 DS23_15824. Qed.
Lemma o2_ax_foe_j3 : @ax_foe_j3_stmt o2_reloc.
Proof. r23_jal_link S23_15834 DS23_15834. Qed.
Lemma o2_ax_foe_j4 : @ax_foe_j4_stmt o2_reloc.
Proof. r23_jal_x0 S23_15874 DS23_15874. Qed.
Lemma o2_ax_at_la : @ax_at_la_stmt o2_reloc (Z_to_bv 64 0x693d8).
Proof. r23_la S23_15898 DS23_15898 S23_1589c DS23_1589c. Qed.
Lemma o2_ax_at_j1 : @ax_at_j1_stmt o2_reloc.
Proof. r23_jal_link S23_158a8 DS23_158a8. Qed.
Lemma o2_ax_at_j2 : @ax_at_j2_stmt o2_reloc.
Proof. r23_jal_link S23_1591c DS23_1591c. Qed.
Lemma o2_ax_guard_lb : @ax_guard_lb_stmt o2_reloc (Z_to_bv 64 0x49a40).
Proof. r23_lb S23_135f8 DS23_135f8 S23_135fc DS23_135fc. Qed.
Lemma o2_r23_code_ok : code_check (@rl_segs o2_reloc) (@rl_delta o2_reloc) r23_code = true.
Proof. vm_refl. Qed.
Lemma o2_ax_statics_lo : (@rl_data_lo o2_reloc o2_data <= 0x2f620 + @rl_delta o2_reloc B_A_2f840)%Z.
Proof. vm_compute; intro H; discriminate H. Qed.
Lemma o2_ax_statics_gap : (0x2f840 + @rl_delta o2_reloc B_A_2f6b0 <= 0x2f620 + @rl_delta o2_reloc B_A_2f840)%Z.
Proof. vm_compute; intro H; discriminate H. Qed.

#[export] Instance o2_r23code : @R23Code o2_reloc o2_data :=
  {| r23_code_ok := o2_r23_code_ok; ax_statics_lo := o2_ax_statics_lo; ax_statics_gap := o2_ax_statics_gap;
     r23_foe_hi := Z_to_bv 64 0x69308; r23_at_hi := Z_to_bv 64 0x693d8; r23_guard_hi := Z_to_bv 64 0x49a40;
     ax_foe_la := o2_ax_foe_la; ax_foe_j1 := o2_ax_foe_j1; ax_foe_j2 := o2_ax_foe_j2; ax_foe_j3 := o2_ax_foe_j3; ax_foe_j4 := o2_ax_foe_j4;
     ax_at_la := o2_ax_at_la; ax_at_j1 := o2_ax_at_j1; ax_at_j2 := o2_ax_at_j2; ax_guard_lb := o2_ax_guard_lb |}.
