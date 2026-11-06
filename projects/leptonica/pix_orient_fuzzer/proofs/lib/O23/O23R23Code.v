(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec SeqExec StepTac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import RefStep.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc RelocBlocks RelocCode RelocImg RelocKit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require Import R23Code.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23Reloc O23RelocImg.
Import ListNotations.
Local Open Scope Z_scope.
Open Scope bv_scope.

Definition o23_cc23_sites : list cchunk := [mkChunk 3004%positive 0x157c8 1 [Some 0x0004a517%Z]; mkChunk 3004%positive 0x157cc 1 [Some 0xef850913%Z]; mkChunk 3004%positive 0x157d8 1 [Some 0x1b5100ef%Z]; mkChunk 3004%positive 0x15824 1 [Some 0x3f1100ef%Z]; mkChunk 3004%positive 0x15834 1 [Some 0x159100ef%Z]; mkChunk 3004%positive 0x15874 1 [Some 0x3a11006f%Z]; mkChunk 3004%positive 0x15898 1 [Some 0x0004a517%Z]; mkChunk 3004%positive 0x1589c 1 [Some 0xe2850993%Z]; mkChunk 3004%positive 0x158a8 1 [Some 0x0e5100ef%Z]; mkChunk 3004%positive 0x1591c 1 [Some 0x2f9100ef%Z]; mkChunk 3003%positive 0x135f8 1 [Some 0x000c1517%Z]; mkChunk 3003%positive 0x135fc 1 [Some 0xb2054503%Z]].
Lemma o23_sites23_ok : code_check (@rl_segs o23_reloc) (@rl_delta o23_reloc) o23_cc23_sites = true.
Proof. vm_refl. Qed.
Lemma S23_157c8 : fetch_word (@rl_segs o23_reloc) (rl (@rl_delta o23_reloc B_E___funcs_on_exit) 0x157c8) = Some (0x0004a517 : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_157c8 : decode_any (0x0004a517 : bv 32) = Some (Auipc 10 74, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_157cc : fetch_word (@rl_segs o23_reloc) (rl (@rl_delta o23_reloc B_E___funcs_on_exit) 0x157cc) = Some (0xef850913 : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_157cc : decode_any (0xef850913 : bv 32) = Some (OpImm ALU_ADD 18 10 3832, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_157d8 : fetch_word (@rl_segs o23_reloc) (rl (@rl_delta o23_reloc B_E___funcs_on_exit) 0x157d8) = Some (0x1b5100ef : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_157d8 : decode_any (0x1b5100ef : bv 32) = Some (Jal 1 68020, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_15824 : fetch_word (@rl_segs o23_reloc) (rl (@rl_delta o23_reloc B_E___funcs_on_exit) 0x15824) = Some (0x3f1100ef : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_15824 : decode_any (0x3f1100ef : bv 32) = Some (Jal 1 68592, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_15834 : fetch_word (@rl_segs o23_reloc) (rl (@rl_delta o23_reloc B_E___funcs_on_exit) 0x15834) = Some (0x159100ef : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_15834 : decode_any (0x159100ef : bv 32) = Some (Jal 1 67928, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_15874 : fetch_word (@rl_segs o23_reloc) (rl (@rl_delta o23_reloc B_E___funcs_on_exit) 0x15874) = Some (0x3a11006f : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_15874 : decode_any (0x3a11006f : bv 32) = Some (Jal 0 68512, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_15898 : fetch_word (@rl_segs o23_reloc) (rl (@rl_delta o23_reloc B_E___funcs_on_exit) 0x15898) = Some (0x0004a517 : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_15898 : decode_any (0x0004a517 : bv 32) = Some (Auipc 10 74, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_1589c : fetch_word (@rl_segs o23_reloc) (rl (@rl_delta o23_reloc B_E___funcs_on_exit) 0x1589c) = Some (0xe2850993 : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_1589c : decode_any (0xe2850993 : bv 32) = Some (OpImm ALU_ADD 19 10 3624, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_158a8 : fetch_word (@rl_segs o23_reloc) (rl (@rl_delta o23_reloc B_E___funcs_on_exit) 0x158a8) = Some (0x0e5100ef : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_158a8 : decode_any (0x0e5100ef : bv 32) = Some (Jal 1 67812, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_1591c : fetch_word (@rl_segs o23_reloc) (rl (@rl_delta o23_reloc B_E___funcs_on_exit) 0x1591c) = Some (0x2f9100ef : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_1591c : decode_any (0x2f9100ef : bv 32) = Some (Jal 1 68344, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_135f8 : fetch_word (@rl_segs o23_reloc) (rl (@rl_delta o23_reloc B_E_target_run) 0x135f8) = Some (0x000c1517 : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_135f8 : decode_any (0x000c1517 : bv 32) = Some (Auipc 10 193, 4%Z).
Proof. vm_refl. Qed.
Lemma S23_135fc : fetch_word (@rl_segs o23_reloc) (rl (@rl_delta o23_reloc B_E_target_run) 0x135fc) = Some (0xb2054503 : bv 32).
Proof. vm_refl. Qed.
Lemma DS23_135fc : decode_any (0xb2054503 : bv 32) = Some (Load SZ1 false 10 10 2848, 4%Z).
Proof. vm_refl. Qed.

Lemma o23_ax_foe_la : @ax_foe_la_stmt o23_reloc (Z_to_bv 64 0x143e70).
Proof. r23_la S23_157c8 DS23_157c8 S23_157cc DS23_157cc. Qed.
Lemma o23_ax_foe_j1 : @ax_foe_j1_stmt o23_reloc.
Proof. r23_jal_link S23_157d8 DS23_157d8. Qed.
Lemma o23_ax_foe_j2 : @ax_foe_j2_stmt o23_reloc.
Proof. r23_jal_link S23_15824 DS23_15824. Qed.
Lemma o23_ax_foe_j3 : @ax_foe_j3_stmt o23_reloc.
Proof. r23_jal_link S23_15834 DS23_15834. Qed.
Lemma o23_ax_foe_j4 : @ax_foe_j4_stmt o23_reloc.
Proof. r23_jal_x0 S23_15874 DS23_15874. Qed.
Lemma o23_ax_at_la : @ax_at_la_stmt o23_reloc (Z_to_bv 64 0x143f40).
Proof. r23_la S23_15898 DS23_15898 S23_1589c DS23_1589c. Qed.
Lemma o23_ax_at_j1 : @ax_at_j1_stmt o23_reloc.
Proof. r23_jal_link S23_158a8 DS23_158a8. Qed.
Lemma o23_ax_at_j2 : @ax_at_j2_stmt o23_reloc.
Proof. r23_jal_link S23_1591c DS23_1591c. Qed.
Lemma o23_ax_guard_lb : @ax_guard_lb_stmt o23_reloc (Z_to_bv 64 0x123f44).
Proof. r23_lb S23_135f8 DS23_135f8 S23_135fc DS23_135fc. Qed.
Lemma o23_r23_code_ok : code_check (@rl_segs o23_reloc) (@rl_delta o23_reloc) r23_code = true.
Proof. vm_refl. Qed.
Lemma o23_ax_statics_lo : (@rl_data_lo o23_reloc o23_data <= 0x2f620 + @rl_delta o23_reloc B_A_2f840)%Z.
Proof. vm_compute; intro H; discriminate H. Qed.
Lemma o23_ax_statics_gap : (0x2f840 + @rl_delta o23_reloc B_A_2f6b0 <= 0x2f620 + @rl_delta o23_reloc B_A_2f840)%Z.
Proof. vm_compute; intro H; discriminate H. Qed.

#[export] Instance o23_r23code : @R23Code o23_reloc o23_data :=
  {| r23_code_ok := o23_r23_code_ok; ax_statics_lo := o23_ax_statics_lo; ax_statics_gap := o23_ax_statics_gap;
     r23_foe_hi := Z_to_bv 64 0x143e70; r23_at_hi := Z_to_bv 64 0x143f40; r23_guard_hi := Z_to_bv 64 0x123f44;
     ax_foe_la := o23_ax_foe_la; ax_foe_j1 := o23_ax_foe_j1; ax_foe_j2 := o23_ax_foe_j2; ax_foe_j3 := o23_ax_foe_j3; ax_foe_j4 := o23_ax_foe_j4;
     ax_at_la := o23_ax_at_la; ax_at_j1 := o23_ax_at_j1; ax_at_j2 := o23_ax_at_j2; ax_guard_lb := o23_ax_guard_lb |}.
