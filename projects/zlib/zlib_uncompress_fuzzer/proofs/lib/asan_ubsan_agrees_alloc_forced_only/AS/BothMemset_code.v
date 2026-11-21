(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress_fuzzer_both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_c74a0 : bv 32 := 0x0e060a63.
Lemma F_c74a0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a6c : word) = Some W_c74a0.
Proof. vm_refl. Qed.
Lemma D_c74a0 : decode_any W_c74a0 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74a4 : bv 32 := 0x00b50023.
Lemma F_c74a4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a70 : word) = Some W_c74a4.
Proof. vm_refl. Qed.
Lemma D_c74a4 : decode_any W_c74a4 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74a8 : bv 32 := 0x00c506b3.
Lemma F_c74a8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a74 : word) = Some W_c74a8.
Proof. vm_refl. Qed.
Lemma D_c74a8 : decode_any W_c74a8 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74ac : bv 32 := 0x00300713.
Lemma F_c74ac : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a78 : word) = Some W_c74ac.
Proof. vm_refl. Qed.
Lemma D_c74ac : decode_any W_c74ac = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74b0 : bv 32 := 0xfeb68fa3.
Lemma F_c74b0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a7c : word) = Some W_c74b0.
Proof. vm_refl. Qed.
Lemma D_c74b0 : decode_any W_c74b0 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74b4 : bv 32 := 0x0ee66063.
Lemma F_c74b4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a80 : word) = Some W_c74b4.
Proof. vm_refl. Qed.
Lemma D_c74b4 : decode_any W_c74b4 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74b8 : bv 32 := 0x00b500a3.
Lemma F_c74b8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a84 : word) = Some W_c74b8.
Proof. vm_refl. Qed.
Lemma D_c74b8 : decode_any W_c74b8 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74bc : bv 32 := 0x00b50123.
Lemma F_c74bc : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a88 : word) = Some W_c74bc.
Proof. vm_refl. Qed.
Lemma D_c74bc : decode_any W_c74bc = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74c0 : bv 32 := 0x00700713.
Lemma F_c74c0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a8c : word) = Some W_c74c0.
Proof. vm_refl. Qed.
Lemma D_c74c0 : decode_any W_c74c0 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74c4 : bv 32 := 0xfeb68ea3.
Lemma F_c74c4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a90 : word) = Some W_c74c4.
Proof. vm_refl. Qed.
Lemma D_c74c4 : decode_any W_c74c4 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74c8 : bv 32 := 0xfeb68f23.
Lemma F_c74c8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a94 : word) = Some W_c74c8.
Proof. vm_refl. Qed.
Lemma D_c74c8 : decode_any W_c74c8 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74cc : bv 32 := 0x0ce66463.
Lemma F_c74cc : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a98 : word) = Some W_c74cc.
Proof. vm_refl. Qed.
Lemma D_c74cc : decode_any W_c74cc = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74d0 : bv 32 := 0x00b501a3.
Lemma F_c74d0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7a9c : word) = Some W_c74d0.
Proof. vm_refl. Qed.
Lemma D_c74d0 : decode_any W_c74d0 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74d4 : bv 32 := 0x00900793.
Lemma F_c74d4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7aa0 : word) = Some W_c74d4.
Proof. vm_refl. Qed.
Lemma D_c74d4 : decode_any W_c74d4 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74d8 : bv 32 := 0xfeb68e23.
Lemma F_c74d8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7aa4 : word) = Some W_c74d8.
Proof. vm_refl. Qed.
Lemma D_c74d8 : decode_any W_c74d8 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74dc : bv 32 := 0x0af66c63.
Lemma F_c74dc : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7aa8 : word) = Some W_c74dc.
Proof. vm_refl. Qed.
Lemma D_c74dc : decode_any W_c74dc = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74e0 : bv 32 := 0x40a006bb.
Lemma F_c74e0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7aac : word) = Some W_c74e0.
Proof. vm_refl. Qed.
Lemma D_c74e0 : decode_any W_c74e0 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74e4 : bv 32 := 0x03859813.
Lemma F_c74e4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7ab0 : word) = Some W_c74e4.
Proof. vm_refl. Qed.
Lemma D_c74e4 : decode_any W_c74e4 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74e8 : bv 32 := 0x101015b7.
Lemma F_c74e8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7ab4 : word) = Some W_c74e8.
Proof. vm_refl. Qed.
Lemma D_c74e8 : decode_any W_c74e8 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74ec : bv 32 := 0x0036f693.
Lemma F_c74ec : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7ab8 : word) = Some W_c74ec.
Proof. vm_refl. Qed.
Lemma D_c74ec : decode_any W_c74ec = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74f0 : bv 32 := 0x00459713.
Lemma F_c74f0 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7abc : word) = Some W_c74f0.
Proof. vm_refl. Qed.
Lemma D_c74f0 : decode_any W_c74f0 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74f4 : bv 32 := 0x40d60633.
Lemma F_c74f4 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7ac0 : word) = Some W_c74f4.
Proof. vm_refl. Qed.
Lemma D_c74f4 : decode_any W_c74f4 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74f8 : bv 32 := 0x00d505b3.
Lemma F_c74f8 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7ac4 : word) = Some W_c74f8.
Proof. vm_refl. Qed.
Lemma D_c74f8 : decode_any W_c74f8 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c74fc : bv 32 := 0x10070693.
Lemma F_c74fc : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7ac8 : word) = Some W_c74fc.
Proof. vm_refl. Qed.
Lemma D_c74fc : decode_any W_c74fc = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7500 : bv 32 := 0xffc67713.
Lemma F_c7500 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7acc : word) = Some W_c7500.
Proof. vm_refl. Qed.
Lemma D_c7500 : decode_any W_c7500 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7504 : bv 32 := 0x02d83633.
Lemma F_c7504 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7ad0 : word) = Some W_c7504.
Proof. vm_refl. Qed.
Lemma D_c7504 : decode_any W_c7504 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7508 : bv 32 := 0x00c5a023.
Lemma F_c7508 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7ad4 : word) = Some W_c7508.
Proof. vm_refl. Qed.
Lemma D_c7508 : decode_any W_c7508 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c750c : bv 32 := 0x00e586b3.
Lemma F_c750c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7ad8 : word) = Some W_c750c.
Proof. vm_refl. Qed.
Lemma D_c750c : decode_any W_c750c = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7510 : bv 32 := 0xfec6ae23.
Lemma F_c7510 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7adc : word) = Some W_c7510.
Proof. vm_refl. Qed.
Lemma D_c7510 : decode_any W_c7510 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7514 : bv 32 := 0x08f76063.
Lemma F_c7514 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7ae0 : word) = Some W_c7514.
Proof. vm_refl. Qed.
Lemma D_c7514 : decode_any W_c7514 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7518 : bv 32 := 0x00c5a223.
Lemma F_c7518 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7ae4 : word) = Some W_c7518.
Proof. vm_refl. Qed.
Lemma D_c7518 : decode_any W_c7518 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c751c : bv 32 := 0x00c5a423.
Lemma F_c751c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7ae8 : word) = Some W_c751c.
Proof. vm_refl. Qed.
Lemma D_c751c : decode_any W_c751c = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7520 : bv 32 := 0x01900793.
Lemma F_c7520 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7aec : word) = Some W_c7520.
Proof. vm_refl. Qed.
Lemma D_c7520 : decode_any W_c7520 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7524 : bv 32 := 0xfec6aa23.
Lemma F_c7524 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7af0 : word) = Some W_c7524.
Proof. vm_refl. Qed.
Lemma D_c7524 : decode_any W_c7524 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7528 : bv 32 := 0xfec6ac23.
Lemma F_c7528 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7af4 : word) = Some W_c7528.
Proof. vm_refl. Qed.
Lemma D_c7528 : decode_any W_c7528 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c752c : bv 32 := 0x06f76463.
Lemma F_c752c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7af8 : word) = Some W_c752c.
Proof. vm_refl. Qed.
Lemma D_c752c : decode_any W_c752c = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7530 : bv 32 := 0x00c5a623.
Lemma F_c7530 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7afc : word) = Some W_c7530.
Proof. vm_refl. Qed.
Lemma D_c7530 : decode_any W_c7530 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7534 : bv 32 := 0x00c5a823.
Lemma F_c7534 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b00 : word) = Some W_c7534.
Proof. vm_refl. Qed.
Lemma D_c7534 : decode_any W_c7534 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7538 : bv 32 := 0x00c5aa23.
Lemma F_c7538 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b04 : word) = Some W_c7538.
Proof. vm_refl. Qed.
Lemma D_c7538 : decode_any W_c7538 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_c753c : bv 32 := 0x00c5ac23.
Lemma F_c753c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b08 : word) = Some W_c753c.
Proof. vm_refl. Qed.
Lemma D_c753c : decode_any W_c753c = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7540 : bv 32 := 0x0045f793.
Lemma F_c7540 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b0c : word) = Some W_c7540.
Proof. vm_refl. Qed.
Lemma D_c7540 : decode_any W_c7540 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7544 : bv 32 := 0x02000813.
Lemma F_c7544 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b10 : word) = Some W_c7544.
Proof. vm_refl. Qed.
Lemma D_c7544 : decode_any W_c7544 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7548 : bv 32 := 0x01878793.
Lemma F_c7548 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b14 : word) = Some W_c7548.
Proof. vm_refl. Qed.
Lemma D_c7548 : decode_any W_c7548 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c754c : bv 32 := 0x40f70733.
Lemma F_c754c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b18 : word) = Some W_c754c.
Proof. vm_refl. Qed.
Lemma D_c754c : decode_any W_c754c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7550 : bv 32 := 0xfec6a223.
Lemma F_c7550 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b1c : word) = Some W_c7550.
Proof. vm_refl. Qed.
Lemma D_c7550 : decode_any W_c7550 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7554 : bv 32 := 0xfec6a423.
Lemma F_c7554 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b20 : word) = Some W_c7554.
Proof. vm_refl. Qed.
Lemma D_c7554 : decode_any W_c7554 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7558 : bv 32 := 0xfec6a623.
Lemma F_c7558 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b24 : word) = Some W_c7558.
Proof. vm_refl. Qed.
Lemma D_c7558 : decode_any W_c7558 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_c755c : bv 32 := 0xfec6a823.
Lemma F_c755c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b28 : word) = Some W_c755c.
Proof. vm_refl. Qed.
Lemma D_c755c : decode_any W_c755c = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7560 : bv 32 := 0x03076a63.
Lemma F_c7560 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b2c : word) = Some W_c7560.
Proof. vm_refl. Qed.
Lemma D_c7560 : decode_any W_c7560 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7564 : bv 32 := 0x02061613.
Lemma F_c7564 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b30 : word) = Some W_c7564.
Proof. vm_refl. Qed.
Lemma D_c7564 : decode_any W_c7564 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7568 : bv 32 := 0x00f585b3.
Lemma F_c7568 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b34 : word) = Some W_c7568.
Proof. vm_refl. Qed.
Lemma D_c7568 : decode_any W_c7568 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c756c : bv 32 := 0x02065693.
Lemma F_c756c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b38 : word) = Some W_c756c.
Proof. vm_refl. Qed.
Lemma D_c756c : decode_any W_c756c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7570 : bv 32 := 0x00d66633.
Lemma F_c7570 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b3c : word) = Some W_c7570.
Proof. vm_refl. Qed.
Lemma D_c7570 : decode_any W_c7570 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7574 : bv 32 := 0x01f00693.
Lemma F_c7574 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b40 : word) = Some W_c7574.
Proof. vm_refl. Qed.
Lemma D_c7574 : decode_any W_c7574 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7578 : bv 32 := 0x00c5b023.
Lemma F_c7578 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b44 : word) = Some W_c7578.
Proof. vm_refl. Qed.
Lemma D_c7578 : decode_any W_c7578 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c757c : bv 32 := 0x00c5b423.
Lemma F_c757c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b48 : word) = Some W_c757c.
Proof. vm_refl. Qed.
Lemma D_c757c : decode_any W_c757c = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7580 : bv 32 := 0x00c5b823.
Lemma F_c7580 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b4c : word) = Some W_c7580.
Proof. vm_refl. Qed.
Lemma D_c7580 : decode_any W_c7580 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7584 : bv 32 := 0x00c5bc23.
Lemma F_c7584 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b50 : word) = Some W_c7584.
Proof. vm_refl. Qed.
Lemma D_c7584 : decode_any W_c7584 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7588 : bv 32 := 0xfe070713.
Lemma F_c7588 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b54 : word) = Some W_c7588.
Proof. vm_refl. Qed.
Lemma D_c7588 : decode_any W_c7588 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_c758c : bv 32 := 0x02058593.
Lemma F_c758c : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b58 : word) = Some W_c758c.
Proof. vm_refl. Qed.
Lemma D_c758c : decode_any W_c758c = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7590 : bv 32 := 0xfee6e4e3.
Lemma F_c7590 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b5c : word) = Some W_c7590.
Proof. vm_refl. Qed.
Lemma D_c7590 : decode_any W_c7590 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7594 : bv 32 := 0x00008067.
Lemma F_c7594 : fetch_word Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments (0xc7b60 : word) = Some W_c7594.
Proof. vm_refl. Qed.
Lemma D_c7594 : decode_any W_c7594 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Abbreviation MSEGS := Tgt_zlib_uncompress_fuzzer_both.M.loaded_segments.
Definition ms_base : Z := 0xc7a6c%Z.
Definition Fo_000 := F_c74a0.
Definition Do_000 := D_c74a0.
Definition Fo_004 := F_c74a4.
Definition Do_004 := D_c74a4.
Definition Fo_008 := F_c74a8.
Definition Do_008 := D_c74a8.
Definition Fo_00c := F_c74ac.
Definition Do_00c := D_c74ac.
Definition Fo_010 := F_c74b0.
Definition Do_010 := D_c74b0.
Definition Fo_014 := F_c74b4.
Definition Do_014 := D_c74b4.
Definition Fo_018 := F_c74b8.
Definition Do_018 := D_c74b8.
Definition Fo_01c := F_c74bc.
Definition Do_01c := D_c74bc.
Definition Fo_020 := F_c74c0.
Definition Do_020 := D_c74c0.
Definition Fo_024 := F_c74c4.
Definition Do_024 := D_c74c4.
Definition Fo_028 := F_c74c8.
Definition Do_028 := D_c74c8.
Definition Fo_02c := F_c74cc.
Definition Do_02c := D_c74cc.
Definition Fo_030 := F_c74d0.
Definition Do_030 := D_c74d0.
Definition Fo_034 := F_c74d4.
Definition Do_034 := D_c74d4.
Definition Fo_038 := F_c74d8.
Definition Do_038 := D_c74d8.
Definition Fo_03c := F_c74dc.
Definition Do_03c := D_c74dc.
Definition Fo_040 := F_c74e0.
Definition Do_040 := D_c74e0.
Definition Fo_044 := F_c74e4.
Definition Do_044 := D_c74e4.
Definition Fo_048 := F_c74e8.
Definition Do_048 := D_c74e8.
Definition Fo_04c := F_c74ec.
Definition Do_04c := D_c74ec.
Definition Fo_050 := F_c74f0.
Definition Do_050 := D_c74f0.
Definition Fo_054 := F_c74f4.
Definition Do_054 := D_c74f4.
Definition Fo_058 := F_c74f8.
Definition Do_058 := D_c74f8.
Definition Fo_05c := F_c74fc.
Definition Do_05c := D_c74fc.
Definition Fo_060 := F_c7500.
Definition Do_060 := D_c7500.
Definition Fo_064 := F_c7504.
Definition Do_064 := D_c7504.
Definition Fo_068 := F_c7508.
Definition Do_068 := D_c7508.
Definition Fo_06c := F_c750c.
Definition Do_06c := D_c750c.
Definition Fo_070 := F_c7510.
Definition Do_070 := D_c7510.
Definition Fo_074 := F_c7514.
Definition Do_074 := D_c7514.
Definition Fo_078 := F_c7518.
Definition Do_078 := D_c7518.
Definition Fo_07c := F_c751c.
Definition Do_07c := D_c751c.
Definition Fo_080 := F_c7520.
Definition Do_080 := D_c7520.
Definition Fo_084 := F_c7524.
Definition Do_084 := D_c7524.
Definition Fo_088 := F_c7528.
Definition Do_088 := D_c7528.
Definition Fo_08c := F_c752c.
Definition Do_08c := D_c752c.
Definition Fo_090 := F_c7530.
Definition Do_090 := D_c7530.
Definition Fo_094 := F_c7534.
Definition Do_094 := D_c7534.
Definition Fo_098 := F_c7538.
Definition Do_098 := D_c7538.
Definition Fo_09c := F_c753c.
Definition Do_09c := D_c753c.
Definition Fo_0a0 := F_c7540.
Definition Do_0a0 := D_c7540.
Definition Fo_0a4 := F_c7544.
Definition Do_0a4 := D_c7544.
Definition Fo_0a8 := F_c7548.
Definition Do_0a8 := D_c7548.
Definition Fo_0ac := F_c754c.
Definition Do_0ac := D_c754c.
Definition Fo_0b0 := F_c7550.
Definition Do_0b0 := D_c7550.
Definition Fo_0b4 := F_c7554.
Definition Do_0b4 := D_c7554.
Definition Fo_0b8 := F_c7558.
Definition Do_0b8 := D_c7558.
Definition Fo_0bc := F_c755c.
Definition Do_0bc := D_c755c.
Definition Fo_0c0 := F_c7560.
Definition Do_0c0 := D_c7560.
Definition Fo_0c4 := F_c7564.
Definition Do_0c4 := D_c7564.
Definition Fo_0c8 := F_c7568.
Definition Do_0c8 := D_c7568.
Definition Fo_0cc := F_c756c.
Definition Do_0cc := D_c756c.
Definition Fo_0d0 := F_c7570.
Definition Do_0d0 := D_c7570.
Definition Fo_0d4 := F_c7574.
Definition Do_0d4 := D_c7574.
Definition Fo_0d8 := F_c7578.
Definition Do_0d8 := D_c7578.
Definition Fo_0dc := F_c757c.
Definition Do_0dc := D_c757c.
Definition Fo_0e0 := F_c7580.
Definition Do_0e0 := D_c7580.
Definition Fo_0e4 := F_c7584.
Definition Do_0e4 := D_c7584.
Definition Fo_0e8 := F_c7588.
Definition Do_0e8 := D_c7588.
Definition Fo_0ec := F_c758c.
Definition Do_0ec := D_c758c.
Definition Fo_0f0 := F_c7590.
Definition Do_0f0 := D_c7590.
Definition Fo_0f4 := F_c7594.
Definition Do_0f4 := D_c7594.
