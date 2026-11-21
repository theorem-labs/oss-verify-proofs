(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress_fuzzer_asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_c5ffc : bv 32 := 0x0e060a63.
Lemma F_c5ffc : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc656c : word) = Some W_c5ffc.
Proof. vm_refl. Qed.
Lemma D_c5ffc : decode_any W_c5ffc = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6000 : bv 32 := 0x00b50023.
Lemma F_c6000 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6570 : word) = Some W_c6000.
Proof. vm_refl. Qed.
Lemma D_c6000 : decode_any W_c6000 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6004 : bv 32 := 0x00c506b3.
Lemma F_c6004 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6574 : word) = Some W_c6004.
Proof. vm_refl. Qed.
Lemma D_c6004 : decode_any W_c6004 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6008 : bv 32 := 0x00300713.
Lemma F_c6008 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6578 : word) = Some W_c6008.
Proof. vm_refl. Qed.
Lemma D_c6008 : decode_any W_c6008 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c600c : bv 32 := 0xfeb68fa3.
Lemma F_c600c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc657c : word) = Some W_c600c.
Proof. vm_refl. Qed.
Lemma D_c600c : decode_any W_c600c = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6010 : bv 32 := 0x0ee66063.
Lemma F_c6010 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6580 : word) = Some W_c6010.
Proof. vm_refl. Qed.
Lemma D_c6010 : decode_any W_c6010 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6014 : bv 32 := 0x00b500a3.
Lemma F_c6014 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6584 : word) = Some W_c6014.
Proof. vm_refl. Qed.
Lemma D_c6014 : decode_any W_c6014 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6018 : bv 32 := 0x00b50123.
Lemma F_c6018 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6588 : word) = Some W_c6018.
Proof. vm_refl. Qed.
Lemma D_c6018 : decode_any W_c6018 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c601c : bv 32 := 0x00700713.
Lemma F_c601c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc658c : word) = Some W_c601c.
Proof. vm_refl. Qed.
Lemma D_c601c : decode_any W_c601c = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6020 : bv 32 := 0xfeb68ea3.
Lemma F_c6020 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6590 : word) = Some W_c6020.
Proof. vm_refl. Qed.
Lemma D_c6020 : decode_any W_c6020 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6024 : bv 32 := 0xfeb68f23.
Lemma F_c6024 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6594 : word) = Some W_c6024.
Proof. vm_refl. Qed.
Lemma D_c6024 : decode_any W_c6024 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6028 : bv 32 := 0x0ce66463.
Lemma F_c6028 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6598 : word) = Some W_c6028.
Proof. vm_refl. Qed.
Lemma D_c6028 : decode_any W_c6028 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_c602c : bv 32 := 0x00b501a3.
Lemma F_c602c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc659c : word) = Some W_c602c.
Proof. vm_refl. Qed.
Lemma D_c602c : decode_any W_c602c = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6030 : bv 32 := 0x00900793.
Lemma F_c6030 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65a0 : word) = Some W_c6030.
Proof. vm_refl. Qed.
Lemma D_c6030 : decode_any W_c6030 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6034 : bv 32 := 0xfeb68e23.
Lemma F_c6034 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65a4 : word) = Some W_c6034.
Proof. vm_refl. Qed.
Lemma D_c6034 : decode_any W_c6034 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6038 : bv 32 := 0x0af66c63.
Lemma F_c6038 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65a8 : word) = Some W_c6038.
Proof. vm_refl. Qed.
Lemma D_c6038 : decode_any W_c6038 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_c603c : bv 32 := 0x40a006bb.
Lemma F_c603c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65ac : word) = Some W_c603c.
Proof. vm_refl. Qed.
Lemma D_c603c : decode_any W_c603c = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6040 : bv 32 := 0x03859813.
Lemma F_c6040 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65b0 : word) = Some W_c6040.
Proof. vm_refl. Qed.
Lemma D_c6040 : decode_any W_c6040 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6044 : bv 32 := 0x101015b7.
Lemma F_c6044 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65b4 : word) = Some W_c6044.
Proof. vm_refl. Qed.
Lemma D_c6044 : decode_any W_c6044 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6048 : bv 32 := 0x0036f693.
Lemma F_c6048 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65b8 : word) = Some W_c6048.
Proof. vm_refl. Qed.
Lemma D_c6048 : decode_any W_c6048 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c604c : bv 32 := 0x00459713.
Lemma F_c604c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65bc : word) = Some W_c604c.
Proof. vm_refl. Qed.
Lemma D_c604c : decode_any W_c604c = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6050 : bv 32 := 0x40d60633.
Lemma F_c6050 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65c0 : word) = Some W_c6050.
Proof. vm_refl. Qed.
Lemma D_c6050 : decode_any W_c6050 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6054 : bv 32 := 0x00d505b3.
Lemma F_c6054 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65c4 : word) = Some W_c6054.
Proof. vm_refl. Qed.
Lemma D_c6054 : decode_any W_c6054 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6058 : bv 32 := 0x10070693.
Lemma F_c6058 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65c8 : word) = Some W_c6058.
Proof. vm_refl. Qed.
Lemma D_c6058 : decode_any W_c6058 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_c605c : bv 32 := 0xffc67713.
Lemma F_c605c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65cc : word) = Some W_c605c.
Proof. vm_refl. Qed.
Lemma D_c605c : decode_any W_c605c = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6060 : bv 32 := 0x02d83633.
Lemma F_c6060 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65d0 : word) = Some W_c6060.
Proof. vm_refl. Qed.
Lemma D_c6060 : decode_any W_c6060 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6064 : bv 32 := 0x00c5a023.
Lemma F_c6064 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65d4 : word) = Some W_c6064.
Proof. vm_refl. Qed.
Lemma D_c6064 : decode_any W_c6064 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6068 : bv 32 := 0x00e586b3.
Lemma F_c6068 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65d8 : word) = Some W_c6068.
Proof. vm_refl. Qed.
Lemma D_c6068 : decode_any W_c6068 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_c606c : bv 32 := 0xfec6ae23.
Lemma F_c606c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65dc : word) = Some W_c606c.
Proof. vm_refl. Qed.
Lemma D_c606c : decode_any W_c606c = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6070 : bv 32 := 0x08f76063.
Lemma F_c6070 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65e0 : word) = Some W_c6070.
Proof. vm_refl. Qed.
Lemma D_c6070 : decode_any W_c6070 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6074 : bv 32 := 0x00c5a223.
Lemma F_c6074 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65e4 : word) = Some W_c6074.
Proof. vm_refl. Qed.
Lemma D_c6074 : decode_any W_c6074 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6078 : bv 32 := 0x00c5a423.
Lemma F_c6078 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65e8 : word) = Some W_c6078.
Proof. vm_refl. Qed.
Lemma D_c6078 : decode_any W_c6078 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c607c : bv 32 := 0x01900793.
Lemma F_c607c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65ec : word) = Some W_c607c.
Proof. vm_refl. Qed.
Lemma D_c607c : decode_any W_c607c = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6080 : bv 32 := 0xfec6aa23.
Lemma F_c6080 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65f0 : word) = Some W_c6080.
Proof. vm_refl. Qed.
Lemma D_c6080 : decode_any W_c6080 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6084 : bv 32 := 0xfec6ac23.
Lemma F_c6084 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65f4 : word) = Some W_c6084.
Proof. vm_refl. Qed.
Lemma D_c6084 : decode_any W_c6084 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6088 : bv 32 := 0x06f76463.
Lemma F_c6088 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65f8 : word) = Some W_c6088.
Proof. vm_refl. Qed.
Lemma D_c6088 : decode_any W_c6088 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_c608c : bv 32 := 0x00c5a623.
Lemma F_c608c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc65fc : word) = Some W_c608c.
Proof. vm_refl. Qed.
Lemma D_c608c : decode_any W_c608c = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6090 : bv 32 := 0x00c5a823.
Lemma F_c6090 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6600 : word) = Some W_c6090.
Proof. vm_refl. Qed.
Lemma D_c6090 : decode_any W_c6090 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6094 : bv 32 := 0x00c5aa23.
Lemma F_c6094 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6604 : word) = Some W_c6094.
Proof. vm_refl. Qed.
Lemma D_c6094 : decode_any W_c6094 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6098 : bv 32 := 0x00c5ac23.
Lemma F_c6098 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6608 : word) = Some W_c6098.
Proof. vm_refl. Qed.
Lemma D_c6098 : decode_any W_c6098 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c609c : bv 32 := 0x0045f793.
Lemma F_c609c : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc660c : word) = Some W_c609c.
Proof. vm_refl. Qed.
Lemma D_c609c : decode_any W_c609c = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60a0 : bv 32 := 0x02000813.
Lemma F_c60a0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6610 : word) = Some W_c60a0.
Proof. vm_refl. Qed.
Lemma D_c60a0 : decode_any W_c60a0 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60a4 : bv 32 := 0x01878793.
Lemma F_c60a4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6614 : word) = Some W_c60a4.
Proof. vm_refl. Qed.
Lemma D_c60a4 : decode_any W_c60a4 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60a8 : bv 32 := 0x40f70733.
Lemma F_c60a8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6618 : word) = Some W_c60a8.
Proof. vm_refl. Qed.
Lemma D_c60a8 : decode_any W_c60a8 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60ac : bv 32 := 0xfec6a223.
Lemma F_c60ac : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc661c : word) = Some W_c60ac.
Proof. vm_refl. Qed.
Lemma D_c60ac : decode_any W_c60ac = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60b0 : bv 32 := 0xfec6a423.
Lemma F_c60b0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6620 : word) = Some W_c60b0.
Proof. vm_refl. Qed.
Lemma D_c60b0 : decode_any W_c60b0 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60b4 : bv 32 := 0xfec6a623.
Lemma F_c60b4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6624 : word) = Some W_c60b4.
Proof. vm_refl. Qed.
Lemma D_c60b4 : decode_any W_c60b4 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60b8 : bv 32 := 0xfec6a823.
Lemma F_c60b8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6628 : word) = Some W_c60b8.
Proof. vm_refl. Qed.
Lemma D_c60b8 : decode_any W_c60b8 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60bc : bv 32 := 0x03076a63.
Lemma F_c60bc : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc662c : word) = Some W_c60bc.
Proof. vm_refl. Qed.
Lemma D_c60bc : decode_any W_c60bc = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60c0 : bv 32 := 0x02061613.
Lemma F_c60c0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6630 : word) = Some W_c60c0.
Proof. vm_refl. Qed.
Lemma D_c60c0 : decode_any W_c60c0 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60c4 : bv 32 := 0x00f585b3.
Lemma F_c60c4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6634 : word) = Some W_c60c4.
Proof. vm_refl. Qed.
Lemma D_c60c4 : decode_any W_c60c4 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60c8 : bv 32 := 0x02065693.
Lemma F_c60c8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6638 : word) = Some W_c60c8.
Proof. vm_refl. Qed.
Lemma D_c60c8 : decode_any W_c60c8 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60cc : bv 32 := 0x00d66633.
Lemma F_c60cc : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc663c : word) = Some W_c60cc.
Proof. vm_refl. Qed.
Lemma D_c60cc : decode_any W_c60cc = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60d0 : bv 32 := 0x01f00693.
Lemma F_c60d0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6640 : word) = Some W_c60d0.
Proof. vm_refl. Qed.
Lemma D_c60d0 : decode_any W_c60d0 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60d4 : bv 32 := 0x00c5b023.
Lemma F_c60d4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6644 : word) = Some W_c60d4.
Proof. vm_refl. Qed.
Lemma D_c60d4 : decode_any W_c60d4 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60d8 : bv 32 := 0x00c5b423.
Lemma F_c60d8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6648 : word) = Some W_c60d8.
Proof. vm_refl. Qed.
Lemma D_c60d8 : decode_any W_c60d8 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60dc : bv 32 := 0x00c5b823.
Lemma F_c60dc : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc664c : word) = Some W_c60dc.
Proof. vm_refl. Qed.
Lemma D_c60dc : decode_any W_c60dc = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60e0 : bv 32 := 0x00c5bc23.
Lemma F_c60e0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6650 : word) = Some W_c60e0.
Proof. vm_refl. Qed.
Lemma D_c60e0 : decode_any W_c60e0 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60e4 : bv 32 := 0xfe070713.
Lemma F_c60e4 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6654 : word) = Some W_c60e4.
Proof. vm_refl. Qed.
Lemma D_c60e4 : decode_any W_c60e4 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60e8 : bv 32 := 0x02058593.
Lemma F_c60e8 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6658 : word) = Some W_c60e8.
Proof. vm_refl. Qed.
Lemma D_c60e8 : decode_any W_c60e8 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60ec : bv 32 := 0xfee6e4e3.
Lemma F_c60ec : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc665c : word) = Some W_c60ec.
Proof. vm_refl. Qed.
Lemma D_c60ec : decode_any W_c60ec = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_c60f0 : bv 32 := 0x00008067.
Lemma F_c60f0 : fetch_word Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments (0xc6660 : word) = Some W_c60f0.
Proof. vm_refl. Qed.
Lemma D_c60f0 : decode_any W_c60f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Abbreviation MSEGS := Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments.
Definition ms_base : Z := 0xc656c%Z.
Definition Fo_000 := F_c5ffc.
Definition Do_000 := D_c5ffc.
Definition Fo_004 := F_c6000.
Definition Do_004 := D_c6000.
Definition Fo_008 := F_c6004.
Definition Do_008 := D_c6004.
Definition Fo_00c := F_c6008.
Definition Do_00c := D_c6008.
Definition Fo_010 := F_c600c.
Definition Do_010 := D_c600c.
Definition Fo_014 := F_c6010.
Definition Do_014 := D_c6010.
Definition Fo_018 := F_c6014.
Definition Do_018 := D_c6014.
Definition Fo_01c := F_c6018.
Definition Do_01c := D_c6018.
Definition Fo_020 := F_c601c.
Definition Do_020 := D_c601c.
Definition Fo_024 := F_c6020.
Definition Do_024 := D_c6020.
Definition Fo_028 := F_c6024.
Definition Do_028 := D_c6024.
Definition Fo_02c := F_c6028.
Definition Do_02c := D_c6028.
Definition Fo_030 := F_c602c.
Definition Do_030 := D_c602c.
Definition Fo_034 := F_c6030.
Definition Do_034 := D_c6030.
Definition Fo_038 := F_c6034.
Definition Do_038 := D_c6034.
Definition Fo_03c := F_c6038.
Definition Do_03c := D_c6038.
Definition Fo_040 := F_c603c.
Definition Do_040 := D_c603c.
Definition Fo_044 := F_c6040.
Definition Do_044 := D_c6040.
Definition Fo_048 := F_c6044.
Definition Do_048 := D_c6044.
Definition Fo_04c := F_c6048.
Definition Do_04c := D_c6048.
Definition Fo_050 := F_c604c.
Definition Do_050 := D_c604c.
Definition Fo_054 := F_c6050.
Definition Do_054 := D_c6050.
Definition Fo_058 := F_c6054.
Definition Do_058 := D_c6054.
Definition Fo_05c := F_c6058.
Definition Do_05c := D_c6058.
Definition Fo_060 := F_c605c.
Definition Do_060 := D_c605c.
Definition Fo_064 := F_c6060.
Definition Do_064 := D_c6060.
Definition Fo_068 := F_c6064.
Definition Do_068 := D_c6064.
Definition Fo_06c := F_c6068.
Definition Do_06c := D_c6068.
Definition Fo_070 := F_c606c.
Definition Do_070 := D_c606c.
Definition Fo_074 := F_c6070.
Definition Do_074 := D_c6070.
Definition Fo_078 := F_c6074.
Definition Do_078 := D_c6074.
Definition Fo_07c := F_c6078.
Definition Do_07c := D_c6078.
Definition Fo_080 := F_c607c.
Definition Do_080 := D_c607c.
Definition Fo_084 := F_c6080.
Definition Do_084 := D_c6080.
Definition Fo_088 := F_c6084.
Definition Do_088 := D_c6084.
Definition Fo_08c := F_c6088.
Definition Do_08c := D_c6088.
Definition Fo_090 := F_c608c.
Definition Do_090 := D_c608c.
Definition Fo_094 := F_c6090.
Definition Do_094 := D_c6090.
Definition Fo_098 := F_c6094.
Definition Do_098 := D_c6094.
Definition Fo_09c := F_c6098.
Definition Do_09c := D_c6098.
Definition Fo_0a0 := F_c609c.
Definition Do_0a0 := D_c609c.
Definition Fo_0a4 := F_c60a0.
Definition Do_0a4 := D_c60a0.
Definition Fo_0a8 := F_c60a4.
Definition Do_0a8 := D_c60a4.
Definition Fo_0ac := F_c60a8.
Definition Do_0ac := D_c60a8.
Definition Fo_0b0 := F_c60ac.
Definition Do_0b0 := D_c60ac.
Definition Fo_0b4 := F_c60b0.
Definition Do_0b4 := D_c60b0.
Definition Fo_0b8 := F_c60b4.
Definition Do_0b8 := D_c60b4.
Definition Fo_0bc := F_c60b8.
Definition Do_0bc := D_c60b8.
Definition Fo_0c0 := F_c60bc.
Definition Do_0c0 := D_c60bc.
Definition Fo_0c4 := F_c60c0.
Definition Do_0c4 := D_c60c0.
Definition Fo_0c8 := F_c60c4.
Definition Do_0c8 := D_c60c4.
Definition Fo_0cc := F_c60c8.
Definition Do_0cc := D_c60c8.
Definition Fo_0d0 := F_c60cc.
Definition Do_0d0 := D_c60cc.
Definition Fo_0d4 := F_c60d0.
Definition Do_0d4 := D_c60d0.
Definition Fo_0d8 := F_c60d4.
Definition Do_0d8 := D_c60d4.
Definition Fo_0dc := F_c60d8.
Definition Do_0dc := D_c60d8.
Definition Fo_0e0 := F_c60dc.
Definition Do_0e0 := D_c60dc.
Definition Fo_0e4 := F_c60e0.
Definition Do_0e4 := D_c60e0.
Definition Fo_0e8 := F_c60e4.
Definition Do_0e8 := D_c60e4.
Definition Fo_0ec := F_c60e8.
Definition Do_0ec := D_c60e8.
Definition Fo_0f0 := F_c60ec.
Definition Do_0f0 := D_c60ec.
Definition Fo_0f4 := F_c60f0.
Definition Do_0f4 := D_c60f0.
