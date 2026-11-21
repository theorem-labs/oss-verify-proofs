(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress2_fuzzer_asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_c6240 : bv 32 := 0x0e060a63.
Lemma F_c6240 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6800 : word) = Some W_c6240.
Proof. vm_refl. Qed.
Lemma D_c6240 : decode_any W_c6240 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6244 : bv 32 := 0x00b50023.
Lemma F_c6244 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6804 : word) = Some W_c6244.
Proof. vm_refl. Qed.
Lemma D_c6244 : decode_any W_c6244 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6248 : bv 32 := 0x00c506b3.
Lemma F_c6248 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6808 : word) = Some W_c6248.
Proof. vm_refl. Qed.
Lemma D_c6248 : decode_any W_c6248 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c624c : bv 32 := 0x00300713.
Lemma F_c624c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc680c : word) = Some W_c624c.
Proof. vm_refl. Qed.
Lemma D_c624c : decode_any W_c624c = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6250 : bv 32 := 0xfeb68fa3.
Lemma F_c6250 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6810 : word) = Some W_c6250.
Proof. vm_refl. Qed.
Lemma D_c6250 : decode_any W_c6250 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6254 : bv 32 := 0x0ee66063.
Lemma F_c6254 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6814 : word) = Some W_c6254.
Proof. vm_refl. Qed.
Lemma D_c6254 : decode_any W_c6254 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6258 : bv 32 := 0x00b500a3.
Lemma F_c6258 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6818 : word) = Some W_c6258.
Proof. vm_refl. Qed.
Lemma D_c6258 : decode_any W_c6258 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c625c : bv 32 := 0x00b50123.
Lemma F_c625c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc681c : word) = Some W_c625c.
Proof. vm_refl. Qed.
Lemma D_c625c : decode_any W_c625c = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6260 : bv 32 := 0x00700713.
Lemma F_c6260 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6820 : word) = Some W_c6260.
Proof. vm_refl. Qed.
Lemma D_c6260 : decode_any W_c6260 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6264 : bv 32 := 0xfeb68ea3.
Lemma F_c6264 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6824 : word) = Some W_c6264.
Proof. vm_refl. Qed.
Lemma D_c6264 : decode_any W_c6264 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6268 : bv 32 := 0xfeb68f23.
Lemma F_c6268 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6828 : word) = Some W_c6268.
Proof. vm_refl. Qed.
Lemma D_c6268 : decode_any W_c6268 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_c626c : bv 32 := 0x0ce66463.
Lemma F_c626c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc682c : word) = Some W_c626c.
Proof. vm_refl. Qed.
Lemma D_c626c : decode_any W_c626c = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6270 : bv 32 := 0x00b501a3.
Lemma F_c6270 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6830 : word) = Some W_c6270.
Proof. vm_refl. Qed.
Lemma D_c6270 : decode_any W_c6270 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6274 : bv 32 := 0x00900793.
Lemma F_c6274 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6834 : word) = Some W_c6274.
Proof. vm_refl. Qed.
Lemma D_c6274 : decode_any W_c6274 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6278 : bv 32 := 0xfeb68e23.
Lemma F_c6278 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6838 : word) = Some W_c6278.
Proof. vm_refl. Qed.
Lemma D_c6278 : decode_any W_c6278 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c627c : bv 32 := 0x0af66c63.
Lemma F_c627c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc683c : word) = Some W_c627c.
Proof. vm_refl. Qed.
Lemma D_c627c : decode_any W_c627c = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6280 : bv 32 := 0x40a006bb.
Lemma F_c6280 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6840 : word) = Some W_c6280.
Proof. vm_refl. Qed.
Lemma D_c6280 : decode_any W_c6280 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6284 : bv 32 := 0x03859813.
Lemma F_c6284 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6844 : word) = Some W_c6284.
Proof. vm_refl. Qed.
Lemma D_c6284 : decode_any W_c6284 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6288 : bv 32 := 0x101015b7.
Lemma F_c6288 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6848 : word) = Some W_c6288.
Proof. vm_refl. Qed.
Lemma D_c6288 : decode_any W_c6288 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

Definition W_c628c : bv 32 := 0x0036f693.
Lemma F_c628c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc684c : word) = Some W_c628c.
Proof. vm_refl. Qed.
Lemma D_c628c : decode_any W_c628c = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6290 : bv 32 := 0x00459713.
Lemma F_c6290 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6850 : word) = Some W_c6290.
Proof. vm_refl. Qed.
Lemma D_c6290 : decode_any W_c6290 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6294 : bv 32 := 0x40d60633.
Lemma F_c6294 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6854 : word) = Some W_c6294.
Proof. vm_refl. Qed.
Lemma D_c6294 : decode_any W_c6294 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6298 : bv 32 := 0x00d505b3.
Lemma F_c6298 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6858 : word) = Some W_c6298.
Proof. vm_refl. Qed.
Lemma D_c6298 : decode_any W_c6298 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c629c : bv 32 := 0x10070693.
Lemma F_c629c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc685c : word) = Some W_c629c.
Proof. vm_refl. Qed.
Lemma D_c629c : decode_any W_c629c = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62a0 : bv 32 := 0xffc67713.
Lemma F_c62a0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6860 : word) = Some W_c62a0.
Proof. vm_refl. Qed.
Lemma D_c62a0 : decode_any W_c62a0 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62a4 : bv 32 := 0x02d83633.
Lemma F_c62a4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6864 : word) = Some W_c62a4.
Proof. vm_refl. Qed.
Lemma D_c62a4 : decode_any W_c62a4 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62a8 : bv 32 := 0x00c5a023.
Lemma F_c62a8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6868 : word) = Some W_c62a8.
Proof. vm_refl. Qed.
Lemma D_c62a8 : decode_any W_c62a8 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62ac : bv 32 := 0x00e586b3.
Lemma F_c62ac : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc686c : word) = Some W_c62ac.
Proof. vm_refl. Qed.
Lemma D_c62ac : decode_any W_c62ac = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62b0 : bv 32 := 0xfec6ae23.
Lemma F_c62b0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6870 : word) = Some W_c62b0.
Proof. vm_refl. Qed.
Lemma D_c62b0 : decode_any W_c62b0 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62b4 : bv 32 := 0x08f76063.
Lemma F_c62b4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6874 : word) = Some W_c62b4.
Proof. vm_refl. Qed.
Lemma D_c62b4 : decode_any W_c62b4 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62b8 : bv 32 := 0x00c5a223.
Lemma F_c62b8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6878 : word) = Some W_c62b8.
Proof. vm_refl. Qed.
Lemma D_c62b8 : decode_any W_c62b8 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62bc : bv 32 := 0x00c5a423.
Lemma F_c62bc : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc687c : word) = Some W_c62bc.
Proof. vm_refl. Qed.
Lemma D_c62bc : decode_any W_c62bc = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62c0 : bv 32 := 0x01900793.
Lemma F_c62c0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6880 : word) = Some W_c62c0.
Proof. vm_refl. Qed.
Lemma D_c62c0 : decode_any W_c62c0 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62c4 : bv 32 := 0xfec6aa23.
Lemma F_c62c4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6884 : word) = Some W_c62c4.
Proof. vm_refl. Qed.
Lemma D_c62c4 : decode_any W_c62c4 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62c8 : bv 32 := 0xfec6ac23.
Lemma F_c62c8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6888 : word) = Some W_c62c8.
Proof. vm_refl. Qed.
Lemma D_c62c8 : decode_any W_c62c8 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62cc : bv 32 := 0x06f76463.
Lemma F_c62cc : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc688c : word) = Some W_c62cc.
Proof. vm_refl. Qed.
Lemma D_c62cc : decode_any W_c62cc = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62d0 : bv 32 := 0x00c5a623.
Lemma F_c62d0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6890 : word) = Some W_c62d0.
Proof. vm_refl. Qed.
Lemma D_c62d0 : decode_any W_c62d0 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62d4 : bv 32 := 0x00c5a823.
Lemma F_c62d4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6894 : word) = Some W_c62d4.
Proof. vm_refl. Qed.
Lemma D_c62d4 : decode_any W_c62d4 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62d8 : bv 32 := 0x00c5aa23.
Lemma F_c62d8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc6898 : word) = Some W_c62d8.
Proof. vm_refl. Qed.
Lemma D_c62d8 : decode_any W_c62d8 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62dc : bv 32 := 0x00c5ac23.
Lemma F_c62dc : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc689c : word) = Some W_c62dc.
Proof. vm_refl. Qed.
Lemma D_c62dc : decode_any W_c62dc = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62e0 : bv 32 := 0x0045f793.
Lemma F_c62e0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc68a0 : word) = Some W_c62e0.
Proof. vm_refl. Qed.
Lemma D_c62e0 : decode_any W_c62e0 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62e4 : bv 32 := 0x02000813.
Lemma F_c62e4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc68a4 : word) = Some W_c62e4.
Proof. vm_refl. Qed.
Lemma D_c62e4 : decode_any W_c62e4 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62e8 : bv 32 := 0x01878793.
Lemma F_c62e8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc68a8 : word) = Some W_c62e8.
Proof. vm_refl. Qed.
Lemma D_c62e8 : decode_any W_c62e8 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62ec : bv 32 := 0x40f70733.
Lemma F_c62ec : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc68ac : word) = Some W_c62ec.
Proof. vm_refl. Qed.
Lemma D_c62ec : decode_any W_c62ec = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62f0 : bv 32 := 0xfec6a223.
Lemma F_c62f0 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc68b0 : word) = Some W_c62f0.
Proof. vm_refl. Qed.
Lemma D_c62f0 : decode_any W_c62f0 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62f4 : bv 32 := 0xfec6a423.
Lemma F_c62f4 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc68b4 : word) = Some W_c62f4.
Proof. vm_refl. Qed.
Lemma D_c62f4 : decode_any W_c62f4 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62f8 : bv 32 := 0xfec6a623.
Lemma F_c62f8 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc68b8 : word) = Some W_c62f8.
Proof. vm_refl. Qed.
Lemma D_c62f8 : decode_any W_c62f8 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_c62fc : bv 32 := 0xfec6a823.
Lemma F_c62fc : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc68bc : word) = Some W_c62fc.
Proof. vm_refl. Qed.
Lemma D_c62fc : decode_any W_c62fc = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6300 : bv 32 := 0x03076a63.
Lemma F_c6300 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc68c0 : word) = Some W_c6300.
Proof. vm_refl. Qed.
Lemma D_c6300 : decode_any W_c6300 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6304 : bv 32 := 0x02061613.
Lemma F_c6304 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc68c4 : word) = Some W_c6304.
Proof. vm_refl. Qed.
Lemma D_c6304 : decode_any W_c6304 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6308 : bv 32 := 0x00f585b3.
Lemma F_c6308 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc68c8 : word) = Some W_c6308.
Proof. vm_refl. Qed.
Lemma D_c6308 : decode_any W_c6308 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c630c : bv 32 := 0x02065693.
Lemma F_c630c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc68cc : word) = Some W_c630c.
Proof. vm_refl. Qed.
Lemma D_c630c : decode_any W_c630c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6310 : bv 32 := 0x00d66633.
Lemma F_c6310 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc68d0 : word) = Some W_c6310.
Proof. vm_refl. Qed.
Lemma D_c6310 : decode_any W_c6310 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6314 : bv 32 := 0x01f00693.
Lemma F_c6314 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc68d4 : word) = Some W_c6314.
Proof. vm_refl. Qed.
Lemma D_c6314 : decode_any W_c6314 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6318 : bv 32 := 0x00c5b023.
Lemma F_c6318 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc68d8 : word) = Some W_c6318.
Proof. vm_refl. Qed.
Lemma D_c6318 : decode_any W_c6318 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c631c : bv 32 := 0x00c5b423.
Lemma F_c631c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc68dc : word) = Some W_c631c.
Proof. vm_refl. Qed.
Lemma D_c631c : decode_any W_c631c = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6320 : bv 32 := 0x00c5b823.
Lemma F_c6320 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc68e0 : word) = Some W_c6320.
Proof. vm_refl. Qed.
Lemma D_c6320 : decode_any W_c6320 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6324 : bv 32 := 0x00c5bc23.
Lemma F_c6324 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc68e4 : word) = Some W_c6324.
Proof. vm_refl. Qed.
Lemma D_c6324 : decode_any W_c6324 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6328 : bv 32 := 0xfe070713.
Lemma F_c6328 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc68e8 : word) = Some W_c6328.
Proof. vm_refl. Qed.
Lemma D_c6328 : decode_any W_c6328 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_c632c : bv 32 := 0x02058593.
Lemma F_c632c : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc68ec : word) = Some W_c632c.
Proof. vm_refl. Qed.
Lemma D_c632c : decode_any W_c632c = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6330 : bv 32 := 0xfee6e4e3.
Lemma F_c6330 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc68f0 : word) = Some W_c6330.
Proof. vm_refl. Qed.
Lemma D_c6330 : decode_any W_c6330 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_c6334 : bv 32 := 0x00008067.
Lemma F_c6334 : fetch_word Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments (0xc68f4 : word) = Some W_c6334.
Proof. vm_refl. Qed.
Lemma D_c6334 : decode_any W_c6334 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Abbreviation MSEGS := Tgt_zlib_uncompress2_fuzzer_asan.M.loaded_segments.
Definition ms_base : Z := 0xc6800%Z.
Definition Fo_000 := F_c6240.
Definition Do_000 := D_c6240.
Definition Fo_004 := F_c6244.
Definition Do_004 := D_c6244.
Definition Fo_008 := F_c6248.
Definition Do_008 := D_c6248.
Definition Fo_00c := F_c624c.
Definition Do_00c := D_c624c.
Definition Fo_010 := F_c6250.
Definition Do_010 := D_c6250.
Definition Fo_014 := F_c6254.
Definition Do_014 := D_c6254.
Definition Fo_018 := F_c6258.
Definition Do_018 := D_c6258.
Definition Fo_01c := F_c625c.
Definition Do_01c := D_c625c.
Definition Fo_020 := F_c6260.
Definition Do_020 := D_c6260.
Definition Fo_024 := F_c6264.
Definition Do_024 := D_c6264.
Definition Fo_028 := F_c6268.
Definition Do_028 := D_c6268.
Definition Fo_02c := F_c626c.
Definition Do_02c := D_c626c.
Definition Fo_030 := F_c6270.
Definition Do_030 := D_c6270.
Definition Fo_034 := F_c6274.
Definition Do_034 := D_c6274.
Definition Fo_038 := F_c6278.
Definition Do_038 := D_c6278.
Definition Fo_03c := F_c627c.
Definition Do_03c := D_c627c.
Definition Fo_040 := F_c6280.
Definition Do_040 := D_c6280.
Definition Fo_044 := F_c6284.
Definition Do_044 := D_c6284.
Definition Fo_048 := F_c6288.
Definition Do_048 := D_c6288.
Definition Fo_04c := F_c628c.
Definition Do_04c := D_c628c.
Definition Fo_050 := F_c6290.
Definition Do_050 := D_c6290.
Definition Fo_054 := F_c6294.
Definition Do_054 := D_c6294.
Definition Fo_058 := F_c6298.
Definition Do_058 := D_c6298.
Definition Fo_05c := F_c629c.
Definition Do_05c := D_c629c.
Definition Fo_060 := F_c62a0.
Definition Do_060 := D_c62a0.
Definition Fo_064 := F_c62a4.
Definition Do_064 := D_c62a4.
Definition Fo_068 := F_c62a8.
Definition Do_068 := D_c62a8.
Definition Fo_06c := F_c62ac.
Definition Do_06c := D_c62ac.
Definition Fo_070 := F_c62b0.
Definition Do_070 := D_c62b0.
Definition Fo_074 := F_c62b4.
Definition Do_074 := D_c62b4.
Definition Fo_078 := F_c62b8.
Definition Do_078 := D_c62b8.
Definition Fo_07c := F_c62bc.
Definition Do_07c := D_c62bc.
Definition Fo_080 := F_c62c0.
Definition Do_080 := D_c62c0.
Definition Fo_084 := F_c62c4.
Definition Do_084 := D_c62c4.
Definition Fo_088 := F_c62c8.
Definition Do_088 := D_c62c8.
Definition Fo_08c := F_c62cc.
Definition Do_08c := D_c62cc.
Definition Fo_090 := F_c62d0.
Definition Do_090 := D_c62d0.
Definition Fo_094 := F_c62d4.
Definition Do_094 := D_c62d4.
Definition Fo_098 := F_c62d8.
Definition Do_098 := D_c62d8.
Definition Fo_09c := F_c62dc.
Definition Do_09c := D_c62dc.
Definition Fo_0a0 := F_c62e0.
Definition Do_0a0 := D_c62e0.
Definition Fo_0a4 := F_c62e4.
Definition Do_0a4 := D_c62e4.
Definition Fo_0a8 := F_c62e8.
Definition Do_0a8 := D_c62e8.
Definition Fo_0ac := F_c62ec.
Definition Do_0ac := D_c62ec.
Definition Fo_0b0 := F_c62f0.
Definition Do_0b0 := D_c62f0.
Definition Fo_0b4 := F_c62f4.
Definition Do_0b4 := D_c62f4.
Definition Fo_0b8 := F_c62f8.
Definition Do_0b8 := D_c62f8.
Definition Fo_0bc := F_c62fc.
Definition Do_0bc := D_c62fc.
Definition Fo_0c0 := F_c6300.
Definition Do_0c0 := D_c6300.
Definition Fo_0c4 := F_c6304.
Definition Do_0c4 := D_c6304.
Definition Fo_0c8 := F_c6308.
Definition Do_0c8 := D_c6308.
Definition Fo_0cc := F_c630c.
Definition Do_0cc := D_c630c.
Definition Fo_0d0 := F_c6310.
Definition Do_0d0 := D_c6310.
Definition Fo_0d4 := F_c6314.
Definition Do_0d4 := D_c6314.
Definition Fo_0d8 := F_c6318.
Definition Do_0d8 := D_c6318.
Definition Fo_0dc := F_c631c.
Definition Do_0dc := D_c631c.
Definition Fo_0e0 := F_c6320.
Definition Do_0e0 := D_c6320.
Definition Fo_0e4 := F_c6324.
Definition Do_0e4 := D_c6324.
Definition Fo_0e8 := F_c6328.
Definition Do_0e8 := D_c6328.
Definition Fo_0ec := F_c632c.
Definition Do_0ec := D_c632c.
Definition Fo_0f0 := F_c6330.
Definition Do_0f0 := D_c6330.
Definition Fo_0f4 := F_c6334.
Definition Do_0f4 := D_c6334.
