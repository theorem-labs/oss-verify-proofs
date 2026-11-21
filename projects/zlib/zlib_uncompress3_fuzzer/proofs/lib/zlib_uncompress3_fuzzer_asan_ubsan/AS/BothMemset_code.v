(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.World Require Import Tgt_zlib_uncompress3_fuzzer_both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_c77d8 : bv 32 := 0x0e060a63.
Lemma F_c77d8 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7df8 : word) = Some W_c77d8.
Proof. vm_refl. Qed.
Lemma D_c77d8 : decode_any W_c77d8 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77dc : bv 32 := 0x00b50023.
Lemma F_c77dc : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7dfc : word) = Some W_c77dc.
Proof. vm_refl. Qed.
Lemma D_c77dc : decode_any W_c77dc = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77e0 : bv 32 := 0x00c506b3.
Lemma F_c77e0 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e00 : word) = Some W_c77e0.
Proof. vm_refl. Qed.
Lemma D_c77e0 : decode_any W_c77e0 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77e4 : bv 32 := 0x00300713.
Lemma F_c77e4 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e04 : word) = Some W_c77e4.
Proof. vm_refl. Qed.
Lemma D_c77e4 : decode_any W_c77e4 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77e8 : bv 32 := 0xfeb68fa3.
Lemma F_c77e8 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e08 : word) = Some W_c77e8.
Proof. vm_refl. Qed.
Lemma D_c77e8 : decode_any W_c77e8 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77ec : bv 32 := 0x0ee66063.
Lemma F_c77ec : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e0c : word) = Some W_c77ec.
Proof. vm_refl. Qed.
Lemma D_c77ec : decode_any W_c77ec = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77f0 : bv 32 := 0x00b500a3.
Lemma F_c77f0 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e10 : word) = Some W_c77f0.
Proof. vm_refl. Qed.
Lemma D_c77f0 : decode_any W_c77f0 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77f4 : bv 32 := 0x00b50123.
Lemma F_c77f4 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e14 : word) = Some W_c77f4.
Proof. vm_refl. Qed.
Lemma D_c77f4 : decode_any W_c77f4 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77f8 : bv 32 := 0x00700713.
Lemma F_c77f8 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e18 : word) = Some W_c77f8.
Proof. vm_refl. Qed.
Lemma D_c77f8 : decode_any W_c77f8 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77fc : bv 32 := 0xfeb68ea3.
Lemma F_c77fc : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e1c : word) = Some W_c77fc.
Proof. vm_refl. Qed.
Lemma D_c77fc : decode_any W_c77fc = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7800 : bv 32 := 0xfeb68f23.
Lemma F_c7800 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e20 : word) = Some W_c7800.
Proof. vm_refl. Qed.
Lemma D_c7800 : decode_any W_c7800 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7804 : bv 32 := 0x0ce66463.
Lemma F_c7804 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e24 : word) = Some W_c7804.
Proof. vm_refl. Qed.
Lemma D_c7804 : decode_any W_c7804 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7808 : bv 32 := 0x00b501a3.
Lemma F_c7808 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e28 : word) = Some W_c7808.
Proof. vm_refl. Qed.
Lemma D_c7808 : decode_any W_c7808 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c780c : bv 32 := 0x00900793.
Lemma F_c780c : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e2c : word) = Some W_c780c.
Proof. vm_refl. Qed.
Lemma D_c780c : decode_any W_c780c = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7810 : bv 32 := 0xfeb68e23.
Lemma F_c7810 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e30 : word) = Some W_c7810.
Proof. vm_refl. Qed.
Lemma D_c7810 : decode_any W_c7810 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7814 : bv 32 := 0x0af66c63.
Lemma F_c7814 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e34 : word) = Some W_c7814.
Proof. vm_refl. Qed.
Lemma D_c7814 : decode_any W_c7814 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7818 : bv 32 := 0x40a006bb.
Lemma F_c7818 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e38 : word) = Some W_c7818.
Proof. vm_refl. Qed.
Lemma D_c7818 : decode_any W_c7818 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c781c : bv 32 := 0x03859813.
Lemma F_c781c : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e3c : word) = Some W_c781c.
Proof. vm_refl. Qed.
Lemma D_c781c : decode_any W_c781c = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7820 : bv 32 := 0x101015b7.
Lemma F_c7820 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e40 : word) = Some W_c7820.
Proof. vm_refl. Qed.
Lemma D_c7820 : decode_any W_c7820 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7824 : bv 32 := 0x0036f693.
Lemma F_c7824 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e44 : word) = Some W_c7824.
Proof. vm_refl. Qed.
Lemma D_c7824 : decode_any W_c7824 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7828 : bv 32 := 0x00459713.
Lemma F_c7828 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e48 : word) = Some W_c7828.
Proof. vm_refl. Qed.
Lemma D_c7828 : decode_any W_c7828 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c782c : bv 32 := 0x40d60633.
Lemma F_c782c : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e4c : word) = Some W_c782c.
Proof. vm_refl. Qed.
Lemma D_c782c : decode_any W_c782c = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7830 : bv 32 := 0x00d505b3.
Lemma F_c7830 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e50 : word) = Some W_c7830.
Proof. vm_refl. Qed.
Lemma D_c7830 : decode_any W_c7830 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7834 : bv 32 := 0x10070693.
Lemma F_c7834 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e54 : word) = Some W_c7834.
Proof. vm_refl. Qed.
Lemma D_c7834 : decode_any W_c7834 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7838 : bv 32 := 0xffc67713.
Lemma F_c7838 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e58 : word) = Some W_c7838.
Proof. vm_refl. Qed.
Lemma D_c7838 : decode_any W_c7838 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c783c : bv 32 := 0x02d83633.
Lemma F_c783c : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e5c : word) = Some W_c783c.
Proof. vm_refl. Qed.
Lemma D_c783c : decode_any W_c783c = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7840 : bv 32 := 0x00c5a023.
Lemma F_c7840 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e60 : word) = Some W_c7840.
Proof. vm_refl. Qed.
Lemma D_c7840 : decode_any W_c7840 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7844 : bv 32 := 0x00e586b3.
Lemma F_c7844 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e64 : word) = Some W_c7844.
Proof. vm_refl. Qed.
Lemma D_c7844 : decode_any W_c7844 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7848 : bv 32 := 0xfec6ae23.
Lemma F_c7848 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e68 : word) = Some W_c7848.
Proof. vm_refl. Qed.
Lemma D_c7848 : decode_any W_c7848 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c784c : bv 32 := 0x08f76063.
Lemma F_c784c : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e6c : word) = Some W_c784c.
Proof. vm_refl. Qed.
Lemma D_c784c : decode_any W_c784c = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7850 : bv 32 := 0x00c5a223.
Lemma F_c7850 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e70 : word) = Some W_c7850.
Proof. vm_refl. Qed.
Lemma D_c7850 : decode_any W_c7850 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7854 : bv 32 := 0x00c5a423.
Lemma F_c7854 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e74 : word) = Some W_c7854.
Proof. vm_refl. Qed.
Lemma D_c7854 : decode_any W_c7854 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7858 : bv 32 := 0x01900793.
Lemma F_c7858 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e78 : word) = Some W_c7858.
Proof. vm_refl. Qed.
Lemma D_c7858 : decode_any W_c7858 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_c785c : bv 32 := 0xfec6aa23.
Lemma F_c785c : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e7c : word) = Some W_c785c.
Proof. vm_refl. Qed.
Lemma D_c785c : decode_any W_c785c = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7860 : bv 32 := 0xfec6ac23.
Lemma F_c7860 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e80 : word) = Some W_c7860.
Proof. vm_refl. Qed.
Lemma D_c7860 : decode_any W_c7860 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7864 : bv 32 := 0x06f76463.
Lemma F_c7864 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e84 : word) = Some W_c7864.
Proof. vm_refl. Qed.
Lemma D_c7864 : decode_any W_c7864 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7868 : bv 32 := 0x00c5a623.
Lemma F_c7868 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e88 : word) = Some W_c7868.
Proof. vm_refl. Qed.
Lemma D_c7868 : decode_any W_c7868 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c786c : bv 32 := 0x00c5a823.
Lemma F_c786c : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e8c : word) = Some W_c786c.
Proof. vm_refl. Qed.
Lemma D_c786c : decode_any W_c786c = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7870 : bv 32 := 0x00c5aa23.
Lemma F_c7870 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e90 : word) = Some W_c7870.
Proof. vm_refl. Qed.
Lemma D_c7870 : decode_any W_c7870 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7874 : bv 32 := 0x00c5ac23.
Lemma F_c7874 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e94 : word) = Some W_c7874.
Proof. vm_refl. Qed.
Lemma D_c7874 : decode_any W_c7874 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7878 : bv 32 := 0x0045f793.
Lemma F_c7878 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e98 : word) = Some W_c7878.
Proof. vm_refl. Qed.
Lemma D_c7878 : decode_any W_c7878 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c787c : bv 32 := 0x02000813.
Lemma F_c787c : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7e9c : word) = Some W_c787c.
Proof. vm_refl. Qed.
Lemma D_c787c : decode_any W_c787c = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7880 : bv 32 := 0x01878793.
Lemma F_c7880 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7ea0 : word) = Some W_c7880.
Proof. vm_refl. Qed.
Lemma D_c7880 : decode_any W_c7880 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7884 : bv 32 := 0x40f70733.
Lemma F_c7884 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7ea4 : word) = Some W_c7884.
Proof. vm_refl. Qed.
Lemma D_c7884 : decode_any W_c7884 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7888 : bv 32 := 0xfec6a223.
Lemma F_c7888 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7ea8 : word) = Some W_c7888.
Proof. vm_refl. Qed.
Lemma D_c7888 : decode_any W_c7888 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_c788c : bv 32 := 0xfec6a423.
Lemma F_c788c : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7eac : word) = Some W_c788c.
Proof. vm_refl. Qed.
Lemma D_c788c : decode_any W_c788c = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7890 : bv 32 := 0xfec6a623.
Lemma F_c7890 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7eb0 : word) = Some W_c7890.
Proof. vm_refl. Qed.
Lemma D_c7890 : decode_any W_c7890 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7894 : bv 32 := 0xfec6a823.
Lemma F_c7894 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7eb4 : word) = Some W_c7894.
Proof. vm_refl. Qed.
Lemma D_c7894 : decode_any W_c7894 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7898 : bv 32 := 0x03076a63.
Lemma F_c7898 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7eb8 : word) = Some W_c7898.
Proof. vm_refl. Qed.
Lemma D_c7898 : decode_any W_c7898 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_c789c : bv 32 := 0x02061613.
Lemma F_c789c : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7ebc : word) = Some W_c789c.
Proof. vm_refl. Qed.
Lemma D_c789c : decode_any W_c789c = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c78a0 : bv 32 := 0x00f585b3.
Lemma F_c78a0 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7ec0 : word) = Some W_c78a0.
Proof. vm_refl. Qed.
Lemma D_c78a0 : decode_any W_c78a0 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c78a4 : bv 32 := 0x02065693.
Lemma F_c78a4 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7ec4 : word) = Some W_c78a4.
Proof. vm_refl. Qed.
Lemma D_c78a4 : decode_any W_c78a4 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c78a8 : bv 32 := 0x00d66633.
Lemma F_c78a8 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7ec8 : word) = Some W_c78a8.
Proof. vm_refl. Qed.
Lemma D_c78a8 : decode_any W_c78a8 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c78ac : bv 32 := 0x01f00693.
Lemma F_c78ac : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7ecc : word) = Some W_c78ac.
Proof. vm_refl. Qed.
Lemma D_c78ac : decode_any W_c78ac = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_c78b0 : bv 32 := 0x00c5b023.
Lemma F_c78b0 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7ed0 : word) = Some W_c78b0.
Proof. vm_refl. Qed.
Lemma D_c78b0 : decode_any W_c78b0 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c78b4 : bv 32 := 0x00c5b423.
Lemma F_c78b4 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7ed4 : word) = Some W_c78b4.
Proof. vm_refl. Qed.
Lemma D_c78b4 : decode_any W_c78b4 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c78b8 : bv 32 := 0x00c5b823.
Lemma F_c78b8 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7ed8 : word) = Some W_c78b8.
Proof. vm_refl. Qed.
Lemma D_c78b8 : decode_any W_c78b8 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c78bc : bv 32 := 0x00c5bc23.
Lemma F_c78bc : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7edc : word) = Some W_c78bc.
Proof. vm_refl. Qed.
Lemma D_c78bc : decode_any W_c78bc = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c78c0 : bv 32 := 0xfe070713.
Lemma F_c78c0 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7ee0 : word) = Some W_c78c0.
Proof. vm_refl. Qed.
Lemma D_c78c0 : decode_any W_c78c0 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_c78c4 : bv 32 := 0x02058593.
Lemma F_c78c4 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7ee4 : word) = Some W_c78c4.
Proof. vm_refl. Qed.
Lemma D_c78c4 : decode_any W_c78c4 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c78c8 : bv 32 := 0xfee6e4e3.
Lemma F_c78c8 : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7ee8 : word) = Some W_c78c8.
Proof. vm_refl. Qed.
Lemma D_c78c8 : decode_any W_c78c8 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_c78cc : bv 32 := 0x00008067.
Lemma F_c78cc : fetch_word Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments (0xc7eec : word) = Some W_c78cc.
Proof. vm_refl. Qed.
Lemma D_c78cc : decode_any W_c78cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Abbreviation MSEGS := Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments.
Definition ms_base : Z := 0xc7df8%Z.
Definition Fo_000 := F_c77d8.
Definition Do_000 := D_c77d8.
Definition Fo_004 := F_c77dc.
Definition Do_004 := D_c77dc.
Definition Fo_008 := F_c77e0.
Definition Do_008 := D_c77e0.
Definition Fo_00c := F_c77e4.
Definition Do_00c := D_c77e4.
Definition Fo_010 := F_c77e8.
Definition Do_010 := D_c77e8.
Definition Fo_014 := F_c77ec.
Definition Do_014 := D_c77ec.
Definition Fo_018 := F_c77f0.
Definition Do_018 := D_c77f0.
Definition Fo_01c := F_c77f4.
Definition Do_01c := D_c77f4.
Definition Fo_020 := F_c77f8.
Definition Do_020 := D_c77f8.
Definition Fo_024 := F_c77fc.
Definition Do_024 := D_c77fc.
Definition Fo_028 := F_c7800.
Definition Do_028 := D_c7800.
Definition Fo_02c := F_c7804.
Definition Do_02c := D_c7804.
Definition Fo_030 := F_c7808.
Definition Do_030 := D_c7808.
Definition Fo_034 := F_c780c.
Definition Do_034 := D_c780c.
Definition Fo_038 := F_c7810.
Definition Do_038 := D_c7810.
Definition Fo_03c := F_c7814.
Definition Do_03c := D_c7814.
Definition Fo_040 := F_c7818.
Definition Do_040 := D_c7818.
Definition Fo_044 := F_c781c.
Definition Do_044 := D_c781c.
Definition Fo_048 := F_c7820.
Definition Do_048 := D_c7820.
Definition Fo_04c := F_c7824.
Definition Do_04c := D_c7824.
Definition Fo_050 := F_c7828.
Definition Do_050 := D_c7828.
Definition Fo_054 := F_c782c.
Definition Do_054 := D_c782c.
Definition Fo_058 := F_c7830.
Definition Do_058 := D_c7830.
Definition Fo_05c := F_c7834.
Definition Do_05c := D_c7834.
Definition Fo_060 := F_c7838.
Definition Do_060 := D_c7838.
Definition Fo_064 := F_c783c.
Definition Do_064 := D_c783c.
Definition Fo_068 := F_c7840.
Definition Do_068 := D_c7840.
Definition Fo_06c := F_c7844.
Definition Do_06c := D_c7844.
Definition Fo_070 := F_c7848.
Definition Do_070 := D_c7848.
Definition Fo_074 := F_c784c.
Definition Do_074 := D_c784c.
Definition Fo_078 := F_c7850.
Definition Do_078 := D_c7850.
Definition Fo_07c := F_c7854.
Definition Do_07c := D_c7854.
Definition Fo_080 := F_c7858.
Definition Do_080 := D_c7858.
Definition Fo_084 := F_c785c.
Definition Do_084 := D_c785c.
Definition Fo_088 := F_c7860.
Definition Do_088 := D_c7860.
Definition Fo_08c := F_c7864.
Definition Do_08c := D_c7864.
Definition Fo_090 := F_c7868.
Definition Do_090 := D_c7868.
Definition Fo_094 := F_c786c.
Definition Do_094 := D_c786c.
Definition Fo_098 := F_c7870.
Definition Do_098 := D_c7870.
Definition Fo_09c := F_c7874.
Definition Do_09c := D_c7874.
Definition Fo_0a0 := F_c7878.
Definition Do_0a0 := D_c7878.
Definition Fo_0a4 := F_c787c.
Definition Do_0a4 := D_c787c.
Definition Fo_0a8 := F_c7880.
Definition Do_0a8 := D_c7880.
Definition Fo_0ac := F_c7884.
Definition Do_0ac := D_c7884.
Definition Fo_0b0 := F_c7888.
Definition Do_0b0 := D_c7888.
Definition Fo_0b4 := F_c788c.
Definition Do_0b4 := D_c788c.
Definition Fo_0b8 := F_c7890.
Definition Do_0b8 := D_c7890.
Definition Fo_0bc := F_c7894.
Definition Do_0bc := D_c7894.
Definition Fo_0c0 := F_c7898.
Definition Do_0c0 := D_c7898.
Definition Fo_0c4 := F_c789c.
Definition Do_0c4 := D_c789c.
Definition Fo_0c8 := F_c78a0.
Definition Do_0c8 := D_c78a0.
Definition Fo_0cc := F_c78a4.
Definition Do_0cc := D_c78a4.
Definition Fo_0d0 := F_c78a8.
Definition Do_0d0 := D_c78a8.
Definition Fo_0d4 := F_c78ac.
Definition Do_0d4 := D_c78ac.
Definition Fo_0d8 := F_c78b0.
Definition Do_0d8 := D_c78b0.
Definition Fo_0dc := F_c78b4.
Definition Do_0dc := D_c78b4.
Definition Fo_0e0 := F_c78b8.
Definition Do_0e0 := D_c78b8.
Definition Fo_0e4 := F_c78bc.
Definition Do_0e4 := D_c78bc.
Definition Fo_0e8 := F_c78c0.
Definition Do_0e8 := D_c78c0.
Definition Fo_0ec := F_c78c4.
Definition Do_0ec := D_c78c4.
Definition Fo_0f0 := F_c78c8.
Definition Do_0f0 := D_c78c8.
Definition Fo_0f4 := F_c78cc.
Definition Do_0f4 := D_c78cc.
