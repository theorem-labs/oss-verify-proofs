(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress2_fuzzer_both.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_c76ec : bv 32 := 0x0e060a63.
Lemma F_c76ec : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d0c : word) = Some W_c76ec.
Proof. vm_refl. Qed.
Lemma D_c76ec : decode_any W_c76ec = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76f0 : bv 32 := 0x00b50023.
Lemma F_c76f0 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d10 : word) = Some W_c76f0.
Proof. vm_refl. Qed.
Lemma D_c76f0 : decode_any W_c76f0 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76f4 : bv 32 := 0x00c506b3.
Lemma F_c76f4 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d14 : word) = Some W_c76f4.
Proof. vm_refl. Qed.
Lemma D_c76f4 : decode_any W_c76f4 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76f8 : bv 32 := 0x00300713.
Lemma F_c76f8 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d18 : word) = Some W_c76f8.
Proof. vm_refl. Qed.
Lemma D_c76f8 : decode_any W_c76f8 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c76fc : bv 32 := 0xfeb68fa3.
Lemma F_c76fc : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d1c : word) = Some W_c76fc.
Proof. vm_refl. Qed.
Lemma D_c76fc : decode_any W_c76fc = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7700 : bv 32 := 0x0ee66063.
Lemma F_c7700 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d20 : word) = Some W_c7700.
Proof. vm_refl. Qed.
Lemma D_c7700 : decode_any W_c7700 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7704 : bv 32 := 0x00b500a3.
Lemma F_c7704 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d24 : word) = Some W_c7704.
Proof. vm_refl. Qed.
Lemma D_c7704 : decode_any W_c7704 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7708 : bv 32 := 0x00b50123.
Lemma F_c7708 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d28 : word) = Some W_c7708.
Proof. vm_refl. Qed.
Lemma D_c7708 : decode_any W_c7708 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c770c : bv 32 := 0x00700713.
Lemma F_c770c : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d2c : word) = Some W_c770c.
Proof. vm_refl. Qed.
Lemma D_c770c : decode_any W_c770c = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7710 : bv 32 := 0xfeb68ea3.
Lemma F_c7710 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d30 : word) = Some W_c7710.
Proof. vm_refl. Qed.
Lemma D_c7710 : decode_any W_c7710 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7714 : bv 32 := 0xfeb68f23.
Lemma F_c7714 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d34 : word) = Some W_c7714.
Proof. vm_refl. Qed.
Lemma D_c7714 : decode_any W_c7714 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7718 : bv 32 := 0x0ce66463.
Lemma F_c7718 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d38 : word) = Some W_c7718.
Proof. vm_refl. Qed.
Lemma D_c7718 : decode_any W_c7718 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_c771c : bv 32 := 0x00b501a3.
Lemma F_c771c : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d3c : word) = Some W_c771c.
Proof. vm_refl. Qed.
Lemma D_c771c : decode_any W_c771c = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7720 : bv 32 := 0x00900793.
Lemma F_c7720 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d40 : word) = Some W_c7720.
Proof. vm_refl. Qed.
Lemma D_c7720 : decode_any W_c7720 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7724 : bv 32 := 0xfeb68e23.
Lemma F_c7724 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d44 : word) = Some W_c7724.
Proof. vm_refl. Qed.
Lemma D_c7724 : decode_any W_c7724 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7728 : bv 32 := 0x0af66c63.
Lemma F_c7728 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d48 : word) = Some W_c7728.
Proof. vm_refl. Qed.
Lemma D_c7728 : decode_any W_c7728 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_c772c : bv 32 := 0x40a006bb.
Lemma F_c772c : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d4c : word) = Some W_c772c.
Proof. vm_refl. Qed.
Lemma D_c772c : decode_any W_c772c = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7730 : bv 32 := 0x03859813.
Lemma F_c7730 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d50 : word) = Some W_c7730.
Proof. vm_refl. Qed.
Lemma D_c7730 : decode_any W_c7730 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7734 : bv 32 := 0x101015b7.
Lemma F_c7734 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d54 : word) = Some W_c7734.
Proof. vm_refl. Qed.
Lemma D_c7734 : decode_any W_c7734 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7738 : bv 32 := 0x0036f693.
Lemma F_c7738 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d58 : word) = Some W_c7738.
Proof. vm_refl. Qed.
Lemma D_c7738 : decode_any W_c7738 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c773c : bv 32 := 0x00459713.
Lemma F_c773c : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d5c : word) = Some W_c773c.
Proof. vm_refl. Qed.
Lemma D_c773c : decode_any W_c773c = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7740 : bv 32 := 0x40d60633.
Lemma F_c7740 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d60 : word) = Some W_c7740.
Proof. vm_refl. Qed.
Lemma D_c7740 : decode_any W_c7740 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7744 : bv 32 := 0x00d505b3.
Lemma F_c7744 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d64 : word) = Some W_c7744.
Proof. vm_refl. Qed.
Lemma D_c7744 : decode_any W_c7744 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7748 : bv 32 := 0x10070693.
Lemma F_c7748 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d68 : word) = Some W_c7748.
Proof. vm_refl. Qed.
Lemma D_c7748 : decode_any W_c7748 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_c774c : bv 32 := 0xffc67713.
Lemma F_c774c : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d6c : word) = Some W_c774c.
Proof. vm_refl. Qed.
Lemma D_c774c : decode_any W_c774c = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7750 : bv 32 := 0x02d83633.
Lemma F_c7750 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d70 : word) = Some W_c7750.
Proof. vm_refl. Qed.
Lemma D_c7750 : decode_any W_c7750 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7754 : bv 32 := 0x00c5a023.
Lemma F_c7754 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d74 : word) = Some W_c7754.
Proof. vm_refl. Qed.
Lemma D_c7754 : decode_any W_c7754 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7758 : bv 32 := 0x00e586b3.
Lemma F_c7758 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d78 : word) = Some W_c7758.
Proof. vm_refl. Qed.
Lemma D_c7758 : decode_any W_c7758 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_c775c : bv 32 := 0xfec6ae23.
Lemma F_c775c : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d7c : word) = Some W_c775c.
Proof. vm_refl. Qed.
Lemma D_c775c : decode_any W_c775c = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7760 : bv 32 := 0x08f76063.
Lemma F_c7760 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d80 : word) = Some W_c7760.
Proof. vm_refl. Qed.
Lemma D_c7760 : decode_any W_c7760 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7764 : bv 32 := 0x00c5a223.
Lemma F_c7764 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d84 : word) = Some W_c7764.
Proof. vm_refl. Qed.
Lemma D_c7764 : decode_any W_c7764 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7768 : bv 32 := 0x00c5a423.
Lemma F_c7768 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d88 : word) = Some W_c7768.
Proof. vm_refl. Qed.
Lemma D_c7768 : decode_any W_c7768 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c776c : bv 32 := 0x01900793.
Lemma F_c776c : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d8c : word) = Some W_c776c.
Proof. vm_refl. Qed.
Lemma D_c776c : decode_any W_c776c = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7770 : bv 32 := 0xfec6aa23.
Lemma F_c7770 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d90 : word) = Some W_c7770.
Proof. vm_refl. Qed.
Lemma D_c7770 : decode_any W_c7770 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7774 : bv 32 := 0xfec6ac23.
Lemma F_c7774 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d94 : word) = Some W_c7774.
Proof. vm_refl. Qed.
Lemma D_c7774 : decode_any W_c7774 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7778 : bv 32 := 0x06f76463.
Lemma F_c7778 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d98 : word) = Some W_c7778.
Proof. vm_refl. Qed.
Lemma D_c7778 : decode_any W_c7778 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_c777c : bv 32 := 0x00c5a623.
Lemma F_c777c : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7d9c : word) = Some W_c777c.
Proof. vm_refl. Qed.
Lemma D_c777c : decode_any W_c777c = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7780 : bv 32 := 0x00c5a823.
Lemma F_c7780 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7da0 : word) = Some W_c7780.
Proof. vm_refl. Qed.
Lemma D_c7780 : decode_any W_c7780 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7784 : bv 32 := 0x00c5aa23.
Lemma F_c7784 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7da4 : word) = Some W_c7784.
Proof. vm_refl. Qed.
Lemma D_c7784 : decode_any W_c7784 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7788 : bv 32 := 0x00c5ac23.
Lemma F_c7788 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7da8 : word) = Some W_c7788.
Proof. vm_refl. Qed.
Lemma D_c7788 : decode_any W_c7788 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c778c : bv 32 := 0x0045f793.
Lemma F_c778c : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7dac : word) = Some W_c778c.
Proof. vm_refl. Qed.
Lemma D_c778c : decode_any W_c778c = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7790 : bv 32 := 0x02000813.
Lemma F_c7790 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7db0 : word) = Some W_c7790.
Proof. vm_refl. Qed.
Lemma D_c7790 : decode_any W_c7790 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7794 : bv 32 := 0x01878793.
Lemma F_c7794 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7db4 : word) = Some W_c7794.
Proof. vm_refl. Qed.
Lemma D_c7794 : decode_any W_c7794 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c7798 : bv 32 := 0x40f70733.
Lemma F_c7798 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7db8 : word) = Some W_c7798.
Proof. vm_refl. Qed.
Lemma D_c7798 : decode_any W_c7798 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c779c : bv 32 := 0xfec6a223.
Lemma F_c779c : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7dbc : word) = Some W_c779c.
Proof. vm_refl. Qed.
Lemma D_c779c : decode_any W_c779c = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77a0 : bv 32 := 0xfec6a423.
Lemma F_c77a0 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7dc0 : word) = Some W_c77a0.
Proof. vm_refl. Qed.
Lemma D_c77a0 : decode_any W_c77a0 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77a4 : bv 32 := 0xfec6a623.
Lemma F_c77a4 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7dc4 : word) = Some W_c77a4.
Proof. vm_refl. Qed.
Lemma D_c77a4 : decode_any W_c77a4 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77a8 : bv 32 := 0xfec6a823.
Lemma F_c77a8 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7dc8 : word) = Some W_c77a8.
Proof. vm_refl. Qed.
Lemma D_c77a8 : decode_any W_c77a8 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77ac : bv 32 := 0x03076a63.
Lemma F_c77ac : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7dcc : word) = Some W_c77ac.
Proof. vm_refl. Qed.
Lemma D_c77ac : decode_any W_c77ac = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77b0 : bv 32 := 0x02061613.
Lemma F_c77b0 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7dd0 : word) = Some W_c77b0.
Proof. vm_refl. Qed.
Lemma D_c77b0 : decode_any W_c77b0 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77b4 : bv 32 := 0x00f585b3.
Lemma F_c77b4 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7dd4 : word) = Some W_c77b4.
Proof. vm_refl. Qed.
Lemma D_c77b4 : decode_any W_c77b4 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77b8 : bv 32 := 0x02065693.
Lemma F_c77b8 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7dd8 : word) = Some W_c77b8.
Proof. vm_refl. Qed.
Lemma D_c77b8 : decode_any W_c77b8 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77bc : bv 32 := 0x00d66633.
Lemma F_c77bc : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7ddc : word) = Some W_c77bc.
Proof. vm_refl. Qed.
Lemma D_c77bc : decode_any W_c77bc = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77c0 : bv 32 := 0x01f00693.
Lemma F_c77c0 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7de0 : word) = Some W_c77c0.
Proof. vm_refl. Qed.
Lemma D_c77c0 : decode_any W_c77c0 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77c4 : bv 32 := 0x00c5b023.
Lemma F_c77c4 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7de4 : word) = Some W_c77c4.
Proof. vm_refl. Qed.
Lemma D_c77c4 : decode_any W_c77c4 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77c8 : bv 32 := 0x00c5b423.
Lemma F_c77c8 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7de8 : word) = Some W_c77c8.
Proof. vm_refl. Qed.
Lemma D_c77c8 : decode_any W_c77c8 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77cc : bv 32 := 0x00c5b823.
Lemma F_c77cc : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7dec : word) = Some W_c77cc.
Proof. vm_refl. Qed.
Lemma D_c77cc : decode_any W_c77cc = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77d0 : bv 32 := 0x00c5bc23.
Lemma F_c77d0 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7df0 : word) = Some W_c77d0.
Proof. vm_refl. Qed.
Lemma D_c77d0 : decode_any W_c77d0 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77d4 : bv 32 := 0xfe070713.
Lemma F_c77d4 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7df4 : word) = Some W_c77d4.
Proof. vm_refl. Qed.
Lemma D_c77d4 : decode_any W_c77d4 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77d8 : bv 32 := 0x02058593.
Lemma F_c77d8 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7df8 : word) = Some W_c77d8.
Proof. vm_refl. Qed.
Lemma D_c77d8 : decode_any W_c77d8 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77dc : bv 32 := 0xfee6e4e3.
Lemma F_c77dc : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7dfc : word) = Some W_c77dc.
Proof. vm_refl. Qed.
Lemma D_c77dc : decode_any W_c77dc = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_c77e0 : bv 32 := 0x00008067.
Lemma F_c77e0 : fetch_word Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments (0xc7e00 : word) = Some W_c77e0.
Proof. vm_refl. Qed.
Lemma D_c77e0 : decode_any W_c77e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Abbreviation MSEGS := Tgt_zlib_uncompress2_fuzzer_both.M.loaded_segments.
Definition ms_base : Z := 0xc7d0c%Z.
Definition Fo_000 := F_c76ec.
Definition Do_000 := D_c76ec.
Definition Fo_004 := F_c76f0.
Definition Do_004 := D_c76f0.
Definition Fo_008 := F_c76f4.
Definition Do_008 := D_c76f4.
Definition Fo_00c := F_c76f8.
Definition Do_00c := D_c76f8.
Definition Fo_010 := F_c76fc.
Definition Do_010 := D_c76fc.
Definition Fo_014 := F_c7700.
Definition Do_014 := D_c7700.
Definition Fo_018 := F_c7704.
Definition Do_018 := D_c7704.
Definition Fo_01c := F_c7708.
Definition Do_01c := D_c7708.
Definition Fo_020 := F_c770c.
Definition Do_020 := D_c770c.
Definition Fo_024 := F_c7710.
Definition Do_024 := D_c7710.
Definition Fo_028 := F_c7714.
Definition Do_028 := D_c7714.
Definition Fo_02c := F_c7718.
Definition Do_02c := D_c7718.
Definition Fo_030 := F_c771c.
Definition Do_030 := D_c771c.
Definition Fo_034 := F_c7720.
Definition Do_034 := D_c7720.
Definition Fo_038 := F_c7724.
Definition Do_038 := D_c7724.
Definition Fo_03c := F_c7728.
Definition Do_03c := D_c7728.
Definition Fo_040 := F_c772c.
Definition Do_040 := D_c772c.
Definition Fo_044 := F_c7730.
Definition Do_044 := D_c7730.
Definition Fo_048 := F_c7734.
Definition Do_048 := D_c7734.
Definition Fo_04c := F_c7738.
Definition Do_04c := D_c7738.
Definition Fo_050 := F_c773c.
Definition Do_050 := D_c773c.
Definition Fo_054 := F_c7740.
Definition Do_054 := D_c7740.
Definition Fo_058 := F_c7744.
Definition Do_058 := D_c7744.
Definition Fo_05c := F_c7748.
Definition Do_05c := D_c7748.
Definition Fo_060 := F_c774c.
Definition Do_060 := D_c774c.
Definition Fo_064 := F_c7750.
Definition Do_064 := D_c7750.
Definition Fo_068 := F_c7754.
Definition Do_068 := D_c7754.
Definition Fo_06c := F_c7758.
Definition Do_06c := D_c7758.
Definition Fo_070 := F_c775c.
Definition Do_070 := D_c775c.
Definition Fo_074 := F_c7760.
Definition Do_074 := D_c7760.
Definition Fo_078 := F_c7764.
Definition Do_078 := D_c7764.
Definition Fo_07c := F_c7768.
Definition Do_07c := D_c7768.
Definition Fo_080 := F_c776c.
Definition Do_080 := D_c776c.
Definition Fo_084 := F_c7770.
Definition Do_084 := D_c7770.
Definition Fo_088 := F_c7774.
Definition Do_088 := D_c7774.
Definition Fo_08c := F_c7778.
Definition Do_08c := D_c7778.
Definition Fo_090 := F_c777c.
Definition Do_090 := D_c777c.
Definition Fo_094 := F_c7780.
Definition Do_094 := D_c7780.
Definition Fo_098 := F_c7784.
Definition Do_098 := D_c7784.
Definition Fo_09c := F_c7788.
Definition Do_09c := D_c7788.
Definition Fo_0a0 := F_c778c.
Definition Do_0a0 := D_c778c.
Definition Fo_0a4 := F_c7790.
Definition Do_0a4 := D_c7790.
Definition Fo_0a8 := F_c7794.
Definition Do_0a8 := D_c7794.
Definition Fo_0ac := F_c7798.
Definition Do_0ac := D_c7798.
Definition Fo_0b0 := F_c779c.
Definition Do_0b0 := D_c779c.
Definition Fo_0b4 := F_c77a0.
Definition Do_0b4 := D_c77a0.
Definition Fo_0b8 := F_c77a4.
Definition Do_0b8 := D_c77a4.
Definition Fo_0bc := F_c77a8.
Definition Do_0bc := D_c77a8.
Definition Fo_0c0 := F_c77ac.
Definition Do_0c0 := D_c77ac.
Definition Fo_0c4 := F_c77b0.
Definition Do_0c4 := D_c77b0.
Definition Fo_0c8 := F_c77b4.
Definition Do_0c8 := D_c77b4.
Definition Fo_0cc := F_c77b8.
Definition Do_0cc := D_c77b8.
Definition Fo_0d0 := F_c77bc.
Definition Do_0d0 := D_c77bc.
Definition Fo_0d4 := F_c77c0.
Definition Do_0d4 := D_c77c0.
Definition Fo_0d8 := F_c77c4.
Definition Do_0d8 := D_c77c4.
Definition Fo_0dc := F_c77c8.
Definition Do_0dc := D_c77c8.
Definition Fo_0e0 := F_c77cc.
Definition Do_0e0 := D_c77cc.
Definition Fo_0e4 := F_c77d0.
Definition Do_0e4 := D_c77d0.
Definition Fo_0e8 := F_c77d4.
Definition Do_0e8 := D_c77d4.
Definition Fo_0ec := F_c77d8.
Definition Do_0ec := D_c77d8.
Definition Fo_0f0 := F_c77dc.
Definition Do_0f0 := D_c77dc.
Definition Fo_0f4 := F_c77e0.
Definition Do_0f4 := D_c77e0.
