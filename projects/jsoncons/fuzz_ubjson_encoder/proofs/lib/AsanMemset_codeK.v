(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_12b848 : bv 32 := 0x0e060a63.
Lemma F_12b848 : fetch_word Asan.M.loaded_segments (0x12b88c : word) = Some W_12b848.
Proof. vm_refl. Qed.
Lemma D_12b848 : decode_any W_12b848 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b84c : bv 32 := 0x00b50023.
Lemma F_12b84c : fetch_word Asan.M.loaded_segments (0x12b890 : word) = Some W_12b84c.
Proof. vm_refl. Qed.
Lemma D_12b84c : decode_any W_12b84c = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b850 : bv 32 := 0x00c506b3.
Lemma F_12b850 : fetch_word Asan.M.loaded_segments (0x12b894 : word) = Some W_12b850.
Proof. vm_refl. Qed.
Lemma D_12b850 : decode_any W_12b850 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b854 : bv 32 := 0x00300713.
Lemma F_12b854 : fetch_word Asan.M.loaded_segments (0x12b898 : word) = Some W_12b854.
Proof. vm_refl. Qed.
Lemma D_12b854 : decode_any W_12b854 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b858 : bv 32 := 0xfeb68fa3.
Lemma F_12b858 : fetch_word Asan.M.loaded_segments (0x12b89c : word) = Some W_12b858.
Proof. vm_refl. Qed.
Lemma D_12b858 : decode_any W_12b858 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b85c : bv 32 := 0x0ee66063.
Lemma F_12b85c : fetch_word Asan.M.loaded_segments (0x12b8a0 : word) = Some W_12b85c.
Proof. vm_refl. Qed.
Lemma D_12b85c : decode_any W_12b85c = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b860 : bv 32 := 0x00b500a3.
Lemma F_12b860 : fetch_word Asan.M.loaded_segments (0x12b8a4 : word) = Some W_12b860.
Proof. vm_refl. Qed.
Lemma D_12b860 : decode_any W_12b860 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b864 : bv 32 := 0x00b50123.
Lemma F_12b864 : fetch_word Asan.M.loaded_segments (0x12b8a8 : word) = Some W_12b864.
Proof. vm_refl. Qed.
Lemma D_12b864 : decode_any W_12b864 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b868 : bv 32 := 0x00700713.
Lemma F_12b868 : fetch_word Asan.M.loaded_segments (0x12b8ac : word) = Some W_12b868.
Proof. vm_refl. Qed.
Lemma D_12b868 : decode_any W_12b868 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b86c : bv 32 := 0xfeb68ea3.
Lemma F_12b86c : fetch_word Asan.M.loaded_segments (0x12b8b0 : word) = Some W_12b86c.
Proof. vm_refl. Qed.
Lemma D_12b86c : decode_any W_12b86c = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b870 : bv 32 := 0xfeb68f23.
Lemma F_12b870 : fetch_word Asan.M.loaded_segments (0x12b8b4 : word) = Some W_12b870.
Proof. vm_refl. Qed.
Lemma D_12b870 : decode_any W_12b870 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b874 : bv 32 := 0x0ce66463.
Lemma F_12b874 : fetch_word Asan.M.loaded_segments (0x12b8b8 : word) = Some W_12b874.
Proof. vm_refl. Qed.
Lemma D_12b874 : decode_any W_12b874 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b878 : bv 32 := 0x00b501a3.
Lemma F_12b878 : fetch_word Asan.M.loaded_segments (0x12b8bc : word) = Some W_12b878.
Proof. vm_refl. Qed.
Lemma D_12b878 : decode_any W_12b878 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b87c : bv 32 := 0x00900793.
Lemma F_12b87c : fetch_word Asan.M.loaded_segments (0x12b8c0 : word) = Some W_12b87c.
Proof. vm_refl. Qed.
Lemma D_12b87c : decode_any W_12b87c = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b880 : bv 32 := 0xfeb68e23.
Lemma F_12b880 : fetch_word Asan.M.loaded_segments (0x12b8c4 : word) = Some W_12b880.
Proof. vm_refl. Qed.
Lemma D_12b880 : decode_any W_12b880 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b884 : bv 32 := 0x0af66c63.
Lemma F_12b884 : fetch_word Asan.M.loaded_segments (0x12b8c8 : word) = Some W_12b884.
Proof. vm_refl. Qed.
Lemma D_12b884 : decode_any W_12b884 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b888 : bv 32 := 0x40a006bb.
Lemma F_12b888 : fetch_word Asan.M.loaded_segments (0x12b8cc : word) = Some W_12b888.
Proof. vm_refl. Qed.
Lemma D_12b888 : decode_any W_12b888 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b88c : bv 32 := 0x03859813.
Lemma F_12b88c : fetch_word Asan.M.loaded_segments (0x12b8d0 : word) = Some W_12b88c.
Proof. vm_refl. Qed.
Lemma D_12b88c : decode_any W_12b88c = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b890 : bv 32 := 0x101015b7.
Lemma F_12b890 : fetch_word Asan.M.loaded_segments (0x12b8d4 : word) = Some W_12b890.
Proof. vm_refl. Qed.
Lemma D_12b890 : decode_any W_12b890 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b894 : bv 32 := 0x0036f693.
Lemma F_12b894 : fetch_word Asan.M.loaded_segments (0x12b8d8 : word) = Some W_12b894.
Proof. vm_refl. Qed.
Lemma D_12b894 : decode_any W_12b894 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b898 : bv 32 := 0x00459713.
Lemma F_12b898 : fetch_word Asan.M.loaded_segments (0x12b8dc : word) = Some W_12b898.
Proof. vm_refl. Qed.
Lemma D_12b898 : decode_any W_12b898 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b89c : bv 32 := 0x40d60633.
Lemma F_12b89c : fetch_word Asan.M.loaded_segments (0x12b8e0 : word) = Some W_12b89c.
Proof. vm_refl. Qed.
Lemma D_12b89c : decode_any W_12b89c = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8a0 : bv 32 := 0x00d505b3.
Lemma F_12b8a0 : fetch_word Asan.M.loaded_segments (0x12b8e4 : word) = Some W_12b8a0.
Proof. vm_refl. Qed.
Lemma D_12b8a0 : decode_any W_12b8a0 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8a4 : bv 32 := 0x10070693.
Lemma F_12b8a4 : fetch_word Asan.M.loaded_segments (0x12b8e8 : word) = Some W_12b8a4.
Proof. vm_refl. Qed.
Lemma D_12b8a4 : decode_any W_12b8a4 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8a8 : bv 32 := 0xffc67713.
Lemma F_12b8a8 : fetch_word Asan.M.loaded_segments (0x12b8ec : word) = Some W_12b8a8.
Proof. vm_refl. Qed.
Lemma D_12b8a8 : decode_any W_12b8a8 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8ac : bv 32 := 0x02d83633.
Lemma F_12b8ac : fetch_word Asan.M.loaded_segments (0x12b8f0 : word) = Some W_12b8ac.
Proof. vm_refl. Qed.
Lemma D_12b8ac : decode_any W_12b8ac = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8b0 : bv 32 := 0x00c5a023.
Lemma F_12b8b0 : fetch_word Asan.M.loaded_segments (0x12b8f4 : word) = Some W_12b8b0.
Proof. vm_refl. Qed.
Lemma D_12b8b0 : decode_any W_12b8b0 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8b4 : bv 32 := 0x00e586b3.
Lemma F_12b8b4 : fetch_word Asan.M.loaded_segments (0x12b8f8 : word) = Some W_12b8b4.
Proof. vm_refl. Qed.
Lemma D_12b8b4 : decode_any W_12b8b4 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8b8 : bv 32 := 0xfec6ae23.
Lemma F_12b8b8 : fetch_word Asan.M.loaded_segments (0x12b8fc : word) = Some W_12b8b8.
Proof. vm_refl. Qed.
Lemma D_12b8b8 : decode_any W_12b8b8 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8bc : bv 32 := 0x08f76063.
Lemma F_12b8bc : fetch_word Asan.M.loaded_segments (0x12b900 : word) = Some W_12b8bc.
Proof. vm_refl. Qed.
Lemma D_12b8bc : decode_any W_12b8bc = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8c0 : bv 32 := 0x00c5a223.
Lemma F_12b8c0 : fetch_word Asan.M.loaded_segments (0x12b904 : word) = Some W_12b8c0.
Proof. vm_refl. Qed.
Lemma D_12b8c0 : decode_any W_12b8c0 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8c4 : bv 32 := 0x00c5a423.
Lemma F_12b8c4 : fetch_word Asan.M.loaded_segments (0x12b908 : word) = Some W_12b8c4.
Proof. vm_refl. Qed.
Lemma D_12b8c4 : decode_any W_12b8c4 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8c8 : bv 32 := 0x01900793.
Lemma F_12b8c8 : fetch_word Asan.M.loaded_segments (0x12b90c : word) = Some W_12b8c8.
Proof. vm_refl. Qed.
Lemma D_12b8c8 : decode_any W_12b8c8 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8cc : bv 32 := 0xfec6aa23.
Lemma F_12b8cc : fetch_word Asan.M.loaded_segments (0x12b910 : word) = Some W_12b8cc.
Proof. vm_refl. Qed.
Lemma D_12b8cc : decode_any W_12b8cc = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8d0 : bv 32 := 0xfec6ac23.
Lemma F_12b8d0 : fetch_word Asan.M.loaded_segments (0x12b914 : word) = Some W_12b8d0.
Proof. vm_refl. Qed.
Lemma D_12b8d0 : decode_any W_12b8d0 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8d4 : bv 32 := 0x06f76463.
Lemma F_12b8d4 : fetch_word Asan.M.loaded_segments (0x12b918 : word) = Some W_12b8d4.
Proof. vm_refl. Qed.
Lemma D_12b8d4 : decode_any W_12b8d4 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8d8 : bv 32 := 0x00c5a623.
Lemma F_12b8d8 : fetch_word Asan.M.loaded_segments (0x12b91c : word) = Some W_12b8d8.
Proof. vm_refl. Qed.
Lemma D_12b8d8 : decode_any W_12b8d8 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8dc : bv 32 := 0x00c5a823.
Lemma F_12b8dc : fetch_word Asan.M.loaded_segments (0x12b920 : word) = Some W_12b8dc.
Proof. vm_refl. Qed.
Lemma D_12b8dc : decode_any W_12b8dc = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8e0 : bv 32 := 0x00c5aa23.
Lemma F_12b8e0 : fetch_word Asan.M.loaded_segments (0x12b924 : word) = Some W_12b8e0.
Proof. vm_refl. Qed.
Lemma D_12b8e0 : decode_any W_12b8e0 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8e4 : bv 32 := 0x00c5ac23.
Lemma F_12b8e4 : fetch_word Asan.M.loaded_segments (0x12b928 : word) = Some W_12b8e4.
Proof. vm_refl. Qed.
Lemma D_12b8e4 : decode_any W_12b8e4 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8e8 : bv 32 := 0x0045f793.
Lemma F_12b8e8 : fetch_word Asan.M.loaded_segments (0x12b92c : word) = Some W_12b8e8.
Proof. vm_refl. Qed.
Lemma D_12b8e8 : decode_any W_12b8e8 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8ec : bv 32 := 0x02000813.
Lemma F_12b8ec : fetch_word Asan.M.loaded_segments (0x12b930 : word) = Some W_12b8ec.
Proof. vm_refl. Qed.
Lemma D_12b8ec : decode_any W_12b8ec = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8f0 : bv 32 := 0x01878793.
Lemma F_12b8f0 : fetch_word Asan.M.loaded_segments (0x12b934 : word) = Some W_12b8f0.
Proof. vm_refl. Qed.
Lemma D_12b8f0 : decode_any W_12b8f0 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8f4 : bv 32 := 0x40f70733.
Lemma F_12b8f4 : fetch_word Asan.M.loaded_segments (0x12b938 : word) = Some W_12b8f4.
Proof. vm_refl. Qed.
Lemma D_12b8f4 : decode_any W_12b8f4 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8f8 : bv 32 := 0xfec6a223.
Lemma F_12b8f8 : fetch_word Asan.M.loaded_segments (0x12b93c : word) = Some W_12b8f8.
Proof. vm_refl. Qed.
Lemma D_12b8f8 : decode_any W_12b8f8 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b8fc : bv 32 := 0xfec6a423.
Lemma F_12b8fc : fetch_word Asan.M.loaded_segments (0x12b940 : word) = Some W_12b8fc.
Proof. vm_refl. Qed.
Lemma D_12b8fc : decode_any W_12b8fc = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b900 : bv 32 := 0xfec6a623.
Lemma F_12b900 : fetch_word Asan.M.loaded_segments (0x12b944 : word) = Some W_12b900.
Proof. vm_refl. Qed.
Lemma D_12b900 : decode_any W_12b900 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b904 : bv 32 := 0xfec6a823.
Lemma F_12b904 : fetch_word Asan.M.loaded_segments (0x12b948 : word) = Some W_12b904.
Proof. vm_refl. Qed.
Lemma D_12b904 : decode_any W_12b904 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b908 : bv 32 := 0x03076a63.
Lemma F_12b908 : fetch_word Asan.M.loaded_segments (0x12b94c : word) = Some W_12b908.
Proof. vm_refl. Qed.
Lemma D_12b908 : decode_any W_12b908 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b90c : bv 32 := 0x02061613.
Lemma F_12b90c : fetch_word Asan.M.loaded_segments (0x12b950 : word) = Some W_12b90c.
Proof. vm_refl. Qed.
Lemma D_12b90c : decode_any W_12b90c = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b910 : bv 32 := 0x00f585b3.
Lemma F_12b910 : fetch_word Asan.M.loaded_segments (0x12b954 : word) = Some W_12b910.
Proof. vm_refl. Qed.
Lemma D_12b910 : decode_any W_12b910 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b914 : bv 32 := 0x02065693.
Lemma F_12b914 : fetch_word Asan.M.loaded_segments (0x12b958 : word) = Some W_12b914.
Proof. vm_refl. Qed.
Lemma D_12b914 : decode_any W_12b914 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b918 : bv 32 := 0x00d66633.
Lemma F_12b918 : fetch_word Asan.M.loaded_segments (0x12b95c : word) = Some W_12b918.
Proof. vm_refl. Qed.
Lemma D_12b918 : decode_any W_12b918 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b91c : bv 32 := 0x01f00693.
Lemma F_12b91c : fetch_word Asan.M.loaded_segments (0x12b960 : word) = Some W_12b91c.
Proof. vm_refl. Qed.
Lemma D_12b91c : decode_any W_12b91c = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b920 : bv 32 := 0x00c5b023.
Lemma F_12b920 : fetch_word Asan.M.loaded_segments (0x12b964 : word) = Some W_12b920.
Proof. vm_refl. Qed.
Lemma D_12b920 : decode_any W_12b920 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b924 : bv 32 := 0x00c5b423.
Lemma F_12b924 : fetch_word Asan.M.loaded_segments (0x12b968 : word) = Some W_12b924.
Proof. vm_refl. Qed.
Lemma D_12b924 : decode_any W_12b924 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b928 : bv 32 := 0x00c5b823.
Lemma F_12b928 : fetch_word Asan.M.loaded_segments (0x12b96c : word) = Some W_12b928.
Proof. vm_refl. Qed.
Lemma D_12b928 : decode_any W_12b928 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b92c : bv 32 := 0x00c5bc23.
Lemma F_12b92c : fetch_word Asan.M.loaded_segments (0x12b970 : word) = Some W_12b92c.
Proof. vm_refl. Qed.
Lemma D_12b92c : decode_any W_12b92c = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b930 : bv 32 := 0xfe070713.
Lemma F_12b930 : fetch_word Asan.M.loaded_segments (0x12b974 : word) = Some W_12b930.
Proof. vm_refl. Qed.
Lemma D_12b930 : decode_any W_12b930 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b934 : bv 32 := 0x02058593.
Lemma F_12b934 : fetch_word Asan.M.loaded_segments (0x12b978 : word) = Some W_12b934.
Proof. vm_refl. Qed.
Lemma D_12b934 : decode_any W_12b934 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b938 : bv 32 := 0xfee6e4e3.
Lemma F_12b938 : fetch_word Asan.M.loaded_segments (0x12b97c : word) = Some W_12b938.
Proof. vm_refl. Qed.
Lemma D_12b938 : decode_any W_12b938 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12b93c : bv 32 := 0x00008067.
Lemma F_12b93c : fetch_word Asan.M.loaded_segments (0x12b980 : word) = Some W_12b93c.
Proof. vm_refl. Qed.
Lemma D_12b93c : decode_any W_12b93c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0x12b88c%Z.
Definition Fo_000 := F_12b848.
Definition Do_000 := D_12b848.
Definition Fo_004 := F_12b84c.
Definition Do_004 := D_12b84c.
Definition Fo_008 := F_12b850.
Definition Do_008 := D_12b850.
Definition Fo_00c := F_12b854.
Definition Do_00c := D_12b854.
Definition Fo_010 := F_12b858.
Definition Do_010 := D_12b858.
Definition Fo_014 := F_12b85c.
Definition Do_014 := D_12b85c.
Definition Fo_018 := F_12b860.
Definition Do_018 := D_12b860.
Definition Fo_01c := F_12b864.
Definition Do_01c := D_12b864.
Definition Fo_020 := F_12b868.
Definition Do_020 := D_12b868.
Definition Fo_024 := F_12b86c.
Definition Do_024 := D_12b86c.
Definition Fo_028 := F_12b870.
Definition Do_028 := D_12b870.
Definition Fo_02c := F_12b874.
Definition Do_02c := D_12b874.
Definition Fo_030 := F_12b878.
Definition Do_030 := D_12b878.
Definition Fo_034 := F_12b87c.
Definition Do_034 := D_12b87c.
Definition Fo_038 := F_12b880.
Definition Do_038 := D_12b880.
Definition Fo_03c := F_12b884.
Definition Do_03c := D_12b884.
Definition Fo_040 := F_12b888.
Definition Do_040 := D_12b888.
Definition Fo_044 := F_12b88c.
Definition Do_044 := D_12b88c.
Definition Fo_048 := F_12b890.
Definition Do_048 := D_12b890.
Definition Fo_04c := F_12b894.
Definition Do_04c := D_12b894.
Definition Fo_050 := F_12b898.
Definition Do_050 := D_12b898.
Definition Fo_054 := F_12b89c.
Definition Do_054 := D_12b89c.
Definition Fo_058 := F_12b8a0.
Definition Do_058 := D_12b8a0.
Definition Fo_05c := F_12b8a4.
Definition Do_05c := D_12b8a4.
Definition Fo_060 := F_12b8a8.
Definition Do_060 := D_12b8a8.
Definition Fo_064 := F_12b8ac.
Definition Do_064 := D_12b8ac.
Definition Fo_068 := F_12b8b0.
Definition Do_068 := D_12b8b0.
Definition Fo_06c := F_12b8b4.
Definition Do_06c := D_12b8b4.
Definition Fo_070 := F_12b8b8.
Definition Do_070 := D_12b8b8.
Definition Fo_074 := F_12b8bc.
Definition Do_074 := D_12b8bc.
Definition Fo_078 := F_12b8c0.
Definition Do_078 := D_12b8c0.
Definition Fo_07c := F_12b8c4.
Definition Do_07c := D_12b8c4.
Definition Fo_080 := F_12b8c8.
Definition Do_080 := D_12b8c8.
Definition Fo_084 := F_12b8cc.
Definition Do_084 := D_12b8cc.
Definition Fo_088 := F_12b8d0.
Definition Do_088 := D_12b8d0.
Definition Fo_08c := F_12b8d4.
Definition Do_08c := D_12b8d4.
Definition Fo_090 := F_12b8d8.
Definition Do_090 := D_12b8d8.
Definition Fo_094 := F_12b8dc.
Definition Do_094 := D_12b8dc.
Definition Fo_098 := F_12b8e0.
Definition Do_098 := D_12b8e0.
Definition Fo_09c := F_12b8e4.
Definition Do_09c := D_12b8e4.
Definition Fo_0a0 := F_12b8e8.
Definition Do_0a0 := D_12b8e8.
Definition Fo_0a4 := F_12b8ec.
Definition Do_0a4 := D_12b8ec.
Definition Fo_0a8 := F_12b8f0.
Definition Do_0a8 := D_12b8f0.
Definition Fo_0ac := F_12b8f4.
Definition Do_0ac := D_12b8f4.
Definition Fo_0b0 := F_12b8f8.
Definition Do_0b0 := D_12b8f8.
Definition Fo_0b4 := F_12b8fc.
Definition Do_0b4 := D_12b8fc.
Definition Fo_0b8 := F_12b900.
Definition Do_0b8 := D_12b900.
Definition Fo_0bc := F_12b904.
Definition Do_0bc := D_12b904.
Definition Fo_0c0 := F_12b908.
Definition Do_0c0 := D_12b908.
Definition Fo_0c4 := F_12b90c.
Definition Do_0c4 := D_12b90c.
Definition Fo_0c8 := F_12b910.
Definition Do_0c8 := D_12b910.
Definition Fo_0cc := F_12b914.
Definition Do_0cc := D_12b914.
Definition Fo_0d0 := F_12b918.
Definition Do_0d0 := D_12b918.
Definition Fo_0d4 := F_12b91c.
Definition Do_0d4 := D_12b91c.
Definition Fo_0d8 := F_12b920.
Definition Do_0d8 := D_12b920.
Definition Fo_0dc := F_12b924.
Definition Do_0dc := D_12b924.
Definition Fo_0e0 := F_12b928.
Definition Do_0e0 := D_12b928.
Definition Fo_0e4 := F_12b92c.
Definition Do_0e4 := D_12b92c.
Definition Fo_0e8 := F_12b930.
Definition Do_0e8 := D_12b930.
Definition Fo_0ec := F_12b934.
Definition Do_0ec := D_12b934.
Definition Fo_0f0 := F_12b938.
Definition Do_0f0 := D_12b938.
Definition Fo_0f4 := F_12b93c.
Definition Do_0f4 := D_12b93c.
