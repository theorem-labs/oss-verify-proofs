(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_c99c4 : bv 32 := 0x0e060a63.
Lemma F_c99c4 : fetch_word AsanUbsan.M.loaded_segments (0xc99c0 : word) = Some W_c99c4.
Proof. vm_refl. Qed.
Lemma D_c99c4 : decode_any W_c99c4 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99c8 : bv 32 := 0x00b50023.
Lemma F_c99c8 : fetch_word AsanUbsan.M.loaded_segments (0xc99c4 : word) = Some W_c99c8.
Proof. vm_refl. Qed.
Lemma D_c99c8 : decode_any W_c99c8 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99cc : bv 32 := 0x00c506b3.
Lemma F_c99cc : fetch_word AsanUbsan.M.loaded_segments (0xc99c8 : word) = Some W_c99cc.
Proof. vm_refl. Qed.
Lemma D_c99cc : decode_any W_c99cc = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99d0 : bv 32 := 0x00300713.
Lemma F_c99d0 : fetch_word AsanUbsan.M.loaded_segments (0xc99cc : word) = Some W_c99d0.
Proof. vm_refl. Qed.
Lemma D_c99d0 : decode_any W_c99d0 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99d4 : bv 32 := 0xfeb68fa3.
Lemma F_c99d4 : fetch_word AsanUbsan.M.loaded_segments (0xc99d0 : word) = Some W_c99d4.
Proof. vm_refl. Qed.
Lemma D_c99d4 : decode_any W_c99d4 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99d8 : bv 32 := 0x0ee66063.
Lemma F_c99d8 : fetch_word AsanUbsan.M.loaded_segments (0xc99d4 : word) = Some W_c99d8.
Proof. vm_refl. Qed.
Lemma D_c99d8 : decode_any W_c99d8 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99dc : bv 32 := 0x00b500a3.
Lemma F_c99dc : fetch_word AsanUbsan.M.loaded_segments (0xc99d8 : word) = Some W_c99dc.
Proof. vm_refl. Qed.
Lemma D_c99dc : decode_any W_c99dc = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99e0 : bv 32 := 0x00b50123.
Lemma F_c99e0 : fetch_word AsanUbsan.M.loaded_segments (0xc99dc : word) = Some W_c99e0.
Proof. vm_refl. Qed.
Lemma D_c99e0 : decode_any W_c99e0 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99e4 : bv 32 := 0x00700713.
Lemma F_c99e4 : fetch_word AsanUbsan.M.loaded_segments (0xc99e0 : word) = Some W_c99e4.
Proof. vm_refl. Qed.
Lemma D_c99e4 : decode_any W_c99e4 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99e8 : bv 32 := 0xfeb68ea3.
Lemma F_c99e8 : fetch_word AsanUbsan.M.loaded_segments (0xc99e4 : word) = Some W_c99e8.
Proof. vm_refl. Qed.
Lemma D_c99e8 : decode_any W_c99e8 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99ec : bv 32 := 0xfeb68f23.
Lemma F_c99ec : fetch_word AsanUbsan.M.loaded_segments (0xc99e8 : word) = Some W_c99ec.
Proof. vm_refl. Qed.
Lemma D_c99ec : decode_any W_c99ec = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99f0 : bv 32 := 0x0ce66463.
Lemma F_c99f0 : fetch_word AsanUbsan.M.loaded_segments (0xc99ec : word) = Some W_c99f0.
Proof. vm_refl. Qed.
Lemma D_c99f0 : decode_any W_c99f0 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99f4 : bv 32 := 0x00b501a3.
Lemma F_c99f4 : fetch_word AsanUbsan.M.loaded_segments (0xc99f0 : word) = Some W_c99f4.
Proof. vm_refl. Qed.
Lemma D_c99f4 : decode_any W_c99f4 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99f8 : bv 32 := 0x00900793.
Lemma F_c99f8 : fetch_word AsanUbsan.M.loaded_segments (0xc99f4 : word) = Some W_c99f8.
Proof. vm_refl. Qed.
Lemma D_c99f8 : decode_any W_c99f8 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99fc : bv 32 := 0xfeb68e23.
Lemma F_c99fc : fetch_word AsanUbsan.M.loaded_segments (0xc99f8 : word) = Some W_c99fc.
Proof. vm_refl. Qed.
Lemma D_c99fc : decode_any W_c99fc = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a00 : bv 32 := 0x0af66c63.
Lemma F_c9a00 : fetch_word AsanUbsan.M.loaded_segments (0xc99fc : word) = Some W_c9a00.
Proof. vm_refl. Qed.
Lemma D_c9a00 : decode_any W_c9a00 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a04 : bv 32 := 0x40a006bb.
Lemma F_c9a04 : fetch_word AsanUbsan.M.loaded_segments (0xc9a00 : word) = Some W_c9a04.
Proof. vm_refl. Qed.
Lemma D_c9a04 : decode_any W_c9a04 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a08 : bv 32 := 0x03859813.
Lemma F_c9a08 : fetch_word AsanUbsan.M.loaded_segments (0xc9a04 : word) = Some W_c9a08.
Proof. vm_refl. Qed.
Lemma D_c9a08 : decode_any W_c9a08 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a0c : bv 32 := 0x101015b7.
Lemma F_c9a0c : fetch_word AsanUbsan.M.loaded_segments (0xc9a08 : word) = Some W_c9a0c.
Proof. vm_refl. Qed.
Lemma D_c9a0c : decode_any W_c9a0c = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a10 : bv 32 := 0x0036f693.
Lemma F_c9a10 : fetch_word AsanUbsan.M.loaded_segments (0xc9a0c : word) = Some W_c9a10.
Proof. vm_refl. Qed.
Lemma D_c9a10 : decode_any W_c9a10 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a14 : bv 32 := 0x00459713.
Lemma F_c9a14 : fetch_word AsanUbsan.M.loaded_segments (0xc9a10 : word) = Some W_c9a14.
Proof. vm_refl. Qed.
Lemma D_c9a14 : decode_any W_c9a14 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a18 : bv 32 := 0x40d60633.
Lemma F_c9a18 : fetch_word AsanUbsan.M.loaded_segments (0xc9a14 : word) = Some W_c9a18.
Proof. vm_refl. Qed.
Lemma D_c9a18 : decode_any W_c9a18 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a1c : bv 32 := 0x00d505b3.
Lemma F_c9a1c : fetch_word AsanUbsan.M.loaded_segments (0xc9a18 : word) = Some W_c9a1c.
Proof. vm_refl. Qed.
Lemma D_c9a1c : decode_any W_c9a1c = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a20 : bv 32 := 0x10070693.
Lemma F_c9a20 : fetch_word AsanUbsan.M.loaded_segments (0xc9a1c : word) = Some W_c9a20.
Proof. vm_refl. Qed.
Lemma D_c9a20 : decode_any W_c9a20 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a24 : bv 32 := 0xffc67713.
Lemma F_c9a24 : fetch_word AsanUbsan.M.loaded_segments (0xc9a20 : word) = Some W_c9a24.
Proof. vm_refl. Qed.
Lemma D_c9a24 : decode_any W_c9a24 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a28 : bv 32 := 0x02d83633.
Lemma F_c9a28 : fetch_word AsanUbsan.M.loaded_segments (0xc9a24 : word) = Some W_c9a28.
Proof. vm_refl. Qed.
Lemma D_c9a28 : decode_any W_c9a28 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a2c : bv 32 := 0x00c5a023.
Lemma F_c9a2c : fetch_word AsanUbsan.M.loaded_segments (0xc9a28 : word) = Some W_c9a2c.
Proof. vm_refl. Qed.
Lemma D_c9a2c : decode_any W_c9a2c = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a30 : bv 32 := 0x00e586b3.
Lemma F_c9a30 : fetch_word AsanUbsan.M.loaded_segments (0xc9a2c : word) = Some W_c9a30.
Proof. vm_refl. Qed.
Lemma D_c9a30 : decode_any W_c9a30 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a34 : bv 32 := 0xfec6ae23.
Lemma F_c9a34 : fetch_word AsanUbsan.M.loaded_segments (0xc9a30 : word) = Some W_c9a34.
Proof. vm_refl. Qed.
Lemma D_c9a34 : decode_any W_c9a34 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a38 : bv 32 := 0x08f76063.
Lemma F_c9a38 : fetch_word AsanUbsan.M.loaded_segments (0xc9a34 : word) = Some W_c9a38.
Proof. vm_refl. Qed.
Lemma D_c9a38 : decode_any W_c9a38 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a3c : bv 32 := 0x00c5a223.
Lemma F_c9a3c : fetch_word AsanUbsan.M.loaded_segments (0xc9a38 : word) = Some W_c9a3c.
Proof. vm_refl. Qed.
Lemma D_c9a3c : decode_any W_c9a3c = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a40 : bv 32 := 0x00c5a423.
Lemma F_c9a40 : fetch_word AsanUbsan.M.loaded_segments (0xc9a3c : word) = Some W_c9a40.
Proof. vm_refl. Qed.
Lemma D_c9a40 : decode_any W_c9a40 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a44 : bv 32 := 0x01900793.
Lemma F_c9a44 : fetch_word AsanUbsan.M.loaded_segments (0xc9a40 : word) = Some W_c9a44.
Proof. vm_refl. Qed.
Lemma D_c9a44 : decode_any W_c9a44 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a48 : bv 32 := 0xfec6aa23.
Lemma F_c9a48 : fetch_word AsanUbsan.M.loaded_segments (0xc9a44 : word) = Some W_c9a48.
Proof. vm_refl. Qed.
Lemma D_c9a48 : decode_any W_c9a48 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a4c : bv 32 := 0xfec6ac23.
Lemma F_c9a4c : fetch_word AsanUbsan.M.loaded_segments (0xc9a48 : word) = Some W_c9a4c.
Proof. vm_refl. Qed.
Lemma D_c9a4c : decode_any W_c9a4c = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a50 : bv 32 := 0x06f76463.
Lemma F_c9a50 : fetch_word AsanUbsan.M.loaded_segments (0xc9a4c : word) = Some W_c9a50.
Proof. vm_refl. Qed.
Lemma D_c9a50 : decode_any W_c9a50 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a54 : bv 32 := 0x00c5a623.
Lemma F_c9a54 : fetch_word AsanUbsan.M.loaded_segments (0xc9a50 : word) = Some W_c9a54.
Proof. vm_refl. Qed.
Lemma D_c9a54 : decode_any W_c9a54 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a58 : bv 32 := 0x00c5a823.
Lemma F_c9a58 : fetch_word AsanUbsan.M.loaded_segments (0xc9a54 : word) = Some W_c9a58.
Proof. vm_refl. Qed.
Lemma D_c9a58 : decode_any W_c9a58 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a5c : bv 32 := 0x00c5aa23.
Lemma F_c9a5c : fetch_word AsanUbsan.M.loaded_segments (0xc9a58 : word) = Some W_c9a5c.
Proof. vm_refl. Qed.
Lemma D_c9a5c : decode_any W_c9a5c = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a60 : bv 32 := 0x00c5ac23.
Lemma F_c9a60 : fetch_word AsanUbsan.M.loaded_segments (0xc9a5c : word) = Some W_c9a60.
Proof. vm_refl. Qed.
Lemma D_c9a60 : decode_any W_c9a60 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a64 : bv 32 := 0x0045f793.
Lemma F_c9a64 : fetch_word AsanUbsan.M.loaded_segments (0xc9a60 : word) = Some W_c9a64.
Proof. vm_refl. Qed.
Lemma D_c9a64 : decode_any W_c9a64 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a68 : bv 32 := 0x02000813.
Lemma F_c9a68 : fetch_word AsanUbsan.M.loaded_segments (0xc9a64 : word) = Some W_c9a68.
Proof. vm_refl. Qed.
Lemma D_c9a68 : decode_any W_c9a68 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a6c : bv 32 := 0x01878793.
Lemma F_c9a6c : fetch_word AsanUbsan.M.loaded_segments (0xc9a68 : word) = Some W_c9a6c.
Proof. vm_refl. Qed.
Lemma D_c9a6c : decode_any W_c9a6c = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a70 : bv 32 := 0x40f70733.
Lemma F_c9a70 : fetch_word AsanUbsan.M.loaded_segments (0xc9a6c : word) = Some W_c9a70.
Proof. vm_refl. Qed.
Lemma D_c9a70 : decode_any W_c9a70 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a74 : bv 32 := 0xfec6a223.
Lemma F_c9a74 : fetch_word AsanUbsan.M.loaded_segments (0xc9a70 : word) = Some W_c9a74.
Proof. vm_refl. Qed.
Lemma D_c9a74 : decode_any W_c9a74 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a78 : bv 32 := 0xfec6a423.
Lemma F_c9a78 : fetch_word AsanUbsan.M.loaded_segments (0xc9a74 : word) = Some W_c9a78.
Proof. vm_refl. Qed.
Lemma D_c9a78 : decode_any W_c9a78 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a7c : bv 32 := 0xfec6a623.
Lemma F_c9a7c : fetch_word AsanUbsan.M.loaded_segments (0xc9a78 : word) = Some W_c9a7c.
Proof. vm_refl. Qed.
Lemma D_c9a7c : decode_any W_c9a7c = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a80 : bv 32 := 0xfec6a823.
Lemma F_c9a80 : fetch_word AsanUbsan.M.loaded_segments (0xc9a7c : word) = Some W_c9a80.
Proof. vm_refl. Qed.
Lemma D_c9a80 : decode_any W_c9a80 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a84 : bv 32 := 0x03076a63.
Lemma F_c9a84 : fetch_word AsanUbsan.M.loaded_segments (0xc9a80 : word) = Some W_c9a84.
Proof. vm_refl. Qed.
Lemma D_c9a84 : decode_any W_c9a84 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a88 : bv 32 := 0x02061613.
Lemma F_c9a88 : fetch_word AsanUbsan.M.loaded_segments (0xc9a84 : word) = Some W_c9a88.
Proof. vm_refl. Qed.
Lemma D_c9a88 : decode_any W_c9a88 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a8c : bv 32 := 0x00f585b3.
Lemma F_c9a8c : fetch_word AsanUbsan.M.loaded_segments (0xc9a88 : word) = Some W_c9a8c.
Proof. vm_refl. Qed.
Lemma D_c9a8c : decode_any W_c9a8c = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a90 : bv 32 := 0x02065693.
Lemma F_c9a90 : fetch_word AsanUbsan.M.loaded_segments (0xc9a8c : word) = Some W_c9a90.
Proof. vm_refl. Qed.
Lemma D_c9a90 : decode_any W_c9a90 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a94 : bv 32 := 0x00d66633.
Lemma F_c9a94 : fetch_word AsanUbsan.M.loaded_segments (0xc9a90 : word) = Some W_c9a94.
Proof. vm_refl. Qed.
Lemma D_c9a94 : decode_any W_c9a94 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a98 : bv 32 := 0x01f00693.
Lemma F_c9a98 : fetch_word AsanUbsan.M.loaded_segments (0xc9a94 : word) = Some W_c9a98.
Proof. vm_refl. Qed.
Lemma D_c9a98 : decode_any W_c9a98 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9a9c : bv 32 := 0x00c5b023.
Lemma F_c9a9c : fetch_word AsanUbsan.M.loaded_segments (0xc9a98 : word) = Some W_c9a9c.
Proof. vm_refl. Qed.
Lemma D_c9a9c : decode_any W_c9a9c = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9aa0 : bv 32 := 0x00c5b423.
Lemma F_c9aa0 : fetch_word AsanUbsan.M.loaded_segments (0xc9a9c : word) = Some W_c9aa0.
Proof. vm_refl. Qed.
Lemma D_c9aa0 : decode_any W_c9aa0 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9aa4 : bv 32 := 0x00c5b823.
Lemma F_c9aa4 : fetch_word AsanUbsan.M.loaded_segments (0xc9aa0 : word) = Some W_c9aa4.
Proof. vm_refl. Qed.
Lemma D_c9aa4 : decode_any W_c9aa4 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9aa8 : bv 32 := 0x00c5bc23.
Lemma F_c9aa8 : fetch_word AsanUbsan.M.loaded_segments (0xc9aa4 : word) = Some W_c9aa8.
Proof. vm_refl. Qed.
Lemma D_c9aa8 : decode_any W_c9aa8 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9aac : bv 32 := 0xfe070713.
Lemma F_c9aac : fetch_word AsanUbsan.M.loaded_segments (0xc9aa8 : word) = Some W_c9aac.
Proof. vm_refl. Qed.
Lemma D_c9aac : decode_any W_c9aac = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9ab0 : bv 32 := 0x02058593.
Lemma F_c9ab0 : fetch_word AsanUbsan.M.loaded_segments (0xc9aac : word) = Some W_c9ab0.
Proof. vm_refl. Qed.
Lemma D_c9ab0 : decode_any W_c9ab0 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9ab4 : bv 32 := 0xfee6e4e3.
Lemma F_c9ab4 : fetch_word AsanUbsan.M.loaded_segments (0xc9ab0 : word) = Some W_c9ab4.
Proof. vm_refl. Qed.
Lemma D_c9ab4 : decode_any W_c9ab4 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9ab8 : bv 32 := 0x00008067.
Lemma F_c9ab8 : fetch_word AsanUbsan.M.loaded_segments (0xc9ab4 : word) = Some W_c9ab8.
Proof. vm_refl. Qed.
Lemma D_c9ab8 : decode_any W_c9ab8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0xc99c0%Z.
Definition Fo_000 := F_c99c4.
Definition Do_000 := D_c99c4.
Definition Fo_004 := F_c99c8.
Definition Do_004 := D_c99c8.
Definition Fo_008 := F_c99cc.
Definition Do_008 := D_c99cc.
Definition Fo_00c := F_c99d0.
Definition Do_00c := D_c99d0.
Definition Fo_010 := F_c99d4.
Definition Do_010 := D_c99d4.
Definition Fo_014 := F_c99d8.
Definition Do_014 := D_c99d8.
Definition Fo_018 := F_c99dc.
Definition Do_018 := D_c99dc.
Definition Fo_01c := F_c99e0.
Definition Do_01c := D_c99e0.
Definition Fo_020 := F_c99e4.
Definition Do_020 := D_c99e4.
Definition Fo_024 := F_c99e8.
Definition Do_024 := D_c99e8.
Definition Fo_028 := F_c99ec.
Definition Do_028 := D_c99ec.
Definition Fo_02c := F_c99f0.
Definition Do_02c := D_c99f0.
Definition Fo_030 := F_c99f4.
Definition Do_030 := D_c99f4.
Definition Fo_034 := F_c99f8.
Definition Do_034 := D_c99f8.
Definition Fo_038 := F_c99fc.
Definition Do_038 := D_c99fc.
Definition Fo_03c := F_c9a00.
Definition Do_03c := D_c9a00.
Definition Fo_040 := F_c9a04.
Definition Do_040 := D_c9a04.
Definition Fo_044 := F_c9a08.
Definition Do_044 := D_c9a08.
Definition Fo_048 := F_c9a0c.
Definition Do_048 := D_c9a0c.
Definition Fo_04c := F_c9a10.
Definition Do_04c := D_c9a10.
Definition Fo_050 := F_c9a14.
Definition Do_050 := D_c9a14.
Definition Fo_054 := F_c9a18.
Definition Do_054 := D_c9a18.
Definition Fo_058 := F_c9a1c.
Definition Do_058 := D_c9a1c.
Definition Fo_05c := F_c9a20.
Definition Do_05c := D_c9a20.
Definition Fo_060 := F_c9a24.
Definition Do_060 := D_c9a24.
Definition Fo_064 := F_c9a28.
Definition Do_064 := D_c9a28.
Definition Fo_068 := F_c9a2c.
Definition Do_068 := D_c9a2c.
Definition Fo_06c := F_c9a30.
Definition Do_06c := D_c9a30.
Definition Fo_070 := F_c9a34.
Definition Do_070 := D_c9a34.
Definition Fo_074 := F_c9a38.
Definition Do_074 := D_c9a38.
Definition Fo_078 := F_c9a3c.
Definition Do_078 := D_c9a3c.
Definition Fo_07c := F_c9a40.
Definition Do_07c := D_c9a40.
Definition Fo_080 := F_c9a44.
Definition Do_080 := D_c9a44.
Definition Fo_084 := F_c9a48.
Definition Do_084 := D_c9a48.
Definition Fo_088 := F_c9a4c.
Definition Do_088 := D_c9a4c.
Definition Fo_08c := F_c9a50.
Definition Do_08c := D_c9a50.
Definition Fo_090 := F_c9a54.
Definition Do_090 := D_c9a54.
Definition Fo_094 := F_c9a58.
Definition Do_094 := D_c9a58.
Definition Fo_098 := F_c9a5c.
Definition Do_098 := D_c9a5c.
Definition Fo_09c := F_c9a60.
Definition Do_09c := D_c9a60.
Definition Fo_0a0 := F_c9a64.
Definition Do_0a0 := D_c9a64.
Definition Fo_0a4 := F_c9a68.
Definition Do_0a4 := D_c9a68.
Definition Fo_0a8 := F_c9a6c.
Definition Do_0a8 := D_c9a6c.
Definition Fo_0ac := F_c9a70.
Definition Do_0ac := D_c9a70.
Definition Fo_0b0 := F_c9a74.
Definition Do_0b0 := D_c9a74.
Definition Fo_0b4 := F_c9a78.
Definition Do_0b4 := D_c9a78.
Definition Fo_0b8 := F_c9a7c.
Definition Do_0b8 := D_c9a7c.
Definition Fo_0bc := F_c9a80.
Definition Do_0bc := D_c9a80.
Definition Fo_0c0 := F_c9a84.
Definition Do_0c0 := D_c9a84.
Definition Fo_0c4 := F_c9a88.
Definition Do_0c4 := D_c9a88.
Definition Fo_0c8 := F_c9a8c.
Definition Do_0c8 := D_c9a8c.
Definition Fo_0cc := F_c9a90.
Definition Do_0cc := D_c9a90.
Definition Fo_0d0 := F_c9a94.
Definition Do_0d0 := D_c9a94.
Definition Fo_0d4 := F_c9a98.
Definition Do_0d4 := D_c9a98.
Definition Fo_0d8 := F_c9a9c.
Definition Do_0d8 := D_c9a9c.
Definition Fo_0dc := F_c9aa0.
Definition Do_0dc := D_c9aa0.
Definition Fo_0e0 := F_c9aa4.
Definition Do_0e0 := D_c9aa4.
Definition Fo_0e4 := F_c9aa8.
Definition Do_0e4 := D_c9aa8.
Definition Fo_0e8 := F_c9aac.
Definition Do_0e8 := D_c9aac.
Definition Fo_0ec := F_c9ab0.
Definition Do_0ec := D_c9ab0.
Definition Fo_0f0 := F_c9ab4.
Definition Do_0f0 := D_c9ab4.
Definition Fo_0f4 := F_c9ab8.
Definition Do_0f4 := D_c9ab8.
