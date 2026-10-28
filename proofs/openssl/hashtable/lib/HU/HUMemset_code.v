(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_2769b8 : bv 32 := 0x0e060a63.
Lemma F_2769b8 : fetch_word Ubsan.M.loaded_segments (0x2bc5a4 : word) = Some W_2769b8.
Proof. vm_refl. Qed.
Lemma D_2769b8 : decode_any W_2769b8 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2769bc : bv 32 := 0x00b50023.
Lemma F_2769bc : fetch_word Ubsan.M.loaded_segments (0x2bc5a8 : word) = Some W_2769bc.
Proof. vm_refl. Qed.
Lemma D_2769bc : decode_any W_2769bc = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2769c0 : bv 32 := 0x00c506b3.
Lemma F_2769c0 : fetch_word Ubsan.M.loaded_segments (0x2bc5ac : word) = Some W_2769c0.
Proof. vm_refl. Qed.
Lemma D_2769c0 : decode_any W_2769c0 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2769c4 : bv 32 := 0x00300713.
Lemma F_2769c4 : fetch_word Ubsan.M.loaded_segments (0x2bc5b0 : word) = Some W_2769c4.
Proof. vm_refl. Qed.
Lemma D_2769c4 : decode_any W_2769c4 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2769c8 : bv 32 := 0xfeb68fa3.
Lemma F_2769c8 : fetch_word Ubsan.M.loaded_segments (0x2bc5b4 : word) = Some W_2769c8.
Proof. vm_refl. Qed.
Lemma D_2769c8 : decode_any W_2769c8 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2769cc : bv 32 := 0x0ee66063.
Lemma F_2769cc : fetch_word Ubsan.M.loaded_segments (0x2bc5b8 : word) = Some W_2769cc.
Proof. vm_refl. Qed.
Lemma D_2769cc : decode_any W_2769cc = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2769d0 : bv 32 := 0x00b500a3.
Lemma F_2769d0 : fetch_word Ubsan.M.loaded_segments (0x2bc5bc : word) = Some W_2769d0.
Proof. vm_refl. Qed.
Lemma D_2769d0 : decode_any W_2769d0 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2769d4 : bv 32 := 0x00b50123.
Lemma F_2769d4 : fetch_word Ubsan.M.loaded_segments (0x2bc5c0 : word) = Some W_2769d4.
Proof. vm_refl. Qed.
Lemma D_2769d4 : decode_any W_2769d4 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2769d8 : bv 32 := 0x00700713.
Lemma F_2769d8 : fetch_word Ubsan.M.loaded_segments (0x2bc5c4 : word) = Some W_2769d8.
Proof. vm_refl. Qed.
Lemma D_2769d8 : decode_any W_2769d8 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2769dc : bv 32 := 0xfeb68ea3.
Lemma F_2769dc : fetch_word Ubsan.M.loaded_segments (0x2bc5c8 : word) = Some W_2769dc.
Proof. vm_refl. Qed.
Lemma D_2769dc : decode_any W_2769dc = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2769e0 : bv 32 := 0xfeb68f23.
Lemma F_2769e0 : fetch_word Ubsan.M.loaded_segments (0x2bc5cc : word) = Some W_2769e0.
Proof. vm_refl. Qed.
Lemma D_2769e0 : decode_any W_2769e0 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2769e4 : bv 32 := 0x0ce66463.
Lemma F_2769e4 : fetch_word Ubsan.M.loaded_segments (0x2bc5d0 : word) = Some W_2769e4.
Proof. vm_refl. Qed.
Lemma D_2769e4 : decode_any W_2769e4 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2769e8 : bv 32 := 0x00b501a3.
Lemma F_2769e8 : fetch_word Ubsan.M.loaded_segments (0x2bc5d4 : word) = Some W_2769e8.
Proof. vm_refl. Qed.
Lemma D_2769e8 : decode_any W_2769e8 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2769ec : bv 32 := 0x00900793.
Lemma F_2769ec : fetch_word Ubsan.M.loaded_segments (0x2bc5d8 : word) = Some W_2769ec.
Proof. vm_refl. Qed.
Lemma D_2769ec : decode_any W_2769ec = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2769f0 : bv 32 := 0xfeb68e23.
Lemma F_2769f0 : fetch_word Ubsan.M.loaded_segments (0x2bc5dc : word) = Some W_2769f0.
Proof. vm_refl. Qed.
Lemma D_2769f0 : decode_any W_2769f0 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2769f4 : bv 32 := 0x0af66c63.
Lemma F_2769f4 : fetch_word Ubsan.M.loaded_segments (0x2bc5e0 : word) = Some W_2769f4.
Proof. vm_refl. Qed.
Lemma D_2769f4 : decode_any W_2769f4 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2769f8 : bv 32 := 0x40a006bb.
Lemma F_2769f8 : fetch_word Ubsan.M.loaded_segments (0x2bc5e4 : word) = Some W_2769f8.
Proof. vm_refl. Qed.
Lemma D_2769f8 : decode_any W_2769f8 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2769fc : bv 32 := 0x03859813.
Lemma F_2769fc : fetch_word Ubsan.M.loaded_segments (0x2bc5e8 : word) = Some W_2769fc.
Proof. vm_refl. Qed.
Lemma D_2769fc : decode_any W_2769fc = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a00 : bv 32 := 0x101015b7.
Lemma F_276a00 : fetch_word Ubsan.M.loaded_segments (0x2bc5ec : word) = Some W_276a00.
Proof. vm_refl. Qed.
Lemma D_276a00 : decode_any W_276a00 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a04 : bv 32 := 0x0036f693.
Lemma F_276a04 : fetch_word Ubsan.M.loaded_segments (0x2bc5f0 : word) = Some W_276a04.
Proof. vm_refl. Qed.
Lemma D_276a04 : decode_any W_276a04 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a08 : bv 32 := 0x00459713.
Lemma F_276a08 : fetch_word Ubsan.M.loaded_segments (0x2bc5f4 : word) = Some W_276a08.
Proof. vm_refl. Qed.
Lemma D_276a08 : decode_any W_276a08 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a0c : bv 32 := 0x40d60633.
Lemma F_276a0c : fetch_word Ubsan.M.loaded_segments (0x2bc5f8 : word) = Some W_276a0c.
Proof. vm_refl. Qed.
Lemma D_276a0c : decode_any W_276a0c = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a10 : bv 32 := 0x00d505b3.
Lemma F_276a10 : fetch_word Ubsan.M.loaded_segments (0x2bc5fc : word) = Some W_276a10.
Proof. vm_refl. Qed.
Lemma D_276a10 : decode_any W_276a10 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a14 : bv 32 := 0x10070693.
Lemma F_276a14 : fetch_word Ubsan.M.loaded_segments (0x2bc600 : word) = Some W_276a14.
Proof. vm_refl. Qed.
Lemma D_276a14 : decode_any W_276a14 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a18 : bv 32 := 0xffc67713.
Lemma F_276a18 : fetch_word Ubsan.M.loaded_segments (0x2bc604 : word) = Some W_276a18.
Proof. vm_refl. Qed.
Lemma D_276a18 : decode_any W_276a18 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a1c : bv 32 := 0x02d83633.
Lemma F_276a1c : fetch_word Ubsan.M.loaded_segments (0x2bc608 : word) = Some W_276a1c.
Proof. vm_refl. Qed.
Lemma D_276a1c : decode_any W_276a1c = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a20 : bv 32 := 0x00c5a023.
Lemma F_276a20 : fetch_word Ubsan.M.loaded_segments (0x2bc60c : word) = Some W_276a20.
Proof. vm_refl. Qed.
Lemma D_276a20 : decode_any W_276a20 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a24 : bv 32 := 0x00e586b3.
Lemma F_276a24 : fetch_word Ubsan.M.loaded_segments (0x2bc610 : word) = Some W_276a24.
Proof. vm_refl. Qed.
Lemma D_276a24 : decode_any W_276a24 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a28 : bv 32 := 0xfec6ae23.
Lemma F_276a28 : fetch_word Ubsan.M.loaded_segments (0x2bc614 : word) = Some W_276a28.
Proof. vm_refl. Qed.
Lemma D_276a28 : decode_any W_276a28 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a2c : bv 32 := 0x08f76063.
Lemma F_276a2c : fetch_word Ubsan.M.loaded_segments (0x2bc618 : word) = Some W_276a2c.
Proof. vm_refl. Qed.
Lemma D_276a2c : decode_any W_276a2c = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a30 : bv 32 := 0x00c5a223.
Lemma F_276a30 : fetch_word Ubsan.M.loaded_segments (0x2bc61c : word) = Some W_276a30.
Proof. vm_refl. Qed.
Lemma D_276a30 : decode_any W_276a30 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a34 : bv 32 := 0x00c5a423.
Lemma F_276a34 : fetch_word Ubsan.M.loaded_segments (0x2bc620 : word) = Some W_276a34.
Proof. vm_refl. Qed.
Lemma D_276a34 : decode_any W_276a34 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a38 : bv 32 := 0x01900793.
Lemma F_276a38 : fetch_word Ubsan.M.loaded_segments (0x2bc624 : word) = Some W_276a38.
Proof. vm_refl. Qed.
Lemma D_276a38 : decode_any W_276a38 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a3c : bv 32 := 0xfec6aa23.
Lemma F_276a3c : fetch_word Ubsan.M.loaded_segments (0x2bc628 : word) = Some W_276a3c.
Proof. vm_refl. Qed.
Lemma D_276a3c : decode_any W_276a3c = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a40 : bv 32 := 0xfec6ac23.
Lemma F_276a40 : fetch_word Ubsan.M.loaded_segments (0x2bc62c : word) = Some W_276a40.
Proof. vm_refl. Qed.
Lemma D_276a40 : decode_any W_276a40 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a44 : bv 32 := 0x06f76463.
Lemma F_276a44 : fetch_word Ubsan.M.loaded_segments (0x2bc630 : word) = Some W_276a44.
Proof. vm_refl. Qed.
Lemma D_276a44 : decode_any W_276a44 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a48 : bv 32 := 0x00c5a623.
Lemma F_276a48 : fetch_word Ubsan.M.loaded_segments (0x2bc634 : word) = Some W_276a48.
Proof. vm_refl. Qed.
Lemma D_276a48 : decode_any W_276a48 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a4c : bv 32 := 0x00c5a823.
Lemma F_276a4c : fetch_word Ubsan.M.loaded_segments (0x2bc638 : word) = Some W_276a4c.
Proof. vm_refl. Qed.
Lemma D_276a4c : decode_any W_276a4c = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a50 : bv 32 := 0x00c5aa23.
Lemma F_276a50 : fetch_word Ubsan.M.loaded_segments (0x2bc63c : word) = Some W_276a50.
Proof. vm_refl. Qed.
Lemma D_276a50 : decode_any W_276a50 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a54 : bv 32 := 0x00c5ac23.
Lemma F_276a54 : fetch_word Ubsan.M.loaded_segments (0x2bc640 : word) = Some W_276a54.
Proof. vm_refl. Qed.
Lemma D_276a54 : decode_any W_276a54 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a58 : bv 32 := 0x0045f793.
Lemma F_276a58 : fetch_word Ubsan.M.loaded_segments (0x2bc644 : word) = Some W_276a58.
Proof. vm_refl. Qed.
Lemma D_276a58 : decode_any W_276a58 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a5c : bv 32 := 0x02000813.
Lemma F_276a5c : fetch_word Ubsan.M.loaded_segments (0x2bc648 : word) = Some W_276a5c.
Proof. vm_refl. Qed.
Lemma D_276a5c : decode_any W_276a5c = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a60 : bv 32 := 0x01878793.
Lemma F_276a60 : fetch_word Ubsan.M.loaded_segments (0x2bc64c : word) = Some W_276a60.
Proof. vm_refl. Qed.
Lemma D_276a60 : decode_any W_276a60 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a64 : bv 32 := 0x40f70733.
Lemma F_276a64 : fetch_word Ubsan.M.loaded_segments (0x2bc650 : word) = Some W_276a64.
Proof. vm_refl. Qed.
Lemma D_276a64 : decode_any W_276a64 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a68 : bv 32 := 0xfec6a223.
Lemma F_276a68 : fetch_word Ubsan.M.loaded_segments (0x2bc654 : word) = Some W_276a68.
Proof. vm_refl. Qed.
Lemma D_276a68 : decode_any W_276a68 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a6c : bv 32 := 0xfec6a423.
Lemma F_276a6c : fetch_word Ubsan.M.loaded_segments (0x2bc658 : word) = Some W_276a6c.
Proof. vm_refl. Qed.
Lemma D_276a6c : decode_any W_276a6c = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a70 : bv 32 := 0xfec6a623.
Lemma F_276a70 : fetch_word Ubsan.M.loaded_segments (0x2bc65c : word) = Some W_276a70.
Proof. vm_refl. Qed.
Lemma D_276a70 : decode_any W_276a70 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a74 : bv 32 := 0xfec6a823.
Lemma F_276a74 : fetch_word Ubsan.M.loaded_segments (0x2bc660 : word) = Some W_276a74.
Proof. vm_refl. Qed.
Lemma D_276a74 : decode_any W_276a74 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a78 : bv 32 := 0x03076a63.
Lemma F_276a78 : fetch_word Ubsan.M.loaded_segments (0x2bc664 : word) = Some W_276a78.
Proof. vm_refl. Qed.
Lemma D_276a78 : decode_any W_276a78 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a7c : bv 32 := 0x02061613.
Lemma F_276a7c : fetch_word Ubsan.M.loaded_segments (0x2bc668 : word) = Some W_276a7c.
Proof. vm_refl. Qed.
Lemma D_276a7c : decode_any W_276a7c = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a80 : bv 32 := 0x00f585b3.
Lemma F_276a80 : fetch_word Ubsan.M.loaded_segments (0x2bc66c : word) = Some W_276a80.
Proof. vm_refl. Qed.
Lemma D_276a80 : decode_any W_276a80 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a84 : bv 32 := 0x02065693.
Lemma F_276a84 : fetch_word Ubsan.M.loaded_segments (0x2bc670 : word) = Some W_276a84.
Proof. vm_refl. Qed.
Lemma D_276a84 : decode_any W_276a84 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a88 : bv 32 := 0x00d66633.
Lemma F_276a88 : fetch_word Ubsan.M.loaded_segments (0x2bc674 : word) = Some W_276a88.
Proof. vm_refl. Qed.
Lemma D_276a88 : decode_any W_276a88 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a8c : bv 32 := 0x01f00693.
Lemma F_276a8c : fetch_word Ubsan.M.loaded_segments (0x2bc678 : word) = Some W_276a8c.
Proof. vm_refl. Qed.
Lemma D_276a8c : decode_any W_276a8c = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a90 : bv 32 := 0x00c5b023.
Lemma F_276a90 : fetch_word Ubsan.M.loaded_segments (0x2bc67c : word) = Some W_276a90.
Proof. vm_refl. Qed.
Lemma D_276a90 : decode_any W_276a90 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a94 : bv 32 := 0x00c5b423.
Lemma F_276a94 : fetch_word Ubsan.M.loaded_segments (0x2bc680 : word) = Some W_276a94.
Proof. vm_refl. Qed.
Lemma D_276a94 : decode_any W_276a94 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a98 : bv 32 := 0x00c5b823.
Lemma F_276a98 : fetch_word Ubsan.M.loaded_segments (0x2bc684 : word) = Some W_276a98.
Proof. vm_refl. Qed.
Lemma D_276a98 : decode_any W_276a98 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276a9c : bv 32 := 0x00c5bc23.
Lemma F_276a9c : fetch_word Ubsan.M.loaded_segments (0x2bc688 : word) = Some W_276a9c.
Proof. vm_refl. Qed.
Lemma D_276a9c : decode_any W_276a9c = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276aa0 : bv 32 := 0xfe070713.
Lemma F_276aa0 : fetch_word Ubsan.M.loaded_segments (0x2bc68c : word) = Some W_276aa0.
Proof. vm_refl. Qed.
Lemma D_276aa0 : decode_any W_276aa0 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276aa4 : bv 32 := 0x02058593.
Lemma F_276aa4 : fetch_word Ubsan.M.loaded_segments (0x2bc690 : word) = Some W_276aa4.
Proof. vm_refl. Qed.
Lemma D_276aa4 : decode_any W_276aa4 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276aa8 : bv 32 := 0xfee6e4e3.
Lemma F_276aa8 : fetch_word Ubsan.M.loaded_segments (0x2bc694 : word) = Some W_276aa8.
Proof. vm_refl. Qed.
Lemma D_276aa8 : decode_any W_276aa8 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_276aac : bv 32 := 0x00008067.
Lemma F_276aac : fetch_word Ubsan.M.loaded_segments (0x2bc698 : word) = Some W_276aac.
Proof. vm_refl. Qed.
Lemma D_276aac : decode_any W_276aac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := Ubsan.M.loaded_segments.
Definition ms_base : Z := 0x2bc5a4%Z.
Definition Fo_000 := F_2769b8.
Definition Do_000 := D_2769b8.
Definition Fo_004 := F_2769bc.
Definition Do_004 := D_2769bc.
Definition Fo_008 := F_2769c0.
Definition Do_008 := D_2769c0.
Definition Fo_00c := F_2769c4.
Definition Do_00c := D_2769c4.
Definition Fo_010 := F_2769c8.
Definition Do_010 := D_2769c8.
Definition Fo_014 := F_2769cc.
Definition Do_014 := D_2769cc.
Definition Fo_018 := F_2769d0.
Definition Do_018 := D_2769d0.
Definition Fo_01c := F_2769d4.
Definition Do_01c := D_2769d4.
Definition Fo_020 := F_2769d8.
Definition Do_020 := D_2769d8.
Definition Fo_024 := F_2769dc.
Definition Do_024 := D_2769dc.
Definition Fo_028 := F_2769e0.
Definition Do_028 := D_2769e0.
Definition Fo_02c := F_2769e4.
Definition Do_02c := D_2769e4.
Definition Fo_030 := F_2769e8.
Definition Do_030 := D_2769e8.
Definition Fo_034 := F_2769ec.
Definition Do_034 := D_2769ec.
Definition Fo_038 := F_2769f0.
Definition Do_038 := D_2769f0.
Definition Fo_03c := F_2769f4.
Definition Do_03c := D_2769f4.
Definition Fo_040 := F_2769f8.
Definition Do_040 := D_2769f8.
Definition Fo_044 := F_2769fc.
Definition Do_044 := D_2769fc.
Definition Fo_048 := F_276a00.
Definition Do_048 := D_276a00.
Definition Fo_04c := F_276a04.
Definition Do_04c := D_276a04.
Definition Fo_050 := F_276a08.
Definition Do_050 := D_276a08.
Definition Fo_054 := F_276a0c.
Definition Do_054 := D_276a0c.
Definition Fo_058 := F_276a10.
Definition Do_058 := D_276a10.
Definition Fo_05c := F_276a14.
Definition Do_05c := D_276a14.
Definition Fo_060 := F_276a18.
Definition Do_060 := D_276a18.
Definition Fo_064 := F_276a1c.
Definition Do_064 := D_276a1c.
Definition Fo_068 := F_276a20.
Definition Do_068 := D_276a20.
Definition Fo_06c := F_276a24.
Definition Do_06c := D_276a24.
Definition Fo_070 := F_276a28.
Definition Do_070 := D_276a28.
Definition Fo_074 := F_276a2c.
Definition Do_074 := D_276a2c.
Definition Fo_078 := F_276a30.
Definition Do_078 := D_276a30.
Definition Fo_07c := F_276a34.
Definition Do_07c := D_276a34.
Definition Fo_080 := F_276a38.
Definition Do_080 := D_276a38.
Definition Fo_084 := F_276a3c.
Definition Do_084 := D_276a3c.
Definition Fo_088 := F_276a40.
Definition Do_088 := D_276a40.
Definition Fo_08c := F_276a44.
Definition Do_08c := D_276a44.
Definition Fo_090 := F_276a48.
Definition Do_090 := D_276a48.
Definition Fo_094 := F_276a4c.
Definition Do_094 := D_276a4c.
Definition Fo_098 := F_276a50.
Definition Do_098 := D_276a50.
Definition Fo_09c := F_276a54.
Definition Do_09c := D_276a54.
Definition Fo_0a0 := F_276a58.
Definition Do_0a0 := D_276a58.
Definition Fo_0a4 := F_276a5c.
Definition Do_0a4 := D_276a5c.
Definition Fo_0a8 := F_276a60.
Definition Do_0a8 := D_276a60.
Definition Fo_0ac := F_276a64.
Definition Do_0ac := D_276a64.
Definition Fo_0b0 := F_276a68.
Definition Do_0b0 := D_276a68.
Definition Fo_0b4 := F_276a6c.
Definition Do_0b4 := D_276a6c.
Definition Fo_0b8 := F_276a70.
Definition Do_0b8 := D_276a70.
Definition Fo_0bc := F_276a74.
Definition Do_0bc := D_276a74.
Definition Fo_0c0 := F_276a78.
Definition Do_0c0 := D_276a78.
Definition Fo_0c4 := F_276a7c.
Definition Do_0c4 := D_276a7c.
Definition Fo_0c8 := F_276a80.
Definition Do_0c8 := D_276a80.
Definition Fo_0cc := F_276a84.
Definition Do_0cc := D_276a84.
Definition Fo_0d0 := F_276a88.
Definition Do_0d0 := D_276a88.
Definition Fo_0d4 := F_276a8c.
Definition Do_0d4 := D_276a8c.
Definition Fo_0d8 := F_276a90.
Definition Do_0d8 := D_276a90.
Definition Fo_0dc := F_276a94.
Definition Do_0dc := D_276a94.
Definition Fo_0e0 := F_276a98.
Definition Do_0e0 := D_276a98.
Definition Fo_0e4 := F_276a9c.
Definition Do_0e4 := D_276a9c.
Definition Fo_0e8 := F_276aa0.
Definition Do_0e8 := D_276aa0.
Definition Fo_0ec := F_276aa4.
Definition Do_0ec := D_276aa4.
Definition Fo_0f0 := F_276aa8.
Definition Do_0f0 := D_276aa8.
Definition Fo_0f4 := F_276aac.
Definition Do_0f4 := D_276aac.
