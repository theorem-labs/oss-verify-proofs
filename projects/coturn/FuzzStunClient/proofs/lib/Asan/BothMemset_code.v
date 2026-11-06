(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_a2bec : bv 32 := 0x0e060a63.
Lemma F_a2bec : fetch_word AsanUbsan.M.loaded_segments (0xa2bec : word) = Some W_a2bec.
Proof. vm_refl. Qed.
Lemma D_a2bec : decode_any W_a2bec = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2bf0 : bv 32 := 0x00b50023.
Lemma F_a2bf0 : fetch_word AsanUbsan.M.loaded_segments (0xa2bf0 : word) = Some W_a2bf0.
Proof. vm_refl. Qed.
Lemma D_a2bf0 : decode_any W_a2bf0 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2bf4 : bv 32 := 0x00c506b3.
Lemma F_a2bf4 : fetch_word AsanUbsan.M.loaded_segments (0xa2bf4 : word) = Some W_a2bf4.
Proof. vm_refl. Qed.
Lemma D_a2bf4 : decode_any W_a2bf4 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2bf8 : bv 32 := 0x00300713.
Lemma F_a2bf8 : fetch_word AsanUbsan.M.loaded_segments (0xa2bf8 : word) = Some W_a2bf8.
Proof. vm_refl. Qed.
Lemma D_a2bf8 : decode_any W_a2bf8 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2bfc : bv 32 := 0xfeb68fa3.
Lemma F_a2bfc : fetch_word AsanUbsan.M.loaded_segments (0xa2bfc : word) = Some W_a2bfc.
Proof. vm_refl. Qed.
Lemma D_a2bfc : decode_any W_a2bfc = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c00 : bv 32 := 0x0ee66063.
Lemma F_a2c00 : fetch_word AsanUbsan.M.loaded_segments (0xa2c00 : word) = Some W_a2c00.
Proof. vm_refl. Qed.
Lemma D_a2c00 : decode_any W_a2c00 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c04 : bv 32 := 0x00b500a3.
Lemma F_a2c04 : fetch_word AsanUbsan.M.loaded_segments (0xa2c04 : word) = Some W_a2c04.
Proof. vm_refl. Qed.
Lemma D_a2c04 : decode_any W_a2c04 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c08 : bv 32 := 0x00b50123.
Lemma F_a2c08 : fetch_word AsanUbsan.M.loaded_segments (0xa2c08 : word) = Some W_a2c08.
Proof. vm_refl. Qed.
Lemma D_a2c08 : decode_any W_a2c08 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c0c : bv 32 := 0x00700713.
Lemma F_a2c0c : fetch_word AsanUbsan.M.loaded_segments (0xa2c0c : word) = Some W_a2c0c.
Proof. vm_refl. Qed.
Lemma D_a2c0c : decode_any W_a2c0c = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c10 : bv 32 := 0xfeb68ea3.
Lemma F_a2c10 : fetch_word AsanUbsan.M.loaded_segments (0xa2c10 : word) = Some W_a2c10.
Proof. vm_refl. Qed.
Lemma D_a2c10 : decode_any W_a2c10 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c14 : bv 32 := 0xfeb68f23.
Lemma F_a2c14 : fetch_word AsanUbsan.M.loaded_segments (0xa2c14 : word) = Some W_a2c14.
Proof. vm_refl. Qed.
Lemma D_a2c14 : decode_any W_a2c14 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c18 : bv 32 := 0x0ce66463.
Lemma F_a2c18 : fetch_word AsanUbsan.M.loaded_segments (0xa2c18 : word) = Some W_a2c18.
Proof. vm_refl. Qed.
Lemma D_a2c18 : decode_any W_a2c18 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c1c : bv 32 := 0x00b501a3.
Lemma F_a2c1c : fetch_word AsanUbsan.M.loaded_segments (0xa2c1c : word) = Some W_a2c1c.
Proof. vm_refl. Qed.
Lemma D_a2c1c : decode_any W_a2c1c = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c20 : bv 32 := 0x00900793.
Lemma F_a2c20 : fetch_word AsanUbsan.M.loaded_segments (0xa2c20 : word) = Some W_a2c20.
Proof. vm_refl. Qed.
Lemma D_a2c20 : decode_any W_a2c20 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c24 : bv 32 := 0xfeb68e23.
Lemma F_a2c24 : fetch_word AsanUbsan.M.loaded_segments (0xa2c24 : word) = Some W_a2c24.
Proof. vm_refl. Qed.
Lemma D_a2c24 : decode_any W_a2c24 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c28 : bv 32 := 0x0af66c63.
Lemma F_a2c28 : fetch_word AsanUbsan.M.loaded_segments (0xa2c28 : word) = Some W_a2c28.
Proof. vm_refl. Qed.
Lemma D_a2c28 : decode_any W_a2c28 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c2c : bv 32 := 0x40a006bb.
Lemma F_a2c2c : fetch_word AsanUbsan.M.loaded_segments (0xa2c2c : word) = Some W_a2c2c.
Proof. vm_refl. Qed.
Lemma D_a2c2c : decode_any W_a2c2c = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c30 : bv 32 := 0x03859813.
Lemma F_a2c30 : fetch_word AsanUbsan.M.loaded_segments (0xa2c30 : word) = Some W_a2c30.
Proof. vm_refl. Qed.
Lemma D_a2c30 : decode_any W_a2c30 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c34 : bv 32 := 0x101015b7.
Lemma F_a2c34 : fetch_word AsanUbsan.M.loaded_segments (0xa2c34 : word) = Some W_a2c34.
Proof. vm_refl. Qed.
Lemma D_a2c34 : decode_any W_a2c34 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c38 : bv 32 := 0x0036f693.
Lemma F_a2c38 : fetch_word AsanUbsan.M.loaded_segments (0xa2c38 : word) = Some W_a2c38.
Proof. vm_refl. Qed.
Lemma D_a2c38 : decode_any W_a2c38 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c3c : bv 32 := 0x00459713.
Lemma F_a2c3c : fetch_word AsanUbsan.M.loaded_segments (0xa2c3c : word) = Some W_a2c3c.
Proof. vm_refl. Qed.
Lemma D_a2c3c : decode_any W_a2c3c = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c40 : bv 32 := 0x40d60633.
Lemma F_a2c40 : fetch_word AsanUbsan.M.loaded_segments (0xa2c40 : word) = Some W_a2c40.
Proof. vm_refl. Qed.
Lemma D_a2c40 : decode_any W_a2c40 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c44 : bv 32 := 0x00d505b3.
Lemma F_a2c44 : fetch_word AsanUbsan.M.loaded_segments (0xa2c44 : word) = Some W_a2c44.
Proof. vm_refl. Qed.
Lemma D_a2c44 : decode_any W_a2c44 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c48 : bv 32 := 0x10070693.
Lemma F_a2c48 : fetch_word AsanUbsan.M.loaded_segments (0xa2c48 : word) = Some W_a2c48.
Proof. vm_refl. Qed.
Lemma D_a2c48 : decode_any W_a2c48 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c4c : bv 32 := 0xffc67713.
Lemma F_a2c4c : fetch_word AsanUbsan.M.loaded_segments (0xa2c4c : word) = Some W_a2c4c.
Proof. vm_refl. Qed.
Lemma D_a2c4c : decode_any W_a2c4c = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c50 : bv 32 := 0x02d83633.
Lemma F_a2c50 : fetch_word AsanUbsan.M.loaded_segments (0xa2c50 : word) = Some W_a2c50.
Proof. vm_refl. Qed.
Lemma D_a2c50 : decode_any W_a2c50 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c54 : bv 32 := 0x00c5a023.
Lemma F_a2c54 : fetch_word AsanUbsan.M.loaded_segments (0xa2c54 : word) = Some W_a2c54.
Proof. vm_refl. Qed.
Lemma D_a2c54 : decode_any W_a2c54 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c58 : bv 32 := 0x00e586b3.
Lemma F_a2c58 : fetch_word AsanUbsan.M.loaded_segments (0xa2c58 : word) = Some W_a2c58.
Proof. vm_refl. Qed.
Lemma D_a2c58 : decode_any W_a2c58 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c5c : bv 32 := 0xfec6ae23.
Lemma F_a2c5c : fetch_word AsanUbsan.M.loaded_segments (0xa2c5c : word) = Some W_a2c5c.
Proof. vm_refl. Qed.
Lemma D_a2c5c : decode_any W_a2c5c = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c60 : bv 32 := 0x08f76063.
Lemma F_a2c60 : fetch_word AsanUbsan.M.loaded_segments (0xa2c60 : word) = Some W_a2c60.
Proof. vm_refl. Qed.
Lemma D_a2c60 : decode_any W_a2c60 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c64 : bv 32 := 0x00c5a223.
Lemma F_a2c64 : fetch_word AsanUbsan.M.loaded_segments (0xa2c64 : word) = Some W_a2c64.
Proof. vm_refl. Qed.
Lemma D_a2c64 : decode_any W_a2c64 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c68 : bv 32 := 0x00c5a423.
Lemma F_a2c68 : fetch_word AsanUbsan.M.loaded_segments (0xa2c68 : word) = Some W_a2c68.
Proof. vm_refl. Qed.
Lemma D_a2c68 : decode_any W_a2c68 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c6c : bv 32 := 0x01900793.
Lemma F_a2c6c : fetch_word AsanUbsan.M.loaded_segments (0xa2c6c : word) = Some W_a2c6c.
Proof. vm_refl. Qed.
Lemma D_a2c6c : decode_any W_a2c6c = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c70 : bv 32 := 0xfec6aa23.
Lemma F_a2c70 : fetch_word AsanUbsan.M.loaded_segments (0xa2c70 : word) = Some W_a2c70.
Proof. vm_refl. Qed.
Lemma D_a2c70 : decode_any W_a2c70 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c74 : bv 32 := 0xfec6ac23.
Lemma F_a2c74 : fetch_word AsanUbsan.M.loaded_segments (0xa2c74 : word) = Some W_a2c74.
Proof. vm_refl. Qed.
Lemma D_a2c74 : decode_any W_a2c74 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c78 : bv 32 := 0x06f76463.
Lemma F_a2c78 : fetch_word AsanUbsan.M.loaded_segments (0xa2c78 : word) = Some W_a2c78.
Proof. vm_refl. Qed.
Lemma D_a2c78 : decode_any W_a2c78 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c7c : bv 32 := 0x00c5a623.
Lemma F_a2c7c : fetch_word AsanUbsan.M.loaded_segments (0xa2c7c : word) = Some W_a2c7c.
Proof. vm_refl. Qed.
Lemma D_a2c7c : decode_any W_a2c7c = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c80 : bv 32 := 0x00c5a823.
Lemma F_a2c80 : fetch_word AsanUbsan.M.loaded_segments (0xa2c80 : word) = Some W_a2c80.
Proof. vm_refl. Qed.
Lemma D_a2c80 : decode_any W_a2c80 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c84 : bv 32 := 0x00c5aa23.
Lemma F_a2c84 : fetch_word AsanUbsan.M.loaded_segments (0xa2c84 : word) = Some W_a2c84.
Proof. vm_refl. Qed.
Lemma D_a2c84 : decode_any W_a2c84 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c88 : bv 32 := 0x00c5ac23.
Lemma F_a2c88 : fetch_word AsanUbsan.M.loaded_segments (0xa2c88 : word) = Some W_a2c88.
Proof. vm_refl. Qed.
Lemma D_a2c88 : decode_any W_a2c88 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c8c : bv 32 := 0x0045f793.
Lemma F_a2c8c : fetch_word AsanUbsan.M.loaded_segments (0xa2c8c : word) = Some W_a2c8c.
Proof. vm_refl. Qed.
Lemma D_a2c8c : decode_any W_a2c8c = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c90 : bv 32 := 0x02000813.
Lemma F_a2c90 : fetch_word AsanUbsan.M.loaded_segments (0xa2c90 : word) = Some W_a2c90.
Proof. vm_refl. Qed.
Lemma D_a2c90 : decode_any W_a2c90 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c94 : bv 32 := 0x01878793.
Lemma F_a2c94 : fetch_word AsanUbsan.M.loaded_segments (0xa2c94 : word) = Some W_a2c94.
Proof. vm_refl. Qed.
Lemma D_a2c94 : decode_any W_a2c94 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c98 : bv 32 := 0x40f70733.
Lemma F_a2c98 : fetch_word AsanUbsan.M.loaded_segments (0xa2c98 : word) = Some W_a2c98.
Proof. vm_refl. Qed.
Lemma D_a2c98 : decode_any W_a2c98 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2c9c : bv 32 := 0xfec6a223.
Lemma F_a2c9c : fetch_word AsanUbsan.M.loaded_segments (0xa2c9c : word) = Some W_a2c9c.
Proof. vm_refl. Qed.
Lemma D_a2c9c : decode_any W_a2c9c = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ca0 : bv 32 := 0xfec6a423.
Lemma F_a2ca0 : fetch_word AsanUbsan.M.loaded_segments (0xa2ca0 : word) = Some W_a2ca0.
Proof. vm_refl. Qed.
Lemma D_a2ca0 : decode_any W_a2ca0 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ca4 : bv 32 := 0xfec6a623.
Lemma F_a2ca4 : fetch_word AsanUbsan.M.loaded_segments (0xa2ca4 : word) = Some W_a2ca4.
Proof. vm_refl. Qed.
Lemma D_a2ca4 : decode_any W_a2ca4 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ca8 : bv 32 := 0xfec6a823.
Lemma F_a2ca8 : fetch_word AsanUbsan.M.loaded_segments (0xa2ca8 : word) = Some W_a2ca8.
Proof. vm_refl. Qed.
Lemma D_a2ca8 : decode_any W_a2ca8 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cac : bv 32 := 0x03076a63.
Lemma F_a2cac : fetch_word AsanUbsan.M.loaded_segments (0xa2cac : word) = Some W_a2cac.
Proof. vm_refl. Qed.
Lemma D_a2cac : decode_any W_a2cac = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cb0 : bv 32 := 0x02061613.
Lemma F_a2cb0 : fetch_word AsanUbsan.M.loaded_segments (0xa2cb0 : word) = Some W_a2cb0.
Proof. vm_refl. Qed.
Lemma D_a2cb0 : decode_any W_a2cb0 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cb4 : bv 32 := 0x00f585b3.
Lemma F_a2cb4 : fetch_word AsanUbsan.M.loaded_segments (0xa2cb4 : word) = Some W_a2cb4.
Proof. vm_refl. Qed.
Lemma D_a2cb4 : decode_any W_a2cb4 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cb8 : bv 32 := 0x02065693.
Lemma F_a2cb8 : fetch_word AsanUbsan.M.loaded_segments (0xa2cb8 : word) = Some W_a2cb8.
Proof. vm_refl. Qed.
Lemma D_a2cb8 : decode_any W_a2cb8 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cbc : bv 32 := 0x00d66633.
Lemma F_a2cbc : fetch_word AsanUbsan.M.loaded_segments (0xa2cbc : word) = Some W_a2cbc.
Proof. vm_refl. Qed.
Lemma D_a2cbc : decode_any W_a2cbc = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cc0 : bv 32 := 0x01f00693.
Lemma F_a2cc0 : fetch_word AsanUbsan.M.loaded_segments (0xa2cc0 : word) = Some W_a2cc0.
Proof. vm_refl. Qed.
Lemma D_a2cc0 : decode_any W_a2cc0 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cc4 : bv 32 := 0x00c5b023.
Lemma F_a2cc4 : fetch_word AsanUbsan.M.loaded_segments (0xa2cc4 : word) = Some W_a2cc4.
Proof. vm_refl. Qed.
Lemma D_a2cc4 : decode_any W_a2cc4 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cc8 : bv 32 := 0x00c5b423.
Lemma F_a2cc8 : fetch_word AsanUbsan.M.loaded_segments (0xa2cc8 : word) = Some W_a2cc8.
Proof. vm_refl. Qed.
Lemma D_a2cc8 : decode_any W_a2cc8 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ccc : bv 32 := 0x00c5b823.
Lemma F_a2ccc : fetch_word AsanUbsan.M.loaded_segments (0xa2ccc : word) = Some W_a2ccc.
Proof. vm_refl. Qed.
Lemma D_a2ccc : decode_any W_a2ccc = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cd0 : bv 32 := 0x00c5bc23.
Lemma F_a2cd0 : fetch_word AsanUbsan.M.loaded_segments (0xa2cd0 : word) = Some W_a2cd0.
Proof. vm_refl. Qed.
Lemma D_a2cd0 : decode_any W_a2cd0 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cd4 : bv 32 := 0xfe070713.
Lemma F_a2cd4 : fetch_word AsanUbsan.M.loaded_segments (0xa2cd4 : word) = Some W_a2cd4.
Proof. vm_refl. Qed.
Lemma D_a2cd4 : decode_any W_a2cd4 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cd8 : bv 32 := 0x02058593.
Lemma F_a2cd8 : fetch_word AsanUbsan.M.loaded_segments (0xa2cd8 : word) = Some W_a2cd8.
Proof. vm_refl. Qed.
Lemma D_a2cd8 : decode_any W_a2cd8 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2cdc : bv 32 := 0xfee6e4e3.
Lemma F_a2cdc : fetch_word AsanUbsan.M.loaded_segments (0xa2cdc : word) = Some W_a2cdc.
Proof. vm_refl. Qed.
Lemma D_a2cdc : decode_any W_a2cdc = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ce0 : bv 32 := 0x00008067.
Lemma F_a2ce0 : fetch_word AsanUbsan.M.loaded_segments (0xa2ce0 : word) = Some W_a2ce0.
Proof. vm_refl. Qed.
Lemma D_a2ce0 : decode_any W_a2ce0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0xa2bec%Z.
Definition Fo_000 := F_a2bec.
Definition Do_000 := D_a2bec.
Definition Fo_004 := F_a2bf0.
Definition Do_004 := D_a2bf0.
Definition Fo_008 := F_a2bf4.
Definition Do_008 := D_a2bf4.
Definition Fo_00c := F_a2bf8.
Definition Do_00c := D_a2bf8.
Definition Fo_010 := F_a2bfc.
Definition Do_010 := D_a2bfc.
Definition Fo_014 := F_a2c00.
Definition Do_014 := D_a2c00.
Definition Fo_018 := F_a2c04.
Definition Do_018 := D_a2c04.
Definition Fo_01c := F_a2c08.
Definition Do_01c := D_a2c08.
Definition Fo_020 := F_a2c0c.
Definition Do_020 := D_a2c0c.
Definition Fo_024 := F_a2c10.
Definition Do_024 := D_a2c10.
Definition Fo_028 := F_a2c14.
Definition Do_028 := D_a2c14.
Definition Fo_02c := F_a2c18.
Definition Do_02c := D_a2c18.
Definition Fo_030 := F_a2c1c.
Definition Do_030 := D_a2c1c.
Definition Fo_034 := F_a2c20.
Definition Do_034 := D_a2c20.
Definition Fo_038 := F_a2c24.
Definition Do_038 := D_a2c24.
Definition Fo_03c := F_a2c28.
Definition Do_03c := D_a2c28.
Definition Fo_040 := F_a2c2c.
Definition Do_040 := D_a2c2c.
Definition Fo_044 := F_a2c30.
Definition Do_044 := D_a2c30.
Definition Fo_048 := F_a2c34.
Definition Do_048 := D_a2c34.
Definition Fo_04c := F_a2c38.
Definition Do_04c := D_a2c38.
Definition Fo_050 := F_a2c3c.
Definition Do_050 := D_a2c3c.
Definition Fo_054 := F_a2c40.
Definition Do_054 := D_a2c40.
Definition Fo_058 := F_a2c44.
Definition Do_058 := D_a2c44.
Definition Fo_05c := F_a2c48.
Definition Do_05c := D_a2c48.
Definition Fo_060 := F_a2c4c.
Definition Do_060 := D_a2c4c.
Definition Fo_064 := F_a2c50.
Definition Do_064 := D_a2c50.
Definition Fo_068 := F_a2c54.
Definition Do_068 := D_a2c54.
Definition Fo_06c := F_a2c58.
Definition Do_06c := D_a2c58.
Definition Fo_070 := F_a2c5c.
Definition Do_070 := D_a2c5c.
Definition Fo_074 := F_a2c60.
Definition Do_074 := D_a2c60.
Definition Fo_078 := F_a2c64.
Definition Do_078 := D_a2c64.
Definition Fo_07c := F_a2c68.
Definition Do_07c := D_a2c68.
Definition Fo_080 := F_a2c6c.
Definition Do_080 := D_a2c6c.
Definition Fo_084 := F_a2c70.
Definition Do_084 := D_a2c70.
Definition Fo_088 := F_a2c74.
Definition Do_088 := D_a2c74.
Definition Fo_08c := F_a2c78.
Definition Do_08c := D_a2c78.
Definition Fo_090 := F_a2c7c.
Definition Do_090 := D_a2c7c.
Definition Fo_094 := F_a2c80.
Definition Do_094 := D_a2c80.
Definition Fo_098 := F_a2c84.
Definition Do_098 := D_a2c84.
Definition Fo_09c := F_a2c88.
Definition Do_09c := D_a2c88.
Definition Fo_0a0 := F_a2c8c.
Definition Do_0a0 := D_a2c8c.
Definition Fo_0a4 := F_a2c90.
Definition Do_0a4 := D_a2c90.
Definition Fo_0a8 := F_a2c94.
Definition Do_0a8 := D_a2c94.
Definition Fo_0ac := F_a2c98.
Definition Do_0ac := D_a2c98.
Definition Fo_0b0 := F_a2c9c.
Definition Do_0b0 := D_a2c9c.
Definition Fo_0b4 := F_a2ca0.
Definition Do_0b4 := D_a2ca0.
Definition Fo_0b8 := F_a2ca4.
Definition Do_0b8 := D_a2ca4.
Definition Fo_0bc := F_a2ca8.
Definition Do_0bc := D_a2ca8.
Definition Fo_0c0 := F_a2cac.
Definition Do_0c0 := D_a2cac.
Definition Fo_0c4 := F_a2cb0.
Definition Do_0c4 := D_a2cb0.
Definition Fo_0c8 := F_a2cb4.
Definition Do_0c8 := D_a2cb4.
Definition Fo_0cc := F_a2cb8.
Definition Do_0cc := D_a2cb8.
Definition Fo_0d0 := F_a2cbc.
Definition Do_0d0 := D_a2cbc.
Definition Fo_0d4 := F_a2cc0.
Definition Do_0d4 := D_a2cc0.
Definition Fo_0d8 := F_a2cc4.
Definition Do_0d8 := D_a2cc4.
Definition Fo_0dc := F_a2cc8.
Definition Do_0dc := D_a2cc8.
Definition Fo_0e0 := F_a2ccc.
Definition Do_0e0 := D_a2ccc.
Definition Fo_0e4 := F_a2cd0.
Definition Do_0e4 := D_a2cd0.
Definition Fo_0e8 := F_a2cd4.
Definition Do_0e8 := D_a2cd4.
Definition Fo_0ec := F_a2cd8.
Definition Do_0ec := D_a2cd8.
Definition Fo_0f0 := F_a2cdc.
Definition Do_0f0 := D_a2cdc.
Definition Fo_0f4 := F_a2ce0.
Definition Do_0f4 := D_a2ce0.
