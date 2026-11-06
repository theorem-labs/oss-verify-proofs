(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_parser.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_108ae0 : bv 32 := 0x0e060a63.
Lemma F_108ae0 : fetch_word AsanUbsan.M.loaded_segments (0x108c9c : word) = Some W_108ae0.
Proof. vm_refl. Qed.
Lemma D_108ae0 : decode_any W_108ae0 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108ae4 : bv 32 := 0x00b50023.
Lemma F_108ae4 : fetch_word AsanUbsan.M.loaded_segments (0x108ca0 : word) = Some W_108ae4.
Proof. vm_refl. Qed.
Lemma D_108ae4 : decode_any W_108ae4 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108ae8 : bv 32 := 0x00c506b3.
Lemma F_108ae8 : fetch_word AsanUbsan.M.loaded_segments (0x108ca4 : word) = Some W_108ae8.
Proof. vm_refl. Qed.
Lemma D_108ae8 : decode_any W_108ae8 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108aec : bv 32 := 0x00300713.
Lemma F_108aec : fetch_word AsanUbsan.M.loaded_segments (0x108ca8 : word) = Some W_108aec.
Proof. vm_refl. Qed.
Lemma D_108aec : decode_any W_108aec = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108af0 : bv 32 := 0xfeb68fa3.
Lemma F_108af0 : fetch_word AsanUbsan.M.loaded_segments (0x108cac : word) = Some W_108af0.
Proof. vm_refl. Qed.
Lemma D_108af0 : decode_any W_108af0 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108af4 : bv 32 := 0x0ee66063.
Lemma F_108af4 : fetch_word AsanUbsan.M.loaded_segments (0x108cb0 : word) = Some W_108af4.
Proof. vm_refl. Qed.
Lemma D_108af4 : decode_any W_108af4 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108af8 : bv 32 := 0x00b500a3.
Lemma F_108af8 : fetch_word AsanUbsan.M.loaded_segments (0x108cb4 : word) = Some W_108af8.
Proof. vm_refl. Qed.
Lemma D_108af8 : decode_any W_108af8 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108afc : bv 32 := 0x00b50123.
Lemma F_108afc : fetch_word AsanUbsan.M.loaded_segments (0x108cb8 : word) = Some W_108afc.
Proof. vm_refl. Qed.
Lemma D_108afc : decode_any W_108afc = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b00 : bv 32 := 0x00700713.
Lemma F_108b00 : fetch_word AsanUbsan.M.loaded_segments (0x108cbc : word) = Some W_108b00.
Proof. vm_refl. Qed.
Lemma D_108b00 : decode_any W_108b00 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b04 : bv 32 := 0xfeb68ea3.
Lemma F_108b04 : fetch_word AsanUbsan.M.loaded_segments (0x108cc0 : word) = Some W_108b04.
Proof. vm_refl. Qed.
Lemma D_108b04 : decode_any W_108b04 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b08 : bv 32 := 0xfeb68f23.
Lemma F_108b08 : fetch_word AsanUbsan.M.loaded_segments (0x108cc4 : word) = Some W_108b08.
Proof. vm_refl. Qed.
Lemma D_108b08 : decode_any W_108b08 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b0c : bv 32 := 0x0ce66463.
Lemma F_108b0c : fetch_word AsanUbsan.M.loaded_segments (0x108cc8 : word) = Some W_108b0c.
Proof. vm_refl. Qed.
Lemma D_108b0c : decode_any W_108b0c = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b10 : bv 32 := 0x00b501a3.
Lemma F_108b10 : fetch_word AsanUbsan.M.loaded_segments (0x108ccc : word) = Some W_108b10.
Proof. vm_refl. Qed.
Lemma D_108b10 : decode_any W_108b10 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b14 : bv 32 := 0x00900793.
Lemma F_108b14 : fetch_word AsanUbsan.M.loaded_segments (0x108cd0 : word) = Some W_108b14.
Proof. vm_refl. Qed.
Lemma D_108b14 : decode_any W_108b14 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b18 : bv 32 := 0xfeb68e23.
Lemma F_108b18 : fetch_word AsanUbsan.M.loaded_segments (0x108cd4 : word) = Some W_108b18.
Proof. vm_refl. Qed.
Lemma D_108b18 : decode_any W_108b18 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b1c : bv 32 := 0x0af66c63.
Lemma F_108b1c : fetch_word AsanUbsan.M.loaded_segments (0x108cd8 : word) = Some W_108b1c.
Proof. vm_refl. Qed.
Lemma D_108b1c : decode_any W_108b1c = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b20 : bv 32 := 0x40a006bb.
Lemma F_108b20 : fetch_word AsanUbsan.M.loaded_segments (0x108cdc : word) = Some W_108b20.
Proof. vm_refl. Qed.
Lemma D_108b20 : decode_any W_108b20 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b24 : bv 32 := 0x03859813.
Lemma F_108b24 : fetch_word AsanUbsan.M.loaded_segments (0x108ce0 : word) = Some W_108b24.
Proof. vm_refl. Qed.
Lemma D_108b24 : decode_any W_108b24 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b28 : bv 32 := 0x101015b7.
Lemma F_108b28 : fetch_word AsanUbsan.M.loaded_segments (0x108ce4 : word) = Some W_108b28.
Proof. vm_refl. Qed.
Lemma D_108b28 : decode_any W_108b28 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b2c : bv 32 := 0x0036f693.
Lemma F_108b2c : fetch_word AsanUbsan.M.loaded_segments (0x108ce8 : word) = Some W_108b2c.
Proof. vm_refl. Qed.
Lemma D_108b2c : decode_any W_108b2c = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b30 : bv 32 := 0x00459713.
Lemma F_108b30 : fetch_word AsanUbsan.M.loaded_segments (0x108cec : word) = Some W_108b30.
Proof. vm_refl. Qed.
Lemma D_108b30 : decode_any W_108b30 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b34 : bv 32 := 0x40d60633.
Lemma F_108b34 : fetch_word AsanUbsan.M.loaded_segments (0x108cf0 : word) = Some W_108b34.
Proof. vm_refl. Qed.
Lemma D_108b34 : decode_any W_108b34 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b38 : bv 32 := 0x00d505b3.
Lemma F_108b38 : fetch_word AsanUbsan.M.loaded_segments (0x108cf4 : word) = Some W_108b38.
Proof. vm_refl. Qed.
Lemma D_108b38 : decode_any W_108b38 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b3c : bv 32 := 0x10070693.
Lemma F_108b3c : fetch_word AsanUbsan.M.loaded_segments (0x108cf8 : word) = Some W_108b3c.
Proof. vm_refl. Qed.
Lemma D_108b3c : decode_any W_108b3c = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b40 : bv 32 := 0xffc67713.
Lemma F_108b40 : fetch_word AsanUbsan.M.loaded_segments (0x108cfc : word) = Some W_108b40.
Proof. vm_refl. Qed.
Lemma D_108b40 : decode_any W_108b40 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b44 : bv 32 := 0x02d83633.
Lemma F_108b44 : fetch_word AsanUbsan.M.loaded_segments (0x108d00 : word) = Some W_108b44.
Proof. vm_refl. Qed.
Lemma D_108b44 : decode_any W_108b44 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b48 : bv 32 := 0x00c5a023.
Lemma F_108b48 : fetch_word AsanUbsan.M.loaded_segments (0x108d04 : word) = Some W_108b48.
Proof. vm_refl. Qed.
Lemma D_108b48 : decode_any W_108b48 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b4c : bv 32 := 0x00e586b3.
Lemma F_108b4c : fetch_word AsanUbsan.M.loaded_segments (0x108d08 : word) = Some W_108b4c.
Proof. vm_refl. Qed.
Lemma D_108b4c : decode_any W_108b4c = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b50 : bv 32 := 0xfec6ae23.
Lemma F_108b50 : fetch_word AsanUbsan.M.loaded_segments (0x108d0c : word) = Some W_108b50.
Proof. vm_refl. Qed.
Lemma D_108b50 : decode_any W_108b50 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b54 : bv 32 := 0x08f76063.
Lemma F_108b54 : fetch_word AsanUbsan.M.loaded_segments (0x108d10 : word) = Some W_108b54.
Proof. vm_refl. Qed.
Lemma D_108b54 : decode_any W_108b54 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b58 : bv 32 := 0x00c5a223.
Lemma F_108b58 : fetch_word AsanUbsan.M.loaded_segments (0x108d14 : word) = Some W_108b58.
Proof. vm_refl. Qed.
Lemma D_108b58 : decode_any W_108b58 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b5c : bv 32 := 0x00c5a423.
Lemma F_108b5c : fetch_word AsanUbsan.M.loaded_segments (0x108d18 : word) = Some W_108b5c.
Proof. vm_refl. Qed.
Lemma D_108b5c : decode_any W_108b5c = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b60 : bv 32 := 0x01900793.
Lemma F_108b60 : fetch_word AsanUbsan.M.loaded_segments (0x108d1c : word) = Some W_108b60.
Proof. vm_refl. Qed.
Lemma D_108b60 : decode_any W_108b60 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b64 : bv 32 := 0xfec6aa23.
Lemma F_108b64 : fetch_word AsanUbsan.M.loaded_segments (0x108d20 : word) = Some W_108b64.
Proof. vm_refl. Qed.
Lemma D_108b64 : decode_any W_108b64 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b68 : bv 32 := 0xfec6ac23.
Lemma F_108b68 : fetch_word AsanUbsan.M.loaded_segments (0x108d24 : word) = Some W_108b68.
Proof. vm_refl. Qed.
Lemma D_108b68 : decode_any W_108b68 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b6c : bv 32 := 0x06f76463.
Lemma F_108b6c : fetch_word AsanUbsan.M.loaded_segments (0x108d28 : word) = Some W_108b6c.
Proof. vm_refl. Qed.
Lemma D_108b6c : decode_any W_108b6c = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b70 : bv 32 := 0x00c5a623.
Lemma F_108b70 : fetch_word AsanUbsan.M.loaded_segments (0x108d2c : word) = Some W_108b70.
Proof. vm_refl. Qed.
Lemma D_108b70 : decode_any W_108b70 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b74 : bv 32 := 0x00c5a823.
Lemma F_108b74 : fetch_word AsanUbsan.M.loaded_segments (0x108d30 : word) = Some W_108b74.
Proof. vm_refl. Qed.
Lemma D_108b74 : decode_any W_108b74 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b78 : bv 32 := 0x00c5aa23.
Lemma F_108b78 : fetch_word AsanUbsan.M.loaded_segments (0x108d34 : word) = Some W_108b78.
Proof. vm_refl. Qed.
Lemma D_108b78 : decode_any W_108b78 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b7c : bv 32 := 0x00c5ac23.
Lemma F_108b7c : fetch_word AsanUbsan.M.loaded_segments (0x108d38 : word) = Some W_108b7c.
Proof. vm_refl. Qed.
Lemma D_108b7c : decode_any W_108b7c = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b80 : bv 32 := 0x0045f793.
Lemma F_108b80 : fetch_word AsanUbsan.M.loaded_segments (0x108d3c : word) = Some W_108b80.
Proof. vm_refl. Qed.
Lemma D_108b80 : decode_any W_108b80 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b84 : bv 32 := 0x02000813.
Lemma F_108b84 : fetch_word AsanUbsan.M.loaded_segments (0x108d40 : word) = Some W_108b84.
Proof. vm_refl. Qed.
Lemma D_108b84 : decode_any W_108b84 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b88 : bv 32 := 0x01878793.
Lemma F_108b88 : fetch_word AsanUbsan.M.loaded_segments (0x108d44 : word) = Some W_108b88.
Proof. vm_refl. Qed.
Lemma D_108b88 : decode_any W_108b88 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b8c : bv 32 := 0x40f70733.
Lemma F_108b8c : fetch_word AsanUbsan.M.loaded_segments (0x108d48 : word) = Some W_108b8c.
Proof. vm_refl. Qed.
Lemma D_108b8c : decode_any W_108b8c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b90 : bv 32 := 0xfec6a223.
Lemma F_108b90 : fetch_word AsanUbsan.M.loaded_segments (0x108d4c : word) = Some W_108b90.
Proof. vm_refl. Qed.
Lemma D_108b90 : decode_any W_108b90 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b94 : bv 32 := 0xfec6a423.
Lemma F_108b94 : fetch_word AsanUbsan.M.loaded_segments (0x108d50 : word) = Some W_108b94.
Proof. vm_refl. Qed.
Lemma D_108b94 : decode_any W_108b94 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b98 : bv 32 := 0xfec6a623.
Lemma F_108b98 : fetch_word AsanUbsan.M.loaded_segments (0x108d54 : word) = Some W_108b98.
Proof. vm_refl. Qed.
Lemma D_108b98 : decode_any W_108b98 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108b9c : bv 32 := 0xfec6a823.
Lemma F_108b9c : fetch_word AsanUbsan.M.loaded_segments (0x108d58 : word) = Some W_108b9c.
Proof. vm_refl. Qed.
Lemma D_108b9c : decode_any W_108b9c = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108ba0 : bv 32 := 0x03076a63.
Lemma F_108ba0 : fetch_word AsanUbsan.M.loaded_segments (0x108d5c : word) = Some W_108ba0.
Proof. vm_refl. Qed.
Lemma D_108ba0 : decode_any W_108ba0 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108ba4 : bv 32 := 0x02061613.
Lemma F_108ba4 : fetch_word AsanUbsan.M.loaded_segments (0x108d60 : word) = Some W_108ba4.
Proof. vm_refl. Qed.
Lemma D_108ba4 : decode_any W_108ba4 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108ba8 : bv 32 := 0x00f585b3.
Lemma F_108ba8 : fetch_word AsanUbsan.M.loaded_segments (0x108d64 : word) = Some W_108ba8.
Proof. vm_refl. Qed.
Lemma D_108ba8 : decode_any W_108ba8 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108bac : bv 32 := 0x02065693.
Lemma F_108bac : fetch_word AsanUbsan.M.loaded_segments (0x108d68 : word) = Some W_108bac.
Proof. vm_refl. Qed.
Lemma D_108bac : decode_any W_108bac = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108bb0 : bv 32 := 0x00d66633.
Lemma F_108bb0 : fetch_word AsanUbsan.M.loaded_segments (0x108d6c : word) = Some W_108bb0.
Proof. vm_refl. Qed.
Lemma D_108bb0 : decode_any W_108bb0 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108bb4 : bv 32 := 0x01f00693.
Lemma F_108bb4 : fetch_word AsanUbsan.M.loaded_segments (0x108d70 : word) = Some W_108bb4.
Proof. vm_refl. Qed.
Lemma D_108bb4 : decode_any W_108bb4 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108bb8 : bv 32 := 0x00c5b023.
Lemma F_108bb8 : fetch_word AsanUbsan.M.loaded_segments (0x108d74 : word) = Some W_108bb8.
Proof. vm_refl. Qed.
Lemma D_108bb8 : decode_any W_108bb8 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108bbc : bv 32 := 0x00c5b423.
Lemma F_108bbc : fetch_word AsanUbsan.M.loaded_segments (0x108d78 : word) = Some W_108bbc.
Proof. vm_refl. Qed.
Lemma D_108bbc : decode_any W_108bbc = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108bc0 : bv 32 := 0x00c5b823.
Lemma F_108bc0 : fetch_word AsanUbsan.M.loaded_segments (0x108d7c : word) = Some W_108bc0.
Proof. vm_refl. Qed.
Lemma D_108bc0 : decode_any W_108bc0 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108bc4 : bv 32 := 0x00c5bc23.
Lemma F_108bc4 : fetch_word AsanUbsan.M.loaded_segments (0x108d80 : word) = Some W_108bc4.
Proof. vm_refl. Qed.
Lemma D_108bc4 : decode_any W_108bc4 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108bc8 : bv 32 := 0xfe070713.
Lemma F_108bc8 : fetch_word AsanUbsan.M.loaded_segments (0x108d84 : word) = Some W_108bc8.
Proof. vm_refl. Qed.
Lemma D_108bc8 : decode_any W_108bc8 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108bcc : bv 32 := 0x02058593.
Lemma F_108bcc : fetch_word AsanUbsan.M.loaded_segments (0x108d88 : word) = Some W_108bcc.
Proof. vm_refl. Qed.
Lemma D_108bcc : decode_any W_108bcc = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108bd0 : bv 32 := 0xfee6e4e3.
Lemma F_108bd0 : fetch_word AsanUbsan.M.loaded_segments (0x108d8c : word) = Some W_108bd0.
Proof. vm_refl. Qed.
Lemma D_108bd0 : decode_any W_108bd0 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_108bd4 : bv 32 := 0x00008067.
Lemma F_108bd4 : fetch_word AsanUbsan.M.loaded_segments (0x108d90 : word) = Some W_108bd4.
Proof. vm_refl. Qed.
Lemma D_108bd4 : decode_any W_108bd4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0x108c9c%Z.
Definition Fo_000 := F_108ae0.
Definition Do_000 := D_108ae0.
Definition Fo_004 := F_108ae4.
Definition Do_004 := D_108ae4.
Definition Fo_008 := F_108ae8.
Definition Do_008 := D_108ae8.
Definition Fo_00c := F_108aec.
Definition Do_00c := D_108aec.
Definition Fo_010 := F_108af0.
Definition Do_010 := D_108af0.
Definition Fo_014 := F_108af4.
Definition Do_014 := D_108af4.
Definition Fo_018 := F_108af8.
Definition Do_018 := D_108af8.
Definition Fo_01c := F_108afc.
Definition Do_01c := D_108afc.
Definition Fo_020 := F_108b00.
Definition Do_020 := D_108b00.
Definition Fo_024 := F_108b04.
Definition Do_024 := D_108b04.
Definition Fo_028 := F_108b08.
Definition Do_028 := D_108b08.
Definition Fo_02c := F_108b0c.
Definition Do_02c := D_108b0c.
Definition Fo_030 := F_108b10.
Definition Do_030 := D_108b10.
Definition Fo_034 := F_108b14.
Definition Do_034 := D_108b14.
Definition Fo_038 := F_108b18.
Definition Do_038 := D_108b18.
Definition Fo_03c := F_108b1c.
Definition Do_03c := D_108b1c.
Definition Fo_040 := F_108b20.
Definition Do_040 := D_108b20.
Definition Fo_044 := F_108b24.
Definition Do_044 := D_108b24.
Definition Fo_048 := F_108b28.
Definition Do_048 := D_108b28.
Definition Fo_04c := F_108b2c.
Definition Do_04c := D_108b2c.
Definition Fo_050 := F_108b30.
Definition Do_050 := D_108b30.
Definition Fo_054 := F_108b34.
Definition Do_054 := D_108b34.
Definition Fo_058 := F_108b38.
Definition Do_058 := D_108b38.
Definition Fo_05c := F_108b3c.
Definition Do_05c := D_108b3c.
Definition Fo_060 := F_108b40.
Definition Do_060 := D_108b40.
Definition Fo_064 := F_108b44.
Definition Do_064 := D_108b44.
Definition Fo_068 := F_108b48.
Definition Do_068 := D_108b48.
Definition Fo_06c := F_108b4c.
Definition Do_06c := D_108b4c.
Definition Fo_070 := F_108b50.
Definition Do_070 := D_108b50.
Definition Fo_074 := F_108b54.
Definition Do_074 := D_108b54.
Definition Fo_078 := F_108b58.
Definition Do_078 := D_108b58.
Definition Fo_07c := F_108b5c.
Definition Do_07c := D_108b5c.
Definition Fo_080 := F_108b60.
Definition Do_080 := D_108b60.
Definition Fo_084 := F_108b64.
Definition Do_084 := D_108b64.
Definition Fo_088 := F_108b68.
Definition Do_088 := D_108b68.
Definition Fo_08c := F_108b6c.
Definition Do_08c := D_108b6c.
Definition Fo_090 := F_108b70.
Definition Do_090 := D_108b70.
Definition Fo_094 := F_108b74.
Definition Do_094 := D_108b74.
Definition Fo_098 := F_108b78.
Definition Do_098 := D_108b78.
Definition Fo_09c := F_108b7c.
Definition Do_09c := D_108b7c.
Definition Fo_0a0 := F_108b80.
Definition Do_0a0 := D_108b80.
Definition Fo_0a4 := F_108b84.
Definition Do_0a4 := D_108b84.
Definition Fo_0a8 := F_108b88.
Definition Do_0a8 := D_108b88.
Definition Fo_0ac := F_108b8c.
Definition Do_0ac := D_108b8c.
Definition Fo_0b0 := F_108b90.
Definition Do_0b0 := D_108b90.
Definition Fo_0b4 := F_108b94.
Definition Do_0b4 := D_108b94.
Definition Fo_0b8 := F_108b98.
Definition Do_0b8 := D_108b98.
Definition Fo_0bc := F_108b9c.
Definition Do_0bc := D_108b9c.
Definition Fo_0c0 := F_108ba0.
Definition Do_0c0 := D_108ba0.
Definition Fo_0c4 := F_108ba4.
Definition Do_0c4 := D_108ba4.
Definition Fo_0c8 := F_108ba8.
Definition Do_0c8 := D_108ba8.
Definition Fo_0cc := F_108bac.
Definition Do_0cc := D_108bac.
Definition Fo_0d0 := F_108bb0.
Definition Do_0d0 := D_108bb0.
Definition Fo_0d4 := F_108bb4.
Definition Do_0d4 := D_108bb4.
Definition Fo_0d8 := F_108bb8.
Definition Do_0d8 := D_108bb8.
Definition Fo_0dc := F_108bbc.
Definition Do_0dc := D_108bbc.
Definition Fo_0e0 := F_108bc0.
Definition Do_0e0 := D_108bc0.
Definition Fo_0e4 := F_108bc4.
Definition Do_0e4 := D_108bc4.
Definition Fo_0e8 := F_108bc8.
Definition Do_0e8 := D_108bc8.
Definition Fo_0ec := F_108bcc.
Definition Do_0ec := D_108bcc.
Definition Fo_0f0 := F_108bd0.
Definition Do_0f0 := D_108bd0.
Definition Fo_0f4 := F_108bd4.
Definition Do_0f4 := D_108bd4.
