(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_149ad0 : bv 32 := 0x0e060a63.
Lemma F_149ad0 : fetch_word AsanUbsan.M.loaded_segments (0x569e10 : word) = Some W_149ad0.
Proof. vm_refl. Qed.
Lemma D_149ad0 : decode_any W_149ad0 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149ad4 : bv 32 := 0x00b50023.
Lemma F_149ad4 : fetch_word AsanUbsan.M.loaded_segments (0x569e14 : word) = Some W_149ad4.
Proof. vm_refl. Qed.
Lemma D_149ad4 : decode_any W_149ad4 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149ad8 : bv 32 := 0x00c506b3.
Lemma F_149ad8 : fetch_word AsanUbsan.M.loaded_segments (0x569e18 : word) = Some W_149ad8.
Proof. vm_refl. Qed.
Lemma D_149ad8 : decode_any W_149ad8 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149adc : bv 32 := 0x00300713.
Lemma F_149adc : fetch_word AsanUbsan.M.loaded_segments (0x569e1c : word) = Some W_149adc.
Proof. vm_refl. Qed.
Lemma D_149adc : decode_any W_149adc = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149ae0 : bv 32 := 0xfeb68fa3.
Lemma F_149ae0 : fetch_word AsanUbsan.M.loaded_segments (0x569e20 : word) = Some W_149ae0.
Proof. vm_refl. Qed.
Lemma D_149ae0 : decode_any W_149ae0 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149ae4 : bv 32 := 0x0ee66063.
Lemma F_149ae4 : fetch_word AsanUbsan.M.loaded_segments (0x569e24 : word) = Some W_149ae4.
Proof. vm_refl. Qed.
Lemma D_149ae4 : decode_any W_149ae4 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149ae8 : bv 32 := 0x00b500a3.
Lemma F_149ae8 : fetch_word AsanUbsan.M.loaded_segments (0x569e28 : word) = Some W_149ae8.
Proof. vm_refl. Qed.
Lemma D_149ae8 : decode_any W_149ae8 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149aec : bv 32 := 0x00b50123.
Lemma F_149aec : fetch_word AsanUbsan.M.loaded_segments (0x569e2c : word) = Some W_149aec.
Proof. vm_refl. Qed.
Lemma D_149aec : decode_any W_149aec = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149af0 : bv 32 := 0x00700713.
Lemma F_149af0 : fetch_word AsanUbsan.M.loaded_segments (0x569e30 : word) = Some W_149af0.
Proof. vm_refl. Qed.
Lemma D_149af0 : decode_any W_149af0 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149af4 : bv 32 := 0xfeb68ea3.
Lemma F_149af4 : fetch_word AsanUbsan.M.loaded_segments (0x569e34 : word) = Some W_149af4.
Proof. vm_refl. Qed.
Lemma D_149af4 : decode_any W_149af4 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149af8 : bv 32 := 0xfeb68f23.
Lemma F_149af8 : fetch_word AsanUbsan.M.loaded_segments (0x569e38 : word) = Some W_149af8.
Proof. vm_refl. Qed.
Lemma D_149af8 : decode_any W_149af8 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149afc : bv 32 := 0x0ce66463.
Lemma F_149afc : fetch_word AsanUbsan.M.loaded_segments (0x569e3c : word) = Some W_149afc.
Proof. vm_refl. Qed.
Lemma D_149afc : decode_any W_149afc = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b00 : bv 32 := 0x00b501a3.
Lemma F_149b00 : fetch_word AsanUbsan.M.loaded_segments (0x569e40 : word) = Some W_149b00.
Proof. vm_refl. Qed.
Lemma D_149b00 : decode_any W_149b00 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b04 : bv 32 := 0x00900793.
Lemma F_149b04 : fetch_word AsanUbsan.M.loaded_segments (0x569e44 : word) = Some W_149b04.
Proof. vm_refl. Qed.
Lemma D_149b04 : decode_any W_149b04 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b08 : bv 32 := 0xfeb68e23.
Lemma F_149b08 : fetch_word AsanUbsan.M.loaded_segments (0x569e48 : word) = Some W_149b08.
Proof. vm_refl. Qed.
Lemma D_149b08 : decode_any W_149b08 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b0c : bv 32 := 0x0af66c63.
Lemma F_149b0c : fetch_word AsanUbsan.M.loaded_segments (0x569e4c : word) = Some W_149b0c.
Proof. vm_refl. Qed.
Lemma D_149b0c : decode_any W_149b0c = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b10 : bv 32 := 0x40a006bb.
Lemma F_149b10 : fetch_word AsanUbsan.M.loaded_segments (0x569e50 : word) = Some W_149b10.
Proof. vm_refl. Qed.
Lemma D_149b10 : decode_any W_149b10 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b14 : bv 32 := 0x03859813.
Lemma F_149b14 : fetch_word AsanUbsan.M.loaded_segments (0x569e54 : word) = Some W_149b14.
Proof. vm_refl. Qed.
Lemma D_149b14 : decode_any W_149b14 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b18 : bv 32 := 0x101015b7.
Lemma F_149b18 : fetch_word AsanUbsan.M.loaded_segments (0x569e58 : word) = Some W_149b18.
Proof. vm_refl. Qed.
Lemma D_149b18 : decode_any W_149b18 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b1c : bv 32 := 0x0036f693.
Lemma F_149b1c : fetch_word AsanUbsan.M.loaded_segments (0x569e5c : word) = Some W_149b1c.
Proof. vm_refl. Qed.
Lemma D_149b1c : decode_any W_149b1c = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b20 : bv 32 := 0x00459713.
Lemma F_149b20 : fetch_word AsanUbsan.M.loaded_segments (0x569e60 : word) = Some W_149b20.
Proof. vm_refl. Qed.
Lemma D_149b20 : decode_any W_149b20 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b24 : bv 32 := 0x40d60633.
Lemma F_149b24 : fetch_word AsanUbsan.M.loaded_segments (0x569e64 : word) = Some W_149b24.
Proof. vm_refl. Qed.
Lemma D_149b24 : decode_any W_149b24 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b28 : bv 32 := 0x00d505b3.
Lemma F_149b28 : fetch_word AsanUbsan.M.loaded_segments (0x569e68 : word) = Some W_149b28.
Proof. vm_refl. Qed.
Lemma D_149b28 : decode_any W_149b28 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b2c : bv 32 := 0x10070693.
Lemma F_149b2c : fetch_word AsanUbsan.M.loaded_segments (0x569e6c : word) = Some W_149b2c.
Proof. vm_refl. Qed.
Lemma D_149b2c : decode_any W_149b2c = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b30 : bv 32 := 0xffc67713.
Lemma F_149b30 : fetch_word AsanUbsan.M.loaded_segments (0x569e70 : word) = Some W_149b30.
Proof. vm_refl. Qed.
Lemma D_149b30 : decode_any W_149b30 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b34 : bv 32 := 0x02d83633.
Lemma F_149b34 : fetch_word AsanUbsan.M.loaded_segments (0x569e74 : word) = Some W_149b34.
Proof. vm_refl. Qed.
Lemma D_149b34 : decode_any W_149b34 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b38 : bv 32 := 0x00c5a023.
Lemma F_149b38 : fetch_word AsanUbsan.M.loaded_segments (0x569e78 : word) = Some W_149b38.
Proof. vm_refl. Qed.
Lemma D_149b38 : decode_any W_149b38 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b3c : bv 32 := 0x00e586b3.
Lemma F_149b3c : fetch_word AsanUbsan.M.loaded_segments (0x569e7c : word) = Some W_149b3c.
Proof. vm_refl. Qed.
Lemma D_149b3c : decode_any W_149b3c = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b40 : bv 32 := 0xfec6ae23.
Lemma F_149b40 : fetch_word AsanUbsan.M.loaded_segments (0x569e80 : word) = Some W_149b40.
Proof. vm_refl. Qed.
Lemma D_149b40 : decode_any W_149b40 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b44 : bv 32 := 0x08f76063.
Lemma F_149b44 : fetch_word AsanUbsan.M.loaded_segments (0x569e84 : word) = Some W_149b44.
Proof. vm_refl. Qed.
Lemma D_149b44 : decode_any W_149b44 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b48 : bv 32 := 0x00c5a223.
Lemma F_149b48 : fetch_word AsanUbsan.M.loaded_segments (0x569e88 : word) = Some W_149b48.
Proof. vm_refl. Qed.
Lemma D_149b48 : decode_any W_149b48 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b4c : bv 32 := 0x00c5a423.
Lemma F_149b4c : fetch_word AsanUbsan.M.loaded_segments (0x569e8c : word) = Some W_149b4c.
Proof. vm_refl. Qed.
Lemma D_149b4c : decode_any W_149b4c = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b50 : bv 32 := 0x01900793.
Lemma F_149b50 : fetch_word AsanUbsan.M.loaded_segments (0x569e90 : word) = Some W_149b50.
Proof. vm_refl. Qed.
Lemma D_149b50 : decode_any W_149b50 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b54 : bv 32 := 0xfec6aa23.
Lemma F_149b54 : fetch_word AsanUbsan.M.loaded_segments (0x569e94 : word) = Some W_149b54.
Proof. vm_refl. Qed.
Lemma D_149b54 : decode_any W_149b54 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b58 : bv 32 := 0xfec6ac23.
Lemma F_149b58 : fetch_word AsanUbsan.M.loaded_segments (0x569e98 : word) = Some W_149b58.
Proof. vm_refl. Qed.
Lemma D_149b58 : decode_any W_149b58 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b5c : bv 32 := 0x06f76463.
Lemma F_149b5c : fetch_word AsanUbsan.M.loaded_segments (0x569e9c : word) = Some W_149b5c.
Proof. vm_refl. Qed.
Lemma D_149b5c : decode_any W_149b5c = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b60 : bv 32 := 0x00c5a623.
Lemma F_149b60 : fetch_word AsanUbsan.M.loaded_segments (0x569ea0 : word) = Some W_149b60.
Proof. vm_refl. Qed.
Lemma D_149b60 : decode_any W_149b60 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b64 : bv 32 := 0x00c5a823.
Lemma F_149b64 : fetch_word AsanUbsan.M.loaded_segments (0x569ea4 : word) = Some W_149b64.
Proof. vm_refl. Qed.
Lemma D_149b64 : decode_any W_149b64 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b68 : bv 32 := 0x00c5aa23.
Lemma F_149b68 : fetch_word AsanUbsan.M.loaded_segments (0x569ea8 : word) = Some W_149b68.
Proof. vm_refl. Qed.
Lemma D_149b68 : decode_any W_149b68 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b6c : bv 32 := 0x00c5ac23.
Lemma F_149b6c : fetch_word AsanUbsan.M.loaded_segments (0x569eac : word) = Some W_149b6c.
Proof. vm_refl. Qed.
Lemma D_149b6c : decode_any W_149b6c = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b70 : bv 32 := 0x0045f793.
Lemma F_149b70 : fetch_word AsanUbsan.M.loaded_segments (0x569eb0 : word) = Some W_149b70.
Proof. vm_refl. Qed.
Lemma D_149b70 : decode_any W_149b70 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b74 : bv 32 := 0x02000813.
Lemma F_149b74 : fetch_word AsanUbsan.M.loaded_segments (0x569eb4 : word) = Some W_149b74.
Proof. vm_refl. Qed.
Lemma D_149b74 : decode_any W_149b74 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b78 : bv 32 := 0x01878793.
Lemma F_149b78 : fetch_word AsanUbsan.M.loaded_segments (0x569eb8 : word) = Some W_149b78.
Proof. vm_refl. Qed.
Lemma D_149b78 : decode_any W_149b78 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b7c : bv 32 := 0x40f70733.
Lemma F_149b7c : fetch_word AsanUbsan.M.loaded_segments (0x569ebc : word) = Some W_149b7c.
Proof. vm_refl. Qed.
Lemma D_149b7c : decode_any W_149b7c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b80 : bv 32 := 0xfec6a223.
Lemma F_149b80 : fetch_word AsanUbsan.M.loaded_segments (0x569ec0 : word) = Some W_149b80.
Proof. vm_refl. Qed.
Lemma D_149b80 : decode_any W_149b80 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b84 : bv 32 := 0xfec6a423.
Lemma F_149b84 : fetch_word AsanUbsan.M.loaded_segments (0x569ec4 : word) = Some W_149b84.
Proof. vm_refl. Qed.
Lemma D_149b84 : decode_any W_149b84 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b88 : bv 32 := 0xfec6a623.
Lemma F_149b88 : fetch_word AsanUbsan.M.loaded_segments (0x569ec8 : word) = Some W_149b88.
Proof. vm_refl. Qed.
Lemma D_149b88 : decode_any W_149b88 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b8c : bv 32 := 0xfec6a823.
Lemma F_149b8c : fetch_word AsanUbsan.M.loaded_segments (0x569ecc : word) = Some W_149b8c.
Proof. vm_refl. Qed.
Lemma D_149b8c : decode_any W_149b8c = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b90 : bv 32 := 0x03076a63.
Lemma F_149b90 : fetch_word AsanUbsan.M.loaded_segments (0x569ed0 : word) = Some W_149b90.
Proof. vm_refl. Qed.
Lemma D_149b90 : decode_any W_149b90 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b94 : bv 32 := 0x02061613.
Lemma F_149b94 : fetch_word AsanUbsan.M.loaded_segments (0x569ed4 : word) = Some W_149b94.
Proof. vm_refl. Qed.
Lemma D_149b94 : decode_any W_149b94 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b98 : bv 32 := 0x00f585b3.
Lemma F_149b98 : fetch_word AsanUbsan.M.loaded_segments (0x569ed8 : word) = Some W_149b98.
Proof. vm_refl. Qed.
Lemma D_149b98 : decode_any W_149b98 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149b9c : bv 32 := 0x02065693.
Lemma F_149b9c : fetch_word AsanUbsan.M.loaded_segments (0x569edc : word) = Some W_149b9c.
Proof. vm_refl. Qed.
Lemma D_149b9c : decode_any W_149b9c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149ba0 : bv 32 := 0x00d66633.
Lemma F_149ba0 : fetch_word AsanUbsan.M.loaded_segments (0x569ee0 : word) = Some W_149ba0.
Proof. vm_refl. Qed.
Lemma D_149ba0 : decode_any W_149ba0 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149ba4 : bv 32 := 0x01f00693.
Lemma F_149ba4 : fetch_word AsanUbsan.M.loaded_segments (0x569ee4 : word) = Some W_149ba4.
Proof. vm_refl. Qed.
Lemma D_149ba4 : decode_any W_149ba4 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149ba8 : bv 32 := 0x00c5b023.
Lemma F_149ba8 : fetch_word AsanUbsan.M.loaded_segments (0x569ee8 : word) = Some W_149ba8.
Proof. vm_refl. Qed.
Lemma D_149ba8 : decode_any W_149ba8 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149bac : bv 32 := 0x00c5b423.
Lemma F_149bac : fetch_word AsanUbsan.M.loaded_segments (0x569eec : word) = Some W_149bac.
Proof. vm_refl. Qed.
Lemma D_149bac : decode_any W_149bac = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149bb0 : bv 32 := 0x00c5b823.
Lemma F_149bb0 : fetch_word AsanUbsan.M.loaded_segments (0x569ef0 : word) = Some W_149bb0.
Proof. vm_refl. Qed.
Lemma D_149bb0 : decode_any W_149bb0 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149bb4 : bv 32 := 0x00c5bc23.
Lemma F_149bb4 : fetch_word AsanUbsan.M.loaded_segments (0x569ef4 : word) = Some W_149bb4.
Proof. vm_refl. Qed.
Lemma D_149bb4 : decode_any W_149bb4 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149bb8 : bv 32 := 0xfe070713.
Lemma F_149bb8 : fetch_word AsanUbsan.M.loaded_segments (0x569ef8 : word) = Some W_149bb8.
Proof. vm_refl. Qed.
Lemma D_149bb8 : decode_any W_149bb8 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149bbc : bv 32 := 0x02058593.
Lemma F_149bbc : fetch_word AsanUbsan.M.loaded_segments (0x569efc : word) = Some W_149bbc.
Proof. vm_refl. Qed.
Lemma D_149bbc : decode_any W_149bbc = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149bc0 : bv 32 := 0xfee6e4e3.
Lemma F_149bc0 : fetch_word AsanUbsan.M.loaded_segments (0x569f00 : word) = Some W_149bc0.
Proof. vm_refl. Qed.
Lemma D_149bc0 : decode_any W_149bc0 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149bc4 : bv 32 := 0x00008067.
Lemma F_149bc4 : fetch_word AsanUbsan.M.loaded_segments (0x569f04 : word) = Some W_149bc4.
Proof. vm_refl. Qed.
Lemma D_149bc4 : decode_any W_149bc4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0x569e10%Z.
Definition Fo_000 := F_149ad0.
Definition Do_000 := D_149ad0.
Definition Fo_004 := F_149ad4.
Definition Do_004 := D_149ad4.
Definition Fo_008 := F_149ad8.
Definition Do_008 := D_149ad8.
Definition Fo_00c := F_149adc.
Definition Do_00c := D_149adc.
Definition Fo_010 := F_149ae0.
Definition Do_010 := D_149ae0.
Definition Fo_014 := F_149ae4.
Definition Do_014 := D_149ae4.
Definition Fo_018 := F_149ae8.
Definition Do_018 := D_149ae8.
Definition Fo_01c := F_149aec.
Definition Do_01c := D_149aec.
Definition Fo_020 := F_149af0.
Definition Do_020 := D_149af0.
Definition Fo_024 := F_149af4.
Definition Do_024 := D_149af4.
Definition Fo_028 := F_149af8.
Definition Do_028 := D_149af8.
Definition Fo_02c := F_149afc.
Definition Do_02c := D_149afc.
Definition Fo_030 := F_149b00.
Definition Do_030 := D_149b00.
Definition Fo_034 := F_149b04.
Definition Do_034 := D_149b04.
Definition Fo_038 := F_149b08.
Definition Do_038 := D_149b08.
Definition Fo_03c := F_149b0c.
Definition Do_03c := D_149b0c.
Definition Fo_040 := F_149b10.
Definition Do_040 := D_149b10.
Definition Fo_044 := F_149b14.
Definition Do_044 := D_149b14.
Definition Fo_048 := F_149b18.
Definition Do_048 := D_149b18.
Definition Fo_04c := F_149b1c.
Definition Do_04c := D_149b1c.
Definition Fo_050 := F_149b20.
Definition Do_050 := D_149b20.
Definition Fo_054 := F_149b24.
Definition Do_054 := D_149b24.
Definition Fo_058 := F_149b28.
Definition Do_058 := D_149b28.
Definition Fo_05c := F_149b2c.
Definition Do_05c := D_149b2c.
Definition Fo_060 := F_149b30.
Definition Do_060 := D_149b30.
Definition Fo_064 := F_149b34.
Definition Do_064 := D_149b34.
Definition Fo_068 := F_149b38.
Definition Do_068 := D_149b38.
Definition Fo_06c := F_149b3c.
Definition Do_06c := D_149b3c.
Definition Fo_070 := F_149b40.
Definition Do_070 := D_149b40.
Definition Fo_074 := F_149b44.
Definition Do_074 := D_149b44.
Definition Fo_078 := F_149b48.
Definition Do_078 := D_149b48.
Definition Fo_07c := F_149b4c.
Definition Do_07c := D_149b4c.
Definition Fo_080 := F_149b50.
Definition Do_080 := D_149b50.
Definition Fo_084 := F_149b54.
Definition Do_084 := D_149b54.
Definition Fo_088 := F_149b58.
Definition Do_088 := D_149b58.
Definition Fo_08c := F_149b5c.
Definition Do_08c := D_149b5c.
Definition Fo_090 := F_149b60.
Definition Do_090 := D_149b60.
Definition Fo_094 := F_149b64.
Definition Do_094 := D_149b64.
Definition Fo_098 := F_149b68.
Definition Do_098 := D_149b68.
Definition Fo_09c := F_149b6c.
Definition Do_09c := D_149b6c.
Definition Fo_0a0 := F_149b70.
Definition Do_0a0 := D_149b70.
Definition Fo_0a4 := F_149b74.
Definition Do_0a4 := D_149b74.
Definition Fo_0a8 := F_149b78.
Definition Do_0a8 := D_149b78.
Definition Fo_0ac := F_149b7c.
Definition Do_0ac := D_149b7c.
Definition Fo_0b0 := F_149b80.
Definition Do_0b0 := D_149b80.
Definition Fo_0b4 := F_149b84.
Definition Do_0b4 := D_149b84.
Definition Fo_0b8 := F_149b88.
Definition Do_0b8 := D_149b88.
Definition Fo_0bc := F_149b8c.
Definition Do_0bc := D_149b8c.
Definition Fo_0c0 := F_149b90.
Definition Do_0c0 := D_149b90.
Definition Fo_0c4 := F_149b94.
Definition Do_0c4 := D_149b94.
Definition Fo_0c8 := F_149b98.
Definition Do_0c8 := D_149b98.
Definition Fo_0cc := F_149b9c.
Definition Do_0cc := D_149b9c.
Definition Fo_0d0 := F_149ba0.
Definition Do_0d0 := D_149ba0.
Definition Fo_0d4 := F_149ba4.
Definition Do_0d4 := D_149ba4.
Definition Fo_0d8 := F_149ba8.
Definition Do_0d8 := D_149ba8.
Definition Fo_0dc := F_149bac.
Definition Do_0dc := D_149bac.
Definition Fo_0e0 := F_149bb0.
Definition Do_0e0 := D_149bb0.
Definition Fo_0e4 := F_149bb4.
Definition Do_0e4 := D_149bb4.
Definition Fo_0e8 := F_149bb8.
Definition Do_0e8 := D_149bb8.
Definition Fo_0ec := F_149bbc.
Definition Do_0ec := D_149bbc.
Definition Fo_0f0 := F_149bc0.
Definition Do_0f0 := D_149bc0.
Definition Fo_0f4 := F_149bc4.
Definition Do_0f4 := D_149bc4.
