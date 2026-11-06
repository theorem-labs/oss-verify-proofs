(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_b6a88 : bv 32 := 0x02053703.
Lemma F_b6a88 : fetch_word Plain.M.loaded_segments (0xb6c40 : word) = Some W_b6a88.
Proof. vm_refl. Qed.
Lemma D_b6a88 : decode_any W_b6a88 = Some (Load SZ8 true 14 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6a8c : bv 32 := 0x00c75793.
Lemma F_b6a8c : fetch_word Plain.M.loaded_segments (0xb6c44 : word) = Some W_b6a8c.
Proof. vm_refl. Qed.
Lemma D_b6a8c : decode_any W_b6a8c = Some (ShiftImm ALU_SRL 15 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6a90 : bv 32 := 0x00078e63.
Lemma F_b6a90 : fetch_word Plain.M.loaded_segments (0xb6c48 : word) = Some W_b6a90.
Proof. vm_refl. Qed.
Lemma D_b6a90 : decode_any W_b6a90 = Some (Branch BC_EQ 15 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6a94 : bv 32 := 0x01f77793.
Lemma F_b6a94 : fetch_word Plain.M.loaded_segments (0xb6c4c : word) = Some W_b6a94.
Proof. vm_refl. Qed.
Lemma D_b6a94 : decode_any W_b6a94 = Some (OpImm ALU_AND 15 14 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6a98 : bv 32 := 0x00079a63.
Lemma F_b6a98 : fetch_word Plain.M.loaded_segments (0xb6c50 : word) = Some W_b6a98.
Proof. vm_refl. Qed.
Lemma D_b6a98 : decode_any W_b6a98 = Some (Branch BC_NE 15 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6a9c : bv 32 := 0xfffff7b7.
Lemma F_b6a9c : fetch_word Plain.M.loaded_segments (0xb6c54 : word) = Some W_b6a9c.
Proof. vm_refl. Qed.
Lemma D_b6a9c : decode_any W_b6a9c = Some (Lui 15 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6aa0 : bv 32 := 0x00f77733.
Lemma F_b6aa0 : fetch_word Plain.M.loaded_segments (0xb6c58 : word) = Some W_b6aa0.
Proof. vm_refl. Qed.
Lemma D_b6aa0 : decode_any W_b6aa0 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6aa4 : bv 32 := 0xff070713.
Lemma F_b6aa4 : fetch_word Plain.M.loaded_segments (0xb6c5c : word) = Some W_b6aa4.
Proof. vm_refl. Qed.
Lemma D_b6aa4 : decode_any W_b6aa4 = Some (OpImm ALU_ADD 14 14 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6aa8 : bv 32 := 0x0200006f.
Lemma F_b6aa8 : fetch_word Plain.M.loaded_segments (0xb6c60 : word) = Some W_b6aa8.
Proof. vm_refl. Qed.
Lemma D_b6aa8 : decode_any W_b6aa8 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6aac : bv 32 := 0x00575713.
Lemma F_b6aac : fetch_word Plain.M.loaded_segments (0xb6c64 : word) = Some W_b6aac.
Proof. vm_refl. Qed.
Lemma D_b6aac : decode_any W_b6aac = Some (ShiftImm ALU_SRL 14 14 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6ab0 : bv 32 := 0xfff6b797.
Lemma F_b6ab0 : fetch_word Plain.M.loaded_segments (0xb6c68 : word) = Some W_b6ab0.
Proof. vm_refl. Qed.
Lemma D_b6ab0 : decode_any W_b6ab0 = Some (Auipc 15 1048427, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6ab4 : bv 32 := 0x07e77713.
Lemma F_b6ab4 : fetch_word Plain.M.loaded_segments (0xb6c6c : word) = Some W_b6ab4.
Proof. vm_refl. Qed.
Lemma D_b6ab4 : decode_any W_b6ab4 = Some (OpImm ALU_AND 14 14 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6ab8 : bv 32 := 0xbe878793.
Lemma F_b6ab8 : fetch_word Plain.M.loaded_segments (0xb6c70 : word) = Some W_b6ab8.
Proof. vm_refl. Qed.
Lemma D_b6ab8 : decode_any W_b6ab8 = Some (OpImm ALU_ADD 15 15 3048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6abc : bv 32 := 0x00e78733.
Lemma F_b6abc : fetch_word Plain.M.loaded_segments (0xb6c74 : word) = Some W_b6abc.
Proof. vm_refl. Qed.
Lemma D_b6abc : decode_any W_b6abc = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6ac0 : bv 32 := 0x00075703.
Lemma F_b6ac0 : fetch_word Plain.M.loaded_segments (0xb6c78 : word) = Some W_b6ac0.
Proof. vm_refl. Qed.
Lemma D_b6ac0 : decode_any W_b6ac0 = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6ac4 : bv 32 := 0x00471713.
Lemma F_b6ac4 : fetch_word Plain.M.loaded_segments (0xb6c7c : word) = Some W_b6ac4.
Proof. vm_refl. Qed.
Lemma D_b6ac4 : decode_any W_b6ac4 = Some (ShiftImm ALU_SLL 14 14 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6ac8 : bv 32 := 0x01053803.
Lemma F_b6ac8 : fetch_word Plain.M.loaded_segments (0xb6c80 : word) = Some W_b6ac8.
Proof. vm_refl. Qed.
Lemma D_b6ac8 : decode_any W_b6ac8 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6acc : bv 32 := 0x02b707b3.
Lemma F_b6acc : fetch_word Plain.M.loaded_segments (0xb6c84 : word) = Some W_b6acc.
Proof. vm_refl. Qed.
Lemma D_b6acc : decode_any W_b6acc = Some (Mul M_MUL 15 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6ad0 : bv 32 := 0x00f807b3.
Lemma F_b6ad0 : fetch_word Plain.M.loaded_segments (0xb6c88 : word) = Some W_b6ad0.
Proof. vm_refl. Qed.
Lemma D_b6ad0 : decode_any W_b6ad0 = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6ad4 : bv 32 := 0x00d7c883.
Lemma F_b6ad4 : fetch_word Plain.M.loaded_segments (0xb6c8c : word) = Some W_b6ad4.
Proof. vm_refl. Qed.
Lemma D_b6ad4 : decode_any W_b6ad4 = Some (Load SZ1 false 17 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6ad8 : bv 32 := 0x40c702b3.
Lemma F_b6ad8 : fetch_word Plain.M.loaded_segments (0xb6c90 : word) = Some W_b6ad8.
Proof. vm_refl. Qed.
Lemma D_b6ad8 : decode_any W_b6ad8 = Some (Op ALU_SUB 5 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6adc : bv 32 := 0xffc28293.
Lemma F_b6adc : fetch_word Plain.M.loaded_segments (0xb6c94 : word) = Some W_b6adc.
Proof. vm_refl. Qed.
Lemma D_b6adc : decode_any W_b6adc = Some (OpImm ALU_ADD 5 5 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6ae0 : bv 32 := 0x01078793.
Lemma F_b6ae0 : fetch_word Plain.M.loaded_segments (0xb6c98 : word) = Some W_b6ae0.
Proof. vm_refl. Qed.
Lemma D_b6ae0 : decode_any W_b6ae0 = Some (OpImm ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6ae4 : bv 32 := 0x00088663.
Lemma F_b6ae4 : fetch_word Plain.M.loaded_segments (0xb6c9c : word) = Some W_b6ae4.
Proof. vm_refl. Qed.
Lemma D_b6ae4 : decode_any W_b6ae4 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6ae8 : bv 32 := 0xffe7d683.
Lemma F_b6ae8 : fetch_word Plain.M.loaded_segments (0xb6ca0 : word) = Some W_b6ae8.
Proof. vm_refl. Qed.
Lemma D_b6ae8 : decode_any W_b6ae8 = Some (Load SZ2 false 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6aec : bv 32 := 0x00168693.
Lemma F_b6aec : fetch_word Plain.M.loaded_segments (0xb6ca4 : word) = Some W_b6aec.
Proof. vm_refl. Qed.
Lemma D_b6aec : decode_any W_b6aec = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6af0 : bv 32 := 0xffc7c383.
Lemma F_b6af0 : fetch_word Plain.M.loaded_segments (0xb6ca8 : word) = Some W_b6af0.
Proof. vm_refl. Qed.
Lemma D_b6af0 : decode_any W_b6af0 = Some (Load SZ1 false 7 15 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6af4 : bv 32 := 0x0042d313.
Lemma F_b6af4 : fetch_word Plain.M.loaded_segments (0xb6cac : word) = Some W_b6af4.
Proof. vm_refl. Qed.
Lemma D_b6af4 : decode_any W_b6af4 = Some (ShiftImm ALU_SRL 6 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6af8 : bv 32 := 0x0ff6f893.
Lemma F_b6af8 : fetch_word Plain.M.loaded_segments (0xb6cb0 : word) = Some W_b6af8.
Proof. vm_refl. Qed.
Lemma D_b6af8 : decode_any W_b6af8 = Some (OpImm ALU_AND 17 13 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6afc : bv 32 := 0x00038463.
Lemma F_b6afc : fetch_word Plain.M.loaded_segments (0xb6cb4 : word) = Some W_b6afc.
Proof. vm_refl. Qed.
Lemma D_b6afc : decode_any W_b6afc = Some (Branch BC_EQ 7 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b00 : bv 32 := 0x00000023.
Lemma F_b6b00 : fetch_word Plain.M.loaded_segments (0xb6cb8 : word) = Some W_b6b00.
Proof. vm_refl. Qed.
Lemma D_b6b00 : decode_any W_b6b00 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b04 : bv 32 := 0x03137e63.
Lemma F_b6b04 : fetch_word Plain.M.loaded_segments (0xb6cbc : word) = Some W_b6b04.
Proof. vm_refl. Qed.
Lemma D_b6b04 : decode_any W_b6b04 = Some (Branch BC_GEU 6 17 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b08 : bv 32 := 0x0052d693.
Lemma F_b6b08 : fetch_word Plain.M.loaded_segments (0xb6cc0 : word) = Some W_b6b08.
Proof. vm_refl. Qed.
Lemma D_b6b08 : decode_any W_b6b08 = Some (ShiftImm ALU_SRL 13 5 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b0c : bv 32 := 0x00d366b3.
Lemma F_b6b0c : fetch_word Plain.M.loaded_segments (0xb6cc4 : word) = Some W_b6b0c.
Proof. vm_refl. Qed.
Lemma D_b6b0c : decode_any W_b6b0c = Some (Op ALU_OR 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b10 : bv 32 := 0x0026d293.
Lemma F_b6b10 : fetch_word Plain.M.loaded_segments (0xb6cc8 : word) = Some W_b6b10.
Proof. vm_refl. Qed.
Lemma D_b6b10 : decode_any W_b6b10 = Some (ShiftImm ALU_SRL 5 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b14 : bv 32 := 0x00d2e6b3.
Lemma F_b6b14 : fetch_word Plain.M.loaded_segments (0xb6ccc : word) = Some W_b6b14.
Proof. vm_refl. Qed.
Lemma D_b6b14 : decode_any W_b6b14 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b18 : bv 32 := 0x0046d293.
Lemma F_b6b18 : fetch_word Plain.M.loaded_segments (0xb6cd0 : word) = Some W_b6b18.
Proof. vm_refl. Qed.
Lemma D_b6b18 : decode_any W_b6b18 = Some (ShiftImm ALU_SRL 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b1c : bv 32 := 0x00d2e6b3.
Lemma F_b6b1c : fetch_word Plain.M.loaded_segments (0xb6cd4 : word) = Some W_b6b1c.
Proof. vm_refl. Qed.
Lemma D_b6b1c : decode_any W_b6b1c = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b20 : bv 32 := 0x00d8f6b3.
Lemma F_b6b20 : fetch_word Plain.M.loaded_segments (0xb6cd8 : word) = Some W_b6b20.
Proof. vm_refl. Qed.
Lemma D_b6b20 : decode_any W_b6b20 = Some (Op ALU_AND 13 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b24 : bv 32 := 0x00d338b3.
Lemma F_b6b24 : fetch_word Plain.M.loaded_segments (0xb6cdc : word) = Some W_b6b24.
Proof. vm_refl. Qed.
Lemma D_b6b24 : decode_any W_b6b24 = Some (Op ALU_SLTU 17 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b28 : bv 32 := 0xfff34293.
Lemma F_b6b28 : fetch_word Plain.M.loaded_segments (0xb6ce0 : word) = Some W_b6b28.
Proof. vm_refl. Qed.
Lemma D_b6b28 : decode_any W_b6b28 = Some (OpImm ALU_XOR 5 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b2c : bv 32 := 0x411008bb.
Lemma F_b6b2c : fetch_word Plain.M.loaded_segments (0xb6ce4 : word) = Some W_b6b2c.
Proof. vm_refl. Qed.
Lemma D_b6b2c : decode_any W_b6b2c = Some (Op32 ALU_SUB 17 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b30 : bv 32 := 0x0058f8b3.
Lemma F_b6b30 : fetch_word Plain.M.loaded_segments (0xb6ce8 : word) = Some W_b6b30.
Proof. vm_refl. Qed.
Lemma D_b6b30 : decode_any W_b6b30 = Some (Op ALU_AND 17 17 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b34 : bv 32 := 0x00d888bb.
Lemma F_b6b34 : fetch_word Plain.M.loaded_segments (0xb6cec : word) = Some W_b6b34.
Proof. vm_refl. Qed.
Lemma D_b6b34 : decode_any W_b6b34 = Some (Op32 ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b38 : bv 32 := 0x01137463.
Lemma F_b6b38 : fetch_word Plain.M.loaded_segments (0xb6cf0 : word) = Some W_b6b38.
Proof. vm_refl. Qed.
Lemma D_b6b38 : decode_any W_b6b38 = Some (Branch BC_GEU 6 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b3c : bv 32 := 0x00000023.
Lemma F_b6b3c : fetch_word Plain.M.loaded_segments (0xb6cf4 : word) = Some W_b6b3c.
Proof. vm_refl. Qed.
Lemma D_b6b3c : decode_any W_b6b3c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b40 : bv 32 := 0x00078693.
Lemma F_b6b40 : fetch_word Plain.M.loaded_segments (0xb6cf8 : word) = Some W_b6b40.
Proof. vm_refl. Qed.
Lemma D_b6b40 : decode_any W_b6b40 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b44 : bv 32 := 0x02088063.
Lemma F_b6b44 : fetch_word Plain.M.loaded_segments (0xb6cfc : word) = Some W_b6b44.
Proof. vm_refl. Qed.
Lemma D_b6b44 : decode_any W_b6b44 = Some (Branch BC_EQ 17 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b48 : bv 32 := 0xfe000813.
Lemma F_b6b48 : fetch_word Plain.M.loaded_segments (0xb6d00 : word) = Some W_b6b48.
Proof. vm_refl. Qed.
Lemma D_b6b48 : decode_any W_b6b48 = Some (OpImm ALU_ADD 16 0 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b4c : bv 32 := 0x0048969b.
Lemma F_b6b4c : fetch_word Plain.M.loaded_segments (0xb6d04 : word) = Some W_b6b4c.
Proof. vm_refl. Qed.
Lemma D_b6b4c : decode_any W_b6b4c = Some (ShiftImm32 ALU_SLL 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b50 : bv 32 := 0x00d786b3.
Lemma F_b6b50 : fetch_word Plain.M.loaded_segments (0xb6d08 : word) = Some W_b6b50.
Proof. vm_refl. Qed.
Lemma D_b6b50 : decode_any W_b6b50 = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b54 : bv 32 := 0xff078ea3.
Lemma F_b6b54 : fetch_word Plain.M.loaded_segments (0xb6d0c : word) = Some W_b6b54.
Proof. vm_refl. Qed.
Lemma D_b6b54 : decode_any W_b6b54 = Some (Store SZ1 15 16 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b58 : bv 32 := 0xff179f23.
Lemma F_b6b58 : fetch_word Plain.M.loaded_segments (0xb6d10 : word) = Some W_b6b58.
Proof. vm_refl. Qed.
Lemma D_b6b58 : decode_any W_b6b58 = Some (Store SZ2 15 17 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b5c : bv 32 := 0xfe068e23.
Lemma F_b6b5c : fetch_word Plain.M.loaded_segments (0xb6d14 : word) = Some W_b6b5c.
Proof. vm_refl. Qed.
Lemma D_b6b5c : decode_any W_b6b5c = Some (Store SZ1 13 0 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b60 : bv 32 := 0x01053803.
Lemma F_b6b60 : fetch_word Plain.M.loaded_segments (0xb6d18 : word) = Some W_b6b60.
Proof. vm_refl. Qed.
Lemma D_b6b60 : decode_any W_b6b60 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b64 : bv 32 := 0x00e78733.
Lemma F_b6b64 : fetch_word Plain.M.loaded_segments (0xb6d1c : word) = Some W_b6b64.
Proof. vm_refl. Qed.
Lemma D_b6b64 : decode_any W_b6b64 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b68 : bv 32 := 0x410687bb.
Lemma F_b6b68 : fetch_word Plain.M.loaded_segments (0xb6d20 : word) = Some W_b6b68.
Proof. vm_refl. Qed.
Lemma D_b6b68 : decode_any W_b6b68 = Some (Op32 ALU_SUB 15 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b6c : bv 32 := 0x00d60633.
Lemma F_b6b6c : fetch_word Plain.M.loaded_segments (0xb6d24 : word) = Some W_b6b6c.
Proof. vm_refl. Qed.
Lemma D_b6b6c : decode_any W_b6b6c = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b70 : bv 32 := 0xffc70513.
Lemma F_b6b70 : fetch_word Plain.M.loaded_segments (0xb6d28 : word) = Some W_b6b70.
Proof. vm_refl. Qed.
Lemma D_b6b70 : decode_any W_b6b70 = Some (OpImm ALU_ADD 10 14 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b74 : bv 32 := 0xff078793.
Lemma F_b6b74 : fetch_word Plain.M.loaded_segments (0xb6d2c : word) = Some W_b6b74.
Proof. vm_refl. Qed.
Lemma D_b6b74 : decode_any W_b6b74 = Some (OpImm ALU_ADD 15 15 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b78 : bv 32 := 0x0047d793.
Lemma F_b6b78 : fetch_word Plain.M.loaded_segments (0xb6d30 : word) = Some W_b6b78.
Proof. vm_refl. Qed.
Lemma D_b6b78 : decode_any W_b6b78 = Some (ShiftImm ALU_SRL 15 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b7c : bv 32 := 0x40c5083b.
Lemma F_b6b7c : fetch_word Plain.M.loaded_segments (0xb6d34 : word) = Some W_b6b7c.
Proof. vm_refl. Qed.
Lemma D_b6b7c : decode_any W_b6b7c = Some (Op32 ALU_SUB 16 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b80 : bv 32 := 0xfeb68ea3.
Lemma F_b6b80 : fetch_word Plain.M.loaded_segments (0xb6d38 : word) = Some W_b6b80.
Proof. vm_refl. Qed.
Lemma D_b6b80 : decode_any W_b6b80 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b84 : bv 32 := 0xfef69f23.
Lemma F_b6b84 : fetch_word Plain.M.loaded_segments (0xb6d3c : word) = Some W_b6b84.
Proof. vm_refl. Qed.
Lemma D_b6b84 : decode_any W_b6b84 = Some (Store SZ2 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b88 : bv 32 := 0x02080463.
Lemma F_b6b88 : fetch_word Plain.M.loaded_segments (0xb6d40 : word) = Some W_b6b88.
Proof. vm_refl. Qed.
Lemma D_b6b88 : decode_any W_b6b88 = Some (Branch BC_EQ 16 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b8c : bv 32 := 0x40c505bb.
Lemma F_b6b8c : fetch_word Plain.M.loaded_segments (0xb6d44 : word) = Some W_b6b8c.
Proof. vm_refl. Qed.
Lemma D_b6b8c : decode_any W_b6b8c = Some (Op32 ALU_SUB 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b90 : bv 32 := 0x40b0063b.
Lemma F_b6b90 : fetch_word Plain.M.loaded_segments (0xb6d48 : word) = Some W_b6b90.
Proof. vm_refl. Qed.
Lemma D_b6b90 : decode_any W_b6b90 = Some (Op32 ALU_SUB 12 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b94 : bv 32 := 0x00c50633.
Lemma F_b6b94 : fetch_word Plain.M.loaded_segments (0xb6d4c : word) = Some W_b6b94.
Proof. vm_refl. Qed.
Lemma D_b6b94 : decode_any W_b6b94 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b98 : bv 32 := 0x00500513.
Lemma F_b6b98 : fetch_word Plain.M.loaded_segments (0xb6d50 : word) = Some W_b6b98.
Proof. vm_refl. Qed.
Lemma D_b6b98 : decode_any W_b6b98 = Some (OpImm ALU_ADD 10 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6b9c : bv 32 := 0x00060023.
Lemma F_b6b9c : fetch_word Plain.M.loaded_segments (0xb6d54 : word) = Some W_b6b9c.
Proof. vm_refl. Qed.
Lemma D_b6b9c : decode_any W_b6b9c = Some (Store SZ1 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6ba0 : bv 32 := 0x00a5cc63.
Lemma F_b6ba0 : fetch_word Plain.M.loaded_segments (0xb6d58 : word) = Some W_b6ba0.
Proof. vm_refl. Qed.
Lemma D_b6ba0 : decode_any W_b6ba0 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6ba4 : bv 32 := 0xfe070ba3.
Lemma F_b6ba4 : fetch_word Plain.M.loaded_segments (0xb6d5c : word) = Some W_b6ba4.
Proof. vm_refl. Qed.
Lemma D_b6ba4 : decode_any W_b6ba4 = Some (Store SZ1 14 0 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6ba8 : bv 32 := 0xfeb72c23.
Lemma F_b6ba8 : fetch_word Plain.M.loaded_segments (0xb6d60 : word) = Some W_b6ba8.
Proof. vm_refl. Qed.
Lemma D_b6ba8 : decode_any W_b6ba8 = Some (Store SZ4 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bac : bv 32 := 0x0100006f.
Lemma F_b6bac : fetch_word Plain.M.loaded_segments (0xb6d64 : word) = Some W_b6bac.
Proof. vm_refl. Qed.
Lemma D_b6bac : decode_any W_b6bac = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bb0 : bv 32 := 0x00000513.
Lemma F_b6bb0 : fetch_word Plain.M.loaded_segments (0xb6d68 : word) = Some W_b6bb0.
Proof. vm_refl. Qed.
Lemma D_b6bb0 : decode_any W_b6bb0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bb4 : bv 32 := 0x0080006f.
Lemma F_b6bb4 : fetch_word Plain.M.loaded_segments (0xb6d6c : word) = Some W_b6bb4.
Proof. vm_refl. Qed.
Lemma D_b6bb4 : decode_any W_b6bb4 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bb8 : bv 32 := 0x00058513.
Lemma F_b6bb8 : fetch_word Plain.M.loaded_segments (0xb6d70 : word) = Some W_b6bb8.
Proof. vm_refl. Qed.
Lemma D_b6bb8 : decode_any W_b6bb8 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bbc : bv 32 := 0xffd6c583.
Lemma F_b6bbc : fetch_word Plain.M.loaded_segments (0xb6d74 : word) = Some W_b6bbc.
Proof. vm_refl. Qed.
Lemma D_b6bbc : decode_any W_b6bbc = Some (Load SZ1 false 11 13 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bc0 : bv 32 := 0x01f5f593.
Lemma F_b6bc0 : fetch_word Plain.M.loaded_segments (0xb6d78 : word) = Some W_b6bc0.
Proof. vm_refl. Qed.
Lemma D_b6bc0 : decode_any W_b6bc0 = Some (OpImm ALU_AND 11 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bc4 : bv 32 := 0x00551513.
Lemma F_b6bc4 : fetch_word Plain.M.loaded_segments (0xb6d7c : word) = Some W_b6bc4.
Proof. vm_refl. Qed.
Lemma D_b6bc4 : decode_any W_b6bc4 = Some (ShiftImm ALU_SLL 10 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bc8 : bv 32 := 0x00b56533.
Lemma F_b6bc8 : fetch_word Plain.M.loaded_segments (0xb6d80 : word) = Some W_b6bc8.
Proof. vm_refl. Qed.
Lemma D_b6bc8 : decode_any W_b6bc8 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bcc : bv 32 := 0xfea68ea3.
Lemma F_b6bcc : fetch_word Plain.M.loaded_segments (0xb6d84 : word) = Some W_b6bcc.
Proof. vm_refl. Qed.
Lemma D_b6bcc : decode_any W_b6bcc = Some (Store SZ1 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bd0 : bv 32 := 0x00068513.
Lemma F_b6bd0 : fetch_word Plain.M.loaded_segments (0xb6d88 : word) = Some W_b6bd0.
Proof. vm_refl. Qed.
Lemma D_b6bd0 : decode_any W_b6bd0 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6bd4 : bv 32 := 0x00008067.
Lemma F_b6bd4 : fetch_word Plain.M.loaded_segments (0xb6d8c : word) = Some W_b6bd4.
Proof. vm_refl. Qed.
Lemma D_b6bd4 : decode_any W_b6bd4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
