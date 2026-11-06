(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_c0c3c : bv 32 := 0x02053703.
Lemma F_c0c3c : fetch_word Ubsan.M.loaded_segments (0xc0df4 : word) = Some W_c0c3c.
Proof. vm_refl. Qed.
Lemma D_c0c3c : decode_any W_c0c3c = Some (Load SZ8 true 14 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c40 : bv 32 := 0x00c75793.
Lemma F_c0c40 : fetch_word Ubsan.M.loaded_segments (0xc0df8 : word) = Some W_c0c40.
Proof. vm_refl. Qed.
Lemma D_c0c40 : decode_any W_c0c40 = Some (ShiftImm ALU_SRL 15 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c44 : bv 32 := 0x00078e63.
Lemma F_c0c44 : fetch_word Ubsan.M.loaded_segments (0xc0dfc : word) = Some W_c0c44.
Proof. vm_refl. Qed.
Lemma D_c0c44 : decode_any W_c0c44 = Some (Branch BC_EQ 15 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c48 : bv 32 := 0x01f77793.
Lemma F_c0c48 : fetch_word Ubsan.M.loaded_segments (0xc0e00 : word) = Some W_c0c48.
Proof. vm_refl. Qed.
Lemma D_c0c48 : decode_any W_c0c48 = Some (OpImm ALU_AND 15 14 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c4c : bv 32 := 0x00079a63.
Lemma F_c0c4c : fetch_word Ubsan.M.loaded_segments (0xc0e04 : word) = Some W_c0c4c.
Proof. vm_refl. Qed.
Lemma D_c0c4c : decode_any W_c0c4c = Some (Branch BC_NE 15 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c50 : bv 32 := 0xfffff7b7.
Lemma F_c0c50 : fetch_word Ubsan.M.loaded_segments (0xc0e08 : word) = Some W_c0c50.
Proof. vm_refl. Qed.
Lemma D_c0c50 : decode_any W_c0c50 = Some (Lui 15 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c54 : bv 32 := 0x00f77733.
Lemma F_c0c54 : fetch_word Ubsan.M.loaded_segments (0xc0e0c : word) = Some W_c0c54.
Proof. vm_refl. Qed.
Lemma D_c0c54 : decode_any W_c0c54 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c58 : bv 32 := 0xff070713.
Lemma F_c0c58 : fetch_word Ubsan.M.loaded_segments (0xc0e10 : word) = Some W_c0c58.
Proof. vm_refl. Qed.
Lemma D_c0c58 : decode_any W_c0c58 = Some (OpImm ALU_ADD 14 14 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c5c : bv 32 := 0x0200006f.
Lemma F_c0c5c : fetch_word Ubsan.M.loaded_segments (0xc0e14 : word) = Some W_c0c5c.
Proof. vm_refl. Qed.
Lemma D_c0c5c : decode_any W_c0c5c = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c60 : bv 32 := 0x00575713.
Lemma F_c0c60 : fetch_word Ubsan.M.loaded_segments (0xc0e18 : word) = Some W_c0c60.
Proof. vm_refl. Qed.
Lemma D_c0c60 : decode_any W_c0c60 = Some (ShiftImm ALU_SRL 14 14 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c64 : bv 32 := 0xfff60797.
Lemma F_c0c64 : fetch_word Ubsan.M.loaded_segments (0xc0e1c : word) = Some W_c0c64.
Proof. vm_refl. Qed.
Lemma D_c0c64 : decode_any W_c0c64 = Some (Auipc 15 1048416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c68 : bv 32 := 0x07e77713.
Lemma F_c0c68 : fetch_word Ubsan.M.loaded_segments (0xc0e20 : word) = Some W_c0c68.
Proof. vm_refl. Qed.
Lemma D_c0c68 : decode_any W_c0c68 = Some (OpImm ALU_AND 14 14 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c6c : bv 32 := 0x73478793.
Lemma F_c0c6c : fetch_word Ubsan.M.loaded_segments (0xc0e24 : word) = Some W_c0c6c.
Proof. vm_refl. Qed.
Lemma D_c0c6c : decode_any W_c0c6c = Some (OpImm ALU_ADD 15 15 1844, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c70 : bv 32 := 0x00e78733.
Lemma F_c0c70 : fetch_word Ubsan.M.loaded_segments (0xc0e28 : word) = Some W_c0c70.
Proof. vm_refl. Qed.
Lemma D_c0c70 : decode_any W_c0c70 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c74 : bv 32 := 0x00075703.
Lemma F_c0c74 : fetch_word Ubsan.M.loaded_segments (0xc0e2c : word) = Some W_c0c74.
Proof. vm_refl. Qed.
Lemma D_c0c74 : decode_any W_c0c74 = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c78 : bv 32 := 0x00471713.
Lemma F_c0c78 : fetch_word Ubsan.M.loaded_segments (0xc0e30 : word) = Some W_c0c78.
Proof. vm_refl. Qed.
Lemma D_c0c78 : decode_any W_c0c78 = Some (ShiftImm ALU_SLL 14 14 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c7c : bv 32 := 0x01053803.
Lemma F_c0c7c : fetch_word Ubsan.M.loaded_segments (0xc0e34 : word) = Some W_c0c7c.
Proof. vm_refl. Qed.
Lemma D_c0c7c : decode_any W_c0c7c = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c80 : bv 32 := 0x02b707b3.
Lemma F_c0c80 : fetch_word Ubsan.M.loaded_segments (0xc0e38 : word) = Some W_c0c80.
Proof. vm_refl. Qed.
Lemma D_c0c80 : decode_any W_c0c80 = Some (Mul M_MUL 15 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c84 : bv 32 := 0x00f807b3.
Lemma F_c0c84 : fetch_word Ubsan.M.loaded_segments (0xc0e3c : word) = Some W_c0c84.
Proof. vm_refl. Qed.
Lemma D_c0c84 : decode_any W_c0c84 = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c88 : bv 32 := 0x00d7c883.
Lemma F_c0c88 : fetch_word Ubsan.M.loaded_segments (0xc0e40 : word) = Some W_c0c88.
Proof. vm_refl. Qed.
Lemma D_c0c88 : decode_any W_c0c88 = Some (Load SZ1 false 17 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c8c : bv 32 := 0x40c702b3.
Lemma F_c0c8c : fetch_word Ubsan.M.loaded_segments (0xc0e44 : word) = Some W_c0c8c.
Proof. vm_refl. Qed.
Lemma D_c0c8c : decode_any W_c0c8c = Some (Op ALU_SUB 5 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c90 : bv 32 := 0xffc28293.
Lemma F_c0c90 : fetch_word Ubsan.M.loaded_segments (0xc0e48 : word) = Some W_c0c90.
Proof. vm_refl. Qed.
Lemma D_c0c90 : decode_any W_c0c90 = Some (OpImm ALU_ADD 5 5 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c94 : bv 32 := 0x01078793.
Lemma F_c0c94 : fetch_word Ubsan.M.loaded_segments (0xc0e4c : word) = Some W_c0c94.
Proof. vm_refl. Qed.
Lemma D_c0c94 : decode_any W_c0c94 = Some (OpImm ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c98 : bv 32 := 0x00088663.
Lemma F_c0c98 : fetch_word Ubsan.M.loaded_segments (0xc0e50 : word) = Some W_c0c98.
Proof. vm_refl. Qed.
Lemma D_c0c98 : decode_any W_c0c98 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0c9c : bv 32 := 0xffe7d683.
Lemma F_c0c9c : fetch_word Ubsan.M.loaded_segments (0xc0e54 : word) = Some W_c0c9c.
Proof. vm_refl. Qed.
Lemma D_c0c9c : decode_any W_c0c9c = Some (Load SZ2 false 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0ca0 : bv 32 := 0x00168693.
Lemma F_c0ca0 : fetch_word Ubsan.M.loaded_segments (0xc0e58 : word) = Some W_c0ca0.
Proof. vm_refl. Qed.
Lemma D_c0ca0 : decode_any W_c0ca0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0ca4 : bv 32 := 0xffc7c383.
Lemma F_c0ca4 : fetch_word Ubsan.M.loaded_segments (0xc0e5c : word) = Some W_c0ca4.
Proof. vm_refl. Qed.
Lemma D_c0ca4 : decode_any W_c0ca4 = Some (Load SZ1 false 7 15 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0ca8 : bv 32 := 0x0042d313.
Lemma F_c0ca8 : fetch_word Ubsan.M.loaded_segments (0xc0e60 : word) = Some W_c0ca8.
Proof. vm_refl. Qed.
Lemma D_c0ca8 : decode_any W_c0ca8 = Some (ShiftImm ALU_SRL 6 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0cac : bv 32 := 0x0ff6f893.
Lemma F_c0cac : fetch_word Ubsan.M.loaded_segments (0xc0e64 : word) = Some W_c0cac.
Proof. vm_refl. Qed.
Lemma D_c0cac : decode_any W_c0cac = Some (OpImm ALU_AND 17 13 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0cb0 : bv 32 := 0x00038463.
Lemma F_c0cb0 : fetch_word Ubsan.M.loaded_segments (0xc0e68 : word) = Some W_c0cb0.
Proof. vm_refl. Qed.
Lemma D_c0cb0 : decode_any W_c0cb0 = Some (Branch BC_EQ 7 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0cb4 : bv 32 := 0x00000023.
Lemma F_c0cb4 : fetch_word Ubsan.M.loaded_segments (0xc0e6c : word) = Some W_c0cb4.
Proof. vm_refl. Qed.
Lemma D_c0cb4 : decode_any W_c0cb4 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0cb8 : bv 32 := 0x03137e63.
Lemma F_c0cb8 : fetch_word Ubsan.M.loaded_segments (0xc0e70 : word) = Some W_c0cb8.
Proof. vm_refl. Qed.
Lemma D_c0cb8 : decode_any W_c0cb8 = Some (Branch BC_GEU 6 17 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0cbc : bv 32 := 0x0052d693.
Lemma F_c0cbc : fetch_word Ubsan.M.loaded_segments (0xc0e74 : word) = Some W_c0cbc.
Proof. vm_refl. Qed.
Lemma D_c0cbc : decode_any W_c0cbc = Some (ShiftImm ALU_SRL 13 5 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0cc0 : bv 32 := 0x00d366b3.
Lemma F_c0cc0 : fetch_word Ubsan.M.loaded_segments (0xc0e78 : word) = Some W_c0cc0.
Proof. vm_refl. Qed.
Lemma D_c0cc0 : decode_any W_c0cc0 = Some (Op ALU_OR 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0cc4 : bv 32 := 0x0026d293.
Lemma F_c0cc4 : fetch_word Ubsan.M.loaded_segments (0xc0e7c : word) = Some W_c0cc4.
Proof. vm_refl. Qed.
Lemma D_c0cc4 : decode_any W_c0cc4 = Some (ShiftImm ALU_SRL 5 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0cc8 : bv 32 := 0x00d2e6b3.
Lemma F_c0cc8 : fetch_word Ubsan.M.loaded_segments (0xc0e80 : word) = Some W_c0cc8.
Proof. vm_refl. Qed.
Lemma D_c0cc8 : decode_any W_c0cc8 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0ccc : bv 32 := 0x0046d293.
Lemma F_c0ccc : fetch_word Ubsan.M.loaded_segments (0xc0e84 : word) = Some W_c0ccc.
Proof. vm_refl. Qed.
Lemma D_c0ccc : decode_any W_c0ccc = Some (ShiftImm ALU_SRL 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0cd0 : bv 32 := 0x00d2e6b3.
Lemma F_c0cd0 : fetch_word Ubsan.M.loaded_segments (0xc0e88 : word) = Some W_c0cd0.
Proof. vm_refl. Qed.
Lemma D_c0cd0 : decode_any W_c0cd0 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0cd4 : bv 32 := 0x00d8f6b3.
Lemma F_c0cd4 : fetch_word Ubsan.M.loaded_segments (0xc0e8c : word) = Some W_c0cd4.
Proof. vm_refl. Qed.
Lemma D_c0cd4 : decode_any W_c0cd4 = Some (Op ALU_AND 13 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0cd8 : bv 32 := 0x00d338b3.
Lemma F_c0cd8 : fetch_word Ubsan.M.loaded_segments (0xc0e90 : word) = Some W_c0cd8.
Proof. vm_refl. Qed.
Lemma D_c0cd8 : decode_any W_c0cd8 = Some (Op ALU_SLTU 17 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0cdc : bv 32 := 0xfff34293.
Lemma F_c0cdc : fetch_word Ubsan.M.loaded_segments (0xc0e94 : word) = Some W_c0cdc.
Proof. vm_refl. Qed.
Lemma D_c0cdc : decode_any W_c0cdc = Some (OpImm ALU_XOR 5 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0ce0 : bv 32 := 0x411008bb.
Lemma F_c0ce0 : fetch_word Ubsan.M.loaded_segments (0xc0e98 : word) = Some W_c0ce0.
Proof. vm_refl. Qed.
Lemma D_c0ce0 : decode_any W_c0ce0 = Some (Op32 ALU_SUB 17 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0ce4 : bv 32 := 0x0058f8b3.
Lemma F_c0ce4 : fetch_word Ubsan.M.loaded_segments (0xc0e9c : word) = Some W_c0ce4.
Proof. vm_refl. Qed.
Lemma D_c0ce4 : decode_any W_c0ce4 = Some (Op ALU_AND 17 17 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0ce8 : bv 32 := 0x00d888bb.
Lemma F_c0ce8 : fetch_word Ubsan.M.loaded_segments (0xc0ea0 : word) = Some W_c0ce8.
Proof. vm_refl. Qed.
Lemma D_c0ce8 : decode_any W_c0ce8 = Some (Op32 ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0cec : bv 32 := 0x01137463.
Lemma F_c0cec : fetch_word Ubsan.M.loaded_segments (0xc0ea4 : word) = Some W_c0cec.
Proof. vm_refl. Qed.
Lemma D_c0cec : decode_any W_c0cec = Some (Branch BC_GEU 6 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0cf0 : bv 32 := 0x00000023.
Lemma F_c0cf0 : fetch_word Ubsan.M.loaded_segments (0xc0ea8 : word) = Some W_c0cf0.
Proof. vm_refl. Qed.
Lemma D_c0cf0 : decode_any W_c0cf0 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0cf4 : bv 32 := 0x00078693.
Lemma F_c0cf4 : fetch_word Ubsan.M.loaded_segments (0xc0eac : word) = Some W_c0cf4.
Proof. vm_refl. Qed.
Lemma D_c0cf4 : decode_any W_c0cf4 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0cf8 : bv 32 := 0x02088063.
Lemma F_c0cf8 : fetch_word Ubsan.M.loaded_segments (0xc0eb0 : word) = Some W_c0cf8.
Proof. vm_refl. Qed.
Lemma D_c0cf8 : decode_any W_c0cf8 = Some (Branch BC_EQ 17 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0cfc : bv 32 := 0xfe000813.
Lemma F_c0cfc : fetch_word Ubsan.M.loaded_segments (0xc0eb4 : word) = Some W_c0cfc.
Proof. vm_refl. Qed.
Lemma D_c0cfc : decode_any W_c0cfc = Some (OpImm ALU_ADD 16 0 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d00 : bv 32 := 0x0048969b.
Lemma F_c0d00 : fetch_word Ubsan.M.loaded_segments (0xc0eb8 : word) = Some W_c0d00.
Proof. vm_refl. Qed.
Lemma D_c0d00 : decode_any W_c0d00 = Some (ShiftImm32 ALU_SLL 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d04 : bv 32 := 0x00d786b3.
Lemma F_c0d04 : fetch_word Ubsan.M.loaded_segments (0xc0ebc : word) = Some W_c0d04.
Proof. vm_refl. Qed.
Lemma D_c0d04 : decode_any W_c0d04 = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d08 : bv 32 := 0xff078ea3.
Lemma F_c0d08 : fetch_word Ubsan.M.loaded_segments (0xc0ec0 : word) = Some W_c0d08.
Proof. vm_refl. Qed.
Lemma D_c0d08 : decode_any W_c0d08 = Some (Store SZ1 15 16 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d0c : bv 32 := 0xff179f23.
Lemma F_c0d0c : fetch_word Ubsan.M.loaded_segments (0xc0ec4 : word) = Some W_c0d0c.
Proof. vm_refl. Qed.
Lemma D_c0d0c : decode_any W_c0d0c = Some (Store SZ2 15 17 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d10 : bv 32 := 0xfe068e23.
Lemma F_c0d10 : fetch_word Ubsan.M.loaded_segments (0xc0ec8 : word) = Some W_c0d10.
Proof. vm_refl. Qed.
Lemma D_c0d10 : decode_any W_c0d10 = Some (Store SZ1 13 0 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d14 : bv 32 := 0x01053803.
Lemma F_c0d14 : fetch_word Ubsan.M.loaded_segments (0xc0ecc : word) = Some W_c0d14.
Proof. vm_refl. Qed.
Lemma D_c0d14 : decode_any W_c0d14 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d18 : bv 32 := 0x00e78733.
Lemma F_c0d18 : fetch_word Ubsan.M.loaded_segments (0xc0ed0 : word) = Some W_c0d18.
Proof. vm_refl. Qed.
Lemma D_c0d18 : decode_any W_c0d18 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d1c : bv 32 := 0x410687bb.
Lemma F_c0d1c : fetch_word Ubsan.M.loaded_segments (0xc0ed4 : word) = Some W_c0d1c.
Proof. vm_refl. Qed.
Lemma D_c0d1c : decode_any W_c0d1c = Some (Op32 ALU_SUB 15 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d20 : bv 32 := 0x00d60633.
Lemma F_c0d20 : fetch_word Ubsan.M.loaded_segments (0xc0ed8 : word) = Some W_c0d20.
Proof. vm_refl. Qed.
Lemma D_c0d20 : decode_any W_c0d20 = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d24 : bv 32 := 0xffc70513.
Lemma F_c0d24 : fetch_word Ubsan.M.loaded_segments (0xc0edc : word) = Some W_c0d24.
Proof. vm_refl. Qed.
Lemma D_c0d24 : decode_any W_c0d24 = Some (OpImm ALU_ADD 10 14 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d28 : bv 32 := 0xff078793.
Lemma F_c0d28 : fetch_word Ubsan.M.loaded_segments (0xc0ee0 : word) = Some W_c0d28.
Proof. vm_refl. Qed.
Lemma D_c0d28 : decode_any W_c0d28 = Some (OpImm ALU_ADD 15 15 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d2c : bv 32 := 0x0047d793.
Lemma F_c0d2c : fetch_word Ubsan.M.loaded_segments (0xc0ee4 : word) = Some W_c0d2c.
Proof. vm_refl. Qed.
Lemma D_c0d2c : decode_any W_c0d2c = Some (ShiftImm ALU_SRL 15 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d30 : bv 32 := 0x40c5083b.
Lemma F_c0d30 : fetch_word Ubsan.M.loaded_segments (0xc0ee8 : word) = Some W_c0d30.
Proof. vm_refl. Qed.
Lemma D_c0d30 : decode_any W_c0d30 = Some (Op32 ALU_SUB 16 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d34 : bv 32 := 0xfeb68ea3.
Lemma F_c0d34 : fetch_word Ubsan.M.loaded_segments (0xc0eec : word) = Some W_c0d34.
Proof. vm_refl. Qed.
Lemma D_c0d34 : decode_any W_c0d34 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d38 : bv 32 := 0xfef69f23.
Lemma F_c0d38 : fetch_word Ubsan.M.loaded_segments (0xc0ef0 : word) = Some W_c0d38.
Proof. vm_refl. Qed.
Lemma D_c0d38 : decode_any W_c0d38 = Some (Store SZ2 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d3c : bv 32 := 0x02080463.
Lemma F_c0d3c : fetch_word Ubsan.M.loaded_segments (0xc0ef4 : word) = Some W_c0d3c.
Proof. vm_refl. Qed.
Lemma D_c0d3c : decode_any W_c0d3c = Some (Branch BC_EQ 16 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d40 : bv 32 := 0x40c505bb.
Lemma F_c0d40 : fetch_word Ubsan.M.loaded_segments (0xc0ef8 : word) = Some W_c0d40.
Proof. vm_refl. Qed.
Lemma D_c0d40 : decode_any W_c0d40 = Some (Op32 ALU_SUB 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d44 : bv 32 := 0x40b0063b.
Lemma F_c0d44 : fetch_word Ubsan.M.loaded_segments (0xc0efc : word) = Some W_c0d44.
Proof. vm_refl. Qed.
Lemma D_c0d44 : decode_any W_c0d44 = Some (Op32 ALU_SUB 12 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d48 : bv 32 := 0x00c50633.
Lemma F_c0d48 : fetch_word Ubsan.M.loaded_segments (0xc0f00 : word) = Some W_c0d48.
Proof. vm_refl. Qed.
Lemma D_c0d48 : decode_any W_c0d48 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d4c : bv 32 := 0x00500513.
Lemma F_c0d4c : fetch_word Ubsan.M.loaded_segments (0xc0f04 : word) = Some W_c0d4c.
Proof. vm_refl. Qed.
Lemma D_c0d4c : decode_any W_c0d4c = Some (OpImm ALU_ADD 10 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d50 : bv 32 := 0x00060023.
Lemma F_c0d50 : fetch_word Ubsan.M.loaded_segments (0xc0f08 : word) = Some W_c0d50.
Proof. vm_refl. Qed.
Lemma D_c0d50 : decode_any W_c0d50 = Some (Store SZ1 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d54 : bv 32 := 0x00a5cc63.
Lemma F_c0d54 : fetch_word Ubsan.M.loaded_segments (0xc0f0c : word) = Some W_c0d54.
Proof. vm_refl. Qed.
Lemma D_c0d54 : decode_any W_c0d54 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d58 : bv 32 := 0xfe070ba3.
Lemma F_c0d58 : fetch_word Ubsan.M.loaded_segments (0xc0f10 : word) = Some W_c0d58.
Proof. vm_refl. Qed.
Lemma D_c0d58 : decode_any W_c0d58 = Some (Store SZ1 14 0 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d5c : bv 32 := 0xfeb72c23.
Lemma F_c0d5c : fetch_word Ubsan.M.loaded_segments (0xc0f14 : word) = Some W_c0d5c.
Proof. vm_refl. Qed.
Lemma D_c0d5c : decode_any W_c0d5c = Some (Store SZ4 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d60 : bv 32 := 0x0100006f.
Lemma F_c0d60 : fetch_word Ubsan.M.loaded_segments (0xc0f18 : word) = Some W_c0d60.
Proof. vm_refl. Qed.
Lemma D_c0d60 : decode_any W_c0d60 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d64 : bv 32 := 0x00000513.
Lemma F_c0d64 : fetch_word Ubsan.M.loaded_segments (0xc0f1c : word) = Some W_c0d64.
Proof. vm_refl. Qed.
Lemma D_c0d64 : decode_any W_c0d64 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d68 : bv 32 := 0x0080006f.
Lemma F_c0d68 : fetch_word Ubsan.M.loaded_segments (0xc0f20 : word) = Some W_c0d68.
Proof. vm_refl. Qed.
Lemma D_c0d68 : decode_any W_c0d68 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d6c : bv 32 := 0x00058513.
Lemma F_c0d6c : fetch_word Ubsan.M.loaded_segments (0xc0f24 : word) = Some W_c0d6c.
Proof. vm_refl. Qed.
Lemma D_c0d6c : decode_any W_c0d6c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d70 : bv 32 := 0xffd6c583.
Lemma F_c0d70 : fetch_word Ubsan.M.loaded_segments (0xc0f28 : word) = Some W_c0d70.
Proof. vm_refl. Qed.
Lemma D_c0d70 : decode_any W_c0d70 = Some (Load SZ1 false 11 13 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d74 : bv 32 := 0x01f5f593.
Lemma F_c0d74 : fetch_word Ubsan.M.loaded_segments (0xc0f2c : word) = Some W_c0d74.
Proof. vm_refl. Qed.
Lemma D_c0d74 : decode_any W_c0d74 = Some (OpImm ALU_AND 11 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d78 : bv 32 := 0x00551513.
Lemma F_c0d78 : fetch_word Ubsan.M.loaded_segments (0xc0f30 : word) = Some W_c0d78.
Proof. vm_refl. Qed.
Lemma D_c0d78 : decode_any W_c0d78 = Some (ShiftImm ALU_SLL 10 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d7c : bv 32 := 0x00b56533.
Lemma F_c0d7c : fetch_word Ubsan.M.loaded_segments (0xc0f34 : word) = Some W_c0d7c.
Proof. vm_refl. Qed.
Lemma D_c0d7c : decode_any W_c0d7c = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d80 : bv 32 := 0xfea68ea3.
Lemma F_c0d80 : fetch_word Ubsan.M.loaded_segments (0xc0f38 : word) = Some W_c0d80.
Proof. vm_refl. Qed.
Lemma D_c0d80 : decode_any W_c0d80 = Some (Store SZ1 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d84 : bv 32 := 0x00068513.
Lemma F_c0d84 : fetch_word Ubsan.M.loaded_segments (0xc0f3c : word) = Some W_c0d84.
Proof. vm_refl. Qed.
Lemma D_c0d84 : decode_any W_c0d84 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c0d88 : bv 32 := 0x00008067.
Lemma F_c0d88 : fetch_word Ubsan.M.loaded_segments (0xc0f40 : word) = Some W_c0d88.
Proof. vm_refl. Qed.
Lemma D_c0d88 : decode_any W_c0d88 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
