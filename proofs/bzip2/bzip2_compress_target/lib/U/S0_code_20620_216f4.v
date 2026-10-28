(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W_20c24 : bv 32 := 0x02053703.
Lemma F_20c24 : fetch_word Ubsan.M.loaded_segments (0x2aaa8 : word) = Some W_20c24.
Proof. vm_refl. Qed.
Lemma D_20c24 : decode_any W_20c24 = Some (Load SZ8 true 14 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c28 : bv 32 := 0x00c75793.
Lemma F_20c28 : fetch_word Ubsan.M.loaded_segments (0x2aaac : word) = Some W_20c28.
Proof. vm_refl. Qed.
Lemma D_20c28 : decode_any W_20c28 = Some (ShiftImm ALU_SRL 15 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c2c : bv 32 := 0x00078e63.
Lemma F_20c2c : fetch_word Ubsan.M.loaded_segments (0x2aab0 : word) = Some W_20c2c.
Proof. vm_refl. Qed.
Lemma D_20c2c : decode_any W_20c2c = Some (Branch BC_EQ 15 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c30 : bv 32 := 0x01f77793.
Lemma F_20c30 : fetch_word Ubsan.M.loaded_segments (0x2aab4 : word) = Some W_20c30.
Proof. vm_refl. Qed.
Lemma D_20c30 : decode_any W_20c30 = Some (OpImm ALU_AND 15 14 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c34 : bv 32 := 0x00079a63.
Lemma F_20c34 : fetch_word Ubsan.M.loaded_segments (0x2aab8 : word) = Some W_20c34.
Proof. vm_refl. Qed.
Lemma D_20c34 : decode_any W_20c34 = Some (Branch BC_NE 15 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c38 : bv 32 := 0xfffff7b7.
Lemma F_20c38 : fetch_word Ubsan.M.loaded_segments (0x2aabc : word) = Some W_20c38.
Proof. vm_refl. Qed.
Lemma D_20c38 : decode_any W_20c38 = Some (Lui 15 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c3c : bv 32 := 0x00f77733.
Lemma F_20c3c : fetch_word Ubsan.M.loaded_segments (0x2aac0 : word) = Some W_20c3c.
Proof. vm_refl. Qed.
Lemma D_20c3c : decode_any W_20c3c = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c40 : bv 32 := 0xff070713.
Lemma F_20c40 : fetch_word Ubsan.M.loaded_segments (0x2aac4 : word) = Some W_20c40.
Proof. vm_refl. Qed.
Lemma D_20c40 : decode_any W_20c40 = Some (OpImm ALU_ADD 14 14 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c44 : bv 32 := 0x0200006f.
Lemma F_20c44 : fetch_word Ubsan.M.loaded_segments (0x2aac8 : word) = Some W_20c44.
Proof. vm_refl. Qed.
Lemma D_20c44 : decode_any W_20c44 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c48 : bv 32 := 0x00575713.
Lemma F_20c48 : fetch_word Ubsan.M.loaded_segments (0x2aacc : word) = Some W_20c48.
Proof. vm_refl. Qed.
Lemma D_20c48 : decode_any W_20c48 = Some (ShiftImm ALU_SRL 14 14 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c4c : bv 32 := 0xfffe6797.
Lemma F_20c4c : fetch_word Ubsan.M.loaded_segments (0x2aad0 : word) = Some W_20c4c.
Proof. vm_refl. Qed.
Lemma D_20c4c : decode_any W_20c4c = Some (Auipc 15 1048550, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c50 : bv 32 := 0x07e77713.
Lemma F_20c50 : fetch_word Ubsan.M.loaded_segments (0x2aad4 : word) = Some W_20c50.
Proof. vm_refl. Qed.
Lemma D_20c50 : decode_any W_20c50 = Some (OpImm ALU_AND 14 14 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c54 : bv 32 := 0x3c878793.
Lemma F_20c54 : fetch_word Ubsan.M.loaded_segments (0x2aad8 : word) = Some W_20c54.
Proof. vm_refl. Qed.
Lemma D_20c54 : decode_any W_20c54 = Some (OpImm ALU_ADD 15 15 968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c58 : bv 32 := 0x00e78733.
Lemma F_20c58 : fetch_word Ubsan.M.loaded_segments (0x2aadc : word) = Some W_20c58.
Proof. vm_refl. Qed.
Lemma D_20c58 : decode_any W_20c58 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c5c : bv 32 := 0x00075703.
Lemma F_20c5c : fetch_word Ubsan.M.loaded_segments (0x2aae0 : word) = Some W_20c5c.
Proof. vm_refl. Qed.
Lemma D_20c5c : decode_any W_20c5c = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c60 : bv 32 := 0x00471713.
Lemma F_20c60 : fetch_word Ubsan.M.loaded_segments (0x2aae4 : word) = Some W_20c60.
Proof. vm_refl. Qed.
Lemma D_20c60 : decode_any W_20c60 = Some (ShiftImm ALU_SLL 14 14 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c64 : bv 32 := 0x01053803.
Lemma F_20c64 : fetch_word Ubsan.M.loaded_segments (0x2aae8 : word) = Some W_20c64.
Proof. vm_refl. Qed.
Lemma D_20c64 : decode_any W_20c64 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c68 : bv 32 := 0x02b707b3.
Lemma F_20c68 : fetch_word Ubsan.M.loaded_segments (0x2aaec : word) = Some W_20c68.
Proof. vm_refl. Qed.
Lemma D_20c68 : decode_any W_20c68 = Some (Mul M_MUL 15 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c6c : bv 32 := 0x00f807b3.
Lemma F_20c6c : fetch_word Ubsan.M.loaded_segments (0x2aaf0 : word) = Some W_20c6c.
Proof. vm_refl. Qed.
Lemma D_20c6c : decode_any W_20c6c = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c70 : bv 32 := 0x00d7c883.
Lemma F_20c70 : fetch_word Ubsan.M.loaded_segments (0x2aaf4 : word) = Some W_20c70.
Proof. vm_refl. Qed.
Lemma D_20c70 : decode_any W_20c70 = Some (Load SZ1 false 17 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c74 : bv 32 := 0x40c702b3.
Lemma F_20c74 : fetch_word Ubsan.M.loaded_segments (0x2aaf8 : word) = Some W_20c74.
Proof. vm_refl. Qed.
Lemma D_20c74 : decode_any W_20c74 = Some (Op ALU_SUB 5 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c78 : bv 32 := 0xffc28293.
Lemma F_20c78 : fetch_word Ubsan.M.loaded_segments (0x2aafc : word) = Some W_20c78.
Proof. vm_refl. Qed.
Lemma D_20c78 : decode_any W_20c78 = Some (OpImm ALU_ADD 5 5 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c7c : bv 32 := 0x01078793.
Lemma F_20c7c : fetch_word Ubsan.M.loaded_segments (0x2ab00 : word) = Some W_20c7c.
Proof. vm_refl. Qed.
Lemma D_20c7c : decode_any W_20c7c = Some (OpImm ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c80 : bv 32 := 0x00088663.
Lemma F_20c80 : fetch_word Ubsan.M.loaded_segments (0x2ab04 : word) = Some W_20c80.
Proof. vm_refl. Qed.
Lemma D_20c80 : decode_any W_20c80 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c84 : bv 32 := 0xffe7d683.
Lemma F_20c84 : fetch_word Ubsan.M.loaded_segments (0x2ab08 : word) = Some W_20c84.
Proof. vm_refl. Qed.
Lemma D_20c84 : decode_any W_20c84 = Some (Load SZ2 false 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c88 : bv 32 := 0x00168693.
Lemma F_20c88 : fetch_word Ubsan.M.loaded_segments (0x2ab0c : word) = Some W_20c88.
Proof. vm_refl. Qed.
Lemma D_20c88 : decode_any W_20c88 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c8c : bv 32 := 0xffc7c383.
Lemma F_20c8c : fetch_word Ubsan.M.loaded_segments (0x2ab10 : word) = Some W_20c8c.
Proof. vm_refl. Qed.
Lemma D_20c8c : decode_any W_20c8c = Some (Load SZ1 false 7 15 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c90 : bv 32 := 0x0042d313.
Lemma F_20c90 : fetch_word Ubsan.M.loaded_segments (0x2ab14 : word) = Some W_20c90.
Proof. vm_refl. Qed.
Lemma D_20c90 : decode_any W_20c90 = Some (ShiftImm ALU_SRL 6 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c94 : bv 32 := 0x0ff6f893.
Lemma F_20c94 : fetch_word Ubsan.M.loaded_segments (0x2ab18 : word) = Some W_20c94.
Proof. vm_refl. Qed.
Lemma D_20c94 : decode_any W_20c94 = Some (OpImm ALU_AND 17 13 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20c98 : bv 32 := 0x00038463.
Lemma F_20c98 : fetch_word Ubsan.M.loaded_segments (0x2ab1c : word) = Some W_20c98.
Proof. vm_refl. Qed.
Lemma D_20c98 : decode_any W_20c98 = Some (Branch BC_EQ 7 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ca0 : bv 32 := 0x03137e63.
Lemma F_20ca0 : fetch_word Ubsan.M.loaded_segments (0x2ab24 : word) = Some W_20ca0.
Proof. vm_refl. Qed.
Lemma D_20ca0 : decode_any W_20ca0 = Some (Branch BC_GEU 6 17 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ca4 : bv 32 := 0x0052d693.
Lemma F_20ca4 : fetch_word Ubsan.M.loaded_segments (0x2ab28 : word) = Some W_20ca4.
Proof. vm_refl. Qed.
Lemma D_20ca4 : decode_any W_20ca4 = Some (ShiftImm ALU_SRL 13 5 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ca8 : bv 32 := 0x00d366b3.
Lemma F_20ca8 : fetch_word Ubsan.M.loaded_segments (0x2ab2c : word) = Some W_20ca8.
Proof. vm_refl. Qed.
Lemma D_20ca8 : decode_any W_20ca8 = Some (Op ALU_OR 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cac : bv 32 := 0x0026d293.
Lemma F_20cac : fetch_word Ubsan.M.loaded_segments (0x2ab30 : word) = Some W_20cac.
Proof. vm_refl. Qed.
Lemma D_20cac : decode_any W_20cac = Some (ShiftImm ALU_SRL 5 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cb0 : bv 32 := 0x00d2e6b3.
Lemma F_20cb0 : fetch_word Ubsan.M.loaded_segments (0x2ab34 : word) = Some W_20cb0.
Proof. vm_refl. Qed.
Lemma D_20cb0 : decode_any W_20cb0 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cb4 : bv 32 := 0x0046d293.
Lemma F_20cb4 : fetch_word Ubsan.M.loaded_segments (0x2ab38 : word) = Some W_20cb4.
Proof. vm_refl. Qed.
Lemma D_20cb4 : decode_any W_20cb4 = Some (ShiftImm ALU_SRL 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cb8 : bv 32 := 0x00d2e6b3.
Lemma F_20cb8 : fetch_word Ubsan.M.loaded_segments (0x2ab3c : word) = Some W_20cb8.
Proof. vm_refl. Qed.
Lemma D_20cb8 : decode_any W_20cb8 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cbc : bv 32 := 0x00d8f6b3.
Lemma F_20cbc : fetch_word Ubsan.M.loaded_segments (0x2ab40 : word) = Some W_20cbc.
Proof. vm_refl. Qed.
Lemma D_20cbc : decode_any W_20cbc = Some (Op ALU_AND 13 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cc0 : bv 32 := 0x00d338b3.
Lemma F_20cc0 : fetch_word Ubsan.M.loaded_segments (0x2ab44 : word) = Some W_20cc0.
Proof. vm_refl. Qed.
Lemma D_20cc0 : decode_any W_20cc0 = Some (Op ALU_SLTU 17 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cc4 : bv 32 := 0xfff34293.
Lemma F_20cc4 : fetch_word Ubsan.M.loaded_segments (0x2ab48 : word) = Some W_20cc4.
Proof. vm_refl. Qed.
Lemma D_20cc4 : decode_any W_20cc4 = Some (OpImm ALU_XOR 5 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cc8 : bv 32 := 0x411008bb.
Lemma F_20cc8 : fetch_word Ubsan.M.loaded_segments (0x2ab4c : word) = Some W_20cc8.
Proof. vm_refl. Qed.
Lemma D_20cc8 : decode_any W_20cc8 = Some (Op32 ALU_SUB 17 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ccc : bv 32 := 0x0058f8b3.
Lemma F_20ccc : fetch_word Ubsan.M.loaded_segments (0x2ab50 : word) = Some W_20ccc.
Proof. vm_refl. Qed.
Lemma D_20ccc : decode_any W_20ccc = Some (Op ALU_AND 17 17 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cd0 : bv 32 := 0x00d888bb.
Lemma F_20cd0 : fetch_word Ubsan.M.loaded_segments (0x2ab54 : word) = Some W_20cd0.
Proof. vm_refl. Qed.
Lemma D_20cd0 : decode_any W_20cd0 = Some (Op32 ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cd4 : bv 32 := 0x01137463.
Lemma F_20cd4 : fetch_word Ubsan.M.loaded_segments (0x2ab58 : word) = Some W_20cd4.
Proof. vm_refl. Qed.
Lemma D_20cd4 : decode_any W_20cd4 = Some (Branch BC_GEU 6 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cdc : bv 32 := 0x00078693.
Lemma F_20cdc : fetch_word Ubsan.M.loaded_segments (0x2ab60 : word) = Some W_20cdc.
Proof. vm_refl. Qed.
Lemma D_20cdc : decode_any W_20cdc = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ce0 : bv 32 := 0x02088063.
Lemma F_20ce0 : fetch_word Ubsan.M.loaded_segments (0x2ab64 : word) = Some W_20ce0.
Proof. vm_refl. Qed.
Lemma D_20ce0 : decode_any W_20ce0 = Some (Branch BC_EQ 17 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ce4 : bv 32 := 0xfe000813.
Lemma F_20ce4 : fetch_word Ubsan.M.loaded_segments (0x2ab68 : word) = Some W_20ce4.
Proof. vm_refl. Qed.
Lemma D_20ce4 : decode_any W_20ce4 = Some (OpImm ALU_ADD 16 0 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ce8 : bv 32 := 0x0048969b.
Lemma F_20ce8 : fetch_word Ubsan.M.loaded_segments (0x2ab6c : word) = Some W_20ce8.
Proof. vm_refl. Qed.
Lemma D_20ce8 : decode_any W_20ce8 = Some (ShiftImm32 ALU_SLL 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cec : bv 32 := 0x00d786b3.
Lemma F_20cec : fetch_word Ubsan.M.loaded_segments (0x2ab70 : word) = Some W_20cec.
Proof. vm_refl. Qed.
Lemma D_20cec : decode_any W_20cec = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cf0 : bv 32 := 0xff078ea3.
Lemma F_20cf0 : fetch_word Ubsan.M.loaded_segments (0x2ab74 : word) = Some W_20cf0.
Proof. vm_refl. Qed.
Lemma D_20cf0 : decode_any W_20cf0 = Some (Store SZ1 15 16 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cf4 : bv 32 := 0xff179f23.
Lemma F_20cf4 : fetch_word Ubsan.M.loaded_segments (0x2ab78 : word) = Some W_20cf4.
Proof. vm_refl. Qed.
Lemma D_20cf4 : decode_any W_20cf4 = Some (Store SZ2 15 17 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cf8 : bv 32 := 0xfe068e23.
Lemma F_20cf8 : fetch_word Ubsan.M.loaded_segments (0x2ab7c : word) = Some W_20cf8.
Proof. vm_refl. Qed.
Lemma D_20cf8 : decode_any W_20cf8 = Some (Store SZ1 13 0 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20cfc : bv 32 := 0x01053803.
Lemma F_20cfc : fetch_word Ubsan.M.loaded_segments (0x2ab80 : word) = Some W_20cfc.
Proof. vm_refl. Qed.
Lemma D_20cfc : decode_any W_20cfc = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d00 : bv 32 := 0x00e78733.
Lemma F_20d00 : fetch_word Ubsan.M.loaded_segments (0x2ab84 : word) = Some W_20d00.
Proof. vm_refl. Qed.
Lemma D_20d00 : decode_any W_20d00 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d04 : bv 32 := 0x410687bb.
Lemma F_20d04 : fetch_word Ubsan.M.loaded_segments (0x2ab88 : word) = Some W_20d04.
Proof. vm_refl. Qed.
Lemma D_20d04 : decode_any W_20d04 = Some (Op32 ALU_SUB 15 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d08 : bv 32 := 0x00d60633.
Lemma F_20d08 : fetch_word Ubsan.M.loaded_segments (0x2ab8c : word) = Some W_20d08.
Proof. vm_refl. Qed.
Lemma D_20d08 : decode_any W_20d08 = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d0c : bv 32 := 0xffc70513.
Lemma F_20d0c : fetch_word Ubsan.M.loaded_segments (0x2ab90 : word) = Some W_20d0c.
Proof. vm_refl. Qed.
Lemma D_20d0c : decode_any W_20d0c = Some (OpImm ALU_ADD 10 14 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d10 : bv 32 := 0xff078793.
Lemma F_20d10 : fetch_word Ubsan.M.loaded_segments (0x2ab94 : word) = Some W_20d10.
Proof. vm_refl. Qed.
Lemma D_20d10 : decode_any W_20d10 = Some (OpImm ALU_ADD 15 15 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d14 : bv 32 := 0x0047d793.
Lemma F_20d14 : fetch_word Ubsan.M.loaded_segments (0x2ab98 : word) = Some W_20d14.
Proof. vm_refl. Qed.
Lemma D_20d14 : decode_any W_20d14 = Some (ShiftImm ALU_SRL 15 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d18 : bv 32 := 0x40c5083b.
Lemma F_20d18 : fetch_word Ubsan.M.loaded_segments (0x2ab9c : word) = Some W_20d18.
Proof. vm_refl. Qed.
Lemma D_20d18 : decode_any W_20d18 = Some (Op32 ALU_SUB 16 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d1c : bv 32 := 0xfeb68ea3.
Lemma F_20d1c : fetch_word Ubsan.M.loaded_segments (0x2aba0 : word) = Some W_20d1c.
Proof. vm_refl. Qed.
Lemma D_20d1c : decode_any W_20d1c = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d20 : bv 32 := 0xfef69f23.
Lemma F_20d20 : fetch_word Ubsan.M.loaded_segments (0x2aba4 : word) = Some W_20d20.
Proof. vm_refl. Qed.
Lemma D_20d20 : decode_any W_20d20 = Some (Store SZ2 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d24 : bv 32 := 0x02080463.
Lemma F_20d24 : fetch_word Ubsan.M.loaded_segments (0x2aba8 : word) = Some W_20d24.
Proof. vm_refl. Qed.
Lemma D_20d24 : decode_any W_20d24 = Some (Branch BC_EQ 16 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d28 : bv 32 := 0x40c505bb.
Lemma F_20d28 : fetch_word Ubsan.M.loaded_segments (0x2abac : word) = Some W_20d28.
Proof. vm_refl. Qed.
Lemma D_20d28 : decode_any W_20d28 = Some (Op32 ALU_SUB 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d2c : bv 32 := 0x40b0063b.
Lemma F_20d2c : fetch_word Ubsan.M.loaded_segments (0x2abb0 : word) = Some W_20d2c.
Proof. vm_refl. Qed.
Lemma D_20d2c : decode_any W_20d2c = Some (Op32 ALU_SUB 12 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d30 : bv 32 := 0x00c50633.
Lemma F_20d30 : fetch_word Ubsan.M.loaded_segments (0x2abb4 : word) = Some W_20d30.
Proof. vm_refl. Qed.
Lemma D_20d30 : decode_any W_20d30 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d34 : bv 32 := 0x00500513.
Lemma F_20d34 : fetch_word Ubsan.M.loaded_segments (0x2abb8 : word) = Some W_20d34.
Proof. vm_refl. Qed.
Lemma D_20d34 : decode_any W_20d34 = Some (OpImm ALU_ADD 10 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d38 : bv 32 := 0x00060023.
Lemma F_20d38 : fetch_word Ubsan.M.loaded_segments (0x2abbc : word) = Some W_20d38.
Proof. vm_refl. Qed.
Lemma D_20d38 : decode_any W_20d38 = Some (Store SZ1 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d3c : bv 32 := 0x00a5cc63.
Lemma F_20d3c : fetch_word Ubsan.M.loaded_segments (0x2abc0 : word) = Some W_20d3c.
Proof. vm_refl. Qed.
Lemma D_20d3c : decode_any W_20d3c = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d40 : bv 32 := 0xfe070ba3.
Lemma F_20d40 : fetch_word Ubsan.M.loaded_segments (0x2abc4 : word) = Some W_20d40.
Proof. vm_refl. Qed.
Lemma D_20d40 : decode_any W_20d40 = Some (Store SZ1 14 0 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d44 : bv 32 := 0xfeb72c23.
Lemma F_20d44 : fetch_word Ubsan.M.loaded_segments (0x2abc8 : word) = Some W_20d44.
Proof. vm_refl. Qed.
Lemma D_20d44 : decode_any W_20d44 = Some (Store SZ4 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d48 : bv 32 := 0x0100006f.
Lemma F_20d48 : fetch_word Ubsan.M.loaded_segments (0x2abcc : word) = Some W_20d48.
Proof. vm_refl. Qed.
Lemma D_20d48 : decode_any W_20d48 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d4c : bv 32 := 0x00000513.
Lemma F_20d4c : fetch_word Ubsan.M.loaded_segments (0x2abd0 : word) = Some W_20d4c.
Proof. vm_refl. Qed.
Lemma D_20d4c : decode_any W_20d4c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d50 : bv 32 := 0x0080006f.
Lemma F_20d50 : fetch_word Ubsan.M.loaded_segments (0x2abd4 : word) = Some W_20d50.
Proof. vm_refl. Qed.
Lemma D_20d50 : decode_any W_20d50 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d54 : bv 32 := 0x00058513.
Lemma F_20d54 : fetch_word Ubsan.M.loaded_segments (0x2abd8 : word) = Some W_20d54.
Proof. vm_refl. Qed.
Lemma D_20d54 : decode_any W_20d54 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d58 : bv 32 := 0xffd6c583.
Lemma F_20d58 : fetch_word Ubsan.M.loaded_segments (0x2abdc : word) = Some W_20d58.
Proof. vm_refl. Qed.
Lemma D_20d58 : decode_any W_20d58 = Some (Load SZ1 false 11 13 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d5c : bv 32 := 0x01f5f593.
Lemma F_20d5c : fetch_word Ubsan.M.loaded_segments (0x2abe0 : word) = Some W_20d5c.
Proof. vm_refl. Qed.
Lemma D_20d5c : decode_any W_20d5c = Some (OpImm ALU_AND 11 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d60 : bv 32 := 0x00551513.
Lemma F_20d60 : fetch_word Ubsan.M.loaded_segments (0x2abe4 : word) = Some W_20d60.
Proof. vm_refl. Qed.
Lemma D_20d60 : decode_any W_20d60 = Some (ShiftImm ALU_SLL 10 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d64 : bv 32 := 0x00b56533.
Lemma F_20d64 : fetch_word Ubsan.M.loaded_segments (0x2abe8 : word) = Some W_20d64.
Proof. vm_refl. Qed.
Lemma D_20d64 : decode_any W_20d64 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d68 : bv 32 := 0xfea68ea3.
Lemma F_20d68 : fetch_word Ubsan.M.loaded_segments (0x2abec : word) = Some W_20d68.
Proof. vm_refl. Qed.
Lemma D_20d68 : decode_any W_20d68 = Some (Store SZ1 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d6c : bv 32 := 0x00068513.
Lemma F_20d6c : fetch_word Ubsan.M.loaded_segments (0x2abf0 : word) = Some W_20d6c.
Proof. vm_refl. Qed.
Lemma D_20d6c : decode_any W_20d6c = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20d70 : bv 32 := 0x00008067.
Lemma F_20d70 : fetch_word Ubsan.M.loaded_segments (0x2ad6c : word) = Some W_20d70.
Proof. vm_refl. Qed.
Lemma D_20d70 : decode_any W_20d70 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20fc8 : bv 32 := 0x00008067.
Lemma F_20fc8 : fetch_word Ubsan.M.loaded_segments (0x2afc4 : word) = Some W_20fc8.
Proof. vm_refl. Qed.
Lemma D_20fc8 : decode_any W_20fc8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21118 : bv 32 := 0xf9010113.
Lemma F_21118 : fetch_word Ubsan.M.loaded_segments (0x2b114 : word) = Some W_21118.
Proof. vm_refl. Qed.
Lemma D_21118 : decode_any W_21118 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2111c : bv 32 := 0x06113423.
Lemma F_2111c : fetch_word Ubsan.M.loaded_segments (0x2b118 : word) = Some W_2111c.
Proof. vm_refl. Qed.
Lemma D_2111c : decode_any W_2111c = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21120 : bv 32 := 0x06813023.
Lemma F_21120 : fetch_word Ubsan.M.loaded_segments (0x2b11c : word) = Some W_21120.
Proof. vm_refl. Qed.
Lemma D_21120 : decode_any W_21120 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21124 : bv 32 := 0x04913c23.
Lemma F_21124 : fetch_word Ubsan.M.loaded_segments (0x2b120 : word) = Some W_21124.
Proof. vm_refl. Qed.
Lemma D_21124 : decode_any W_21124 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21128 : bv 32 := 0x05213823.
Lemma F_21128 : fetch_word Ubsan.M.loaded_segments (0x2b124 : word) = Some W_21128.
Proof. vm_refl. Qed.
Lemma D_21128 : decode_any W_21128 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2112c : bv 32 := 0x05313423.
Lemma F_2112c : fetch_word Ubsan.M.loaded_segments (0x2b128 : word) = Some W_2112c.
Proof. vm_refl. Qed.
Lemma D_2112c : decode_any W_2112c = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21130 : bv 32 := 0x05413023.
Lemma F_21130 : fetch_word Ubsan.M.loaded_segments (0x2b12c : word) = Some W_21130.
Proof. vm_refl. Qed.
Lemma D_21130 : decode_any W_21130 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21134 : bv 32 := 0x03513c23.
Lemma F_21134 : fetch_word Ubsan.M.loaded_segments (0x2b130 : word) = Some W_21134.
Proof. vm_refl. Qed.
Lemma D_21134 : decode_any W_21134 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21138 : bv 32 := 0x03613823.
Lemma F_21138 : fetch_word Ubsan.M.loaded_segments (0x2b134 : word) = Some W_21138.
Proof. vm_refl. Qed.
Lemma D_21138 : decode_any W_21138 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2113c : bv 32 := 0x00060413.
Lemma F_2113c : fetch_word Ubsan.M.loaded_segments (0x2b138 : word) = Some W_2113c.
Proof. vm_refl. Qed.
Lemma D_2113c : decode_any W_2113c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21140 : bv 32 := 0x00050493.
Lemma F_21140 : fetch_word Ubsan.M.loaded_segments (0x2b13c : word) = Some W_21140.
Proof. vm_refl. Qed.
Lemma D_21140 : decode_any W_21140 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21144 : bv 32 := 0x00007517.
Lemma F_21144 : fetch_word Ubsan.M.loaded_segments (0x2b140 : word) = Some W_21144.
Proof. vm_refl. Qed.
Lemma D_21144 : decode_any W_21144 = Some (Auipc 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21148 : bv 32 := 0xff853a83.
Lemma F_21148 : fetch_word Ubsan.M.loaded_segments (0x2b144 : word) = Some W_21148.
Proof. vm_refl. Qed.
Lemma D_21148 : decode_any W_21148 = Some (Load SZ8 true 21 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2114c : bv 32 := 0x000ab503.
Lemma F_2114c : fetch_word Ubsan.M.loaded_segments (0x2b148 : word) = Some W_2114c.
Proof. vm_refl. Qed.
Lemma D_2114c : decode_any W_2114c = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21150 : bv 32 := 0x02a13423.
Lemma F_21150 : fetch_word Ubsan.M.loaded_segments (0x2b14c : word) = Some W_21150.
Proof. vm_refl. Qed.
Lemma D_21150 : decode_any W_21150 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21154 : bv 32 := 0x0284b503.
Lemma F_21154 : fetch_word Ubsan.M.loaded_segments (0x2b150 : word) = Some W_21154.
Proof. vm_refl. Qed.
Lemma D_21154 : decode_any W_21154 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21158 : bv 32 := 0x0384b603.
Lemma F_21158 : fetch_word Ubsan.M.loaded_segments (0x2b154 : word) = Some W_21158.
Proof. vm_refl. Qed.
Lemma D_21158 : decode_any W_21158 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2115c : bv 32 := 0x40c50b33.
Lemma F_2115c : fetch_word Ubsan.M.loaded_segments (0x2b158 : word) = Some W_2115c.
Proof. vm_refl. Qed.
Lemma D_2115c : decode_any W_2115c = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21160 : bv 32 := 0x00c546b3.
Lemma F_21160 : fetch_word Ubsan.M.loaded_segments (0x2b15c : word) = Some W_21160.
Proof. vm_refl. Qed.
Lemma D_21160 : decode_any W_21160 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21164 : bv 32 := 0x00c13423.
Lemma F_21164 : fetch_word Ubsan.M.loaded_segments (0x2b160 : word) = Some W_21164.
Proof. vm_refl. Qed.
Lemma D_21164 : decode_any W_21164 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21168 : bv 32 := 0x01613823.
Lemma F_21168 : fetch_word Ubsan.M.loaded_segments (0x2b164 : word) = Some W_21168.
Proof. vm_refl. Qed.
Lemma D_21168 : decode_any W_21168 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2116c : bv 32 := 0x00b13c23.
Lemma F_2116c : fetch_word Ubsan.M.loaded_segments (0x2b168 : word) = Some W_2116c.
Proof. vm_refl. Qed.
Lemma D_2116c : decode_any W_2116c = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21170 : bv 32 := 0x02813023.
Lemma F_21170 : fetch_word Ubsan.M.loaded_segments (0x2b16c : word) = Some W_21170.
Proof. vm_refl. Qed.
Lemma D_21170 : decode_any W_21170 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21174 : bv 32 := 0x008b0b33.
Lemma F_21174 : fetch_word Ubsan.M.loaded_segments (0x2b170 : word) = Some W_21174.
Proof. vm_refl. Qed.
Lemma D_21174 : decode_any W_21174 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21178 : bv 32 := 0x00d03933.
Lemma F_21178 : fetch_word Ubsan.M.loaded_segments (0x2b174 : word) = Some W_21178.
Proof. vm_refl. Qed.
Lemma D_21178 : decode_any W_21178 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2117c : bv 32 := 0x00c50663.
Lemma F_2117c : fetch_word Ubsan.M.loaded_segments (0x2b178 : word) = Some W_2117c.
Proof. vm_refl. Qed.
Lemma D_2117c : decode_any W_2117c = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21180 : bv 32 := 0x00810993.
Lemma F_21180 : fetch_word Ubsan.M.loaded_segments (0x2b17c : word) = Some W_21180.
Proof. vm_refl. Qed.
Lemma D_21180 : decode_any W_21180 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21184 : bv 32 := 0x0080006f.
Lemma F_21184 : fetch_word Ubsan.M.loaded_segments (0x2b180 : word) = Some W_21184.
Proof. vm_refl. Qed.
Lemma D_21184 : decode_any W_21184 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21188 : bv 32 := 0x01810993.
Lemma F_21188 : fetch_word Ubsan.M.loaded_segments (0x2b184 : word) = Some W_21188.
Proof. vm_refl. Qed.
Lemma D_21188 : decode_any W_21188 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2118c : bv 32 := 0x0784a503.
Lemma F_2118c : fetch_word Ubsan.M.loaded_segments (0x2b188 : word) = Some W_2118c.
Proof. vm_refl. Qed.
Lemma D_2118c : decode_any W_2118c = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21190 : bv 32 := 0x00190913.
Lemma F_21190 : fetch_word Ubsan.M.loaded_segments (0x2b18c : word) = Some W_21190.
Proof. vm_refl. Qed.
Lemma D_21190 : decode_any W_21190 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21194 : bv 32 := 0x04200893.
Lemma F_21194 : fetch_word Ubsan.M.loaded_segments (0x2b190 : word) = Some W_21194.
Proof. vm_refl. Qed.
Lemma D_21194 : decode_any W_21194 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21198 : bv 32 := 0x00098593.
Lemma F_21198 : fetch_word Ubsan.M.loaded_segments (0x2b194 : word) = Some W_21198.
Proof. vm_refl. Qed.
Lemma D_21198 : decode_any W_21198 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2119c : bv 32 := 0x00090613.
Lemma F_2119c : fetch_word Ubsan.M.loaded_segments (0x2b198 : word) = Some W_2119c.
Proof. vm_refl. Qed.
Lemma D_2119c : decode_any W_2119c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211a0 : bv 32 := 0x00000073.
Lemma F_211a0 : fetch_word Ubsan.M.loaded_segments (0x2b19c : word) = Some W_211a0.
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma E_211a0 : is_ecall W_211a0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_211a4 : bv 32 := 0x9e0fe0ef.
Lemma F_211a4 : fetch_word Ubsan.M.loaded_segments (0x2b1a0 : word) = Some W_211a4.
Proof. vm_refl. Qed.
Lemma D_211a4 : decode_any W_211a4 = Some (Jal 1 2089440, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211a8 : bv 32 := 0x09651863.
Lemma F_211a8 : fetch_word Ubsan.M.loaded_segments (0x2b1a4 : word) = Some W_211a8.
Proof. vm_refl. Qed.
Lemma D_211a8 : decode_any W_211a8 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211ac : bv 32 := 0x0584b503.
Lemma F_211ac : fetch_word Ubsan.M.loaded_segments (0x2b1a8 : word) = Some W_211ac.
Proof. vm_refl. Qed.
Lemma D_211ac : decode_any W_211ac = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211b0 : bv 32 := 0x0604b583.
Lemma F_211b0 : fetch_word Ubsan.M.loaded_segments (0x2b1ac : word) = Some W_211b0.
Proof. vm_refl. Qed.
Lemma D_211b0 : decode_any W_211b0 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211b4 : bv 32 := 0x00b505b3.
Lemma F_211b4 : fetch_word Ubsan.M.loaded_segments (0x2b1b0 : word) = Some W_211b4.
Proof. vm_refl. Qed.
Lemma D_211b4 : decode_any W_211b4 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211b8 : bv 32 := 0x02b4b023.
Lemma F_211b8 : fetch_word Ubsan.M.loaded_segments (0x2b1b4 : word) = Some W_211b8.
Proof. vm_refl. Qed.
Lemma D_211b8 : decode_any W_211b8 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211bc : bv 32 := 0x02a4b423.
Lemma F_211bc : fetch_word Ubsan.M.loaded_segments (0x2b1b8 : word) = Some W_211bc.
Proof. vm_refl. Qed.
Lemma D_211bc : decode_any W_211bc = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211c0 : bv 32 := 0x02a4bc23.
Lemma F_211c0 : fetch_word Ubsan.M.loaded_segments (0x2b1bc : word) = Some W_211c0.
Proof. vm_refl. Qed.
Lemma D_211c0 : decode_any W_211c0 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211c4 : bv 32 := 0x00040513.
Lemma F_211c4 : fetch_word Ubsan.M.loaded_segments (0x2b1c0 : word) = Some W_211c4.
Proof. vm_refl. Qed.
Lemma D_211c4 : decode_any W_211c4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211c8 : bv 32 := 0x000ab583.
Lemma F_211c8 : fetch_word Ubsan.M.loaded_segments (0x2b1c4 : word) = Some W_211c8.
Proof. vm_refl. Qed.
Lemma D_211c8 : decode_any W_211c8 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211cc : bv 32 := 0x02813603.
Lemma F_211cc : fetch_word Ubsan.M.loaded_segments (0x2b1c8 : word) = Some W_211cc.
Proof. vm_refl. Qed.
Lemma D_211cc : decode_any W_211cc = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211d0 : bv 32 := 0x0cc59a63.
Lemma F_211d0 : fetch_word Ubsan.M.loaded_segments (0x2b1cc : word) = Some W_211d0.
Proof. vm_refl. Qed.
Lemma D_211d0 : decode_any W_211d0 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211d4 : bv 32 := 0x06813083.
Lemma F_211d4 : fetch_word Ubsan.M.loaded_segments (0x2b1d0 : word) = Some W_211d4.
Proof. vm_refl. Qed.
Lemma D_211d4 : decode_any W_211d4 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211d8 : bv 32 := 0x06013403.
Lemma F_211d8 : fetch_word Ubsan.M.loaded_segments (0x2b1d4 : word) = Some W_211d8.
Proof. vm_refl. Qed.
Lemma D_211d8 : decode_any W_211d8 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211dc : bv 32 := 0x05813483.
Lemma F_211dc : fetch_word Ubsan.M.loaded_segments (0x2b1d8 : word) = Some W_211dc.
Proof. vm_refl. Qed.
Lemma D_211dc : decode_any W_211dc = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211e0 : bv 32 := 0x05013903.
Lemma F_211e0 : fetch_word Ubsan.M.loaded_segments (0x2b1dc : word) = Some W_211e0.
Proof. vm_refl. Qed.
Lemma D_211e0 : decode_any W_211e0 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211e4 : bv 32 := 0x04813983.
Lemma F_211e4 : fetch_word Ubsan.M.loaded_segments (0x2b1e0 : word) = Some W_211e4.
Proof. vm_refl. Qed.
Lemma D_211e4 : decode_any W_211e4 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211e8 : bv 32 := 0x04013a03.
Lemma F_211e8 : fetch_word Ubsan.M.loaded_segments (0x2b1e4 : word) = Some W_211e8.
Proof. vm_refl. Qed.
Lemma D_211e8 : decode_any W_211e8 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211ec : bv 32 := 0x03813a83.
Lemma F_211ec : fetch_word Ubsan.M.loaded_segments (0x2b1e8 : word) = Some W_211ec.
Proof. vm_refl. Qed.
Lemma D_211ec : decode_any W_211ec = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211f0 : bv 32 := 0x03013b03.
Lemma F_211f0 : fetch_word Ubsan.M.loaded_segments (0x2b1ec : word) = Some W_211f0.
Proof. vm_refl. Qed.
Lemma D_211f0 : decode_any W_211f0 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211f4 : bv 32 := 0x07010113.
Lemma F_211f4 : fetch_word Ubsan.M.loaded_segments (0x2b1f0 : word) = Some W_211f4.
Proof. vm_refl. Qed.
Lemma D_211f4 : decode_any W_211f4 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211f8 : bv 32 := 0x00008067.
Lemma F_211f8 : fetch_word Ubsan.M.loaded_segments (0x2b1f4 : word) = Some W_211f8.
Proof. vm_refl. Qed.
Lemma D_211f8 : decode_any W_211f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_211fc : bv 32 := 0x00800713.
Lemma F_211fc : fetch_word Ubsan.M.loaded_segments (0x2b1f8 : word) = Some W_211fc.
Proof. vm_refl. Qed.
Lemma D_211fc : decode_any W_211fc = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21200 : bv 32 := 0x000a0593.
Lemma F_21200 : fetch_word Ubsan.M.loaded_segments (0x2b1fc : word) = Some W_21200.
Proof. vm_refl. Qed.
Lemma D_21200 : decode_any W_21200 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21204 : bv 32 := 0x00e98733.
Lemma F_21204 : fetch_word Ubsan.M.loaded_segments (0x2b200 : word) = Some W_21204.
Proof. vm_refl. Qed.
Lemma D_21204 : decode_any W_21204 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21208 : bv 32 := 0x00073783.
Lemma F_21208 : fetch_word Ubsan.M.loaded_segments (0x2b204 : word) = Some W_21208.
Proof. vm_refl. Qed.
Lemma D_21208 : decode_any W_21208 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2120c : bv 32 := 0x40ab0b33.
Lemma F_2120c : fetch_word Ubsan.M.loaded_segments (0x2b208 : word) = Some W_2120c.
Proof. vm_refl. Qed.
Lemma D_2120c : decode_any W_2120c = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21210 : bv 32 := 0x0784a503.
Lemma F_21210 : fetch_word Ubsan.M.loaded_segments (0x2b20c : word) = Some W_21210.
Proof. vm_refl. Qed.
Lemma D_21210 : decode_any W_21210 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21214 : bv 32 := 0x40c9093b.
Lemma F_21214 : fetch_word Ubsan.M.loaded_segments (0x2b210 : word) = Some W_21214.
Proof. vm_refl. Qed.
Lemma D_21214 : decode_any W_21214 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21218 : bv 32 := 0x40d787b3.
Lemma F_21218 : fetch_word Ubsan.M.loaded_segments (0x2b214 : word) = Some W_21218.
Proof. vm_refl. Qed.
Lemma D_21218 : decode_any W_21218 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2121c : bv 32 := 0x00f73023.
Lemma F_2121c : fetch_word Ubsan.M.loaded_segments (0x2b218 : word) = Some W_2121c.
Proof. vm_refl. Qed.
Lemma D_2121c : decode_any W_2121c = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21220 : bv 32 := 0x04200893.
Lemma F_21220 : fetch_word Ubsan.M.loaded_segments (0x2b21c : word) = Some W_21220.
Proof. vm_refl. Qed.
Lemma D_21220 : decode_any W_21220 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21224 : bv 32 := 0x00090613.
Lemma F_21224 : fetch_word Ubsan.M.loaded_segments (0x2b220 : word) = Some W_21224.
Proof. vm_refl. Qed.
Lemma D_21224 : decode_any W_21224 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21228 : bv 32 := 0x00000073.
Lemma F_21228 : fetch_word Ubsan.M.loaded_segments (0x2b224 : word) = Some W_21228.
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Lemma E_21228 : is_ecall W_21228 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_2122c : bv 32 := 0x958fe0ef.
Lemma F_2122c : fetch_word Ubsan.M.loaded_segments (0x2b228 : word) = Some W_2122c.
Proof. vm_refl. Qed.
Lemma D_2122c : decode_any W_2122c = Some (Jal 1 2089304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21230 : bv 32 := 0x000a0993.
Lemma F_21230 : fetch_word Ubsan.M.loaded_segments (0x2b22c : word) = Some W_21230.
Proof. vm_refl. Qed.
Lemma D_21230 : decode_any W_21230 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21234 : bv 32 := 0xf7650ce3.
Lemma F_21234 : fetch_word Ubsan.M.loaded_segments (0x2b230 : word) = Some W_21234.
Proof. vm_refl. Qed.
Lemma D_21234 : decode_any W_21234 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21238 : bv 32 := 0x02054c63.
Lemma F_21238 : fetch_word Ubsan.M.loaded_segments (0x2b234 : word) = Some W_21238.
Proof. vm_refl. Qed.
Lemma D_21238 : decode_any W_21238 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2123c : bv 32 := 0x0089b583.
Lemma F_2123c : fetch_word Ubsan.M.loaded_segments (0x2b238 : word) = Some W_2123c.
Proof. vm_refl. Qed.
Lemma D_2123c : decode_any W_2123c = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21240 : bv 32 := 0x00a5b633.
Lemma F_21240 : fetch_word Ubsan.M.loaded_segments (0x2b23c : word) = Some W_21240.
Proof. vm_refl. Qed.
Lemma D_21240 : decode_any W_21240 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21244 : bv 32 := 0x00461a13.
Lemma F_21244 : fetch_word Ubsan.M.loaded_segments (0x2b240 : word) = Some W_21244.
Proof. vm_refl. Qed.
Lemma D_21244 : decode_any W_21244 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21248 : bv 32 := 0x01498a33.
Lemma F_21248 : fetch_word Ubsan.M.loaded_segments (0x2b244 : word) = Some W_21248.
Proof. vm_refl. Qed.
Lemma D_21248 : decode_any W_21248 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2124c : bv 32 := 0x000a3703.
Lemma F_2124c : fetch_word Ubsan.M.loaded_segments (0x2b248 : word) = Some W_2124c.
Proof. vm_refl. Qed.
Lemma D_2124c : decode_any W_2124c = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21250 : bv 32 := 0x40c006b3.
Lemma F_21250 : fetch_word Ubsan.M.loaded_segments (0x2b24c : word) = Some W_21250.
Proof. vm_refl. Qed.
Lemma D_21250 : decode_any W_21250 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21254 : bv 32 := 0x00b6f6b3.
Lemma F_21254 : fetch_word Ubsan.M.loaded_segments (0x2b250 : word) = Some W_21254.
Proof. vm_refl. Qed.
Lemma D_21254 : decode_any W_21254 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21258 : bv 32 := 0x40d506b3.
Lemma F_21258 : fetch_word Ubsan.M.loaded_segments (0x2b254 : word) = Some W_21258.
Proof. vm_refl. Qed.
Lemma D_21258 : decode_any W_21258 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2125c : bv 32 := 0x00d70733.
Lemma F_2125c : fetch_word Ubsan.M.loaded_segments (0x2b258 : word) = Some W_2125c.
Proof. vm_refl. Qed.
Lemma D_2125c : decode_any W_2125c = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21260 : bv 32 := 0x00ea3023.
Lemma F_21260 : fetch_word Ubsan.M.loaded_segments (0x2b25c : word) = Some W_21260.
Proof. vm_refl. Qed.
Lemma D_21260 : decode_any W_21260 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21264 : bv 32 := 0xf8a5fce3.
Lemma F_21264 : fetch_word Ubsan.M.loaded_segments (0x2b260 : word) = Some W_21264.
Proof. vm_refl. Qed.
Lemma D_21264 : decode_any W_21264 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21268 : bv 32 := 0x01800713.
Lemma F_21268 : fetch_word Ubsan.M.loaded_segments (0x2b264 : word) = Some W_21268.
Proof. vm_refl. Qed.
Lemma D_21268 : decode_any W_21268 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2126c : bv 32 := 0xf95ff06f.
Lemma F_2126c : fetch_word Ubsan.M.loaded_segments (0x2b268 : word) = Some W_2126c.
Proof. vm_refl. Qed.
Lemma D_2126c : decode_any W_2126c = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21404 : bv 32 := 0xff010113.
Lemma F_21404 : fetch_word Ubsan.M.loaded_segments (0x2b570 : word) = Some W_21404.
Proof. vm_refl. Qed.
Lemma D_21404 : decode_any W_21404 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21408 : bv 32 := 0x00113423.
Lemma F_21408 : fetch_word Ubsan.M.loaded_segments (0x2b574 : word) = Some W_21408.
Proof. vm_refl. Qed.
Lemma D_21408 : decode_any W_21408 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2140c : bv 32 := 0x00813023.
Lemma F_2140c : fetch_word Ubsan.M.loaded_segments (0x2b578 : word) = Some W_2140c.
Proof. vm_refl. Qed.
Lemma D_2140c : decode_any W_2140c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21410 : bv 32 := 0x660000ef.
Lemma F_21410 : fetch_word Ubsan.M.loaded_segments (0x2b57c : word) = Some W_21410.
Proof. vm_refl. Qed.
Lemma D_21410 : decode_any W_21410 = Some (Jal 1 1632, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21414 : bv 32 := 0x00053403.
Lemma F_21414 : fetch_word Ubsan.M.loaded_segments (0x2b580 : word) = Some W_21414.
Proof. vm_refl. Qed.
Lemma D_21414 : decode_any W_21414 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21418 : bv 32 := 0x12041663.
Lemma F_21418 : fetch_word Ubsan.M.loaded_segments (0x2b584 : word) = Some W_21418.
Proof. vm_refl. Qed.
Lemma D_21418 : decode_any W_21418 = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2141c : bv 32 := 0x00009517.
Lemma F_2141c : fetch_word Ubsan.M.loaded_segments (0x2b588 : word) = Some W_2141c.
Proof. vm_refl. Qed.
Lemma D_2141c : decode_any W_2141c = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21420 : bv 32 := 0xa0053403.
Lemma F_21420 : fetch_word Ubsan.M.loaded_segments (0x2b58c : word) = Some W_21420.
Proof. vm_refl. Qed.
Lemma D_21420 : decode_any W_21420 = Some (Load SZ8 true 8 10 2560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21424 : bv 32 := 0x04040a63.
Lemma F_21424 : fetch_word Ubsan.M.loaded_segments (0x2b590 : word) = Some W_21424.
Proof. vm_refl. Qed.
Lemma D_21424 : decode_any W_21424 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21428 : bv 32 := 0x08c42503.
Lemma F_21428 : fetch_word Ubsan.M.loaded_segments (0x2b594 : word) = Some W_21428.
Proof. vm_refl. Qed.
Lemma D_21428 : decode_any W_21428 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2142c : bv 32 := 0x00054663.
Lemma F_2142c : fetch_word Ubsan.M.loaded_segments (0x2b598 : word) = Some W_2142c.
Proof. vm_refl. Qed.
Lemma D_2142c : decode_any W_2142c = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21438 : bv 32 := 0x02843503.
Lemma F_21438 : fetch_word Ubsan.M.loaded_segments (0x2b5a4 : word) = Some W_21438.
Proof. vm_refl. Qed.
Lemma D_21438 : decode_any W_21438 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2143c : bv 32 := 0x03843583.
Lemma F_2143c : fetch_word Ubsan.M.loaded_segments (0x2b5a8 : word) = Some W_2143c.
Proof. vm_refl. Qed.
Lemma D_2143c : decode_any W_2143c = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21440 : bv 32 := 0x00b50c63.
Lemma F_21440 : fetch_word Ubsan.M.loaded_segments (0x2b5ac : word) = Some W_21440.
Proof. vm_refl. Qed.
Lemma D_21440 : decode_any W_21440 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21458 : bv 32 := 0x00843503.
Lemma F_21458 : fetch_word Ubsan.M.loaded_segments (0x2b5c4 : word) = Some W_21458.
Proof. vm_refl. Qed.
Lemma D_21458 : decode_any W_21458 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2145c : bv 32 := 0x01043583.
Lemma F_2145c : fetch_word Ubsan.M.loaded_segments (0x2b5c8 : word) = Some W_2145c.
Proof. vm_refl. Qed.
Lemma D_2145c : decode_any W_2145c = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21460 : bv 32 := 0x00b50c63.
Lemma F_21460 : fetch_word Ubsan.M.loaded_segments (0x2b5cc : word) = Some W_21460.
Proof. vm_refl. Qed.
Lemma D_21460 : decode_any W_21460 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21478 : bv 32 := 0x00009517.
Lemma F_21478 : fetch_word Ubsan.M.loaded_segments (0x2b5e4 : word) = Some W_21478.
Proof. vm_refl. Qed.
Lemma D_21478 : decode_any W_21478 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2147c : bv 32 := 0xa9453403.
Lemma F_2147c : fetch_word Ubsan.M.loaded_segments (0x2b5e8 : word) = Some W_2147c.
Proof. vm_refl. Qed.
Lemma D_2147c : decode_any W_2147c = Some (Load SZ8 true 8 10 2708, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21480 : bv 32 := 0x04040a63.
Lemma F_21480 : fetch_word Ubsan.M.loaded_segments (0x2b5ec : word) = Some W_21480.
Proof. vm_refl. Qed.
Lemma D_21480 : decode_any W_21480 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21484 : bv 32 := 0x08c42503.
Lemma F_21484 : fetch_word Ubsan.M.loaded_segments (0x2b5f0 : word) = Some W_21484.
Proof. vm_refl. Qed.
Lemma D_21484 : decode_any W_21484 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21488 : bv 32 := 0x00054663.
Lemma F_21488 : fetch_word Ubsan.M.loaded_segments (0x2b5f4 : word) = Some W_21488.
Proof. vm_refl. Qed.
Lemma D_21488 : decode_any W_21488 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21494 : bv 32 := 0x02843503.
Lemma F_21494 : fetch_word Ubsan.M.loaded_segments (0x2b600 : word) = Some W_21494.
Proof. vm_refl. Qed.
Lemma D_21494 : decode_any W_21494 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21498 : bv 32 := 0x03843583.
Lemma F_21498 : fetch_word Ubsan.M.loaded_segments (0x2b604 : word) = Some W_21498.
Proof. vm_refl. Qed.
Lemma D_21498 : decode_any W_21498 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2149c : bv 32 := 0x00b50c63.
Lemma F_2149c : fetch_word Ubsan.M.loaded_segments (0x2b608 : word) = Some W_2149c.
Proof. vm_refl. Qed.
Lemma D_2149c : decode_any W_2149c = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_214a0 : bv 32 := 0x04843683.
Lemma F_214a0 : fetch_word Ubsan.M.loaded_segments (0x2b60c : word) = Some W_214a0.
Proof. vm_refl. Qed.
Lemma D_214a0 : decode_any W_214a0 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_214a4 : bv 32 := 0x00040513.
Lemma F_214a4 : fetch_word Ubsan.M.loaded_segments (0x2b610 : word) = Some W_214a4.
Proof. vm_refl. Qed.
Lemma D_214a4 : decode_any W_214a4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_214a8 : bv 32 := 0x00000593.
Lemma F_214a8 : fetch_word Ubsan.M.loaded_segments (0x2b614 : word) = Some W_214a8.
Proof. vm_refl. Qed.
Lemma D_214a8 : decode_any W_214a8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_214ac : bv 32 := 0x00000613.
Lemma F_214ac : fetch_word Ubsan.M.loaded_segments (0x2b618 : word) = Some W_214ac.
Proof. vm_refl. Qed.
Lemma D_214ac : decode_any W_214ac = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_214b0 : bv 32 := 0x000680e7.
Lemma F_214b0 : fetch_word Ubsan.M.loaded_segments (0x2b61c : word) = Some W_214b0.
Proof. vm_refl. Qed.
Lemma D_214b0 : decode_any W_214b0 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_214b4 : bv 32 := 0x00843503.
Lemma F_214b4 : fetch_word Ubsan.M.loaded_segments (0x2b620 : word) = Some W_214b4.
Proof. vm_refl. Qed.
Lemma D_214b4 : decode_any W_214b4 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_214b8 : bv 32 := 0x01043583.
Lemma F_214b8 : fetch_word Ubsan.M.loaded_segments (0x2b624 : word) = Some W_214b8.
Proof. vm_refl. Qed.
Lemma D_214b8 : decode_any W_214b8 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_214bc : bv 32 := 0x00b50c63.
Lemma F_214bc : fetch_word Ubsan.M.loaded_segments (0x2b628 : word) = Some W_214bc.
Proof. vm_refl. Qed.
Lemma D_214bc : decode_any W_214bc = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_214d4 : bv 32 := 0x00009517.
Lemma F_214d4 : fetch_word Ubsan.M.loaded_segments (0x2b640 : word) = Some W_214d4.
Proof. vm_refl. Qed.
Lemma D_214d4 : decode_any W_214d4 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_214d8 : bv 32 := 0x85853403.
Lemma F_214d8 : fetch_word Ubsan.M.loaded_segments (0x2b644 : word) = Some W_214d8.
Proof. vm_refl. Qed.
Lemma D_214d8 : decode_any W_214d8 = Some (Load SZ8 true 8 10 2136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_214dc : bv 32 := 0x0a040e63.
Lemma F_214dc : fetch_word Ubsan.M.loaded_segments (0x2b648 : word) = Some W_214dc.
Proof. vm_refl. Qed.
Lemma D_214dc : decode_any W_214dc = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_214e0 : bv 32 := 0x08c42503.
Lemma F_214e0 : fetch_word Ubsan.M.loaded_segments (0x2b64c : word) = Some W_214e0.
Proof. vm_refl. Qed.
Lemma D_214e0 : decode_any W_214e0 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_214e4 : bv 32 := 0x00054663.
Lemma F_214e4 : fetch_word Ubsan.M.loaded_segments (0x2b650 : word) = Some W_214e4.
Proof. vm_refl. Qed.
Lemma D_214e4 : decode_any W_214e4 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_214f0 : bv 32 := 0x02843503.
Lemma F_214f0 : fetch_word Ubsan.M.loaded_segments (0x2b65c : word) = Some W_214f0.
Proof. vm_refl. Qed.
Lemma D_214f0 : decode_any W_214f0 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_214f4 : bv 32 := 0x03843583.
Lemma F_214f4 : fetch_word Ubsan.M.loaded_segments (0x2b660 : word) = Some W_214f4.
Proof. vm_refl. Qed.
Lemma D_214f4 : decode_any W_214f4 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_214f8 : bv 32 := 0x00b50c63.
Lemma F_214f8 : fetch_word Ubsan.M.loaded_segments (0x2b664 : word) = Some W_214f8.
Proof. vm_refl. Qed.
Lemma D_214f8 : decode_any W_214f8 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21510 : bv 32 := 0x00843503.
Lemma F_21510 : fetch_word Ubsan.M.loaded_segments (0x2b67c : word) = Some W_21510.
Proof. vm_refl. Qed.
Lemma D_21510 : decode_any W_21510 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21514 : bv 32 := 0x01043583.
Lemma F_21514 : fetch_word Ubsan.M.loaded_segments (0x2b680 : word) = Some W_21514.
Proof. vm_refl. Qed.
Lemma D_21514 : decode_any W_21514 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21518 : bv 32 := 0x08b50063.
Lemma F_21518 : fetch_word Ubsan.M.loaded_segments (0x2b684 : word) = Some W_21518.
Proof. vm_refl. Qed.
Lemma D_21518 : decode_any W_21518 = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21598 : bv 32 := 0x00813083.
Lemma F_21598 : fetch_word Ubsan.M.loaded_segments (0x2b704 : word) = Some W_21598.
Proof. vm_refl. Qed.
Lemma D_21598 : decode_any W_21598 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2159c : bv 32 := 0x00013403.
Lemma F_2159c : fetch_word Ubsan.M.loaded_segments (0x2b708 : word) = Some W_2159c.
Proof. vm_refl. Qed.
Lemma D_2159c : decode_any W_2159c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_215a0 : bv 32 := 0x01010113.
Lemma F_215a0 : fetch_word Ubsan.M.loaded_segments (0x2b70c : word) = Some W_215a0.
Proof. vm_refl. Qed.
Lemma D_215a0 : decode_any W_215a0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_215a4 : bv 32 := 0x00008067.
Lemma F_215a4 : fetch_word Ubsan.M.loaded_segments (0x2b710 : word) = Some W_215a4.
Proof. vm_refl. Qed.
Lemma D_215a4 : decode_any W_215a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

