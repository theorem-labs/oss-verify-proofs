(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.


(* [comment removed for export] *)
Definition W_1d81c : bv 32 := 0x02053703.
Lemma F_1d81c : fetch_word Ubsan.M.loaded_segments (0x1d81c : word) = Some W_1d81c.
Proof. vm_refl. Qed.
Lemma D_1d81c : decode_any W_1d81c = Some (Load SZ8 true 14 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d820 : bv 32 := 0x00c75793.
Lemma F_1d820 : fetch_word Ubsan.M.loaded_segments (0x1d820 : word) = Some W_1d820.
Proof. vm_refl. Qed.
Lemma D_1d820 : decode_any W_1d820 = Some (ShiftImm ALU_SRL 15 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d824 : bv 32 := 0x00078e63.
Lemma F_1d824 : fetch_word Ubsan.M.loaded_segments (0x1d824 : word) = Some W_1d824.
Proof. vm_refl. Qed.
Lemma D_1d824 : decode_any W_1d824 = Some (Branch BC_EQ 15 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d828 : bv 32 := 0x01f77793.
Lemma F_1d828 : fetch_word Ubsan.M.loaded_segments (0x1d828 : word) = Some W_1d828.
Proof. vm_refl. Qed.
Lemma D_1d828 : decode_any W_1d828 = Some (OpImm ALU_AND 15 14 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d82c : bv 32 := 0x00079a63.
Lemma F_1d82c : fetch_word Ubsan.M.loaded_segments (0x1d82c : word) = Some W_1d82c.
Proof. vm_refl. Qed.
Lemma D_1d82c : decode_any W_1d82c = Some (Branch BC_NE 15 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d830 : bv 32 := 0xfffff7b7.
Lemma F_1d830 : fetch_word Ubsan.M.loaded_segments (0x1d830 : word) = Some W_1d830.
Proof. vm_refl. Qed.
Lemma D_1d830 : decode_any W_1d830 = Some (Lui 15 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d834 : bv 32 := 0x00f77733.
Lemma F_1d834 : fetch_word Ubsan.M.loaded_segments (0x1d834 : word) = Some W_1d834.
Proof. vm_refl. Qed.
Lemma D_1d834 : decode_any W_1d834 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d838 : bv 32 := 0xff070713.
Lemma F_1d838 : fetch_word Ubsan.M.loaded_segments (0x1d838 : word) = Some W_1d838.
Proof. vm_refl. Qed.
Lemma D_1d838 : decode_any W_1d838 = Some (OpImm ALU_ADD 14 14 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d83c : bv 32 := 0x0200006f.
Lemma F_1d83c : fetch_word Ubsan.M.loaded_segments (0x1d83c : word) = Some W_1d83c.
Proof. vm_refl. Qed.
Lemma D_1d83c : decode_any W_1d83c = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d840 : bv 32 := 0x00575713.
Lemma F_1d840 : fetch_word Ubsan.M.loaded_segments (0x1d840 : word) = Some W_1d840.
Proof. vm_refl. Qed.
Lemma D_1d840 : decode_any W_1d840 = Some (ShiftImm ALU_SRL 14 14 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d844 : bv 32 := 0xffff4797.
Lemma F_1d844 : fetch_word Ubsan.M.loaded_segments (0x1d844 : word) = Some W_1d844.
Proof. vm_refl. Qed.
Lemma D_1d844 : decode_any W_1d844 = Some (Auipc 15 1048564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d848 : bv 32 := 0x07e77713.
Lemma F_1d848 : fetch_word Ubsan.M.loaded_segments (0x1d848 : word) = Some W_1d848.
Proof. vm_refl. Qed.
Lemma D_1d848 : decode_any W_1d848 = Some (OpImm ALU_AND 14 14 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d84c : bv 32 := 0x87478793.
Lemma F_1d84c : fetch_word Ubsan.M.loaded_segments (0x1d84c : word) = Some W_1d84c.
Proof. vm_refl. Qed.
Lemma D_1d84c : decode_any W_1d84c = Some (OpImm ALU_ADD 15 15 2164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d850 : bv 32 := 0x00e78733.
Lemma F_1d850 : fetch_word Ubsan.M.loaded_segments (0x1d850 : word) = Some W_1d850.
Proof. vm_refl. Qed.
Lemma D_1d850 : decode_any W_1d850 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d854 : bv 32 := 0x00075703.
Lemma F_1d854 : fetch_word Ubsan.M.loaded_segments (0x1d854 : word) = Some W_1d854.
Proof. vm_refl. Qed.
Lemma D_1d854 : decode_any W_1d854 = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d858 : bv 32 := 0x00471713.
Lemma F_1d858 : fetch_word Ubsan.M.loaded_segments (0x1d858 : word) = Some W_1d858.
Proof. vm_refl. Qed.
Lemma D_1d858 : decode_any W_1d858 = Some (ShiftImm ALU_SLL 14 14 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d85c : bv 32 := 0x01053803.
Lemma F_1d85c : fetch_word Ubsan.M.loaded_segments (0x1d85c : word) = Some W_1d85c.
Proof. vm_refl. Qed.
Lemma D_1d85c : decode_any W_1d85c = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d860 : bv 32 := 0x02b707b3.
Lemma F_1d860 : fetch_word Ubsan.M.loaded_segments (0x1d860 : word) = Some W_1d860.
Proof. vm_refl. Qed.
Lemma D_1d860 : decode_any W_1d860 = Some (Mul M_MUL 15 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d864 : bv 32 := 0x00f807b3.
Lemma F_1d864 : fetch_word Ubsan.M.loaded_segments (0x1d864 : word) = Some W_1d864.
Proof. vm_refl. Qed.
Lemma D_1d864 : decode_any W_1d864 = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d868 : bv 32 := 0x00d7c883.
Lemma F_1d868 : fetch_word Ubsan.M.loaded_segments (0x1d868 : word) = Some W_1d868.
Proof. vm_refl. Qed.
Lemma D_1d868 : decode_any W_1d868 = Some (Load SZ1 false 17 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d86c : bv 32 := 0x40c702b3.
Lemma F_1d86c : fetch_word Ubsan.M.loaded_segments (0x1d86c : word) = Some W_1d86c.
Proof. vm_refl. Qed.
Lemma D_1d86c : decode_any W_1d86c = Some (Op ALU_SUB 5 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d870 : bv 32 := 0xffc28293.
Lemma F_1d870 : fetch_word Ubsan.M.loaded_segments (0x1d870 : word) = Some W_1d870.
Proof. vm_refl. Qed.
Lemma D_1d870 : decode_any W_1d870 = Some (OpImm ALU_ADD 5 5 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d874 : bv 32 := 0x01078793.
Lemma F_1d874 : fetch_word Ubsan.M.loaded_segments (0x1d874 : word) = Some W_1d874.
Proof. vm_refl. Qed.
Lemma D_1d874 : decode_any W_1d874 = Some (OpImm ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d878 : bv 32 := 0x00088663.
Lemma F_1d878 : fetch_word Ubsan.M.loaded_segments (0x1d878 : word) = Some W_1d878.
Proof. vm_refl. Qed.
Lemma D_1d878 : decode_any W_1d878 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d87c : bv 32 := 0xffe7d683.
Lemma F_1d87c : fetch_word Ubsan.M.loaded_segments (0x1d87c : word) = Some W_1d87c.
Proof. vm_refl. Qed.
Lemma D_1d87c : decode_any W_1d87c = Some (Load SZ2 false 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d880 : bv 32 := 0x00168693.
Lemma F_1d880 : fetch_word Ubsan.M.loaded_segments (0x1d880 : word) = Some W_1d880.
Proof. vm_refl. Qed.
Lemma D_1d880 : decode_any W_1d880 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d884 : bv 32 := 0xffc7c383.
Lemma F_1d884 : fetch_word Ubsan.M.loaded_segments (0x1d884 : word) = Some W_1d884.
Proof. vm_refl. Qed.
Lemma D_1d884 : decode_any W_1d884 = Some (Load SZ1 false 7 15 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d888 : bv 32 := 0x0042d313.
Lemma F_1d888 : fetch_word Ubsan.M.loaded_segments (0x1d888 : word) = Some W_1d888.
Proof. vm_refl. Qed.
Lemma D_1d888 : decode_any W_1d888 = Some (ShiftImm ALU_SRL 6 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d88c : bv 32 := 0x0ff6f893.
Lemma F_1d88c : fetch_word Ubsan.M.loaded_segments (0x1d88c : word) = Some W_1d88c.
Proof. vm_refl. Qed.
Lemma D_1d88c : decode_any W_1d88c = Some (OpImm ALU_AND 17 13 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d890 : bv 32 := 0x00038463.
Lemma F_1d890 : fetch_word Ubsan.M.loaded_segments (0x1d890 : word) = Some W_1d890.
Proof. vm_refl. Qed.
Lemma D_1d890 : decode_any W_1d890 = Some (Branch BC_EQ 7 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d898 : bv 32 := 0x03137e63.
Lemma F_1d898 : fetch_word Ubsan.M.loaded_segments (0x1d898 : word) = Some W_1d898.
Proof. vm_refl. Qed.
Lemma D_1d898 : decode_any W_1d898 = Some (Branch BC_GEU 6 17 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d89c : bv 32 := 0x0052d693.
Lemma F_1d89c : fetch_word Ubsan.M.loaded_segments (0x1d89c : word) = Some W_1d89c.
Proof. vm_refl. Qed.
Lemma D_1d89c : decode_any W_1d89c = Some (ShiftImm ALU_SRL 13 5 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8a0 : bv 32 := 0x00d366b3.
Lemma F_1d8a0 : fetch_word Ubsan.M.loaded_segments (0x1d8a0 : word) = Some W_1d8a0.
Proof. vm_refl. Qed.
Lemma D_1d8a0 : decode_any W_1d8a0 = Some (Op ALU_OR 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8a4 : bv 32 := 0x0026d293.
Lemma F_1d8a4 : fetch_word Ubsan.M.loaded_segments (0x1d8a4 : word) = Some W_1d8a4.
Proof. vm_refl. Qed.
Lemma D_1d8a4 : decode_any W_1d8a4 = Some (ShiftImm ALU_SRL 5 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8a8 : bv 32 := 0x00d2e6b3.
Lemma F_1d8a8 : fetch_word Ubsan.M.loaded_segments (0x1d8a8 : word) = Some W_1d8a8.
Proof. vm_refl. Qed.
Lemma D_1d8a8 : decode_any W_1d8a8 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8ac : bv 32 := 0x0046d293.
Lemma F_1d8ac : fetch_word Ubsan.M.loaded_segments (0x1d8ac : word) = Some W_1d8ac.
Proof. vm_refl. Qed.
Lemma D_1d8ac : decode_any W_1d8ac = Some (ShiftImm ALU_SRL 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8b0 : bv 32 := 0x00d2e6b3.
Lemma F_1d8b0 : fetch_word Ubsan.M.loaded_segments (0x1d8b0 : word) = Some W_1d8b0.
Proof. vm_refl. Qed.
Lemma D_1d8b0 : decode_any W_1d8b0 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8b4 : bv 32 := 0x00d8f6b3.
Lemma F_1d8b4 : fetch_word Ubsan.M.loaded_segments (0x1d8b4 : word) = Some W_1d8b4.
Proof. vm_refl. Qed.
Lemma D_1d8b4 : decode_any W_1d8b4 = Some (Op ALU_AND 13 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8b8 : bv 32 := 0x00d338b3.
Lemma F_1d8b8 : fetch_word Ubsan.M.loaded_segments (0x1d8b8 : word) = Some W_1d8b8.
Proof. vm_refl. Qed.
Lemma D_1d8b8 : decode_any W_1d8b8 = Some (Op ALU_SLTU 17 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8bc : bv 32 := 0xfff34293.
Lemma F_1d8bc : fetch_word Ubsan.M.loaded_segments (0x1d8bc : word) = Some W_1d8bc.
Proof. vm_refl. Qed.
Lemma D_1d8bc : decode_any W_1d8bc = Some (OpImm ALU_XOR 5 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8c0 : bv 32 := 0x411008bb.
Lemma F_1d8c0 : fetch_word Ubsan.M.loaded_segments (0x1d8c0 : word) = Some W_1d8c0.
Proof. vm_refl. Qed.
Lemma D_1d8c0 : decode_any W_1d8c0 = Some (Op32 ALU_SUB 17 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8c4 : bv 32 := 0x0058f8b3.
Lemma F_1d8c4 : fetch_word Ubsan.M.loaded_segments (0x1d8c4 : word) = Some W_1d8c4.
Proof. vm_refl. Qed.
Lemma D_1d8c4 : decode_any W_1d8c4 = Some (Op ALU_AND 17 17 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8c8 : bv 32 := 0x00d888bb.
Lemma F_1d8c8 : fetch_word Ubsan.M.loaded_segments (0x1d8c8 : word) = Some W_1d8c8.
Proof. vm_refl. Qed.
Lemma D_1d8c8 : decode_any W_1d8c8 = Some (Op32 ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8cc : bv 32 := 0x01137463.
Lemma F_1d8cc : fetch_word Ubsan.M.loaded_segments (0x1d8cc : word) = Some W_1d8cc.
Proof. vm_refl. Qed.
Lemma D_1d8cc : decode_any W_1d8cc = Some (Branch BC_GEU 6 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8d4 : bv 32 := 0x00078693.
Lemma F_1d8d4 : fetch_word Ubsan.M.loaded_segments (0x1d8d4 : word) = Some W_1d8d4.
Proof. vm_refl. Qed.
Lemma D_1d8d4 : decode_any W_1d8d4 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8d8 : bv 32 := 0x02088063.
Lemma F_1d8d8 : fetch_word Ubsan.M.loaded_segments (0x1d8d8 : word) = Some W_1d8d8.
Proof. vm_refl. Qed.
Lemma D_1d8d8 : decode_any W_1d8d8 = Some (Branch BC_EQ 17 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8dc : bv 32 := 0xfe000813.
Lemma F_1d8dc : fetch_word Ubsan.M.loaded_segments (0x1d8dc : word) = Some W_1d8dc.
Proof. vm_refl. Qed.
Lemma D_1d8dc : decode_any W_1d8dc = Some (OpImm ALU_ADD 16 0 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8e0 : bv 32 := 0x0048969b.
Lemma F_1d8e0 : fetch_word Ubsan.M.loaded_segments (0x1d8e0 : word) = Some W_1d8e0.
Proof. vm_refl. Qed.
Lemma D_1d8e0 : decode_any W_1d8e0 = Some (ShiftImm32 ALU_SLL 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8e4 : bv 32 := 0x00d786b3.
Lemma F_1d8e4 : fetch_word Ubsan.M.loaded_segments (0x1d8e4 : word) = Some W_1d8e4.
Proof. vm_refl. Qed.
Lemma D_1d8e4 : decode_any W_1d8e4 = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8e8 : bv 32 := 0xff078ea3.
Lemma F_1d8e8 : fetch_word Ubsan.M.loaded_segments (0x1d8e8 : word) = Some W_1d8e8.
Proof. vm_refl. Qed.
Lemma D_1d8e8 : decode_any W_1d8e8 = Some (Store SZ1 15 16 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8ec : bv 32 := 0xff179f23.
Lemma F_1d8ec : fetch_word Ubsan.M.loaded_segments (0x1d8ec : word) = Some W_1d8ec.
Proof. vm_refl. Qed.
Lemma D_1d8ec : decode_any W_1d8ec = Some (Store SZ2 15 17 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8f0 : bv 32 := 0xfe068e23.
Lemma F_1d8f0 : fetch_word Ubsan.M.loaded_segments (0x1d8f0 : word) = Some W_1d8f0.
Proof. vm_refl. Qed.
Lemma D_1d8f0 : decode_any W_1d8f0 = Some (Store SZ1 13 0 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8f4 : bv 32 := 0x01053803.
Lemma F_1d8f4 : fetch_word Ubsan.M.loaded_segments (0x1d8f4 : word) = Some W_1d8f4.
Proof. vm_refl. Qed.
Lemma D_1d8f4 : decode_any W_1d8f4 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8f8 : bv 32 := 0x00e78733.
Lemma F_1d8f8 : fetch_word Ubsan.M.loaded_segments (0x1d8f8 : word) = Some W_1d8f8.
Proof. vm_refl. Qed.
Lemma D_1d8f8 : decode_any W_1d8f8 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d8fc : bv 32 := 0x410687bb.
Lemma F_1d8fc : fetch_word Ubsan.M.loaded_segments (0x1d8fc : word) = Some W_1d8fc.
Proof. vm_refl. Qed.
Lemma D_1d8fc : decode_any W_1d8fc = Some (Op32 ALU_SUB 15 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d900 : bv 32 := 0x00d60633.
Lemma F_1d900 : fetch_word Ubsan.M.loaded_segments (0x1d900 : word) = Some W_1d900.
Proof. vm_refl. Qed.
Lemma D_1d900 : decode_any W_1d900 = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d904 : bv 32 := 0xffc70513.
Lemma F_1d904 : fetch_word Ubsan.M.loaded_segments (0x1d904 : word) = Some W_1d904.
Proof. vm_refl. Qed.
Lemma D_1d904 : decode_any W_1d904 = Some (OpImm ALU_ADD 10 14 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d908 : bv 32 := 0xff078793.
Lemma F_1d908 : fetch_word Ubsan.M.loaded_segments (0x1d908 : word) = Some W_1d908.
Proof. vm_refl. Qed.
Lemma D_1d908 : decode_any W_1d908 = Some (OpImm ALU_ADD 15 15 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d90c : bv 32 := 0x0047d793.
Lemma F_1d90c : fetch_word Ubsan.M.loaded_segments (0x1d90c : word) = Some W_1d90c.
Proof. vm_refl. Qed.
Lemma D_1d90c : decode_any W_1d90c = Some (ShiftImm ALU_SRL 15 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d910 : bv 32 := 0x40c5083b.
Lemma F_1d910 : fetch_word Ubsan.M.loaded_segments (0x1d910 : word) = Some W_1d910.
Proof. vm_refl. Qed.
Lemma D_1d910 : decode_any W_1d910 = Some (Op32 ALU_SUB 16 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d914 : bv 32 := 0xfeb68ea3.
Lemma F_1d914 : fetch_word Ubsan.M.loaded_segments (0x1d914 : word) = Some W_1d914.
Proof. vm_refl. Qed.
Lemma D_1d914 : decode_any W_1d914 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d918 : bv 32 := 0xfef69f23.
Lemma F_1d918 : fetch_word Ubsan.M.loaded_segments (0x1d918 : word) = Some W_1d918.
Proof. vm_refl. Qed.
Lemma D_1d918 : decode_any W_1d918 = Some (Store SZ2 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d91c : bv 32 := 0x02080463.
Lemma F_1d91c : fetch_word Ubsan.M.loaded_segments (0x1d91c : word) = Some W_1d91c.
Proof. vm_refl. Qed.
Lemma D_1d91c : decode_any W_1d91c = Some (Branch BC_EQ 16 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d920 : bv 32 := 0x40c505bb.
Lemma F_1d920 : fetch_word Ubsan.M.loaded_segments (0x1d920 : word) = Some W_1d920.
Proof. vm_refl. Qed.
Lemma D_1d920 : decode_any W_1d920 = Some (Op32 ALU_SUB 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d924 : bv 32 := 0x40b0063b.
Lemma F_1d924 : fetch_word Ubsan.M.loaded_segments (0x1d924 : word) = Some W_1d924.
Proof. vm_refl. Qed.
Lemma D_1d924 : decode_any W_1d924 = Some (Op32 ALU_SUB 12 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d928 : bv 32 := 0x00c50633.
Lemma F_1d928 : fetch_word Ubsan.M.loaded_segments (0x1d928 : word) = Some W_1d928.
Proof. vm_refl. Qed.
Lemma D_1d928 : decode_any W_1d928 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d92c : bv 32 := 0x00500513.
Lemma F_1d92c : fetch_word Ubsan.M.loaded_segments (0x1d92c : word) = Some W_1d92c.
Proof. vm_refl. Qed.
Lemma D_1d92c : decode_any W_1d92c = Some (OpImm ALU_ADD 10 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d930 : bv 32 := 0x00060023.
Lemma F_1d930 : fetch_word Ubsan.M.loaded_segments (0x1d930 : word) = Some W_1d930.
Proof. vm_refl. Qed.
Lemma D_1d930 : decode_any W_1d930 = Some (Store SZ1 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d934 : bv 32 := 0x00a5cc63.
Lemma F_1d934 : fetch_word Ubsan.M.loaded_segments (0x1d934 : word) = Some W_1d934.
Proof. vm_refl. Qed.
Lemma D_1d934 : decode_any W_1d934 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d938 : bv 32 := 0xfe070ba3.
Lemma F_1d938 : fetch_word Ubsan.M.loaded_segments (0x1d938 : word) = Some W_1d938.
Proof. vm_refl. Qed.
Lemma D_1d938 : decode_any W_1d938 = Some (Store SZ1 14 0 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d93c : bv 32 := 0xfeb72c23.
Lemma F_1d93c : fetch_word Ubsan.M.loaded_segments (0x1d93c : word) = Some W_1d93c.
Proof. vm_refl. Qed.
Lemma D_1d93c : decode_any W_1d93c = Some (Store SZ4 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d940 : bv 32 := 0x0100006f.
Lemma F_1d940 : fetch_word Ubsan.M.loaded_segments (0x1d940 : word) = Some W_1d940.
Proof. vm_refl. Qed.
Lemma D_1d940 : decode_any W_1d940 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d944 : bv 32 := 0x00000513.
Lemma F_1d944 : fetch_word Ubsan.M.loaded_segments (0x1d944 : word) = Some W_1d944.
Proof. vm_refl. Qed.
Lemma D_1d944 : decode_any W_1d944 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d948 : bv 32 := 0x0080006f.
Lemma F_1d948 : fetch_word Ubsan.M.loaded_segments (0x1d948 : word) = Some W_1d948.
Proof. vm_refl. Qed.
Lemma D_1d948 : decode_any W_1d948 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d94c : bv 32 := 0x00058513.
Lemma F_1d94c : fetch_word Ubsan.M.loaded_segments (0x1d94c : word) = Some W_1d94c.
Proof. vm_refl. Qed.
Lemma D_1d94c : decode_any W_1d94c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d950 : bv 32 := 0xffd6c583.
Lemma F_1d950 : fetch_word Ubsan.M.loaded_segments (0x1d950 : word) = Some W_1d950.
Proof. vm_refl. Qed.
Lemma D_1d950 : decode_any W_1d950 = Some (Load SZ1 false 11 13 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d954 : bv 32 := 0x01f5f593.
Lemma F_1d954 : fetch_word Ubsan.M.loaded_segments (0x1d954 : word) = Some W_1d954.
Proof. vm_refl. Qed.
Lemma D_1d954 : decode_any W_1d954 = Some (OpImm ALU_AND 11 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d958 : bv 32 := 0x00551513.
Lemma F_1d958 : fetch_word Ubsan.M.loaded_segments (0x1d958 : word) = Some W_1d958.
Proof. vm_refl. Qed.
Lemma D_1d958 : decode_any W_1d958 = Some (ShiftImm ALU_SLL 10 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d95c : bv 32 := 0x00b56533.
Lemma F_1d95c : fetch_word Ubsan.M.loaded_segments (0x1d95c : word) = Some W_1d95c.
Proof. vm_refl. Qed.
Lemma D_1d95c : decode_any W_1d95c = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d960 : bv 32 := 0xfea68ea3.
Lemma F_1d960 : fetch_word Ubsan.M.loaded_segments (0x1d960 : word) = Some W_1d960.
Proof. vm_refl. Qed.
Lemma D_1d960 : decode_any W_1d960 = Some (Store SZ1 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d964 : bv 32 := 0x00068513.
Lemma F_1d964 : fetch_word Ubsan.M.loaded_segments (0x1d964 : word) = Some W_1d964.
Proof. vm_refl. Qed.
Lemma D_1d964 : decode_any W_1d964 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d968 : bv 32 := 0x00008067.
Lemma F_1d968 : fetch_word Ubsan.M.loaded_segments (0x1d968 : word) = Some W_1d968.
Proof. vm_refl. Qed.
Lemma D_1d968 : decode_any W_1d968 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dcf0 : bv 32 := 0x00008067.
Lemma F_1dcf0 : fetch_word Ubsan.M.loaded_segments (0x1dcf0 : word) = Some W_1dcf0.
Proof. vm_refl. Qed.
Lemma D_1dcf0 : decode_any W_1dcf0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e22c : bv 32 := 0xff010113.
Lemma F_1e22c : fetch_word Ubsan.M.loaded_segments (0x1e22c : word) = Some W_1e22c.
Proof. vm_refl. Qed.
Lemma D_1e22c : decode_any W_1e22c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e230 : bv 32 := 0x00113423.
Lemma F_1e230 : fetch_word Ubsan.M.loaded_segments (0x1e230 : word) = Some W_1e230.
Proof. vm_refl. Qed.
Lemma D_1e230 : decode_any W_1e230 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e234 : bv 32 := 0x00813023.
Lemma F_1e234 : fetch_word Ubsan.M.loaded_segments (0x1e234 : word) = Some W_1e234.
Proof. vm_refl. Qed.
Lemma D_1e234 : decode_any W_1e234 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e238 : bv 32 := 0x5d0000ef.
Lemma F_1e238 : fetch_word Ubsan.M.loaded_segments (0x1e238 : word) = Some W_1e238.
Proof. vm_refl. Qed.
Lemma D_1e238 : decode_any W_1e238 = Some (Jal 1 1488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e23c : bv 32 := 0x00053403.
Lemma F_1e23c : fetch_word Ubsan.M.loaded_segments (0x1e23c : word) = Some W_1e23c.
Proof. vm_refl. Qed.
Lemma D_1e23c : decode_any W_1e23c = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e240 : bv 32 := 0x12041663.
Lemma F_1e240 : fetch_word Ubsan.M.loaded_segments (0x1e240 : word) = Some W_1e240.
Proof. vm_refl. Qed.
Lemma D_1e240 : decode_any W_1e240 = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e244 : bv 32 := 0x00008517.
Lemma F_1e244 : fetch_word Ubsan.M.loaded_segments (0x1e244 : word) = Some W_1e244.
Proof. vm_refl. Qed.
Lemma D_1e244 : decode_any W_1e244 = Some (Auipc 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e248 : bv 32 := 0x7a453403.
Lemma F_1e248 : fetch_word Ubsan.M.loaded_segments (0x1e248 : word) = Some W_1e248.
Proof. vm_refl. Qed.
Lemma D_1e248 : decode_any W_1e248 = Some (Load SZ8 true 8 10 1956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e24c : bv 32 := 0x04040a63.
Lemma F_1e24c : fetch_word Ubsan.M.loaded_segments (0x1e24c : word) = Some W_1e24c.
Proof. vm_refl. Qed.
Lemma D_1e24c : decode_any W_1e24c = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e250 : bv 32 := 0x08c42503.
Lemma F_1e250 : fetch_word Ubsan.M.loaded_segments (0x1e250 : word) = Some W_1e250.
Proof. vm_refl. Qed.
Lemma D_1e250 : decode_any W_1e250 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e254 : bv 32 := 0x00054663.
Lemma F_1e254 : fetch_word Ubsan.M.loaded_segments (0x1e254 : word) = Some W_1e254.
Proof. vm_refl. Qed.
Lemma D_1e254 : decode_any W_1e254 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e260 : bv 32 := 0x02843503.
Lemma F_1e260 : fetch_word Ubsan.M.loaded_segments (0x1e260 : word) = Some W_1e260.
Proof. vm_refl. Qed.
Lemma D_1e260 : decode_any W_1e260 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e264 : bv 32 := 0x03843583.
Lemma F_1e264 : fetch_word Ubsan.M.loaded_segments (0x1e264 : word) = Some W_1e264.
Proof. vm_refl. Qed.
Lemma D_1e264 : decode_any W_1e264 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e268 : bv 32 := 0x00b50c63.
Lemma F_1e268 : fetch_word Ubsan.M.loaded_segments (0x1e268 : word) = Some W_1e268.
Proof. vm_refl. Qed.
Lemma D_1e268 : decode_any W_1e268 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e280 : bv 32 := 0x00843503.
Lemma F_1e280 : fetch_word Ubsan.M.loaded_segments (0x1e280 : word) = Some W_1e280.
Proof. vm_refl. Qed.
Lemma D_1e280 : decode_any W_1e280 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e284 : bv 32 := 0x01043583.
Lemma F_1e284 : fetch_word Ubsan.M.loaded_segments (0x1e284 : word) = Some W_1e284.
Proof. vm_refl. Qed.
Lemma D_1e284 : decode_any W_1e284 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e288 : bv 32 := 0x00b50c63.
Lemma F_1e288 : fetch_word Ubsan.M.loaded_segments (0x1e288 : word) = Some W_1e288.
Proof. vm_refl. Qed.
Lemma D_1e288 : decode_any W_1e288 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e2a0 : bv 32 := 0x00009517.
Lemma F_1e2a0 : fetch_word Ubsan.M.loaded_segments (0x1e2a0 : word) = Some W_1e2a0.
Proof. vm_refl. Qed.
Lemma D_1e2a0 : decode_any W_1e2a0 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e2a4 : bv 32 := 0x83853403.
Lemma F_1e2a4 : fetch_word Ubsan.M.loaded_segments (0x1e2a4 : word) = Some W_1e2a4.
Proof. vm_refl. Qed.
Lemma D_1e2a4 : decode_any W_1e2a4 = Some (Load SZ8 true 8 10 2104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e2a8 : bv 32 := 0x04040a63.
Lemma F_1e2a8 : fetch_word Ubsan.M.loaded_segments (0x1e2a8 : word) = Some W_1e2a8.
Proof. vm_refl. Qed.
Lemma D_1e2a8 : decode_any W_1e2a8 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e2ac : bv 32 := 0x08c42503.
Lemma F_1e2ac : fetch_word Ubsan.M.loaded_segments (0x1e2ac : word) = Some W_1e2ac.
Proof. vm_refl. Qed.
Lemma D_1e2ac : decode_any W_1e2ac = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e2b0 : bv 32 := 0x00054663.
Lemma F_1e2b0 : fetch_word Ubsan.M.loaded_segments (0x1e2b0 : word) = Some W_1e2b0.
Proof. vm_refl. Qed.
Lemma D_1e2b0 : decode_any W_1e2b0 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e2bc : bv 32 := 0x02843503.
Lemma F_1e2bc : fetch_word Ubsan.M.loaded_segments (0x1e2bc : word) = Some W_1e2bc.
Proof. vm_refl. Qed.
Lemma D_1e2bc : decode_any W_1e2bc = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e2c0 : bv 32 := 0x03843583.
Lemma F_1e2c0 : fetch_word Ubsan.M.loaded_segments (0x1e2c0 : word) = Some W_1e2c0.
Proof. vm_refl. Qed.
Lemma D_1e2c0 : decode_any W_1e2c0 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e2c4 : bv 32 := 0x00b50c63.
Lemma F_1e2c4 : fetch_word Ubsan.M.loaded_segments (0x1e2c4 : word) = Some W_1e2c4.
Proof. vm_refl. Qed.
Lemma D_1e2c4 : decode_any W_1e2c4 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e2c8 : bv 32 := 0x04843683.
Lemma F_1e2c8 : fetch_word Ubsan.M.loaded_segments (0x1e2c8 : word) = Some W_1e2c8.
Proof. vm_refl. Qed.
Lemma D_1e2c8 : decode_any W_1e2c8 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e2cc : bv 32 := 0x00040513.
Lemma F_1e2cc : fetch_word Ubsan.M.loaded_segments (0x1e2cc : word) = Some W_1e2cc.
Proof. vm_refl. Qed.
Lemma D_1e2cc : decode_any W_1e2cc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e2d0 : bv 32 := 0x00000593.
Lemma F_1e2d0 : fetch_word Ubsan.M.loaded_segments (0x1e2d0 : word) = Some W_1e2d0.
Proof. vm_refl. Qed.
Lemma D_1e2d0 : decode_any W_1e2d0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e2d4 : bv 32 := 0x00000613.
Lemma F_1e2d4 : fetch_word Ubsan.M.loaded_segments (0x1e2d4 : word) = Some W_1e2d4.
Proof. vm_refl. Qed.
Lemma D_1e2d4 : decode_any W_1e2d4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e2d8 : bv 32 := 0x000680e7.
Lemma F_1e2d8 : fetch_word Ubsan.M.loaded_segments (0x1e2d8 : word) = Some W_1e2d8.
Proof. vm_refl. Qed.
Lemma D_1e2d8 : decode_any W_1e2d8 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e2dc : bv 32 := 0x00843503.
Lemma F_1e2dc : fetch_word Ubsan.M.loaded_segments (0x1e2dc : word) = Some W_1e2dc.
Proof. vm_refl. Qed.
Lemma D_1e2dc : decode_any W_1e2dc = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e2e0 : bv 32 := 0x01043583.
Lemma F_1e2e0 : fetch_word Ubsan.M.loaded_segments (0x1e2e0 : word) = Some W_1e2e0.
Proof. vm_refl. Qed.
Lemma D_1e2e0 : decode_any W_1e2e0 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e2e4 : bv 32 := 0x00b50c63.
Lemma F_1e2e4 : fetch_word Ubsan.M.loaded_segments (0x1e2e4 : word) = Some W_1e2e4.
Proof. vm_refl. Qed.
Lemma D_1e2e4 : decode_any W_1e2e4 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e2fc : bv 32 := 0x00008517.
Lemma F_1e2fc : fetch_word Ubsan.M.loaded_segments (0x1e2fc : word) = Some W_1e2fc.
Proof. vm_refl. Qed.
Lemma D_1e2fc : decode_any W_1e2fc = Some (Auipc 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e300 : bv 32 := 0x5fc53403.
Lemma F_1e300 : fetch_word Ubsan.M.loaded_segments (0x1e300 : word) = Some W_1e300.
Proof. vm_refl. Qed.
Lemma D_1e300 : decode_any W_1e300 = Some (Load SZ8 true 8 10 1532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e304 : bv 32 := 0x0a040e63.
Lemma F_1e304 : fetch_word Ubsan.M.loaded_segments (0x1e304 : word) = Some W_1e304.
Proof. vm_refl. Qed.
Lemma D_1e304 : decode_any W_1e304 = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e308 : bv 32 := 0x08c42503.
Lemma F_1e308 : fetch_word Ubsan.M.loaded_segments (0x1e308 : word) = Some W_1e308.
Proof. vm_refl. Qed.
Lemma D_1e308 : decode_any W_1e308 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e30c : bv 32 := 0x00054663.
Lemma F_1e30c : fetch_word Ubsan.M.loaded_segments (0x1e30c : word) = Some W_1e30c.
Proof. vm_refl. Qed.
Lemma D_1e30c : decode_any W_1e30c = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e318 : bv 32 := 0x02843503.
Lemma F_1e318 : fetch_word Ubsan.M.loaded_segments (0x1e318 : word) = Some W_1e318.
Proof. vm_refl. Qed.
Lemma D_1e318 : decode_any W_1e318 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e31c : bv 32 := 0x03843583.
Lemma F_1e31c : fetch_word Ubsan.M.loaded_segments (0x1e31c : word) = Some W_1e31c.
Proof. vm_refl. Qed.
Lemma D_1e31c : decode_any W_1e31c = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e320 : bv 32 := 0x00b50c63.
Lemma F_1e320 : fetch_word Ubsan.M.loaded_segments (0x1e320 : word) = Some W_1e320.
Proof. vm_refl. Qed.
Lemma D_1e320 : decode_any W_1e320 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e338 : bv 32 := 0x00843503.
Lemma F_1e338 : fetch_word Ubsan.M.loaded_segments (0x1e338 : word) = Some W_1e338.
Proof. vm_refl. Qed.
Lemma D_1e338 : decode_any W_1e338 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e33c : bv 32 := 0x01043583.
Lemma F_1e33c : fetch_word Ubsan.M.loaded_segments (0x1e33c : word) = Some W_1e33c.
Proof. vm_refl. Qed.
Lemma D_1e33c : decode_any W_1e33c = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e340 : bv 32 := 0x08b50063.
Lemma F_1e340 : fetch_word Ubsan.M.loaded_segments (0x1e340 : word) = Some W_1e340.
Proof. vm_refl. Qed.
Lemma D_1e340 : decode_any W_1e340 = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e3c0 : bv 32 := 0x00813083.
Lemma F_1e3c0 : fetch_word Ubsan.M.loaded_segments (0x1e3c0 : word) = Some W_1e3c0.
Proof. vm_refl. Qed.
Lemma D_1e3c0 : decode_any W_1e3c0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e3c4 : bv 32 := 0x00013403.
Lemma F_1e3c4 : fetch_word Ubsan.M.loaded_segments (0x1e3c4 : word) = Some W_1e3c4.
Proof. vm_refl. Qed.
Lemma D_1e3c4 : decode_any W_1e3c4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e3c8 : bv 32 := 0x01010113.
Lemma F_1e3c8 : fetch_word Ubsan.M.loaded_segments (0x1e3c8 : word) = Some W_1e3c8.
Proof. vm_refl. Qed.
Lemma D_1e3c8 : decode_any W_1e3c8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e3cc : bv 32 := 0x00008067.
Lemma F_1e3cc : fetch_word Ubsan.M.loaded_segments (0x1e3cc : word) = Some W_1e3cc.
Proof. vm_refl. Qed.
Lemma D_1e3cc : decode_any W_1e3cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e3d0 : bv 32 := 0xf9010113.
Lemma F_1e3d0 : fetch_word Ubsan.M.loaded_segments (0x1e3d0 : word) = Some W_1e3d0.
Proof. vm_refl. Qed.
Lemma D_1e3d0 : decode_any W_1e3d0 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e3d4 : bv 32 := 0x06113423.
Lemma F_1e3d4 : fetch_word Ubsan.M.loaded_segments (0x1e3d4 : word) = Some W_1e3d4.
Proof. vm_refl. Qed.
Lemma D_1e3d4 : decode_any W_1e3d4 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e3d8 : bv 32 := 0x06813023.
Lemma F_1e3d8 : fetch_word Ubsan.M.loaded_segments (0x1e3d8 : word) = Some W_1e3d8.
Proof. vm_refl. Qed.
Lemma D_1e3d8 : decode_any W_1e3d8 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e3dc : bv 32 := 0x04913c23.
Lemma F_1e3dc : fetch_word Ubsan.M.loaded_segments (0x1e3dc : word) = Some W_1e3dc.
Proof. vm_refl. Qed.
Lemma D_1e3dc : decode_any W_1e3dc = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e3e0 : bv 32 := 0x05213823.
Lemma F_1e3e0 : fetch_word Ubsan.M.loaded_segments (0x1e3e0 : word) = Some W_1e3e0.
Proof. vm_refl. Qed.
Lemma D_1e3e0 : decode_any W_1e3e0 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e3e4 : bv 32 := 0x05313423.
Lemma F_1e3e4 : fetch_word Ubsan.M.loaded_segments (0x1e3e4 : word) = Some W_1e3e4.
Proof. vm_refl. Qed.
Lemma D_1e3e4 : decode_any W_1e3e4 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e3e8 : bv 32 := 0x05413023.
Lemma F_1e3e8 : fetch_word Ubsan.M.loaded_segments (0x1e3e8 : word) = Some W_1e3e8.
Proof. vm_refl. Qed.
Lemma D_1e3e8 : decode_any W_1e3e8 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e3ec : bv 32 := 0x03513c23.
Lemma F_1e3ec : fetch_word Ubsan.M.loaded_segments (0x1e3ec : word) = Some W_1e3ec.
Proof. vm_refl. Qed.
Lemma D_1e3ec : decode_any W_1e3ec = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e3f0 : bv 32 := 0x03613823.
Lemma F_1e3f0 : fetch_word Ubsan.M.loaded_segments (0x1e3f0 : word) = Some W_1e3f0.
Proof. vm_refl. Qed.
Lemma D_1e3f0 : decode_any W_1e3f0 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e3f4 : bv 32 := 0x00060413.
Lemma F_1e3f4 : fetch_word Ubsan.M.loaded_segments (0x1e3f4 : word) = Some W_1e3f4.
Proof. vm_refl. Qed.
Lemma D_1e3f4 : decode_any W_1e3f4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e3f8 : bv 32 := 0x00050493.
Lemma F_1e3f8 : fetch_word Ubsan.M.loaded_segments (0x1e3f8 : word) = Some W_1e3f8.
Proof. vm_refl. Qed.
Lemma D_1e3f8 : decode_any W_1e3f8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e3fc : bv 32 := 0x00007517.
Lemma F_1e3fc : fetch_word Ubsan.M.loaded_segments (0x1e3fc : word) = Some W_1e3fc.
Proof. vm_refl. Qed.
Lemma D_1e3fc : decode_any W_1e3fc = Some (Auipc 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e400 : bv 32 := 0x3a453a83.
Lemma F_1e400 : fetch_word Ubsan.M.loaded_segments (0x1e400 : word) = Some W_1e400.
Proof. vm_refl. Qed.
Lemma D_1e400 : decode_any W_1e400 = Some (Load SZ8 true 21 10 932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e404 : bv 32 := 0x000ab503.
Lemma F_1e404 : fetch_word Ubsan.M.loaded_segments (0x1e404 : word) = Some W_1e404.
Proof. vm_refl. Qed.
Lemma D_1e404 : decode_any W_1e404 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e408 : bv 32 := 0x02a13423.
Lemma F_1e408 : fetch_word Ubsan.M.loaded_segments (0x1e408 : word) = Some W_1e408.
Proof. vm_refl. Qed.
Lemma D_1e408 : decode_any W_1e408 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e40c : bv 32 := 0x0284b503.
Lemma F_1e40c : fetch_word Ubsan.M.loaded_segments (0x1e40c : word) = Some W_1e40c.
Proof. vm_refl. Qed.
Lemma D_1e40c : decode_any W_1e40c = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e410 : bv 32 := 0x0384b603.
Lemma F_1e410 : fetch_word Ubsan.M.loaded_segments (0x1e410 : word) = Some W_1e410.
Proof. vm_refl. Qed.
Lemma D_1e410 : decode_any W_1e410 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e414 : bv 32 := 0x40c50b33.
Lemma F_1e414 : fetch_word Ubsan.M.loaded_segments (0x1e414 : word) = Some W_1e414.
Proof. vm_refl. Qed.
Lemma D_1e414 : decode_any W_1e414 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e418 : bv 32 := 0x00c546b3.
Lemma F_1e418 : fetch_word Ubsan.M.loaded_segments (0x1e418 : word) = Some W_1e418.
Proof. vm_refl. Qed.
Lemma D_1e418 : decode_any W_1e418 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e41c : bv 32 := 0x00c13423.
Lemma F_1e41c : fetch_word Ubsan.M.loaded_segments (0x1e41c : word) = Some W_1e41c.
Proof. vm_refl. Qed.
Lemma D_1e41c : decode_any W_1e41c = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e420 : bv 32 := 0x01613823.
Lemma F_1e420 : fetch_word Ubsan.M.loaded_segments (0x1e420 : word) = Some W_1e420.
Proof. vm_refl. Qed.
Lemma D_1e420 : decode_any W_1e420 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e424 : bv 32 := 0x00b13c23.
Lemma F_1e424 : fetch_word Ubsan.M.loaded_segments (0x1e424 : word) = Some W_1e424.
Proof. vm_refl. Qed.
Lemma D_1e424 : decode_any W_1e424 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e428 : bv 32 := 0x02813023.
Lemma F_1e428 : fetch_word Ubsan.M.loaded_segments (0x1e428 : word) = Some W_1e428.
Proof. vm_refl. Qed.
Lemma D_1e428 : decode_any W_1e428 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e42c : bv 32 := 0x008b0b33.
Lemma F_1e42c : fetch_word Ubsan.M.loaded_segments (0x1e42c : word) = Some W_1e42c.
Proof. vm_refl. Qed.
Lemma D_1e42c : decode_any W_1e42c = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e430 : bv 32 := 0x00d03933.
Lemma F_1e430 : fetch_word Ubsan.M.loaded_segments (0x1e430 : word) = Some W_1e430.
Proof. vm_refl. Qed.
Lemma D_1e430 : decode_any W_1e430 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e434 : bv 32 := 0x00c50663.
Lemma F_1e434 : fetch_word Ubsan.M.loaded_segments (0x1e434 : word) = Some W_1e434.
Proof. vm_refl. Qed.
Lemma D_1e434 : decode_any W_1e434 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e438 : bv 32 := 0x00810993.
Lemma F_1e438 : fetch_word Ubsan.M.loaded_segments (0x1e438 : word) = Some W_1e438.
Proof. vm_refl. Qed.
Lemma D_1e438 : decode_any W_1e438 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e43c : bv 32 := 0x0080006f.
Lemma F_1e43c : fetch_word Ubsan.M.loaded_segments (0x1e43c : word) = Some W_1e43c.
Proof. vm_refl. Qed.
Lemma D_1e43c : decode_any W_1e43c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e440 : bv 32 := 0x01810993.
Lemma F_1e440 : fetch_word Ubsan.M.loaded_segments (0x1e440 : word) = Some W_1e440.
Proof. vm_refl. Qed.
Lemma D_1e440 : decode_any W_1e440 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e444 : bv 32 := 0x0784a503.
Lemma F_1e444 : fetch_word Ubsan.M.loaded_segments (0x1e444 : word) = Some W_1e444.
Proof. vm_refl. Qed.
Lemma D_1e444 : decode_any W_1e444 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e448 : bv 32 := 0x00190913.
Lemma F_1e448 : fetch_word Ubsan.M.loaded_segments (0x1e448 : word) = Some W_1e448.
Proof. vm_refl. Qed.
Lemma D_1e448 : decode_any W_1e448 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e44c : bv 32 := 0x04200893.
Lemma F_1e44c : fetch_word Ubsan.M.loaded_segments (0x1e44c : word) = Some W_1e44c.
Proof. vm_refl. Qed.
Lemma D_1e44c : decode_any W_1e44c = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e450 : bv 32 := 0x00098593.
Lemma F_1e450 : fetch_word Ubsan.M.loaded_segments (0x1e450 : word) = Some W_1e450.
Proof. vm_refl. Qed.
Lemma D_1e450 : decode_any W_1e450 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e454 : bv 32 := 0x00090613.
Lemma F_1e454 : fetch_word Ubsan.M.loaded_segments (0x1e454 : word) = Some W_1e454.
Proof. vm_refl. Qed.
Lemma D_1e454 : decode_any W_1e454 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e458 : bv 32 := 0x00000073.
Lemma F_1e458 : fetch_word Ubsan.M.loaded_segments (0x1e458 : word) = Some W_1e458.
Proof. vm_refl. Qed.
Lemma D_1e458 : decode_any W_1e458 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1e458 : is_ecall W_1e458 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_1e45c : bv 32 := 0xc9dfd0ef.
Lemma F_1e45c : fetch_word Ubsan.M.loaded_segments (0x1e45c : word) = Some W_1e45c.
Proof. vm_refl. Qed.
Lemma D_1e45c : decode_any W_1e45c = Some (Jal 1 2088092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e460 : bv 32 := 0x09651863.
Lemma F_1e460 : fetch_word Ubsan.M.loaded_segments (0x1e460 : word) = Some W_1e460.
Proof. vm_refl. Qed.
Lemma D_1e460 : decode_any W_1e460 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e464 : bv 32 := 0x0584b503.
Lemma F_1e464 : fetch_word Ubsan.M.loaded_segments (0x1e464 : word) = Some W_1e464.
Proof. vm_refl. Qed.
Lemma D_1e464 : decode_any W_1e464 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e468 : bv 32 := 0x0604b583.
Lemma F_1e468 : fetch_word Ubsan.M.loaded_segments (0x1e468 : word) = Some W_1e468.
Proof. vm_refl. Qed.
Lemma D_1e468 : decode_any W_1e468 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e46c : bv 32 := 0x00b505b3.
Lemma F_1e46c : fetch_word Ubsan.M.loaded_segments (0x1e46c : word) = Some W_1e46c.
Proof. vm_refl. Qed.
Lemma D_1e46c : decode_any W_1e46c = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e470 : bv 32 := 0x02b4b023.
Lemma F_1e470 : fetch_word Ubsan.M.loaded_segments (0x1e470 : word) = Some W_1e470.
Proof. vm_refl. Qed.
Lemma D_1e470 : decode_any W_1e470 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e474 : bv 32 := 0x02a4b423.
Lemma F_1e474 : fetch_word Ubsan.M.loaded_segments (0x1e474 : word) = Some W_1e474.
Proof. vm_refl. Qed.
Lemma D_1e474 : decode_any W_1e474 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e478 : bv 32 := 0x02a4bc23.
Lemma F_1e478 : fetch_word Ubsan.M.loaded_segments (0x1e478 : word) = Some W_1e478.
Proof. vm_refl. Qed.
Lemma D_1e478 : decode_any W_1e478 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e47c : bv 32 := 0x00040513.
Lemma F_1e47c : fetch_word Ubsan.M.loaded_segments (0x1e47c : word) = Some W_1e47c.
Proof. vm_refl. Qed.
Lemma D_1e47c : decode_any W_1e47c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e480 : bv 32 := 0x000ab583.
Lemma F_1e480 : fetch_word Ubsan.M.loaded_segments (0x1e480 : word) = Some W_1e480.
Proof. vm_refl. Qed.
Lemma D_1e480 : decode_any W_1e480 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e484 : bv 32 := 0x02813603.
Lemma F_1e484 : fetch_word Ubsan.M.loaded_segments (0x1e484 : word) = Some W_1e484.
Proof. vm_refl. Qed.
Lemma D_1e484 : decode_any W_1e484 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e488 : bv 32 := 0x0cc59a63.
Lemma F_1e488 : fetch_word Ubsan.M.loaded_segments (0x1e488 : word) = Some W_1e488.
Proof. vm_refl. Qed.
Lemma D_1e488 : decode_any W_1e488 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e48c : bv 32 := 0x06813083.
Lemma F_1e48c : fetch_word Ubsan.M.loaded_segments (0x1e48c : word) = Some W_1e48c.
Proof. vm_refl. Qed.
Lemma D_1e48c : decode_any W_1e48c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e490 : bv 32 := 0x06013403.
Lemma F_1e490 : fetch_word Ubsan.M.loaded_segments (0x1e490 : word) = Some W_1e490.
Proof. vm_refl. Qed.
Lemma D_1e490 : decode_any W_1e490 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e494 : bv 32 := 0x05813483.
Lemma F_1e494 : fetch_word Ubsan.M.loaded_segments (0x1e494 : word) = Some W_1e494.
Proof. vm_refl. Qed.
Lemma D_1e494 : decode_any W_1e494 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e498 : bv 32 := 0x05013903.
Lemma F_1e498 : fetch_word Ubsan.M.loaded_segments (0x1e498 : word) = Some W_1e498.
Proof. vm_refl. Qed.
Lemma D_1e498 : decode_any W_1e498 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e49c : bv 32 := 0x04813983.
Lemma F_1e49c : fetch_word Ubsan.M.loaded_segments (0x1e49c : word) = Some W_1e49c.
Proof. vm_refl. Qed.
Lemma D_1e49c : decode_any W_1e49c = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4a0 : bv 32 := 0x04013a03.
Lemma F_1e4a0 : fetch_word Ubsan.M.loaded_segments (0x1e4a0 : word) = Some W_1e4a0.
Proof. vm_refl. Qed.
Lemma D_1e4a0 : decode_any W_1e4a0 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4a4 : bv 32 := 0x03813a83.
Lemma F_1e4a4 : fetch_word Ubsan.M.loaded_segments (0x1e4a4 : word) = Some W_1e4a4.
Proof. vm_refl. Qed.
Lemma D_1e4a4 : decode_any W_1e4a4 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4a8 : bv 32 := 0x03013b03.
Lemma F_1e4a8 : fetch_word Ubsan.M.loaded_segments (0x1e4a8 : word) = Some W_1e4a8.
Proof. vm_refl. Qed.
Lemma D_1e4a8 : decode_any W_1e4a8 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4ac : bv 32 := 0x07010113.
Lemma F_1e4ac : fetch_word Ubsan.M.loaded_segments (0x1e4ac : word) = Some W_1e4ac.
Proof. vm_refl. Qed.
Lemma D_1e4ac : decode_any W_1e4ac = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4b0 : bv 32 := 0x00008067.
Lemma F_1e4b0 : fetch_word Ubsan.M.loaded_segments (0x1e4b0 : word) = Some W_1e4b0.
Proof. vm_refl. Qed.
Lemma D_1e4b0 : decode_any W_1e4b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4b4 : bv 32 := 0x00800713.
Lemma F_1e4b4 : fetch_word Ubsan.M.loaded_segments (0x1e4b4 : word) = Some W_1e4b4.
Proof. vm_refl. Qed.
Lemma D_1e4b4 : decode_any W_1e4b4 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4b8 : bv 32 := 0x000a0593.
Lemma F_1e4b8 : fetch_word Ubsan.M.loaded_segments (0x1e4b8 : word) = Some W_1e4b8.
Proof. vm_refl. Qed.
Lemma D_1e4b8 : decode_any W_1e4b8 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4bc : bv 32 := 0x00e98733.
Lemma F_1e4bc : fetch_word Ubsan.M.loaded_segments (0x1e4bc : word) = Some W_1e4bc.
Proof. vm_refl. Qed.
Lemma D_1e4bc : decode_any W_1e4bc = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4c0 : bv 32 := 0x00073783.
Lemma F_1e4c0 : fetch_word Ubsan.M.loaded_segments (0x1e4c0 : word) = Some W_1e4c0.
Proof. vm_refl. Qed.
Lemma D_1e4c0 : decode_any W_1e4c0 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4c4 : bv 32 := 0x40ab0b33.
Lemma F_1e4c4 : fetch_word Ubsan.M.loaded_segments (0x1e4c4 : word) = Some W_1e4c4.
Proof. vm_refl. Qed.
Lemma D_1e4c4 : decode_any W_1e4c4 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4c8 : bv 32 := 0x0784a503.
Lemma F_1e4c8 : fetch_word Ubsan.M.loaded_segments (0x1e4c8 : word) = Some W_1e4c8.
Proof. vm_refl. Qed.
Lemma D_1e4c8 : decode_any W_1e4c8 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4cc : bv 32 := 0x40c9093b.
Lemma F_1e4cc : fetch_word Ubsan.M.loaded_segments (0x1e4cc : word) = Some W_1e4cc.
Proof. vm_refl. Qed.
Lemma D_1e4cc : decode_any W_1e4cc = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4d0 : bv 32 := 0x40d787b3.
Lemma F_1e4d0 : fetch_word Ubsan.M.loaded_segments (0x1e4d0 : word) = Some W_1e4d0.
Proof. vm_refl. Qed.
Lemma D_1e4d0 : decode_any W_1e4d0 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4d4 : bv 32 := 0x00f73023.
Lemma F_1e4d4 : fetch_word Ubsan.M.loaded_segments (0x1e4d4 : word) = Some W_1e4d4.
Proof. vm_refl. Qed.
Lemma D_1e4d4 : decode_any W_1e4d4 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4d8 : bv 32 := 0x04200893.
Lemma F_1e4d8 : fetch_word Ubsan.M.loaded_segments (0x1e4d8 : word) = Some W_1e4d8.
Proof. vm_refl. Qed.
Lemma D_1e4d8 : decode_any W_1e4d8 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4dc : bv 32 := 0x00090613.
Lemma F_1e4dc : fetch_word Ubsan.M.loaded_segments (0x1e4dc : word) = Some W_1e4dc.
Proof. vm_refl. Qed.
Lemma D_1e4dc : decode_any W_1e4dc = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4e0 : bv 32 := 0x00000073.
Lemma F_1e4e0 : fetch_word Ubsan.M.loaded_segments (0x1e4e0 : word) = Some W_1e4e0.
Proof. vm_refl. Qed.
Lemma D_1e4e0 : decode_any W_1e4e0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1e4e0 : is_ecall W_1e4e0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_1e4e4 : bv 32 := 0xc15fd0ef.
Lemma F_1e4e4 : fetch_word Ubsan.M.loaded_segments (0x1e4e4 : word) = Some W_1e4e4.
Proof. vm_refl. Qed.
Lemma D_1e4e4 : decode_any W_1e4e4 = Some (Jal 1 2087956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4e8 : bv 32 := 0x000a0993.
Lemma F_1e4e8 : fetch_word Ubsan.M.loaded_segments (0x1e4e8 : word) = Some W_1e4e8.
Proof. vm_refl. Qed.
Lemma D_1e4e8 : decode_any W_1e4e8 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4ec : bv 32 := 0xf7650ce3.
Lemma F_1e4ec : fetch_word Ubsan.M.loaded_segments (0x1e4ec : word) = Some W_1e4ec.
Proof. vm_refl. Qed.
Lemma D_1e4ec : decode_any W_1e4ec = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4f0 : bv 32 := 0x02054c63.
Lemma F_1e4f0 : fetch_word Ubsan.M.loaded_segments (0x1e4f0 : word) = Some W_1e4f0.
Proof. vm_refl. Qed.
Lemma D_1e4f0 : decode_any W_1e4f0 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4f4 : bv 32 := 0x0089b583.
Lemma F_1e4f4 : fetch_word Ubsan.M.loaded_segments (0x1e4f4 : word) = Some W_1e4f4.
Proof. vm_refl. Qed.
Lemma D_1e4f4 : decode_any W_1e4f4 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4f8 : bv 32 := 0x00a5b633.
Lemma F_1e4f8 : fetch_word Ubsan.M.loaded_segments (0x1e4f8 : word) = Some W_1e4f8.
Proof. vm_refl. Qed.
Lemma D_1e4f8 : decode_any W_1e4f8 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e4fc : bv 32 := 0x00461a13.
Lemma F_1e4fc : fetch_word Ubsan.M.loaded_segments (0x1e4fc : word) = Some W_1e4fc.
Proof. vm_refl. Qed.
Lemma D_1e4fc : decode_any W_1e4fc = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e500 : bv 32 := 0x01498a33.
Lemma F_1e500 : fetch_word Ubsan.M.loaded_segments (0x1e500 : word) = Some W_1e500.
Proof. vm_refl. Qed.
Lemma D_1e500 : decode_any W_1e500 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e504 : bv 32 := 0x000a3703.
Lemma F_1e504 : fetch_word Ubsan.M.loaded_segments (0x1e504 : word) = Some W_1e504.
Proof. vm_refl. Qed.
Lemma D_1e504 : decode_any W_1e504 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e508 : bv 32 := 0x40c006b3.
Lemma F_1e508 : fetch_word Ubsan.M.loaded_segments (0x1e508 : word) = Some W_1e508.
Proof. vm_refl. Qed.
Lemma D_1e508 : decode_any W_1e508 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e50c : bv 32 := 0x00b6f6b3.
Lemma F_1e50c : fetch_word Ubsan.M.loaded_segments (0x1e50c : word) = Some W_1e50c.
Proof. vm_refl. Qed.
Lemma D_1e50c : decode_any W_1e50c = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e510 : bv 32 := 0x40d506b3.
Lemma F_1e510 : fetch_word Ubsan.M.loaded_segments (0x1e510 : word) = Some W_1e510.
Proof. vm_refl. Qed.
Lemma D_1e510 : decode_any W_1e510 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e514 : bv 32 := 0x00d70733.
Lemma F_1e514 : fetch_word Ubsan.M.loaded_segments (0x1e514 : word) = Some W_1e514.
Proof. vm_refl. Qed.
Lemma D_1e514 : decode_any W_1e514 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e518 : bv 32 := 0x00ea3023.
Lemma F_1e518 : fetch_word Ubsan.M.loaded_segments (0x1e518 : word) = Some W_1e518.
Proof. vm_refl. Qed.
Lemma D_1e518 : decode_any W_1e518 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e51c : bv 32 := 0xf8a5fce3.
Lemma F_1e51c : fetch_word Ubsan.M.loaded_segments (0x1e51c : word) = Some W_1e51c.
Proof. vm_refl. Qed.
Lemma D_1e51c : decode_any W_1e51c = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e520 : bv 32 := 0x01800713.
Lemma F_1e520 : fetch_word Ubsan.M.loaded_segments (0x1e520 : word) = Some W_1e520.
Proof. vm_refl. Qed.
Lemma D_1e520 : decode_any W_1e520 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e524 : bv 32 := 0xf95ff06f.
Lemma F_1e524 : fetch_word Ubsan.M.loaded_segments (0x1e524 : word) = Some W_1e524.
Proof. vm_refl. Qed.
Lemma D_1e524 : decode_any W_1e524 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.
