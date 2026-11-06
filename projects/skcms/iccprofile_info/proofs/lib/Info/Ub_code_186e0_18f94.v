(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
Unset Nia Cache.
Unset Lia Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_186e0 : bv 32 := 0x00062703.
Lemma F_186e0 : fetch_word Ubsan.M.loaded_segments (0x186e0 : word) = Some W_186e0.
Proof. vm_refl. Qed.
Lemma D_186e0 : decode_any W_186e0 = Some (Load SZ4 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_186e4 : bv 32 := 0x00d777b3.
Lemma F_186e4 : fetch_word Ubsan.M.loaded_segments (0x186e4 : word) = Some W_186e4.
Proof. vm_refl. Qed.
Lemma D_186e4 : decode_any W_186e4 = Some (Op ALU_AND 15 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_186e8 : bv 32 := 0x1606282f.
Lemma F_186e8 : fetch_word Ubsan.M.loaded_segments (0x186e8 : word) = Some W_186e8.
Proof. vm_refl. Qed.
Lemma D_186e8 : decode_any W_186e8 = Some (Lr AW true true 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_186ec : bv 32 := 0x00e81663.
Lemma F_186ec : fetch_word Ubsan.M.loaded_segments (0x186ec : word) = Some W_186ec.
Proof. vm_refl. Qed.
Lemma D_186ec : decode_any W_186ec = Some (Branch BC_NE 16 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_186f0 : bv 32 := 0x1ef628af.
Lemma F_186f0 : fetch_word Ubsan.M.loaded_segments (0x186f0 : word) = Some W_186f0.
Proof. vm_refl. Qed.
Lemma D_186f0 : decode_any W_186f0 = Some (Sc AW true true 17 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_186f4 : bv 32 := 0xfe089ae3.
Lemma F_186f4 : fetch_word Ubsan.M.loaded_segments (0x186f4 : word) = Some W_186f4.
Proof. vm_refl. Qed.
Lemma D_186f4 : decode_any W_186f4 = Some (Branch BC_NE 17 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_186f8 : bv 32 := 0x0008081b.
Lemma F_186f8 : fetch_word Ubsan.M.loaded_segments (0x186f8 : word) = Some W_186f8.
Proof. vm_refl. Qed.
Lemma D_186f8 : decode_any W_186f8 = Some (OpImm32 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_186fc : bv 32 := 0xfee812e3.
Lemma F_186fc : fetch_word Ubsan.M.loaded_segments (0x186fc : word) = Some W_186fc.
Proof. vm_refl. Qed.
Lemma D_186fc : decode_any W_186fc = Some (Branch BC_NE 16 14 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e44 : bv 32 := 0x02053703.
Lemma F_18e44 : fetch_word Ubsan.M.loaded_segments (0x18e44 : word) = Some W_18e44.
Proof. vm_refl. Qed.
Lemma D_18e44 : decode_any W_18e44 = Some (Load SZ8 true 14 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e48 : bv 32 := 0x00c75793.
Lemma F_18e48 : fetch_word Ubsan.M.loaded_segments (0x18e48 : word) = Some W_18e48.
Proof. vm_refl. Qed.
Lemma D_18e48 : decode_any W_18e48 = Some (ShiftImm ALU_SRL 15 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e4c : bv 32 := 0x00078e63.
Lemma F_18e4c : fetch_word Ubsan.M.loaded_segments (0x18e4c : word) = Some W_18e4c.
Proof. vm_refl. Qed.
Lemma D_18e4c : decode_any W_18e4c = Some (Branch BC_EQ 15 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e50 : bv 32 := 0x01f77793.
Lemma F_18e50 : fetch_word Ubsan.M.loaded_segments (0x18e50 : word) = Some W_18e50.
Proof. vm_refl. Qed.
Lemma D_18e50 : decode_any W_18e50 = Some (OpImm ALU_AND 15 14 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e54 : bv 32 := 0x00079a63.
Lemma F_18e54 : fetch_word Ubsan.M.loaded_segments (0x18e54 : word) = Some W_18e54.
Proof. vm_refl. Qed.
Lemma D_18e54 : decode_any W_18e54 = Some (Branch BC_NE 15 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e58 : bv 32 := 0xfffff7b7.
Lemma F_18e58 : fetch_word Ubsan.M.loaded_segments (0x18e58 : word) = Some W_18e58.
Proof. vm_refl. Qed.
Lemma D_18e58 : decode_any W_18e58 = Some (Lui 15 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e5c : bv 32 := 0x00f77733.
Lemma F_18e5c : fetch_word Ubsan.M.loaded_segments (0x18e5c : word) = Some W_18e5c.
Proof. vm_refl. Qed.
Lemma D_18e5c : decode_any W_18e5c = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e60 : bv 32 := 0xff070713.
Lemma F_18e60 : fetch_word Ubsan.M.loaded_segments (0x18e60 : word) = Some W_18e60.
Proof. vm_refl. Qed.
Lemma D_18e60 : decode_any W_18e60 = Some (OpImm ALU_ADD 14 14 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e64 : bv 32 := 0x0200006f.
Lemma F_18e64 : fetch_word Ubsan.M.loaded_segments (0x18e64 : word) = Some W_18e64.
Proof. vm_refl. Qed.
Lemma D_18e64 : decode_any W_18e64 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e68 : bv 32 := 0x00575713.
Lemma F_18e68 : fetch_word Ubsan.M.loaded_segments (0x18e68 : word) = Some W_18e68.
Proof. vm_refl. Qed.
Lemma D_18e68 : decode_any W_18e68 = Some (ShiftImm ALU_SRL 14 14 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e6c : bv 32 := 0xffff7797.
Lemma F_18e6c : fetch_word Ubsan.M.loaded_segments (0x18e6c : word) = Some W_18e6c.
Proof. vm_refl. Qed.
Lemma D_18e6c : decode_any W_18e6c = Some (Auipc 15 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e70 : bv 32 := 0x07e77713.
Lemma F_18e70 : fetch_word Ubsan.M.loaded_segments (0x18e70 : word) = Some W_18e70.
Proof. vm_refl. Qed.
Lemma D_18e70 : decode_any W_18e70 = Some (OpImm ALU_AND 14 14 126, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e74 : bv 32 := 0x6a078793.
Lemma F_18e74 : fetch_word Ubsan.M.loaded_segments (0x18e74 : word) = Some W_18e74.
Proof. vm_refl. Qed.
Lemma D_18e74 : decode_any W_18e74 = Some (OpImm ALU_ADD 15 15 1696, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e78 : bv 32 := 0x00e78733.
Lemma F_18e78 : fetch_word Ubsan.M.loaded_segments (0x18e78 : word) = Some W_18e78.
Proof. vm_refl. Qed.
Lemma D_18e78 : decode_any W_18e78 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e7c : bv 32 := 0x00075703.
Lemma F_18e7c : fetch_word Ubsan.M.loaded_segments (0x18e7c : word) = Some W_18e7c.
Proof. vm_refl. Qed.
Lemma D_18e7c : decode_any W_18e7c = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e80 : bv 32 := 0x00471713.
Lemma F_18e80 : fetch_word Ubsan.M.loaded_segments (0x18e80 : word) = Some W_18e80.
Proof. vm_refl. Qed.
Lemma D_18e80 : decode_any W_18e80 = Some (ShiftImm ALU_SLL 14 14 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e84 : bv 32 := 0x01053803.
Lemma F_18e84 : fetch_word Ubsan.M.loaded_segments (0x18e84 : word) = Some W_18e84.
Proof. vm_refl. Qed.
Lemma D_18e84 : decode_any W_18e84 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e88 : bv 32 := 0x02b707b3.
Lemma F_18e88 : fetch_word Ubsan.M.loaded_segments (0x18e88 : word) = Some W_18e88.
Proof. vm_refl. Qed.
Lemma D_18e88 : decode_any W_18e88 = Some (Mul M_MUL 15 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e8c : bv 32 := 0x00f807b3.
Lemma F_18e8c : fetch_word Ubsan.M.loaded_segments (0x18e8c : word) = Some W_18e8c.
Proof. vm_refl. Qed.
Lemma D_18e8c : decode_any W_18e8c = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e90 : bv 32 := 0x00d7c883.
Lemma F_18e90 : fetch_word Ubsan.M.loaded_segments (0x18e90 : word) = Some W_18e90.
Proof. vm_refl. Qed.
Lemma D_18e90 : decode_any W_18e90 = Some (Load SZ1 false 17 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e94 : bv 32 := 0x40c702b3.
Lemma F_18e94 : fetch_word Ubsan.M.loaded_segments (0x18e94 : word) = Some W_18e94.
Proof. vm_refl. Qed.
Lemma D_18e94 : decode_any W_18e94 = Some (Op ALU_SUB 5 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e98 : bv 32 := 0xffc28293.
Lemma F_18e98 : fetch_word Ubsan.M.loaded_segments (0x18e98 : word) = Some W_18e98.
Proof. vm_refl. Qed.
Lemma D_18e98 : decode_any W_18e98 = Some (OpImm ALU_ADD 5 5 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_18e9c : bv 32 := 0x01078793.
Lemma F_18e9c : fetch_word Ubsan.M.loaded_segments (0x18e9c : word) = Some W_18e9c.
Proof. vm_refl. Qed.
Lemma D_18e9c : decode_any W_18e9c = Some (OpImm ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ea0 : bv 32 := 0x00088663.
Lemma F_18ea0 : fetch_word Ubsan.M.loaded_segments (0x18ea0 : word) = Some W_18ea0.
Proof. vm_refl. Qed.
Lemma D_18ea0 : decode_any W_18ea0 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ea4 : bv 32 := 0xffe7d683.
Lemma F_18ea4 : fetch_word Ubsan.M.loaded_segments (0x18ea4 : word) = Some W_18ea4.
Proof. vm_refl. Qed.
Lemma D_18ea4 : decode_any W_18ea4 = Some (Load SZ2 false 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ea8 : bv 32 := 0x00168693.
Lemma F_18ea8 : fetch_word Ubsan.M.loaded_segments (0x18ea8 : word) = Some W_18ea8.
Proof. vm_refl. Qed.
Lemma D_18ea8 : decode_any W_18ea8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_18eac : bv 32 := 0xffc7c383.
Lemma F_18eac : fetch_word Ubsan.M.loaded_segments (0x18eac : word) = Some W_18eac.
Proof. vm_refl. Qed.
Lemma D_18eac : decode_any W_18eac = Some (Load SZ1 false 7 15 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_18eb0 : bv 32 := 0x0042d313.
Lemma F_18eb0 : fetch_word Ubsan.M.loaded_segments (0x18eb0 : word) = Some W_18eb0.
Proof. vm_refl. Qed.
Lemma D_18eb0 : decode_any W_18eb0 = Some (ShiftImm ALU_SRL 6 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_18eb4 : bv 32 := 0x0ff6f893.
Lemma F_18eb4 : fetch_word Ubsan.M.loaded_segments (0x18eb4 : word) = Some W_18eb4.
Proof. vm_refl. Qed.
Lemma D_18eb4 : decode_any W_18eb4 = Some (OpImm ALU_AND 17 13 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_18eb8 : bv 32 := 0x00038463.
Lemma F_18eb8 : fetch_word Ubsan.M.loaded_segments (0x18eb8 : word) = Some W_18eb8.
Proof. vm_refl. Qed.
Lemma D_18eb8 : decode_any W_18eb8 = Some (Branch BC_EQ 7 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ec0 : bv 32 := 0x03137e63.
Lemma F_18ec0 : fetch_word Ubsan.M.loaded_segments (0x18ec0 : word) = Some W_18ec0.
Proof. vm_refl. Qed.
Lemma D_18ec0 : decode_any W_18ec0 = Some (Branch BC_GEU 6 17 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ec4 : bv 32 := 0x0052d693.
Lemma F_18ec4 : fetch_word Ubsan.M.loaded_segments (0x18ec4 : word) = Some W_18ec4.
Proof. vm_refl. Qed.
Lemma D_18ec4 : decode_any W_18ec4 = Some (ShiftImm ALU_SRL 13 5 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ec8 : bv 32 := 0x00d366b3.
Lemma F_18ec8 : fetch_word Ubsan.M.loaded_segments (0x18ec8 : word) = Some W_18ec8.
Proof. vm_refl. Qed.
Lemma D_18ec8 : decode_any W_18ec8 = Some (Op ALU_OR 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ecc : bv 32 := 0x0026d293.
Lemma F_18ecc : fetch_word Ubsan.M.loaded_segments (0x18ecc : word) = Some W_18ecc.
Proof. vm_refl. Qed.
Lemma D_18ecc : decode_any W_18ecc = Some (ShiftImm ALU_SRL 5 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ed0 : bv 32 := 0x00d2e6b3.
Lemma F_18ed0 : fetch_word Ubsan.M.loaded_segments (0x18ed0 : word) = Some W_18ed0.
Proof. vm_refl. Qed.
Lemma D_18ed0 : decode_any W_18ed0 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ed4 : bv 32 := 0x0046d293.
Lemma F_18ed4 : fetch_word Ubsan.M.loaded_segments (0x18ed4 : word) = Some W_18ed4.
Proof. vm_refl. Qed.
Lemma D_18ed4 : decode_any W_18ed4 = Some (ShiftImm ALU_SRL 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ed8 : bv 32 := 0x00d2e6b3.
Lemma F_18ed8 : fetch_word Ubsan.M.loaded_segments (0x18ed8 : word) = Some W_18ed8.
Proof. vm_refl. Qed.
Lemma D_18ed8 : decode_any W_18ed8 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_18edc : bv 32 := 0x00d8f6b3.
Lemma F_18edc : fetch_word Ubsan.M.loaded_segments (0x18edc : word) = Some W_18edc.
Proof. vm_refl. Qed.
Lemma D_18edc : decode_any W_18edc = Some (Op ALU_AND 13 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ee0 : bv 32 := 0x00d338b3.
Lemma F_18ee0 : fetch_word Ubsan.M.loaded_segments (0x18ee0 : word) = Some W_18ee0.
Proof. vm_refl. Qed.
Lemma D_18ee0 : decode_any W_18ee0 = Some (Op ALU_SLTU 17 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ee4 : bv 32 := 0xfff34293.
Lemma F_18ee4 : fetch_word Ubsan.M.loaded_segments (0x18ee4 : word) = Some W_18ee4.
Proof. vm_refl. Qed.
Lemma D_18ee4 : decode_any W_18ee4 = Some (OpImm ALU_XOR 5 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ee8 : bv 32 := 0x411008bb.
Lemma F_18ee8 : fetch_word Ubsan.M.loaded_segments (0x18ee8 : word) = Some W_18ee8.
Proof. vm_refl. Qed.
Lemma D_18ee8 : decode_any W_18ee8 = Some (Op32 ALU_SUB 17 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_18eec : bv 32 := 0x0058f8b3.
Lemma F_18eec : fetch_word Ubsan.M.loaded_segments (0x18eec : word) = Some W_18eec.
Proof. vm_refl. Qed.
Lemma D_18eec : decode_any W_18eec = Some (Op ALU_AND 17 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ef0 : bv 32 := 0x00d888bb.
Lemma F_18ef0 : fetch_word Ubsan.M.loaded_segments (0x18ef0 : word) = Some W_18ef0.
Proof. vm_refl. Qed.
Lemma D_18ef0 : decode_any W_18ef0 = Some (Op32 ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ef4 : bv 32 := 0x01137463.
Lemma F_18ef4 : fetch_word Ubsan.M.loaded_segments (0x18ef4 : word) = Some W_18ef4.
Proof. vm_refl. Qed.
Lemma D_18ef4 : decode_any W_18ef4 = Some (Branch BC_GEU 6 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18efc : bv 32 := 0x00078693.
Lemma F_18efc : fetch_word Ubsan.M.loaded_segments (0x18efc : word) = Some W_18efc.
Proof. vm_refl. Qed.
Lemma D_18efc : decode_any W_18efc = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f00 : bv 32 := 0x02088063.
Lemma F_18f00 : fetch_word Ubsan.M.loaded_segments (0x18f00 : word) = Some W_18f00.
Proof. vm_refl. Qed.
Lemma D_18f00 : decode_any W_18f00 = Some (Branch BC_EQ 17 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f04 : bv 32 := 0xfe000813.
Lemma F_18f04 : fetch_word Ubsan.M.loaded_segments (0x18f04 : word) = Some W_18f04.
Proof. vm_refl. Qed.
Lemma D_18f04 : decode_any W_18f04 = Some (OpImm ALU_ADD 16 0 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f08 : bv 32 := 0x0048969b.
Lemma F_18f08 : fetch_word Ubsan.M.loaded_segments (0x18f08 : word) = Some W_18f08.
Proof. vm_refl. Qed.
Lemma D_18f08 : decode_any W_18f08 = Some (ShiftImm32 ALU_SLL 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f0c : bv 32 := 0x00d786b3.
Lemma F_18f0c : fetch_word Ubsan.M.loaded_segments (0x18f0c : word) = Some W_18f0c.
Proof. vm_refl. Qed.
Lemma D_18f0c : decode_any W_18f0c = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f10 : bv 32 := 0xff078ea3.
Lemma F_18f10 : fetch_word Ubsan.M.loaded_segments (0x18f10 : word) = Some W_18f10.
Proof. vm_refl. Qed.
Lemma D_18f10 : decode_any W_18f10 = Some (Store SZ1 15 16 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f14 : bv 32 := 0xff179f23.
Lemma F_18f14 : fetch_word Ubsan.M.loaded_segments (0x18f14 : word) = Some W_18f14.
Proof. vm_refl. Qed.
Lemma D_18f14 : decode_any W_18f14 = Some (Store SZ2 15 17 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f18 : bv 32 := 0xfe068e23.
Lemma F_18f18 : fetch_word Ubsan.M.loaded_segments (0x18f18 : word) = Some W_18f18.
Proof. vm_refl. Qed.
Lemma D_18f18 : decode_any W_18f18 = Some (Store SZ1 13 0 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f1c : bv 32 := 0x01053803.
Lemma F_18f1c : fetch_word Ubsan.M.loaded_segments (0x18f1c : word) = Some W_18f1c.
Proof. vm_refl. Qed.
Lemma D_18f1c : decode_any W_18f1c = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f20 : bv 32 := 0x00e78733.
Lemma F_18f20 : fetch_word Ubsan.M.loaded_segments (0x18f20 : word) = Some W_18f20.
Proof. vm_refl. Qed.
Lemma D_18f20 : decode_any W_18f20 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f24 : bv 32 := 0x410687bb.
Lemma F_18f24 : fetch_word Ubsan.M.loaded_segments (0x18f24 : word) = Some W_18f24.
Proof. vm_refl. Qed.
Lemma D_18f24 : decode_any W_18f24 = Some (Op32 ALU_SUB 15 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f28 : bv 32 := 0x00d60633.
Lemma F_18f28 : fetch_word Ubsan.M.loaded_segments (0x18f28 : word) = Some W_18f28.
Proof. vm_refl. Qed.
Lemma D_18f28 : decode_any W_18f28 = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f2c : bv 32 := 0xffc70513.
Lemma F_18f2c : fetch_word Ubsan.M.loaded_segments (0x18f2c : word) = Some W_18f2c.
Proof. vm_refl. Qed.
Lemma D_18f2c : decode_any W_18f2c = Some (OpImm ALU_ADD 10 14 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f30 : bv 32 := 0xff078793.
Lemma F_18f30 : fetch_word Ubsan.M.loaded_segments (0x18f30 : word) = Some W_18f30.
Proof. vm_refl. Qed.
Lemma D_18f30 : decode_any W_18f30 = Some (OpImm ALU_ADD 15 15 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f34 : bv 32 := 0x0047d793.
Lemma F_18f34 : fetch_word Ubsan.M.loaded_segments (0x18f34 : word) = Some W_18f34.
Proof. vm_refl. Qed.
Lemma D_18f34 : decode_any W_18f34 = Some (ShiftImm ALU_SRL 15 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f38 : bv 32 := 0x40c5083b.
Lemma F_18f38 : fetch_word Ubsan.M.loaded_segments (0x18f38 : word) = Some W_18f38.
Proof. vm_refl. Qed.
Lemma D_18f38 : decode_any W_18f38 = Some (Op32 ALU_SUB 16 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f3c : bv 32 := 0xfeb68ea3.
Lemma F_18f3c : fetch_word Ubsan.M.loaded_segments (0x18f3c : word) = Some W_18f3c.
Proof. vm_refl. Qed.
Lemma D_18f3c : decode_any W_18f3c = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f40 : bv 32 := 0xfef69f23.
Lemma F_18f40 : fetch_word Ubsan.M.loaded_segments (0x18f40 : word) = Some W_18f40.
Proof. vm_refl. Qed.
Lemma D_18f40 : decode_any W_18f40 = Some (Store SZ2 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f44 : bv 32 := 0x02080463.
Lemma F_18f44 : fetch_word Ubsan.M.loaded_segments (0x18f44 : word) = Some W_18f44.
Proof. vm_refl. Qed.
Lemma D_18f44 : decode_any W_18f44 = Some (Branch BC_EQ 16 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f48 : bv 32 := 0x40c505bb.
Lemma F_18f48 : fetch_word Ubsan.M.loaded_segments (0x18f48 : word) = Some W_18f48.
Proof. vm_refl. Qed.
Lemma D_18f48 : decode_any W_18f48 = Some (Op32 ALU_SUB 11 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f4c : bv 32 := 0x40b0063b.
Lemma F_18f4c : fetch_word Ubsan.M.loaded_segments (0x18f4c : word) = Some W_18f4c.
Proof. vm_refl. Qed.
Lemma D_18f4c : decode_any W_18f4c = Some (Op32 ALU_SUB 12 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f50 : bv 32 := 0x00c50633.
Lemma F_18f50 : fetch_word Ubsan.M.loaded_segments (0x18f50 : word) = Some W_18f50.
Proof. vm_refl. Qed.
Lemma D_18f50 : decode_any W_18f50 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f54 : bv 32 := 0x00500513.
Lemma F_18f54 : fetch_word Ubsan.M.loaded_segments (0x18f54 : word) = Some W_18f54.
Proof. vm_refl. Qed.
Lemma D_18f54 : decode_any W_18f54 = Some (OpImm ALU_ADD 10 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f58 : bv 32 := 0x00060023.
Lemma F_18f58 : fetch_word Ubsan.M.loaded_segments (0x18f58 : word) = Some W_18f58.
Proof. vm_refl. Qed.
Lemma D_18f58 : decode_any W_18f58 = Some (Store SZ1 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f5c : bv 32 := 0x00a5cc63.
Lemma F_18f5c : fetch_word Ubsan.M.loaded_segments (0x18f5c : word) = Some W_18f5c.
Proof. vm_refl. Qed.
Lemma D_18f5c : decode_any W_18f5c = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f60 : bv 32 := 0xfe070ba3.
Lemma F_18f60 : fetch_word Ubsan.M.loaded_segments (0x18f60 : word) = Some W_18f60.
Proof. vm_refl. Qed.
Lemma D_18f60 : decode_any W_18f60 = Some (Store SZ1 14 0 4087, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f64 : bv 32 := 0xfeb72c23.
Lemma F_18f64 : fetch_word Ubsan.M.loaded_segments (0x18f64 : word) = Some W_18f64.
Proof. vm_refl. Qed.
Lemma D_18f64 : decode_any W_18f64 = Some (Store SZ4 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f68 : bv 32 := 0x0100006f.
Lemma F_18f68 : fetch_word Ubsan.M.loaded_segments (0x18f68 : word) = Some W_18f68.
Proof. vm_refl. Qed.
Lemma D_18f68 : decode_any W_18f68 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f6c : bv 32 := 0x00000513.
Lemma F_18f6c : fetch_word Ubsan.M.loaded_segments (0x18f6c : word) = Some W_18f6c.
Proof. vm_refl. Qed.
Lemma D_18f6c : decode_any W_18f6c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f70 : bv 32 := 0x0080006f.
Lemma F_18f70 : fetch_word Ubsan.M.loaded_segments (0x18f70 : word) = Some W_18f70.
Proof. vm_refl. Qed.
Lemma D_18f70 : decode_any W_18f70 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f74 : bv 32 := 0x00058513.
Lemma F_18f74 : fetch_word Ubsan.M.loaded_segments (0x18f74 : word) = Some W_18f74.
Proof. vm_refl. Qed.
Lemma D_18f74 : decode_any W_18f74 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f78 : bv 32 := 0xffd6c583.
Lemma F_18f78 : fetch_word Ubsan.M.loaded_segments (0x18f78 : word) = Some W_18f78.
Proof. vm_refl. Qed.
Lemma D_18f78 : decode_any W_18f78 = Some (Load SZ1 false 11 13 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f7c : bv 32 := 0x01f5f593.
Lemma F_18f7c : fetch_word Ubsan.M.loaded_segments (0x18f7c : word) = Some W_18f7c.
Proof. vm_refl. Qed.
Lemma D_18f7c : decode_any W_18f7c = Some (OpImm ALU_AND 11 11 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f80 : bv 32 := 0x00551513.
Lemma F_18f80 : fetch_word Ubsan.M.loaded_segments (0x18f80 : word) = Some W_18f80.
Proof. vm_refl. Qed.
Lemma D_18f80 : decode_any W_18f80 = Some (ShiftImm ALU_SLL 10 10 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f84 : bv 32 := 0x00b56533.
Lemma F_18f84 : fetch_word Ubsan.M.loaded_segments (0x18f84 : word) = Some W_18f84.
Proof. vm_refl. Qed.
Lemma D_18f84 : decode_any W_18f84 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f88 : bv 32 := 0xfea68ea3.
Lemma F_18f88 : fetch_word Ubsan.M.loaded_segments (0x18f88 : word) = Some W_18f88.
Proof. vm_refl. Qed.
Lemma D_18f88 : decode_any W_18f88 = Some (Store SZ1 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f8c : bv 32 := 0x00068513.
Lemma F_18f8c : fetch_word Ubsan.M.loaded_segments (0x18f8c : word) = Some W_18f8c.
Proof. vm_refl. Qed.
Lemma D_18f8c : decode_any W_18f8c = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18f90 : bv 32 := 0x00008067.
Lemma F_18f90 : fetch_word Ubsan.M.loaded_segments (0x18f90 : word) = Some W_18f90.
Proof. vm_refl. Qed.
Lemma D_18f90 : decode_any W_18f90 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
