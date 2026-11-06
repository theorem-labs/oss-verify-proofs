(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_d7138 : bv 32 := 0x0604b583.
Lemma F_d7138 : fetch_word Ubsan.M.loaded_segments (0xd716c : word) = Some W_d7138.
Proof. vm_refl. Qed.
Lemma D_d7138 : decode_any W_d7138 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_d713c : bv 32 := 0x00b505b3.
Lemma F_d713c : fetch_word Ubsan.M.loaded_segments (0xd7170 : word) = Some W_d713c.
Proof. vm_refl. Qed.
Lemma D_d713c : decode_any W_d713c = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7140 : bv 32 := 0x02b4b023.
Lemma F_d7140 : fetch_word Ubsan.M.loaded_segments (0xd7174 : word) = Some W_d7140.
Proof. vm_refl. Qed.
Lemma D_d7140 : decode_any W_d7140 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7144 : bv 32 := 0x02a4b423.
Lemma F_d7144 : fetch_word Ubsan.M.loaded_segments (0xd7178 : word) = Some W_d7144.
Proof. vm_refl. Qed.
Lemma D_d7144 : decode_any W_d7144 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7148 : bv 32 := 0x02a4bc23.
Lemma F_d7148 : fetch_word Ubsan.M.loaded_segments (0xd717c : word) = Some W_d7148.
Proof. vm_refl. Qed.
Lemma D_d7148 : decode_any W_d7148 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d714c : bv 32 := 0x00040513.
Lemma F_d714c : fetch_word Ubsan.M.loaded_segments (0xd7180 : word) = Some W_d714c.
Proof. vm_refl. Qed.
Lemma D_d714c : decode_any W_d714c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7150 : bv 32 := 0x000ab583.
Lemma F_d7150 : fetch_word Ubsan.M.loaded_segments (0xd7184 : word) = Some W_d7150.
Proof. vm_refl. Qed.
Lemma D_d7150 : decode_any W_d7150 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7154 : bv 32 := 0x02813603.
Lemma F_d7154 : fetch_word Ubsan.M.loaded_segments (0xd7188 : word) = Some W_d7154.
Proof. vm_refl. Qed.
Lemma D_d7154 : decode_any W_d7154 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7158 : bv 32 := 0x0cc59a63.
Lemma F_d7158 : fetch_word Ubsan.M.loaded_segments (0xd718c : word) = Some W_d7158.
Proof. vm_refl. Qed.
Lemma D_d7158 : decode_any W_d7158 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_d715c : bv 32 := 0x06813083.
Lemma F_d715c : fetch_word Ubsan.M.loaded_segments (0xd7190 : word) = Some W_d715c.
Proof. vm_refl. Qed.
Lemma D_d715c : decode_any W_d715c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7160 : bv 32 := 0x06013403.
Lemma F_d7160 : fetch_word Ubsan.M.loaded_segments (0xd7194 : word) = Some W_d7160.
Proof. vm_refl. Qed.
Lemma D_d7160 : decode_any W_d7160 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7164 : bv 32 := 0x05813483.
Lemma F_d7164 : fetch_word Ubsan.M.loaded_segments (0xd7198 : word) = Some W_d7164.
Proof. vm_refl. Qed.
Lemma D_d7164 : decode_any W_d7164 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7168 : bv 32 := 0x05013903.
Lemma F_d7168 : fetch_word Ubsan.M.loaded_segments (0xd719c : word) = Some W_d7168.
Proof. vm_refl. Qed.
Lemma D_d7168 : decode_any W_d7168 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_d716c : bv 32 := 0x04813983.
Lemma F_d716c : fetch_word Ubsan.M.loaded_segments (0xd71a0 : word) = Some W_d716c.
Proof. vm_refl. Qed.
Lemma D_d716c : decode_any W_d716c = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7170 : bv 32 := 0x04013a03.
Lemma F_d7170 : fetch_word Ubsan.M.loaded_segments (0xd71a4 : word) = Some W_d7170.
Proof. vm_refl. Qed.
Lemma D_d7170 : decode_any W_d7170 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7174 : bv 32 := 0x03813a83.
Lemma F_d7174 : fetch_word Ubsan.M.loaded_segments (0xd71a8 : word) = Some W_d7174.
Proof. vm_refl. Qed.
Lemma D_d7174 : decode_any W_d7174 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7178 : bv 32 := 0x03013b03.
Lemma F_d7178 : fetch_word Ubsan.M.loaded_segments (0xd71ac : word) = Some W_d7178.
Proof. vm_refl. Qed.
Lemma D_d7178 : decode_any W_d7178 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_d717c : bv 32 := 0x07010113.
Lemma F_d717c : fetch_word Ubsan.M.loaded_segments (0xd71b0 : word) = Some W_d717c.
Proof. vm_refl. Qed.
Lemma D_d717c : decode_any W_d717c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7180 : bv 32 := 0x00008067.
Lemma F_d7180 : fetch_word Ubsan.M.loaded_segments (0xd71b4 : word) = Some W_d7180.
Proof. vm_refl. Qed.
Lemma D_d7180 : decode_any W_d7180 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7184 : bv 32 := 0x00800713.
Lemma F_d7184 : fetch_word Ubsan.M.loaded_segments (0xd71b8 : word) = Some W_d7184.
Proof. vm_refl. Qed.
Lemma D_d7184 : decode_any W_d7184 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7188 : bv 32 := 0x000a0593.
Lemma F_d7188 : fetch_word Ubsan.M.loaded_segments (0xd71bc : word) = Some W_d7188.
Proof. vm_refl. Qed.
Lemma D_d7188 : decode_any W_d7188 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d718c : bv 32 := 0x00e98733.
Lemma F_d718c : fetch_word Ubsan.M.loaded_segments (0xd71c0 : word) = Some W_d718c.
Proof. vm_refl. Qed.
Lemma D_d718c : decode_any W_d718c = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7190 : bv 32 := 0x00073783.
Lemma F_d7190 : fetch_word Ubsan.M.loaded_segments (0xd71c4 : word) = Some W_d7190.
Proof. vm_refl. Qed.
Lemma D_d7190 : decode_any W_d7190 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7194 : bv 32 := 0x40ab0b33.
Lemma F_d7194 : fetch_word Ubsan.M.loaded_segments (0xd71c8 : word) = Some W_d7194.
Proof. vm_refl. Qed.
Lemma D_d7194 : decode_any W_d7194 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7198 : bv 32 := 0x0784a503.
Lemma F_d7198 : fetch_word Ubsan.M.loaded_segments (0xd71cc : word) = Some W_d7198.
Proof. vm_refl. Qed.
Lemma D_d7198 : decode_any W_d7198 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_d719c : bv 32 := 0x40c9093b.
Lemma F_d719c : fetch_word Ubsan.M.loaded_segments (0xd71d0 : word) = Some W_d719c.
Proof. vm_refl. Qed.
Lemma D_d719c : decode_any W_d719c = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d71a0 : bv 32 := 0x40d787b3.
Lemma F_d71a0 : fetch_word Ubsan.M.loaded_segments (0xd71d4 : word) = Some W_d71a0.
Proof. vm_refl. Qed.
Lemma D_d71a0 : decode_any W_d71a0 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_d71a4 : bv 32 := 0x00f73023.
Lemma F_d71a4 : fetch_word Ubsan.M.loaded_segments (0xd71d8 : word) = Some W_d71a4.
Proof. vm_refl. Qed.
Lemma D_d71a4 : decode_any W_d71a4 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d71a8 : bv 32 := 0x04200893.
Lemma F_d71a8 : fetch_word Ubsan.M.loaded_segments (0xd71dc : word) = Some W_d71a8.
Proof. vm_refl. Qed.
Lemma D_d71a8 : decode_any W_d71a8 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_d71ac : bv 32 := 0x00090613.
Lemma F_d71ac : fetch_word Ubsan.M.loaded_segments (0xd71e0 : word) = Some W_d71ac.
Proof. vm_refl. Qed.
Lemma D_d71ac : decode_any W_d71ac = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d71b0 : bv 32 := 0x00000073.
Lemma F_d71b0 : fetch_word Ubsan.M.loaded_segments (0xd71e4 : word) = Some W_d71b0.
Proof. vm_refl. Qed.

Lemma E_d71b0 : is_ecall W_d71b0 = true.
Proof. reflexivity. Qed.

Definition W_d71b4 : bv 32 := 0xe2dfa0ef.
Lemma F_d71b4 : fetch_word Ubsan.M.loaded_segments (0xd71e8 : word) = Some W_d71b4.
Proof. vm_refl. Qed.
Lemma D_d71b4 : decode_any W_d71b4 = Some (Jal 1 2076204, 4%Z).
Proof. vm_refl. Qed.

Definition W_d71b8 : bv 32 := 0x000a0993.
Lemma F_d71b8 : fetch_word Ubsan.M.loaded_segments (0xd71ec : word) = Some W_d71b8.
Proof. vm_refl. Qed.
Lemma D_d71b8 : decode_any W_d71b8 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d71bc : bv 32 := 0xf7650ce3.
Lemma F_d71bc : fetch_word Ubsan.M.loaded_segments (0xd71f0 : word) = Some W_d71bc.
Proof. vm_refl. Qed.
Lemma D_d71bc : decode_any W_d71bc = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_d71c0 : bv 32 := 0x02054c63.
Lemma F_d71c0 : fetch_word Ubsan.M.loaded_segments (0xd71f4 : word) = Some W_d71c0.
Proof. vm_refl. Qed.
Lemma D_d71c0 : decode_any W_d71c0 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d71c4 : bv 32 := 0x0089b583.
Lemma F_d71c4 : fetch_word Ubsan.M.loaded_segments (0xd71f8 : word) = Some W_d71c4.
Proof. vm_refl. Qed.
Lemma D_d71c4 : decode_any W_d71c4 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d71c8 : bv 32 := 0x00a5b633.
Lemma F_d71c8 : fetch_word Ubsan.M.loaded_segments (0xd71fc : word) = Some W_d71c8.
Proof. vm_refl. Qed.
Lemma D_d71c8 : decode_any W_d71c8 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_d71cc : bv 32 := 0x00461a13.
Lemma F_d71cc : fetch_word Ubsan.M.loaded_segments (0xd7200 : word) = Some W_d71cc.
Proof. vm_refl. Qed.
Lemma D_d71cc : decode_any W_d71cc = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_d71d0 : bv 32 := 0x01498a33.
Lemma F_d71d0 : fetch_word Ubsan.M.loaded_segments (0xd7204 : word) = Some W_d71d0.
Proof. vm_refl. Qed.
Lemma D_d71d0 : decode_any W_d71d0 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_d71d4 : bv 32 := 0x000a3703.
Lemma F_d71d4 : fetch_word Ubsan.M.loaded_segments (0xd7208 : word) = Some W_d71d4.
Proof. vm_refl. Qed.
Lemma D_d71d4 : decode_any W_d71d4 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d71d8 : bv 32 := 0x40c006b3.
Lemma F_d71d8 : fetch_word Ubsan.M.loaded_segments (0xd720c : word) = Some W_d71d8.
Proof. vm_refl. Qed.
Lemma D_d71d8 : decode_any W_d71d8 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d71dc : bv 32 := 0x00b6f6b3.
Lemma F_d71dc : fetch_word Ubsan.M.loaded_segments (0xd7210 : word) = Some W_d71dc.
Proof. vm_refl. Qed.
Lemma D_d71dc : decode_any W_d71dc = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_d71e0 : bv 32 := 0x40d506b3.
Lemma F_d71e0 : fetch_word Ubsan.M.loaded_segments (0xd7214 : word) = Some W_d71e0.
Proof. vm_refl. Qed.
Lemma D_d71e0 : decode_any W_d71e0 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_d71e4 : bv 32 := 0x00d70733.
Lemma F_d71e4 : fetch_word Ubsan.M.loaded_segments (0xd7218 : word) = Some W_d71e4.
Proof. vm_refl. Qed.
Lemma D_d71e4 : decode_any W_d71e4 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_d71e8 : bv 32 := 0x00ea3023.
Lemma F_d71e8 : fetch_word Ubsan.M.loaded_segments (0xd721c : word) = Some W_d71e8.
Proof. vm_refl. Qed.
Lemma D_d71e8 : decode_any W_d71e8 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d71ec : bv 32 := 0xf8a5fce3.
Lemma F_d71ec : fetch_word Ubsan.M.loaded_segments (0xd7220 : word) = Some W_d71ec.
Proof. vm_refl. Qed.
Lemma D_d71ec : decode_any W_d71ec = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_d71f0 : bv 32 := 0x01800713.
Lemma F_d71f0 : fetch_word Ubsan.M.loaded_segments (0xd7224 : word) = Some W_d71f0.
Proof. vm_refl. Qed.
Lemma D_d71f0 : decode_any W_d71f0 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d71f4 : bv 32 := 0xf95ff06f.
Lemma F_d71f4 : fetch_word Ubsan.M.loaded_segments (0xd7228 : word) = Some W_d71f4.
Proof. vm_refl. Qed.
Lemma D_d71f4 : decode_any W_d71f4 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7238 : bv 32 := 0x00008067.
Lemma F_d7238 : fetch_word Ubsan.M.loaded_segments (0xd726c : word) = Some W_d7238.
Proof. vm_refl. Qed.
Lemma D_d7238 : decode_any W_d7238 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
