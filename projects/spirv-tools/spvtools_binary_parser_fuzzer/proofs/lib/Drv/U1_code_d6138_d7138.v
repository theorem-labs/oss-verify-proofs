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

Definition W_d70a0 : bv 32 := 0xf9010113.
Lemma F_d70a0 : fetch_word Ubsan.M.loaded_segments (0xd70d4 : word) = Some W_d70a0.
Proof. vm_refl. Qed.
Lemma D_d70a0 : decode_any W_d70a0 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70a4 : bv 32 := 0x06113423.
Lemma F_d70a4 : fetch_word Ubsan.M.loaded_segments (0xd70d8 : word) = Some W_d70a4.
Proof. vm_refl. Qed.
Lemma D_d70a4 : decode_any W_d70a4 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70a8 : bv 32 := 0x06813023.
Lemma F_d70a8 : fetch_word Ubsan.M.loaded_segments (0xd70dc : word) = Some W_d70a8.
Proof. vm_refl. Qed.
Lemma D_d70a8 : decode_any W_d70a8 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70ac : bv 32 := 0x04913c23.
Lemma F_d70ac : fetch_word Ubsan.M.loaded_segments (0xd70e0 : word) = Some W_d70ac.
Proof. vm_refl. Qed.
Lemma D_d70ac : decode_any W_d70ac = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70b0 : bv 32 := 0x05213823.
Lemma F_d70b0 : fetch_word Ubsan.M.loaded_segments (0xd70e4 : word) = Some W_d70b0.
Proof. vm_refl. Qed.
Lemma D_d70b0 : decode_any W_d70b0 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70b4 : bv 32 := 0x05313423.
Lemma F_d70b4 : fetch_word Ubsan.M.loaded_segments (0xd70e8 : word) = Some W_d70b4.
Proof. vm_refl. Qed.
Lemma D_d70b4 : decode_any W_d70b4 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70b8 : bv 32 := 0x05413023.
Lemma F_d70b8 : fetch_word Ubsan.M.loaded_segments (0xd70ec : word) = Some W_d70b8.
Proof. vm_refl. Qed.
Lemma D_d70b8 : decode_any W_d70b8 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70bc : bv 32 := 0x03513c23.
Lemma F_d70bc : fetch_word Ubsan.M.loaded_segments (0xd70f0 : word) = Some W_d70bc.
Proof. vm_refl. Qed.
Lemma D_d70bc : decode_any W_d70bc = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70c0 : bv 32 := 0x03613823.
Lemma F_d70c0 : fetch_word Ubsan.M.loaded_segments (0xd70f4 : word) = Some W_d70c0.
Proof. vm_refl. Qed.
Lemma D_d70c0 : decode_any W_d70c0 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70c4 : bv 32 := 0x00060413.
Lemma F_d70c4 : fetch_word Ubsan.M.loaded_segments (0xd70f8 : word) = Some W_d70c4.
Proof. vm_refl. Qed.
Lemma D_d70c4 : decode_any W_d70c4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70c8 : bv 32 := 0x00050493.
Lemma F_d70c8 : fetch_word Ubsan.M.loaded_segments (0xd70fc : word) = Some W_d70c8.
Proof. vm_refl. Qed.
Lemma D_d70c8 : decode_any W_d70c8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70cc : bv 32 := 0x00018517.
Lemma F_d70cc : fetch_word Ubsan.M.loaded_segments (0xd7100 : word) = Some W_d70cc.
Proof. vm_refl. Qed.
Lemma D_d70cc : decode_any W_d70cc = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70d0 : bv 32 := 0xd1053a83.
Lemma F_d70d0 : fetch_word Ubsan.M.loaded_segments (0xd7104 : word) = Some W_d70d0.
Proof. vm_refl. Qed.
Lemma D_d70d0 : decode_any W_d70d0 = Some (Load SZ8 true 21 10 3344, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70d4 : bv 32 := 0x000ab503.
Lemma F_d70d4 : fetch_word Ubsan.M.loaded_segments (0xd7108 : word) = Some W_d70d4.
Proof. vm_refl. Qed.
Lemma D_d70d4 : decode_any W_d70d4 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70d8 : bv 32 := 0x02a13423.
Lemma F_d70d8 : fetch_word Ubsan.M.loaded_segments (0xd710c : word) = Some W_d70d8.
Proof. vm_refl. Qed.
Lemma D_d70d8 : decode_any W_d70d8 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70dc : bv 32 := 0x0284b503.
Lemma F_d70dc : fetch_word Ubsan.M.loaded_segments (0xd7110 : word) = Some W_d70dc.
Proof. vm_refl. Qed.
Lemma D_d70dc : decode_any W_d70dc = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70e0 : bv 32 := 0x0384b603.
Lemma F_d70e0 : fetch_word Ubsan.M.loaded_segments (0xd7114 : word) = Some W_d70e0.
Proof. vm_refl. Qed.
Lemma D_d70e0 : decode_any W_d70e0 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70e4 : bv 32 := 0x40c50b33.
Lemma F_d70e4 : fetch_word Ubsan.M.loaded_segments (0xd7118 : word) = Some W_d70e4.
Proof. vm_refl. Qed.
Lemma D_d70e4 : decode_any W_d70e4 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70e8 : bv 32 := 0x00c546b3.
Lemma F_d70e8 : fetch_word Ubsan.M.loaded_segments (0xd711c : word) = Some W_d70e8.
Proof. vm_refl. Qed.
Lemma D_d70e8 : decode_any W_d70e8 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70ec : bv 32 := 0x00c13423.
Lemma F_d70ec : fetch_word Ubsan.M.loaded_segments (0xd7120 : word) = Some W_d70ec.
Proof. vm_refl. Qed.
Lemma D_d70ec : decode_any W_d70ec = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70f0 : bv 32 := 0x01613823.
Lemma F_d70f0 : fetch_word Ubsan.M.loaded_segments (0xd7124 : word) = Some W_d70f0.
Proof. vm_refl. Qed.
Lemma D_d70f0 : decode_any W_d70f0 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70f4 : bv 32 := 0x00b13c23.
Lemma F_d70f4 : fetch_word Ubsan.M.loaded_segments (0xd7128 : word) = Some W_d70f4.
Proof. vm_refl. Qed.
Lemma D_d70f4 : decode_any W_d70f4 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70f8 : bv 32 := 0x02813023.
Lemma F_d70f8 : fetch_word Ubsan.M.loaded_segments (0xd712c : word) = Some W_d70f8.
Proof. vm_refl. Qed.
Lemma D_d70f8 : decode_any W_d70f8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_d70fc : bv 32 := 0x008b0b33.
Lemma F_d70fc : fetch_word Ubsan.M.loaded_segments (0xd7130 : word) = Some W_d70fc.
Proof. vm_refl. Qed.
Lemma D_d70fc : decode_any W_d70fc = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7100 : bv 32 := 0x00d03933.
Lemma F_d7100 : fetch_word Ubsan.M.loaded_segments (0xd7134 : word) = Some W_d7100.
Proof. vm_refl. Qed.
Lemma D_d7100 : decode_any W_d7100 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7104 : bv 32 := 0x00c50663.
Lemma F_d7104 : fetch_word Ubsan.M.loaded_segments (0xd7138 : word) = Some W_d7104.
Proof. vm_refl. Qed.
Lemma D_d7104 : decode_any W_d7104 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7108 : bv 32 := 0x00810993.
Lemma F_d7108 : fetch_word Ubsan.M.loaded_segments (0xd713c : word) = Some W_d7108.
Proof. vm_refl. Qed.
Lemma D_d7108 : decode_any W_d7108 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d710c : bv 32 := 0x0080006f.
Lemma F_d710c : fetch_word Ubsan.M.loaded_segments (0xd7140 : word) = Some W_d710c.
Proof. vm_refl. Qed.
Lemma D_d710c : decode_any W_d710c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7110 : bv 32 := 0x01810993.
Lemma F_d7110 : fetch_word Ubsan.M.loaded_segments (0xd7144 : word) = Some W_d7110.
Proof. vm_refl. Qed.
Lemma D_d7110 : decode_any W_d7110 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7114 : bv 32 := 0x0784a503.
Lemma F_d7114 : fetch_word Ubsan.M.loaded_segments (0xd7148 : word) = Some W_d7114.
Proof. vm_refl. Qed.
Lemma D_d7114 : decode_any W_d7114 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7118 : bv 32 := 0x00190913.
Lemma F_d7118 : fetch_word Ubsan.M.loaded_segments (0xd714c : word) = Some W_d7118.
Proof. vm_refl. Qed.
Lemma D_d7118 : decode_any W_d7118 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_d711c : bv 32 := 0x04200893.
Lemma F_d711c : fetch_word Ubsan.M.loaded_segments (0xd7150 : word) = Some W_d711c.
Proof. vm_refl. Qed.
Lemma D_d711c : decode_any W_d711c = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7120 : bv 32 := 0x00098593.
Lemma F_d7120 : fetch_word Ubsan.M.loaded_segments (0xd7154 : word) = Some W_d7120.
Proof. vm_refl. Qed.
Lemma D_d7120 : decode_any W_d7120 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7124 : bv 32 := 0x00090613.
Lemma F_d7124 : fetch_word Ubsan.M.loaded_segments (0xd7158 : word) = Some W_d7124.
Proof. vm_refl. Qed.
Lemma D_d7124 : decode_any W_d7124 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7128 : bv 32 := 0x00000073.
Lemma F_d7128 : fetch_word Ubsan.M.loaded_segments (0xd715c : word) = Some W_d7128.
Proof. vm_refl. Qed.

Lemma E_d7128 : is_ecall W_d7128 = true.
Proof. reflexivity. Qed.

Definition W_d712c : bv 32 := 0xeb5fa0ef.
Lemma F_d712c : fetch_word Ubsan.M.loaded_segments (0xd7160 : word) = Some W_d712c.
Proof. vm_refl. Qed.
Lemma D_d712c : decode_any W_d712c = Some (Jal 1 2076340, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7130 : bv 32 := 0x09651863.
Lemma F_d7130 : fetch_word Ubsan.M.loaded_segments (0xd7164 : word) = Some W_d7130.
Proof. vm_refl. Qed.
Lemma D_d7130 : decode_any W_d7130 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_d7134 : bv 32 := 0x0584b503.
Lemma F_d7134 : fetch_word Ubsan.M.loaded_segments (0xd7168 : word) = Some W_d7134.
Proof. vm_refl. Qed.
Lemma D_d7134 : decode_any W_d7134 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.
