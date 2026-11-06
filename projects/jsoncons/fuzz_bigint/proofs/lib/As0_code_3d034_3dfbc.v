(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_3d034 : bv 32 := 0x00060793.
Lemma F_3d034 : fetch_word Asan.M.loaded_segments (0x3d034 : word) = Some W_3d034.
Proof. vm_refl. Qed.
Lemma D_3d034 : decode_any W_3d034 = Some (OpImm ALU_ADD 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d038 : bv 32 := 0x00058713.
Lemma F_3d038 : fetch_word Asan.M.loaded_segments (0x3d038 : word) = Some W_3d038.
Proof. vm_refl. Qed.
Lemma D_3d038 : decode_any W_3d038 = Some (OpImm ALU_ADD 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d03c : bv 32 := 0x0009d597.
Lemma F_3d03c : fetch_word Asan.M.loaded_segments (0x3d03c : word) = Some W_3d03c.
Proof. vm_refl. Qed.
Lemma D_3d03c : decode_any W_3d03c = Some (Auipc 11 157, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d040 : bv 32 := 0x49c58593.
Lemma F_3d040 : fetch_word Asan.M.loaded_segments (0x3d040 : word) = Some W_3d040.
Proof. vm_refl. Qed.
Lemma D_3d040 : decode_any W_3d040 = Some (OpImm ALU_ADD 11 11 1180, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d044 : bv 32 := 0x00050613.
Lemma F_3d044 : fetch_word Asan.M.loaded_segments (0x3d044 : word) = Some W_3d044.
Proof. vm_refl. Qed.
Lemma D_3d044 : decode_any W_3d044 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d048 : bv 32 := 0x00058513.
Lemma F_3d048 : fetch_word Asan.M.loaded_segments (0x3d048 : word) = Some W_3d048.
Proof. vm_refl. Qed.
Lemma D_3d048 : decode_any W_3d048 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d04c : bv 32 := 0x00060593.
Lemma F_3d04c : fetch_word Asan.M.loaded_segments (0x3d04c : word) = Some W_3d04c.
Proof. vm_refl. Qed.
Lemma D_3d04c : decode_any W_3d04c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d050 : bv 32 := 0x00000613.
Lemma F_3d050 : fetch_word Asan.M.loaded_segments (0x3d050 : word) = Some W_3d050.
Proof. vm_refl. Qed.
Lemma D_3d050 : decode_any W_3d050 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d054 : bv 32 := 0x00000693.
Lemma F_3d054 : fetch_word Asan.M.loaded_segments (0x3d054 : word) = Some W_3d054.
Proof. vm_refl. Qed.
Lemma D_3d054 : decode_any W_3d054 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d058 : bv 32 := 0x0040006f.
Lemma F_3d058 : fetch_word Asan.M.loaded_segments (0x3d058 : word) = Some W_3d058.
Proof. vm_refl. Qed.
Lemma D_3d058 : decode_any W_3d058 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d05c : bv 32 := 0xfc010113.
Lemma F_3d05c : fetch_word Asan.M.loaded_segments (0x3d05c : word) = Some W_3d05c.
Proof. vm_refl. Qed.
Lemma D_3d05c : decode_any W_3d05c = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d060 : bv 32 := 0x02113c23.
Lemma F_3d060 : fetch_word Asan.M.loaded_segments (0x3d060 : word) = Some W_3d060.
Proof. vm_refl. Qed.
Lemma D_3d060 : decode_any W_3d060 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d064 : bv 32 := 0x02813823.
Lemma F_3d064 : fetch_word Asan.M.loaded_segments (0x3d064 : word) = Some W_3d064.
Proof. vm_refl. Qed.
Lemma D_3d064 : decode_any W_3d064 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d068 : bv 32 := 0x02913423.
Lemma F_3d068 : fetch_word Asan.M.loaded_segments (0x3d068 : word) = Some W_3d068.
Proof. vm_refl. Qed.
Lemma D_3d068 : decode_any W_3d068 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d06c : bv 32 := 0x03213023.
Lemma F_3d06c : fetch_word Asan.M.loaded_segments (0x3d06c : word) = Some W_3d06c.
Proof. vm_refl. Qed.
Lemma D_3d06c : decode_any W_3d06c = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d070 : bv 32 := 0x01313c23.
Lemma F_3d070 : fetch_word Asan.M.loaded_segments (0x3d070 : word) = Some W_3d070.
Proof. vm_refl. Qed.
Lemma D_3d070 : decode_any W_3d070 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d074 : bv 32 := 0x01413823.
Lemma F_3d074 : fetch_word Asan.M.loaded_segments (0x3d074 : word) = Some W_3d074.
Proof. vm_refl. Qed.
Lemma D_3d074 : decode_any W_3d074 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d078 : bv 32 := 0x01513423.
Lemma F_3d078 : fetch_word Asan.M.loaded_segments (0x3d078 : word) = Some W_3d078.
Proof. vm_refl. Qed.
Lemma D_3d078 : decode_any W_3d078 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d07c : bv 32 := 0x01613023.
Lemma F_3d07c : fetch_word Asan.M.loaded_segments (0x3d07c : word) = Some W_3d07c.
Proof. vm_refl. Qed.
Lemma D_3d07c : decode_any W_3d07c = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d080 : bv 32 := 0x02058e63.
Lemma F_3d080 : fetch_word Asan.M.loaded_segments (0x3d080 : word) = Some W_3d080.
Proof. vm_refl. Qed.
Lemma D_3d080 : decode_any W_3d080 = Some (Branch BC_EQ 11 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d084 : bv 32 := 0x00078a13.
Lemma F_3d084 : fetch_word Asan.M.loaded_segments (0x3d084 : word) = Some W_3d084.
Proof. vm_refl. Qed.
Lemma D_3d084 : decode_any W_3d084 = Some (OpImm ALU_ADD 20 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d088 : bv 32 := 0x00070413.
Lemma F_3d088 : fetch_word Asan.M.loaded_segments (0x3d088 : word) = Some W_3d088.
Proof. vm_refl. Qed.
Lemma D_3d088 : decode_any W_3d088 = Some (OpImm ALU_ADD 8 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d08c : bv 32 := 0x00058493.
Lemma F_3d08c : fetch_word Asan.M.loaded_segments (0x3d08c : word) = Some W_3d08c.
Proof. vm_refl. Qed.
Lemma D_3d08c : decode_any W_3d08c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d090 : bv 32 := 0x00050993.
Lemma F_3d090 : fetch_word Asan.M.loaded_segments (0x3d090 : word) = Some W_3d090.
Proof. vm_refl. Qed.
Lemma D_3d090 : decode_any W_3d090 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d094 : bv 32 := 0x00060a93.
Lemma F_3d094 : fetch_word Asan.M.loaded_segments (0x3d094 : word) = Some W_3d094.
Proof. vm_refl. Qed.
Lemma D_3d094 : decode_any W_3d094 = Some (OpImm ALU_ADD 21 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d098 : bv 32 := 0x00068b13.
Lemma F_3d098 : fetch_word Asan.M.loaded_segments (0x3d098 : word) = Some W_3d098.
Proof. vm_refl. Qed.
Lemma D_3d098 : decode_any W_3d098 = Some (OpImm ALU_ADD 22 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d09c : bv 32 := 0xff058913.
Lemma F_3d09c : fetch_word Asan.M.loaded_segments (0x3d09c : word) = Some W_3d09c.
Proof. vm_refl. Qed.
Lemma D_3d09c : decode_any W_3d09c = Some (OpImm ALU_ADD 18 11 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0a0 : bv 32 := 0x00058513.
Lemma F_3d0a0 : fetch_word Asan.M.loaded_segments (0x3d0a0 : word) = Some W_3d0a0.
Proof. vm_refl. Qed.
Lemma D_3d0a0 : decode_any W_3d0a0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0a4 : bv 32 := 0x7d1300ef.
Lemma F_3d0a4 : fetch_word Asan.M.loaded_segments (0x3d0a4 : word) = Some W_3d0a4.
Proof. vm_refl. Qed.
Lemma D_3d0a4 : decode_any W_3d0a4 = Some (Jal 1 200656, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0a8 : bv 32 := 0x02050e63.
Lemma F_3d0a8 : fetch_word Asan.M.loaded_segments (0x3d0a8 : word) = Some W_3d0a8.
Proof. vm_refl. Qed.
Lemma D_3d0a8 : decode_any W_3d0a8 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0ac : bv 32 := 0x00194503.
Lemma F_3d0ac : fetch_word Asan.M.loaded_segments (0x3d0ac : word) = Some W_3d0ac.
Proof. vm_refl. Qed.
Lemma D_3d0ac : decode_any W_3d0ac = Some (Load SZ1 false 10 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0b0 : bv 32 := 0x0fc57513.
Lemma F_3d0b0 : fetch_word Asan.M.loaded_segments (0x3d0b0 : word) = Some W_3d0b0.
Proof. vm_refl. Qed.
Lemma D_3d0b0 : decode_any W_3d0b0 = Some (OpImm ALU_AND 10 10 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0b4 : bv 32 := 0x00150513.
Lemma F_3d0b4 : fetch_word Asan.M.loaded_segments (0x3d0b4 : word) = Some W_3d0b4.
Proof. vm_refl. Qed.
Lemma D_3d0b4 : decode_any W_3d0b4 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0b8 : bv 32 := 0x00a900a3.
Lemma F_3d0b8 : fetch_word Asan.M.loaded_segments (0x3d0b8 : word) = Some W_3d0b8.
Proof. vm_refl. Qed.
Lemma D_3d0b8 : decode_any W_3d0b8 = Some (Store SZ1 18 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0bc : bv 32 := 0x03813083.
Lemma F_3d0bc : fetch_word Asan.M.loaded_segments (0x3d0bc : word) = Some W_3d0bc.
Proof. vm_refl. Qed.
Lemma D_3d0bc : decode_any W_3d0bc = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0c0 : bv 32 := 0x03013403.
Lemma F_3d0c0 : fetch_word Asan.M.loaded_segments (0x3d0c0 : word) = Some W_3d0c0.
Proof. vm_refl. Qed.
Lemma D_3d0c0 : decode_any W_3d0c0 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0c4 : bv 32 := 0x02813483.
Lemma F_3d0c4 : fetch_word Asan.M.loaded_segments (0x3d0c4 : word) = Some W_3d0c4.
Proof. vm_refl. Qed.
Lemma D_3d0c4 : decode_any W_3d0c4 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0c8 : bv 32 := 0x02013903.
Lemma F_3d0c8 : fetch_word Asan.M.loaded_segments (0x3d0c8 : word) = Some W_3d0c8.
Proof. vm_refl. Qed.
Lemma D_3d0c8 : decode_any W_3d0c8 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0cc : bv 32 := 0x01813983.
Lemma F_3d0cc : fetch_word Asan.M.loaded_segments (0x3d0cc : word) = Some W_3d0cc.
Proof. vm_refl. Qed.
Lemma D_3d0cc : decode_any W_3d0cc = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0d0 : bv 32 := 0x01013a03.
Lemma F_3d0d0 : fetch_word Asan.M.loaded_segments (0x3d0d0 : word) = Some W_3d0d0.
Proof. vm_refl. Qed.
Lemma D_3d0d0 : decode_any W_3d0d0 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0d4 : bv 32 := 0x00813a83.
Lemma F_3d0d4 : fetch_word Asan.M.loaded_segments (0x3d0d4 : word) = Some W_3d0d4.
Proof. vm_refl. Qed.
Lemma D_3d0d4 : decode_any W_3d0d4 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0d8 : bv 32 := 0x00013b03.
Lemma F_3d0d8 : fetch_word Asan.M.loaded_segments (0x3d0d8 : word) = Some W_3d0d8.
Proof. vm_refl. Qed.
Lemma D_3d0d8 : decode_any W_3d0d8 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0dc : bv 32 := 0x04010113.
Lemma F_3d0dc : fetch_word Asan.M.loaded_segments (0x3d0dc : word) = Some W_3d0dc.
Proof. vm_refl. Qed.
Lemma D_3d0dc : decode_any W_3d0dc = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0e0 : bv 32 := 0x00008067.
Lemma F_3d0e0 : fetch_word Asan.M.loaded_segments (0x3d0e0 : word) = Some W_3d0e0.
Proof. vm_refl. Qed.
Lemma D_3d0e0 : decode_any W_3d0e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0e4 : bv 32 := 0xffc97693.
Lemma F_3d0e4 : fetch_word Asan.M.loaded_segments (0x3d0e4 : word) = Some W_3d0e4.
Proof. vm_refl. Qed.
Lemma D_3d0e4 : decode_any W_3d0e4 = Some (OpImm ALU_AND 13 18 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0e8 : bv 32 := 0x00391513.
Lemma F_3d0e8 : fetch_word Asan.M.loaded_segments (0x3d0e8 : word) = Some W_3d0e8.
Proof. vm_refl. Qed.
Lemma D_3d0e8 : decode_any W_3d0e8 = Some (ShiftImm ALU_SLL 10 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0ec : bv 32 := 0x0ff00613.
Lemma F_3d0ec : fetch_word Asan.M.loaded_segments (0x3d0ec : word) = Some W_3d0ec.
Proof. vm_refl. Qed.
Lemma D_3d0ec : decode_any W_3d0ec = Some (OpImm ALU_ADD 12 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0f0 : bv 32 := 0x00200713.
Lemma F_3d0f0 : fetch_word Asan.M.loaded_segments (0x3d0f0 : word) = Some W_3d0f0.
Proof. vm_refl. Qed.
Lemma D_3d0f0 : decode_any W_3d0f0 = Some (OpImm ALU_ADD 14 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0f4 : bv 32 := 0x00300593.
Lemma F_3d0f4 : fetch_word Asan.M.loaded_segments (0x3d0f4 : word) = Some W_3d0f4.
Proof. vm_refl. Qed.
Lemma D_3d0f4 : decode_any W_3d0f4 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0f8 : bv 32 := 0x00a617bb.
Lemma F_3d0f8 : fetch_word Asan.M.loaded_segments (0x3d0f8 : word) = Some W_3d0f8.
Proof. vm_refl. Qed.
Lemma D_3d0f8 : decode_any W_3d0f8 = Some (Op32 ALU_SLL 15 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d0fc : bv 32 := 0x00a7173b.
Lemma F_3d0fc : fetch_word Asan.M.loaded_segments (0x3d0fc : word) = Some W_3d0fc.
Proof. vm_refl. Qed.
Lemma D_3d0fc : decode_any W_3d0fc = Some (Op32 ALU_SLL 14 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d100 : bv 32 := 0x00a5983b.
Lemma F_3d100 : fetch_word Asan.M.loaded_segments (0x3d100 : word) = Some W_3d100.
Proof. vm_refl. Qed.
Lemma D_3d100 : decode_any W_3d100 = Some (Op32 ALU_SLL 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d104 : bv 32 := 0x1606a62f.
Lemma F_3d104 : fetch_word Asan.M.loaded_segments (0x3d104 : word) = Some W_3d104.
Proof. vm_refl. Qed.
Lemma D_3d104 : decode_any W_3d104 = Some (Lr AW true true 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d108 : bv 32 := 0x00f678b3.
Lemma F_3d108 : fetch_word Asan.M.loaded_segments (0x3d108 : word) = Some W_3d108.
Proof. vm_refl. Qed.
Lemma D_3d108 : decode_any W_3d108 = Some (Op ALU_AND 17 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d10c : bv 32 := 0x08e89063.
Lemma F_3d10c : fetch_word Asan.M.loaded_segments (0x3d10c : word) = Some W_3d10c.
Proof. vm_refl. Qed.
Lemma D_3d10c : decode_any W_3d10c = Some (Branch BC_NE 17 14 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d110 : bv 32 := 0x010648b3.
Lemma F_3d110 : fetch_word Asan.M.loaded_segments (0x3d110 : word) = Some W_3d110.
Proof. vm_refl. Qed.
Lemma D_3d110 : decode_any W_3d110 = Some (Op ALU_XOR 17 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d114 : bv 32 := 0x00f8f8b3.
Lemma F_3d114 : fetch_word Asan.M.loaded_segments (0x3d114 : word) = Some W_3d114.
Proof. vm_refl. Qed.
Lemma D_3d114 : decode_any W_3d114 = Some (Op ALU_AND 17 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d118 : bv 32 := 0x011648b3.
Lemma F_3d118 : fetch_word Asan.M.loaded_segments (0x3d118 : word) = Some W_3d118.
Proof. vm_refl. Qed.
Lemma D_3d118 : decode_any W_3d118 = Some (Op ALU_XOR 17 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d11c : bv 32 := 0x1b16a8af.
Lemma F_3d11c : fetch_word Asan.M.loaded_segments (0x3d11c : word) = Some W_3d11c.
Proof. vm_refl. Qed.
Lemma D_3d11c : decode_any W_3d11c = Some (Sc AW false true 17 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d120 : bv 32 := 0xfe0892e3.
Lemma F_3d120 : fetch_word Asan.M.loaded_segments (0x3d120 : word) = Some W_3d120.
Proof. vm_refl. Qed.
Lemma D_3d120 : decode_any W_3d120 = Some (Branch BC_NE 17 0 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d124 : bv 32 := 0xfff00513.
Lemma F_3d124 : fetch_word Asan.M.loaded_segments (0x3d124 : word) = Some W_3d124.
Proof. vm_refl. Qed.
Lemma D_3d124 : decode_any W_3d124 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d128 : bv 32 := 0x02051513.
Lemma F_3d128 : fetch_word Asan.M.loaded_segments (0x3d128 : word) = Some W_3d128.
Proof. vm_refl. Qed.
Lemma D_3d128 : decode_any W_3d128 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d12c : bv 32 := 0x00a93823.
Lemma F_3d12c : fetch_word Asan.M.loaded_segments (0x3d12c : word) = Some W_3d12c.
Proof. vm_refl. Qed.
Lemma D_3d12c : decode_any W_3d12c = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d130 : bv 32 := 0x00194503.
Lemma F_3d130 : fetch_word Asan.M.loaded_segments (0x3d130 : word) = Some W_3d130.
Proof. vm_refl. Qed.
Lemma D_3d130 : decode_any W_3d130 = Some (Load SZ1 false 10 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d134 : bv 32 := 0x00357593.
Lemma F_3d134 : fetch_word Asan.M.loaded_segments (0x3d134 : word) = Some W_3d134.
Proof. vm_refl. Qed.
Lemma D_3d134 : decode_any W_3d134 = Some (OpImm ALU_AND 11 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d138 : bv 32 := 0x08ba1863.
Lemma F_3d138 : fetch_word Asan.M.loaded_segments (0x3d138 : word) = Some W_3d138.
Proof. vm_refl. Qed.
Lemma D_3d138 : decode_any W_3d138 = Some (Branch BC_NE 20 11 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d13c : bv 32 := 0xffea7693.
Lemma F_3d13c : fetch_word Asan.M.loaded_segments (0x3d13c : word) = Some W_3d13c.
Proof. vm_refl. Qed.
Lemma D_3d13c : decode_any W_3d13c = Some (OpImm ALU_AND 13 20 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d140 : bv 32 := 0x00200713.
Lemma F_3d140 : fetch_word Asan.M.loaded_segments (0x3d140 : word) = Some W_3d140.
Proof. vm_refl. Qed.
Lemma D_3d140 : decode_any W_3d140 = Some (OpImm ALU_ADD 14 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d144 : bv 32 := 0x14e69663.
Lemma F_3d144 : fetch_word Asan.M.loaded_segments (0x3d144 : word) = Some W_3d144.
Proof. vm_refl. Qed.
Lemma D_3d144 : decode_any W_3d144 = Some (Branch BC_NE 13 14 332, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d148 : bv 32 := 0x00098697.
Lemma F_3d148 : fetch_word Asan.M.loaded_segments (0x3d148 : word) = Some W_3d148.
Proof. vm_refl. Qed.
Lemma D_3d148 : decode_any W_3d148 = Some (Auipc 13 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d14c : bv 32 := 0x7686b683.
Lemma F_3d14c : fetch_word Asan.M.loaded_segments (0x3d14c : word) = Some W_3d14c.
Proof. vm_refl. Qed.
Lemma D_3d14c : decode_any W_3d14c = Some (Load SZ8 true 13 13 1896, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d150 : bv 32 := 0x0586c683.
Lemma F_3d150 : fetch_word Asan.M.loaded_segments (0x3d150 : word) = Some W_3d150.
Proof. vm_refl. Qed.
Lemma D_3d150 : decode_any W_3d150 = Some (Load SZ1 false 13 13 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d154 : bv 32 := 0x0016f693.
Lemma F_3d154 : fetch_word Asan.M.loaded_segments (0x3d154 : word) = Some W_3d154.
Proof. vm_refl. Qed.
Lemma D_3d154 : decode_any W_3d154 = Some (OpImm ALU_AND 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d158 : bv 32 := 0x12068c63.
Lemma F_3d158 : fetch_word Asan.M.loaded_segments (0x3d158 : word) = Some W_3d158.
Proof. vm_refl. Qed.
Lemma D_3d158 : decode_any W_3d158 = Some (Branch BC_EQ 13 0 312, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d15c : bv 32 := 0x000b0613.
Lemma F_3d15c : fetch_word Asan.M.loaded_segments (0x3d15c : word) = Some W_3d15c.
Proof. vm_refl. Qed.
Lemma D_3d15c : decode_any W_3d15c = Some (OpImm ALU_ADD 12 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d160 : bv 32 := 0x000a8593.
Lemma F_3d160 : fetch_word Asan.M.loaded_segments (0x3d160 : word) = Some W_3d160.
Proof. vm_refl. Qed.
Lemma D_3d160 : decode_any W_3d160 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d164 : bv 32 := 0x000a8c63.
Lemma F_3d164 : fetch_word Asan.M.loaded_segments (0x3d164 : word) = Some W_3d164.
Proof. vm_refl. Qed.
Lemma D_3d164 : decode_any W_3d164 = Some (Branch BC_EQ 21 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d168 : bv 32 := 0x00295683.
Lemma F_3d168 : fetch_word Asan.M.loaded_segments (0x3d168 : word) = Some W_3d168.
Proof. vm_refl. Qed.
Lemma D_3d168 : decode_any W_3d168 = Some (Load SZ2 false 13 18 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d16c : bv 32 := 0x00496703.
Lemma F_3d16c : fetch_word Asan.M.loaded_segments (0x3d16c : word) = Some W_3d16c.
Proof. vm_refl. Qed.
Lemma D_3d16c : decode_any W_3d16c = Some (Load SZ4 false 14 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d170 : bv 32 := 0x02069693.
Lemma F_3d170 : fetch_word Asan.M.loaded_segments (0x3d170 : word) = Some W_3d170.
Proof. vm_refl. Qed.
Lemma D_3d170 : decode_any W_3d170 = Some (ShiftImm ALU_SLL 13 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d174 : bv 32 := 0x00e6e6b3.
Lemma F_3d174 : fetch_word Asan.M.loaded_segments (0x3d174 : word) = Some W_3d174.
Proof. vm_refl. Qed.
Lemma D_3d174 : decode_any W_3d174 = Some (Op ALU_OR 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d178 : bv 32 := 0x10d59663.
Lemma F_3d178 : fetch_word Asan.M.loaded_segments (0x3d178 : word) = Some W_3d178.
Proof. vm_refl. Qed.
Lemma D_3d178 : decode_any W_3d178 = Some (Branch BC_NE 11 13 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d17c : bv 32 := 0x00800693.
Lemma F_3d17c : fetch_word Asan.M.loaded_segments (0x3d17c : word) = Some W_3d17c.
Proof. vm_refl. Qed.
Lemma D_3d17c : decode_any W_3d17c = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d180 : bv 32 := 0x0ad67863.
Lemma F_3d180 : fetch_word Asan.M.loaded_segments (0x3d180 : word) = Some W_3d180.
Proof. vm_refl. Qed.
Lemma D_3d180 : decode_any W_3d180 = Some (Branch BC_GEU 12 13 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d184 : bv 32 := 0x00000693.
Lemma F_3d184 : fetch_word Asan.M.loaded_segments (0x3d184 : word) = Some W_3d184.
Proof. vm_refl. Qed.
Lemma D_3d184 : decode_any W_3d184 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d188 : bv 32 := 0x0f00006f.
Lemma F_3d188 : fetch_word Asan.M.loaded_segments (0x3d188 : word) = Some W_3d188.
Proof. vm_refl. Qed.
Lemma D_3d188 : decode_any W_3d188 = Some (Jal 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d18c : bv 32 := 0x00a6553b.
Lemma F_3d18c : fetch_word Asan.M.loaded_segments (0x3d18c : word) = Some W_3d18c.
Proof. vm_refl. Qed.
Lemma D_3d18c : decode_any W_3d18c = Some (Op32 ALU_SRL 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d190 : bv 32 := 0x0ff57513.
Lemma F_3d190 : fetch_word Asan.M.loaded_segments (0x3d190 : word) = Some W_3d190.
Proof. vm_refl. Qed.
Lemma D_3d190 : decode_any W_3d190 = Some (OpImm ALU_AND 10 10 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d194 : bv 32 := 0x06b51663.
Lemma F_3d194 : fetch_word Asan.M.loaded_segments (0x3d194 : word) = Some W_3d194.
Proof. vm_refl. Qed.
Lemma D_3d194 : decode_any W_3d194 = Some (Branch BC_NE 10 11 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d198 : bv 32 := 0x00048513.
Lemma F_3d198 : fetch_word Asan.M.loaded_segments (0x3d198 : word) = Some W_3d198.
Proof. vm_refl. Qed.
Lemma D_3d198 : decode_any W_3d198 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d19c : bv 32 := 0x00040593.
Lemma F_3d19c : fetch_word Asan.M.loaded_segments (0x3d19c : word) = Some W_3d19c.
Proof. vm_refl. Qed.
Lemma D_3d19c : decode_any W_3d19c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1a0 : bv 32 := 0x03813083.
Lemma F_3d1a0 : fetch_word Asan.M.loaded_segments (0x3d1a0 : word) = Some W_3d1a0.
Proof. vm_refl. Qed.
Lemma D_3d1a0 : decode_any W_3d1a0 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1a4 : bv 32 := 0x03013403.
Lemma F_3d1a4 : fetch_word Asan.M.loaded_segments (0x3d1a4 : word) = Some W_3d1a4.
Proof. vm_refl. Qed.
Lemma D_3d1a4 : decode_any W_3d1a4 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1a8 : bv 32 := 0x02813483.
Lemma F_3d1a8 : fetch_word Asan.M.loaded_segments (0x3d1a8 : word) = Some W_3d1a8.
Proof. vm_refl. Qed.
Lemma D_3d1a8 : decode_any W_3d1a8 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1ac : bv 32 := 0x02013903.
Lemma F_3d1ac : fetch_word Asan.M.loaded_segments (0x3d1ac : word) = Some W_3d1ac.
Proof. vm_refl. Qed.
Lemma D_3d1ac : decode_any W_3d1ac = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1b0 : bv 32 := 0x01813983.
Lemma F_3d1b0 : fetch_word Asan.M.loaded_segments (0x3d1b0 : word) = Some W_3d1b0.
Proof. vm_refl. Qed.
Lemma D_3d1b0 : decode_any W_3d1b0 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1b4 : bv 32 := 0x01013a03.
Lemma F_3d1b4 : fetch_word Asan.M.loaded_segments (0x3d1b4 : word) = Some W_3d1b4.
Proof. vm_refl. Qed.
Lemma D_3d1b4 : decode_any W_3d1b4 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1b8 : bv 32 := 0x00813a83.
Lemma F_3d1b8 : fetch_word Asan.M.loaded_segments (0x3d1b8 : word) = Some W_3d1b8.
Proof. vm_refl. Qed.
Lemma D_3d1b8 : decode_any W_3d1b8 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1bc : bv 32 := 0x00013b03.
Lemma F_3d1bc : fetch_word Asan.M.loaded_segments (0x3d1bc : word) = Some W_3d1bc.
Proof. vm_refl. Qed.
Lemma D_3d1bc : decode_any W_3d1bc = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1c0 : bv 32 := 0x04010113.
Lemma F_3d1c0 : fetch_word Asan.M.loaded_segments (0x3d1c0 : word) = Some W_3d1c0.
Proof. vm_refl. Qed.
Lemma D_3d1c0 : decode_any W_3d1c0 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1c4 : bv 32 := 0x10c2606f.
Lemma F_3d1c4 : fetch_word Asan.M.loaded_segments (0x3d1c4 : word) = Some W_3d1c4.
Proof. vm_refl. Qed.
Lemma D_3d1c4 : decode_any W_3d1c4 = Some (Jal 0 155916, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1c8 : bv 32 := 0x7ff98513.
Lemma F_3d1c8 : fetch_word Asan.M.loaded_segments (0x3d1c8 : word) = Some W_3d1c8.
Proof. vm_refl. Qed.
Lemma D_3d1c8 : decode_any W_3d1c8 = Some (OpImm ALU_ADD 10 19 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1cc : bv 32 := 0x62d50503.
Lemma F_3d1cc : fetch_word Asan.M.loaded_segments (0x3d1cc : word) = Some W_3d1cc.
Proof. vm_refl. Qed.
Lemma D_3d1cc : decode_any W_3d1cc = Some (Load SZ1 true 10 10 1581, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1d0 : bv 32 := 0x0230000f.
Lemma F_3d1d0 : fetch_word Asan.M.loaded_segments (0x3d1d0 : word) = Some W_3d1d0.
Proof. vm_refl. Qed.
Lemma D_3d1d0 : decode_any W_3d1d0 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1d4 : bv 32 := 0x0a050e63.
Lemma F_3d1d4 : fetch_word Asan.M.loaded_segments (0x3d1d4 : word) = Some W_3d1d4.
Proof. vm_refl. Qed.
Lemma D_3d1d4 : decode_any W_3d1d4 = Some (Branch BC_EQ 10 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1d8 : bv 32 := 0x00040513.
Lemma F_3d1d8 : fetch_word Asan.M.loaded_segments (0x3d1d8 : word) = Some W_3d1d8.
Proof. vm_refl. Qed.
Lemma D_3d1d8 : decode_any W_3d1d8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1dc : bv 32 := 0x5e12b0ef.
Lemma F_3d1dc : fetch_word Asan.M.loaded_segments (0x3d1dc : word) = Some W_3d1dc.
Proof. vm_refl. Qed.
Lemma D_3d1dc : decode_any W_3d1dc = Some (Jal 1 179680, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1e0 : bv 32 := 0x0a051863.
Lemma F_3d1e0 : fetch_word Asan.M.loaded_segments (0x3d1e0 : word) = Some W_3d1e0.
Proof. vm_refl. Qed.
Lemma D_3d1e0 : decode_any W_3d1e0 = Some (Branch BC_NE 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1e4 : bv 32 := 0xff14c603.
Lemma F_3d1e4 : fetch_word Asan.M.loaded_segments (0x3d1e4 : word) = Some W_3d1e4.
Proof. vm_refl. Qed.
Lemma D_3d1e4 : decode_any W_3d1e4 = Some (Load SZ1 false 12 9 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1e8 : bv 32 := 0x00367613.
Lemma F_3d1e8 : fetch_word Asan.M.loaded_segments (0x3d1e8 : word) = Some W_3d1e8.
Proof. vm_refl. Qed.
Lemma D_3d1e8 : decode_any W_3d1e8 = Some (OpImm ALU_AND 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1ec : bv 32 := 0x00048513.
Lemma F_3d1ec : fetch_word Asan.M.loaded_segments (0x3d1ec : word) = Some W_3d1ec.
Proof. vm_refl. Qed.
Lemma D_3d1ec : decode_any W_3d1ec = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1f0 : bv 32 := 0x00040593.
Lemma F_3d1f0 : fetch_word Asan.M.loaded_segments (0x3d1f0 : word) = Some W_3d1f0.
Proof. vm_refl. Qed.
Lemma D_3d1f0 : decode_any W_3d1f0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1f4 : bv 32 := 0x000a0693.
Lemma F_3d1f4 : fetch_word Asan.M.loaded_segments (0x3d1f4 : word) = Some W_3d1f4.
Proof. vm_refl. Qed.
Lemma D_3d1f4 : decode_any W_3d1f4 = Some (OpImm ALU_ADD 13 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1f8 : bv 32 := 0x051260ef.
Lemma F_3d1f8 : fetch_word Asan.M.loaded_segments (0x3d1f8 : word) = Some W_3d1f8.
Proof. vm_refl. Qed.
Lemma D_3d1f8 : decode_any W_3d1f8 = Some (Jal 1 157776, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d1fc : bv 32 := 0x0940006f.
Lemma F_3d1fc : fetch_word Asan.M.loaded_segments (0x3d1fc : word) = Some W_3d1fc.
Proof. vm_refl. Qed.
Lemma D_3d1fc : decode_any W_3d1fc = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d200 : bv 32 := 0x00048513.
Lemma F_3d200 : fetch_word Asan.M.loaded_segments (0x3d200 : word) = Some W_3d200.
Proof. vm_refl. Qed.
Lemma D_3d200 : decode_any W_3d200 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d204 : bv 32 := 0x00040593.
Lemma F_3d204 : fetch_word Asan.M.loaded_segments (0x3d204 : word) = Some W_3d204.
Proof. vm_refl. Qed.
Lemma D_3d204 : decode_any W_3d204 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d208 : bv 32 := 0x03813083.
Lemma F_3d208 : fetch_word Asan.M.loaded_segments (0x3d208 : word) = Some W_3d208.
Proof. vm_refl. Qed.
Lemma D_3d208 : decode_any W_3d208 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d20c : bv 32 := 0x03013403.
Lemma F_3d20c : fetch_word Asan.M.loaded_segments (0x3d20c : word) = Some W_3d20c.
Proof. vm_refl. Qed.
Lemma D_3d20c : decode_any W_3d20c = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d210 : bv 32 := 0x02813483.
Lemma F_3d210 : fetch_word Asan.M.loaded_segments (0x3d210 : word) = Some W_3d210.
Proof. vm_refl. Qed.
Lemma D_3d210 : decode_any W_3d210 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d214 : bv 32 := 0x02013903.
Lemma F_3d214 : fetch_word Asan.M.loaded_segments (0x3d214 : word) = Some W_3d214.
Proof. vm_refl. Qed.
Lemma D_3d214 : decode_any W_3d214 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d218 : bv 32 := 0x01813983.
Lemma F_3d218 : fetch_word Asan.M.loaded_segments (0x3d218 : word) = Some W_3d218.
Proof. vm_refl. Qed.
Lemma D_3d218 : decode_any W_3d218 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d21c : bv 32 := 0x01013a03.
Lemma F_3d21c : fetch_word Asan.M.loaded_segments (0x3d21c : word) = Some W_3d21c.
Proof. vm_refl. Qed.
Lemma D_3d21c : decode_any W_3d21c = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d220 : bv 32 := 0x00813a83.
Lemma F_3d220 : fetch_word Asan.M.loaded_segments (0x3d220 : word) = Some W_3d220.
Proof. vm_refl. Qed.
Lemma D_3d220 : decode_any W_3d220 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d224 : bv 32 := 0x00013b03.
Lemma F_3d224 : fetch_word Asan.M.loaded_segments (0x3d224 : word) = Some W_3d224.
Proof. vm_refl. Qed.
Lemma D_3d224 : decode_any W_3d224 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d228 : bv 32 := 0x04010113.
Lemma F_3d228 : fetch_word Asan.M.loaded_segments (0x3d228 : word) = Some W_3d228.
Proof. vm_refl. Qed.
Lemma D_3d228 : decode_any W_3d228 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d22c : bv 32 := 0x5b02606f.
Lemma F_3d22c : fetch_word Asan.M.loaded_segments (0x3d22c : word) = Some W_3d22c.
Proof. vm_refl. Qed.
Lemma D_3d22c : decode_any W_3d22c = Some (Jal 0 157104, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d230 : bv 32 := 0x20000713.
Lemma F_3d230 : fetch_word Asan.M.loaded_segments (0x3d230 : word) = Some W_3d230.
Proof. vm_refl. Qed.
Lemma D_3d230 : decode_any W_3d230 = Some (OpImm ALU_ADD 14 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d234 : bv 32 := 0x00060693.
Lemma F_3d234 : fetch_word Asan.M.loaded_segments (0x3d234 : word) = Some W_3d234.
Proof. vm_refl. Qed.
Lemma D_3d234 : decode_any W_3d234 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d238 : bv 32 := 0x00e66463.
Lemma F_3d238 : fetch_word Asan.M.loaded_segments (0x3d238 : word) = Some W_3d238.
Proof. vm_refl. Qed.
Lemma D_3d238 : decode_any W_3d238 = Some (Branch BC_LTU 12 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d23c : bv 32 := 0x20000693.
Lemma F_3d23c : fetch_word Asan.M.loaded_segments (0x3d23c : word) = Some W_3d23c.
Proof. vm_refl. Qed.
Lemma D_3d23c : decode_any W_3d23c = Some (OpImm ALU_ADD 13 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d240 : bv 32 := 0xfff68713.
Lemma F_3d240 : fetch_word Asan.M.loaded_segments (0x3d240 : word) = Some W_3d240.
Proof. vm_refl. Qed.
Lemma D_3d240 : decode_any W_3d240 = Some (OpImm ALU_ADD 14 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d244 : bv 32 := 0x00e6f733.
Lemma F_3d244 : fetch_word Asan.M.loaded_segments (0x3d244 : word) = Some W_3d244.
Proof. vm_refl. Qed.
Lemma D_3d244 : decode_any W_3d244 = Some (Op ALU_AND 14 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d248 : bv 32 := 0x0a071663.
Lemma F_3d248 : fetch_word Asan.M.loaded_segments (0x3d248 : word) = Some W_3d248.
Proof. vm_refl. Qed.
Lemma D_3d248 : decode_any W_3d248 = Some (Branch BC_NE 14 0 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d24c : bv 32 := 0xfffd3717.
Lemma F_3d24c : fetch_word Asan.M.loaded_segments (0x3d24c : word) = Some W_3d24c.
Proof. vm_refl. Qed.
Lemma D_3d24c : decode_any W_3d24c = Some (Auipc 14 1048531, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d250 : bv 32 := 0x19c73703.
Lemma F_3d250 : fetch_word Asan.M.loaded_segments (0x3d250 : word) = Some W_3d250.
Proof. vm_refl. Qed.
Lemma D_3d250 : decode_any W_3d250 = Some (Load SZ8 true 14 14 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d254 : bv 32 := 0x40d007b3.
Lemma F_3d254 : fetch_word Asan.M.loaded_segments (0x3d254 : word) = Some W_3d254.
Proof. vm_refl. Qed.
Lemma D_3d254 : decode_any W_3d254 = Some (Op ALU_SUB 15 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d258 : bv 32 := 0x00f6f6b3.
Lemma F_3d258 : fetch_word Asan.M.loaded_segments (0x3d258 : word) = Some W_3d258.
Proof. vm_refl. Qed.
Lemma D_3d258 : decode_any W_3d258 = Some (Op ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d25c : bv 32 := 0x02e686b3.
Lemma F_3d25c : fetch_word Asan.M.loaded_segments (0x3d25c : word) = Some W_3d25c.
Proof. vm_refl. Qed.
Lemma D_3d25c : decode_any W_3d25c = Some (Mul M_MUL 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d260 : bv 32 := 0xfffd3717.
Lemma F_3d260 : fetch_word Asan.M.loaded_segments (0x3d260 : word) = Some W_3d260.
Proof. vm_refl. Qed.
Lemma D_3d260 : decode_any W_3d260 = Some (Auipc 14 1048531, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d264 : bv 32 := 0x03a6d693.
Lemma F_3d264 : fetch_word Asan.M.loaded_segments (0x3d264 : word) = Some W_3d264.
Proof. vm_refl. Qed.
Lemma D_3d264 : decode_any W_3d264 = Some (ShiftImm ALU_SRL 13 13 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d268 : bv 32 := 0x1b870713.
Lemma F_3d268 : fetch_word Asan.M.loaded_segments (0x3d268 : word) = Some W_3d268.
Proof. vm_refl. Qed.
Lemma D_3d268 : decode_any W_3d268 = Some (OpImm ALU_ADD 14 14 440, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d26c : bv 32 := 0x00d706b3.
Lemma F_3d26c : fetch_word Asan.M.loaded_segments (0x3d26c : word) = Some W_3d26c.
Proof. vm_refl. Qed.
Lemma D_3d26c : decode_any W_3d26c = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d270 : bv 32 := 0x0006c683.
Lemma F_3d270 : fetch_word Asan.M.loaded_segments (0x3d270 : word) = Some W_3d270.
Proof. vm_refl. Qed.
Lemma D_3d270 : decode_any W_3d270 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d274 : bv 32 := 0xffe68693.
Lemma F_3d274 : fetch_word Asan.M.loaded_segments (0x3d274 : word) = Some W_3d274.
Proof. vm_refl. Qed.
Lemma D_3d274 : decode_any W_3d274 = Some (OpImm ALU_ADD 13 13 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d278 : bv 32 := 0x03951513.
Lemma F_3d278 : fetch_word Asan.M.loaded_segments (0x3d278 : word) = Some W_3d278.
Proof. vm_refl. Qed.
Lemma D_3d278 : decode_any W_3d278 = Some (ShiftImm ALU_SLL 10 10 57, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d27c : bv 32 := 0x03d55513.
Lemma F_3d27c : fetch_word Asan.M.loaded_segments (0x3d27c : word) = Some W_3d27c.
Proof. vm_refl. Qed.
Lemma D_3d27c : decode_any W_3d27c = Some (ShiftImm ALU_SRL 10 10 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d280 : bv 32 := 0x00a68863.
Lemma F_3d280 : fetch_word Asan.M.loaded_segments (0x3d280 : word) = Some W_3d280.
Proof. vm_refl. Qed.
Lemma D_3d280 : decode_any W_3d280 = Some (Branch BC_EQ 13 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d284 : bv 32 := 0x00048513.
Lemma F_3d284 : fetch_word Asan.M.loaded_segments (0x3d284 : word) = Some W_3d284.
Proof. vm_refl. Qed.
Lemma D_3d284 : decode_any W_3d284 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d288 : bv 32 := 0x00040693.
Lemma F_3d288 : fetch_word Asan.M.loaded_segments (0x3d288 : word) = Some W_3d288.
Proof. vm_refl. Qed.
Lemma D_3d288 : decode_any W_3d288 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d28c : bv 32 := 0x2d4260ef.
Lemma F_3d28c : fetch_word Asan.M.loaded_segments (0x3d28c : word) = Some W_3d28c.
Proof. vm_refl. Qed.
Lemma D_3d28c : decode_any W_3d28c = Some (Jal 1 156372, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d290 : bv 32 := 0x7202b0ef.
Lemma F_3d290 : fetch_word Asan.M.loaded_segments (0x3d290 : word) = Some W_3d290.
Proof. vm_refl. Qed.
Lemma D_3d290 : decode_any W_3d290 = Some (Jal 1 177952, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d294 : bv 32 := 0xff24d583.
Lemma F_3d294 : fetch_word Asan.M.loaded_segments (0x3d294 : word) = Some W_3d294.
Proof. vm_refl. Qed.
Lemma D_3d294 : decode_any W_3d294 = Some (Load SZ2 false 11 9 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d298 : bv 32 := 0xff44e603.
Lemma F_3d298 : fetch_word Asan.M.loaded_segments (0x3d298 : word) = Some W_3d298.
Proof. vm_refl. Qed.
Lemma D_3d298 : decode_any W_3d298 = Some (Load SZ4 false 12 9 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d29c : bv 32 := 0x02053683.
Lemma F_3d29c : fetch_word Asan.M.loaded_segments (0x3d29c : word) = Some W_3d29c.
Proof. vm_refl. Qed.
Lemma D_3d29c : decode_any W_3d29c = Some (Load SZ8 true 13 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2a0 : bv 32 := 0x01853703.
Lemma F_3d2a0 : fetch_word Asan.M.loaded_segments (0x3d2a0 : word) = Some W_3d2a0.
Proof. vm_refl. Qed.
Lemma D_3d2a0 : decode_any W_3d2a0 = Some (Load SZ8 true 14 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2a4 : bv 32 := 0x02059593.
Lemma F_3d2a4 : fetch_word Asan.M.loaded_segments (0x3d2a4 : word) = Some W_3d2a4.
Proof. vm_refl. Qed.
Lemma D_3d2a4 : decode_any W_3d2a4 = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2a8 : bv 32 := 0x00c5e5b3.
Lemma F_3d2a8 : fetch_word Asan.M.loaded_segments (0x3d2a8 : word) = Some W_3d2a8.
Proof. vm_refl. Qed.
Lemma D_3d2a8 : decode_any W_3d2a8 = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2ac : bv 32 := 0x00d585b3.
Lemma F_3d2ac : fetch_word Asan.M.loaded_segments (0x3d2ac : word) = Some W_3d2ac.
Proof. vm_refl. Qed.
Lemma D_3d2ac : decode_any W_3d2ac = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2b0 : bv 32 := 0x00170713.
Lemma F_3d2b0 : fetch_word Asan.M.loaded_segments (0x3d2b0 : word) = Some W_3d2b0.
Proof. vm_refl. Qed.
Lemma D_3d2b0 : decode_any W_3d2b0 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2b4 : bv 32 := 0x00e53c23.
Lemma F_3d2b4 : fetch_word Asan.M.loaded_segments (0x3d2b4 : word) = Some W_3d2b4.
Proof. vm_refl. Qed.
Lemma D_3d2b4 : decode_any W_3d2b4 = Some (Store SZ8 10 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2b8 : bv 32 := 0x02b53023.
Lemma F_3d2b8 : fetch_word Asan.M.loaded_segments (0x3d2b8 : word) = Some W_3d2b8.
Proof. vm_refl. Qed.
Lemma D_3d2b8 : decode_any W_3d2b8 = Some (Store SZ8 10 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2bc : bv 32 := 0x00098513.
Lemma F_3d2bc : fetch_word Asan.M.loaded_segments (0x3d2bc : word) = Some W_3d2bc.
Proof. vm_refl. Qed.
Lemma D_3d2bc : decode_any W_3d2bc = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2c0 : bv 32 := 0x00090593.
Lemma F_3d2c0 : fetch_word Asan.M.loaded_segments (0x3d2c0 : word) = Some W_3d2c0.
Proof. vm_refl. Qed.
Lemma D_3d2c0 : decode_any W_3d2c0 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2c4 : bv 32 := 0x00048613.
Lemma F_3d2c4 : fetch_word Asan.M.loaded_segments (0x3d2c4 : word) = Some W_3d2c4.
Proof. vm_refl. Qed.
Lemma D_3d2c4 : decode_any W_3d2c4 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2c8 : bv 32 := 0x00040693.
Lemma F_3d2c8 : fetch_word Asan.M.loaded_segments (0x3d2c8 : word) = Some W_3d2c8.
Proof. vm_refl. Qed.
Lemma D_3d2c8 : decode_any W_3d2c8 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2cc : bv 32 := 0x03813083.
Lemma F_3d2cc : fetch_word Asan.M.loaded_segments (0x3d2cc : word) = Some W_3d2cc.
Proof. vm_refl. Qed.
Lemma D_3d2cc : decode_any W_3d2cc = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2d0 : bv 32 := 0x03013403.
Lemma F_3d2d0 : fetch_word Asan.M.loaded_segments (0x3d2d0 : word) = Some W_3d2d0.
Proof. vm_refl. Qed.
Lemma D_3d2d0 : decode_any W_3d2d0 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2d4 : bv 32 := 0x02813483.
Lemma F_3d2d4 : fetch_word Asan.M.loaded_segments (0x3d2d4 : word) = Some W_3d2d4.
Proof. vm_refl. Qed.
Lemma D_3d2d4 : decode_any W_3d2d4 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2d8 : bv 32 := 0x02013903.
Lemma F_3d2d8 : fetch_word Asan.M.loaded_segments (0x3d2d8 : word) = Some W_3d2d8.
Proof. vm_refl. Qed.
Lemma D_3d2d8 : decode_any W_3d2d8 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2dc : bv 32 := 0x01813983.
Lemma F_3d2dc : fetch_word Asan.M.loaded_segments (0x3d2dc : word) = Some W_3d2dc.
Proof. vm_refl. Qed.
Lemma D_3d2dc : decode_any W_3d2dc = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2e0 : bv 32 := 0x01013a03.
Lemma F_3d2e0 : fetch_word Asan.M.loaded_segments (0x3d2e0 : word) = Some W_3d2e0.
Proof. vm_refl. Qed.
Lemma D_3d2e0 : decode_any W_3d2e0 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2e4 : bv 32 := 0x00813a83.
Lemma F_3d2e4 : fetch_word Asan.M.loaded_segments (0x3d2e4 : word) = Some W_3d2e4.
Proof. vm_refl. Qed.
Lemma D_3d2e4 : decode_any W_3d2e4 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2e8 : bv 32 := 0x00013b03.
Lemma F_3d2e8 : fetch_word Asan.M.loaded_segments (0x3d2e8 : word) = Some W_3d2e8.
Proof. vm_refl. Qed.
Lemma D_3d2e8 : decode_any W_3d2e8 = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2ec : bv 32 := 0x04010113.
Lemma F_3d2ec : fetch_word Asan.M.loaded_segments (0x3d2ec : word) = Some W_3d2ec.
Proof. vm_refl. Qed.
Lemma D_3d2ec : decode_any W_3d2ec = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2f0 : bv 32 := 0x2cc0406f.
Lemma F_3d2f0 : fetch_word Asan.M.loaded_segments (0x3d2f0 : word) = Some W_3d2f0.
Proof. vm_refl. Qed.
Lemma D_3d2f0 : decode_any W_3d2f0 = Some (Jal 0 17100, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2f4 : bv 32 := 0xfffe2517.
Lemma F_3d2f4 : fetch_word Asan.M.loaded_segments (0x3d2f4 : word) = Some W_3d2f4.
Proof. vm_refl. Qed.
Lemma D_3d2f4 : decode_any W_3d2f4 = Some (Auipc 10 1048546, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2f8 : bv 32 := 0xfffd7597.
Lemma F_3d2f8 : fetch_word Asan.M.loaded_segments (0x3d2f8 : word) = Some W_3d2f8.
Proof. vm_refl. Qed.
Lemma D_3d2f8 : decode_any W_3d2f8 = Some (Auipc 11 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d2fc : bv 32 := 0x1a350513.
Lemma F_3d2fc : fetch_word Asan.M.loaded_segments (0x3d2fc : word) = Some W_3d2fc.
Proof. vm_refl. Qed.
Lemma D_3d2fc : decode_any W_3d2fc = Some (OpImm ALU_ADD 10 10 419, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d300 : bv 32 := 0x01e58613.
Lemma F_3d300 : fetch_word Asan.M.loaded_segments (0x3d300 : word) = Some W_3d300.
Proof. vm_refl. Qed.
Lemma D_3d300 : decode_any W_3d300 = Some (OpImm ALU_ADD 12 11 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d304 : bv 32 := 0x1e300593.
Lemma F_3d304 : fetch_word Asan.M.loaded_segments (0x3d304 : word) = Some W_3d304.
Proof. vm_refl. Qed.
Lemma D_3d304 : decode_any W_3d304 = Some (OpImm ALU_ADD 11 0 483, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d308 : bv 32 := 0x00000693.
Lemma F_3d308 : fetch_word Asan.M.loaded_segments (0x3d308 : word) = Some W_3d308.
Proof. vm_refl. Qed.
Lemma D_3d308 : decode_any W_3d308 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d30c : bv 32 := 0x00000713.
Lemma F_3d30c : fetch_word Asan.M.loaded_segments (0x3d30c : word) = Some W_3d30c.
Proof. vm_refl. Qed.
Lemma D_3d30c : decode_any W_3d30c = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d310 : bv 32 := 0x5593b0ef.
Lemma F_3d310 : fetch_word Asan.M.loaded_segments (0x3d310 : word) = Some W_3d310.
Proof. vm_refl. Qed.
Lemma D_3d310 : decode_any W_3d310 = Some (Jal 1 245080, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d314 : bv 32 := 0xff010113.
Lemma F_3d314 : fetch_word Asan.M.loaded_segments (0x3d314 : word) = Some W_3d314.
Proof. vm_refl. Qed.
Lemma D_3d314 : decode_any W_3d314 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d318 : bv 32 := 0x00113423.
Lemma F_3d318 : fetch_word Asan.M.loaded_segments (0x3d318 : word) = Some W_3d318.
Proof. vm_refl. Qed.
Lemma D_3d318 : decode_any W_3d318 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d31c : bv 32 := 0x00813023.
Lemma F_3d31c : fetch_word Asan.M.loaded_segments (0x3d31c : word) = Some W_3d31c.
Proof. vm_refl. Qed.
Lemma D_3d31c : decode_any W_3d31c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d320 : bv 32 := 0x00058693.
Lemma F_3d320 : fetch_word Asan.M.loaded_segments (0x3d320 : word) = Some W_3d320.
Proof. vm_refl. Qed.
Lemma D_3d320 : decode_any W_3d320 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d324 : bv 32 := 0x00050593.
Lemma F_3d324 : fetch_word Asan.M.loaded_segments (0x3d324 : word) = Some W_3d324.
Proof. vm_refl. Qed.
Lemma D_3d324 : decode_any W_3d324 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d328 : bv 32 := 0x0009d517.
Lemma F_3d328 : fetch_word Asan.M.loaded_segments (0x3d328 : word) = Some W_3d328.
Proof. vm_refl. Qed.
Lemma D_3d328 : decode_any W_3d328 = Some (Auipc 10 157, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d32c : bv 32 := 0x00800613.
Lemma F_3d32c : fetch_word Asan.M.loaded_segments (0x3d32c : word) = Some W_3d32c.
Proof. vm_refl. Qed.
Lemma D_3d32c : decode_any W_3d32c = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d330 : bv 32 := 0x00100713.
Lemma F_3d330 : fetch_word Asan.M.loaded_segments (0x3d330 : word) = Some W_3d330.
Proof. vm_refl. Qed.
Lemma D_3d330 : decode_any W_3d330 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d334 : bv 32 := 0x1b050513.
Lemma F_3d334 : fetch_word Asan.M.loaded_segments (0x3d334 : word) = Some W_3d334.
Proof. vm_refl. Qed.
Lemma D_3d334 : decode_any W_3d334 = Some (OpImm ALU_ADD 10 10 432, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d338 : bv 32 := 0x00100793.
Lemma F_3d338 : fetch_word Asan.M.loaded_segments (0x3d338 : word) = Some W_3d338.
Proof. vm_refl. Qed.
Lemma D_3d338 : decode_any W_3d338 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d33c : bv 32 := 0x034000ef.
Lemma F_3d33c : fetch_word Asan.M.loaded_segments (0x3d33c : word) = Some W_3d33c.
Proof. vm_refl. Qed.
Lemma D_3d33c : decode_any W_3d33c = Some (Jal 1 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d340 : bv 32 := 0x00050a63.
Lemma F_3d340 : fetch_word Asan.M.loaded_segments (0x3d340 : word) = Some W_3d340.
Proof. vm_refl. Qed.
Lemma D_3d340 : decode_any W_3d340 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d344 : bv 32 := 0x00813083.
Lemma F_3d344 : fetch_word Asan.M.loaded_segments (0x3d344 : word) = Some W_3d344.
Proof. vm_refl. Qed.
Lemma D_3d344 : decode_any W_3d344 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d348 : bv 32 := 0x00013403.
Lemma F_3d348 : fetch_word Asan.M.loaded_segments (0x3d348 : word) = Some W_3d348.
Proof. vm_refl. Qed.
Lemma D_3d348 : decode_any W_3d348 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d34c : bv 32 := 0x01010113.
Lemma F_3d34c : fetch_word Asan.M.loaded_segments (0x3d34c : word) = Some W_3d34c.
Proof. vm_refl. Qed.
Lemma D_3d34c : decode_any W_3d34c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d350 : bv 32 := 0x00008067.
Lemma F_3d350 : fetch_word Asan.M.loaded_segments (0x3d350 : word) = Some W_3d350.
Proof. vm_refl. Qed.
Lemma D_3d350 : decode_any W_3d350 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d354 : bv 32 := 0x00050413.
Lemma F_3d354 : fetch_word Asan.M.loaded_segments (0x3d354 : word) = Some W_3d354.
Proof. vm_refl. Qed.
Lemma D_3d354 : decode_any W_3d354 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d358 : bv 32 := 0x0e93c0ef.
Lemma F_3d358 : fetch_word Asan.M.loaded_segments (0x3d358 : word) = Some W_3d358.
Proof. vm_refl. Qed.
Lemma D_3d358 : decode_any W_3d358 = Some (Jal 1 248040, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d35c : bv 32 := 0x00040513.
Lemma F_3d35c : fetch_word Asan.M.loaded_segments (0x3d35c : word) = Some W_3d35c.
Proof. vm_refl. Qed.
Lemma D_3d35c : decode_any W_3d35c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d360 : bv 32 := 0x00813083.
Lemma F_3d360 : fetch_word Asan.M.loaded_segments (0x3d360 : word) = Some W_3d360.
Proof. vm_refl. Qed.
Lemma D_3d360 : decode_any W_3d360 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d364 : bv 32 := 0x00013403.
Lemma F_3d364 : fetch_word Asan.M.loaded_segments (0x3d364 : word) = Some W_3d364.
Proof. vm_refl. Qed.
Lemma D_3d364 : decode_any W_3d364 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d368 : bv 32 := 0x01010113.
Lemma F_3d368 : fetch_word Asan.M.loaded_segments (0x3d368 : word) = Some W_3d368.
Proof. vm_refl. Qed.
Lemma D_3d368 : decode_any W_3d368 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d36c : bv 32 := 0x00008067.
Lemma F_3d36c : fetch_word Asan.M.loaded_segments (0x3d36c : word) = Some W_3d36c.
Proof. vm_refl. Qed.
Lemma D_3d36c : decode_any W_3d36c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d370 : bv 32 := 0xf8010113.
Lemma F_3d370 : fetch_word Asan.M.loaded_segments (0x3d370 : word) = Some W_3d370.
Proof. vm_refl. Qed.
Lemma D_3d370 : decode_any W_3d370 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d374 : bv 32 := 0x06113c23.
Lemma F_3d374 : fetch_word Asan.M.loaded_segments (0x3d374 : word) = Some W_3d374.
Proof. vm_refl. Qed.
Lemma D_3d374 : decode_any W_3d374 = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d378 : bv 32 := 0x06813823.
Lemma F_3d378 : fetch_word Asan.M.loaded_segments (0x3d378 : word) = Some W_3d378.
Proof. vm_refl. Qed.
Lemma D_3d378 : decode_any W_3d378 = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d37c : bv 32 := 0x06913423.
Lemma F_3d37c : fetch_word Asan.M.loaded_segments (0x3d37c : word) = Some W_3d37c.
Proof. vm_refl. Qed.
Lemma D_3d37c : decode_any W_3d37c = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d380 : bv 32 := 0x07213023.
Lemma F_3d380 : fetch_word Asan.M.loaded_segments (0x3d380 : word) = Some W_3d380.
Proof. vm_refl. Qed.
Lemma D_3d380 : decode_any W_3d380 = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d384 : bv 32 := 0x05313c23.
Lemma F_3d384 : fetch_word Asan.M.loaded_segments (0x3d384 : word) = Some W_3d384.
Proof. vm_refl. Qed.
Lemma D_3d384 : decode_any W_3d384 = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d388 : bv 32 := 0x05413823.
Lemma F_3d388 : fetch_word Asan.M.loaded_segments (0x3d388 : word) = Some W_3d388.
Proof. vm_refl. Qed.
Lemma D_3d388 : decode_any W_3d388 = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d38c : bv 32 := 0x05513423.
Lemma F_3d38c : fetch_word Asan.M.loaded_segments (0x3d38c : word) = Some W_3d38c.
Proof. vm_refl. Qed.
Lemma D_3d38c : decode_any W_3d38c = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d390 : bv 32 := 0x05613023.
Lemma F_3d390 : fetch_word Asan.M.loaded_segments (0x3d390 : word) = Some W_3d390.
Proof. vm_refl. Qed.
Lemma D_3d390 : decode_any W_3d390 = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d394 : bv 32 := 0x03713c23.
Lemma F_3d394 : fetch_word Asan.M.loaded_segments (0x3d394 : word) = Some W_3d394.
Proof. vm_refl. Qed.
Lemma D_3d394 : decode_any W_3d394 = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d398 : bv 32 := 0x03813823.
Lemma F_3d398 : fetch_word Asan.M.loaded_segments (0x3d398 : word) = Some W_3d398.
Proof. vm_refl. Qed.
Lemma D_3d398 : decode_any W_3d398 = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d39c : bv 32 := 0x03913423.
Lemma F_3d39c : fetch_word Asan.M.loaded_segments (0x3d39c : word) = Some W_3d39c.
Proof. vm_refl. Qed.
Lemma D_3d39c : decode_any W_3d39c = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3a0 : bv 32 := 0x03a13023.
Lemma F_3d3a0 : fetch_word Asan.M.loaded_segments (0x3d3a0 : word) = Some W_3d3a0.
Proof. vm_refl. Qed.
Lemma D_3d3a0 : decode_any W_3d3a0 = Some (Store SZ8 2 26 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3a4 : bv 32 := 0x01b13c23.
Lemma F_3d3a4 : fetch_word Asan.M.loaded_segments (0x3d3a4 : word) = Some W_3d3a4.
Proof. vm_refl. Qed.
Lemma D_3d3a4 : decode_any W_3d3a4 = Some (Store SZ8 2 27 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3a8 : bv 32 := 0x00078493.
Lemma F_3d3a8 : fetch_word Asan.M.loaded_segments (0x3d3a8 : word) = Some W_3d3a8.
Proof. vm_refl. Qed.
Lemma D_3d3a8 : decode_any W_3d3a8 = Some (OpImm ALU_ADD 9 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3ac : bv 32 := 0x00070d93.
Lemma F_3d3ac : fetch_word Asan.M.loaded_segments (0x3d3ac : word) = Some W_3d3ac.
Proof. vm_refl. Qed.
Lemma D_3d3ac : decode_any W_3d3ac = Some (OpImm ALU_ADD 27 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3b0 : bv 32 := 0x00068b93.
Lemma F_3d3b0 : fetch_word Asan.M.loaded_segments (0x3d3b0 : word) = Some W_3d3b0.
Proof. vm_refl. Qed.
Lemma D_3d3b0 : decode_any W_3d3b0 = Some (OpImm ALU_ADD 23 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3b4 : bv 32 := 0x00060913.
Lemma F_3d3b4 : fetch_word Asan.M.loaded_segments (0x3d3b4 : word) = Some W_3d3b4.
Proof. vm_refl. Qed.
Lemma D_3d3b4 : decode_any W_3d3b4 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3b8 : bv 32 := 0x00058a93.
Lemma F_3d3b8 : fetch_word Asan.M.loaded_segments (0x3d3b8 : word) = Some W_3d3b8.
Proof. vm_refl. Qed.
Lemma D_3d3b8 : decode_any W_3d3b8 = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3bc : bv 32 := 0x00050b13.
Lemma F_3d3bc : fetch_word Asan.M.loaded_segments (0x3d3bc : word) = Some W_3d3bc.
Proof. vm_refl. Qed.
Lemma D_3d3bc : decode_any W_3d3bc = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3c0 : bv 32 := 0x515280ef.
Lemma F_3d3c0 : fetch_word Asan.M.loaded_segments (0x3d3c0 : word) = Some W_3d3c0.
Proof. vm_refl. Qed.
Lemma D_3d3c0 : decode_any W_3d3c0 = Some (Jal 1 167188, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3c4 : bv 32 := 0x7e050463.
Lemma F_3d3c4 : fetch_word Asan.M.loaded_segments (0x3d3c4 : word) = Some W_3d3c4.
Proof. vm_refl. Qed.
Lemma D_3d3c4 : decode_any W_3d3c4 = Some (Branch BC_EQ 10 0 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3c8 : bv 32 := 0x1d52e0ef.
Lemma F_3d3c8 : fetch_word Asan.M.loaded_segments (0x3d3c8 : word) = Some W_3d3c8.
Proof. vm_refl. Qed.
Lemma D_3d3c8 : decode_any W_3d3c8 = Some (Jal 1 190932, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3cc : bv 32 := 0x7e051663.
Lemma F_3d3cc : fetch_word Asan.M.loaded_segments (0x3d3cc : word) = Some W_3d3cc.
Proof. vm_refl. Qed.
Lemma D_3d3cc : decode_any W_3d3cc = Some (Branch BC_NE 10 0 2028, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3d0 : bv 32 := 0x080b86e3.
Lemma F_3d3d0 : fetch_word Asan.M.loaded_segments (0x3d3d0 : word) = Some W_3d3d0.
Proof. vm_refl. Qed.
Lemma D_3d3d0 : decode_any W_3d3d0 = Some (Branch BC_EQ 23 0 2188, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3d4 : bv 32 := 0x00800513.
Lemma F_3d3d4 : fetch_word Asan.M.loaded_segments (0x3d3d4 : word) = Some W_3d3d4.
Proof. vm_refl. Qed.
Lemma D_3d3d4 : decode_any W_3d3d4 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3d8 : bv 32 := 0x02a97e63.
Lemma F_3d3d8 : fetch_word Asan.M.loaded_segments (0x3d3d8 : word) = Some W_3d3d8.
Proof. vm_refl. Qed.
Lemma D_3d3d8 : decode_any W_3d3d8 = Some (Branch BC_GEU 18 10 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3dc : bv 32 := 0x00000593.
Lemma F_3d3dc : fetch_word Asan.M.loaded_segments (0x3d3dc : word) = Some W_3d3dc.
Proof. vm_refl. Qed.
Lemma D_3d3dc : decode_any W_3d3dc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3e0 : bv 32 := 0x00090413.
Lemma F_3d3e0 : fetch_word Asan.M.loaded_segments (0x3d3e0 : word) = Some W_3d3e0.
Proof. vm_refl. Qed.
Lemma D_3d3e0 : decode_any W_3d3e0 = Some (OpImm ALU_ADD 8 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3e4 : bv 32 := 0x01256463.
Lemma F_3d3e4 : fetch_word Asan.M.loaded_segments (0x3d3e4 : word) = Some W_3d3e4.
Proof. vm_refl. Qed.
Lemma D_3d3e4 : decode_any W_3d3e4 = Some (Branch BC_LTU 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3e8 : bv 32 := 0x00800413.
Lemma F_3d3e8 : fetch_word Asan.M.loaded_segments (0x3d3e8 : word) = Some W_3d3e8.
Proof. vm_refl. Qed.
Lemma D_3d3e8 : decode_any W_3d3e8 = Some (OpImm ALU_ADD 8 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3ec : bv 32 := 0xfff40c93.
Lemma F_3d3ec : fetch_word Asan.M.loaded_segments (0x3d3ec : word) = Some W_3d3ec.
Proof. vm_refl. Qed.
Lemma D_3d3ec : decode_any W_3d3ec = Some (OpImm ALU_ADD 25 8 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3f0 : bv 32 := 0x01947533.
Lemma F_3d3f0 : fetch_word Asan.M.loaded_segments (0x3d3f0 : word) = Some W_3d3f0.
Proof. vm_refl. Qed.
Lemma D_3d3f0 : decode_any W_3d3f0 = Some (Op ALU_AND 10 8 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3f4 : bv 32 := 0x7c051a63.
Lemma F_3d3f4 : fetch_word Asan.M.loaded_segments (0x3d3f4 : word) = Some W_3d3f4.
Proof. vm_refl. Qed.
Lemma D_3d3f4 : decode_any W_3d3f4 = Some (Branch BC_NE 10 0 2004, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3f8 : bv 32 := 0x03100513.
Lemma F_3d3f8 : fetch_word Asan.M.loaded_segments (0x3d3f8 : word) = Some W_3d3f8.
Proof. vm_refl. Qed.
Lemma D_3d3f8 : decode_any W_3d3f8 = Some (OpImm ALU_ADD 10 0 49, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d3fc : bv 32 := 0x7ffb0d13.
Lemma F_3d3fc : fetch_word Asan.M.loaded_segments (0x3d3fc : word) = Some W_3d3fc.
Proof. vm_refl. Qed.
Lemma D_3d3fc : decode_any W_3d3fc = Some (OpImm ALU_ADD 26 22 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d400 : bv 32 := 0x00913423.
Lemma F_3d400 : fetch_word Asan.M.loaded_segments (0x3d400 : word) = Some W_3d400.
Proof. vm_refl. Qed.
Lemma D_3d400 : decode_any W_3d400 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d404 : bv 32 := 0x00b13823.
Lemma F_3d404 : fetch_word Asan.M.loaded_segments (0x3d404 : word) = Some W_3d404.
Proof. vm_refl. Qed.
Lemma D_3d404 : decode_any W_3d404 = Some (Store SZ8 2 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d408 : bv 32 := 0x06aaf463.
Lemma F_3d408 : fetch_word Asan.M.loaded_segments (0x3d408 : word) = Some W_3d408.
Proof. vm_refl. Qed.
Lemma D_3d408 : decode_any W_3d408 = Some (Branch BC_GEU 21 10 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d40c : bv 32 := 0x00000993.
Lemma F_3d40c : fetch_word Asan.M.loaded_segments (0x3d40c : word) = Some W_3d40c.
Proof. vm_refl. Qed.
Lemma D_3d40c : decode_any W_3d40c = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d410 : bv 32 := 0x0cc0006f.
Lemma F_3d410 : fetch_word Asan.M.loaded_segments (0x3d410 : word) = Some W_3d410.
Proof. vm_refl. Qed.
Lemma D_3d410 : decode_any W_3d410 = Some (Jal 0 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d414 : bv 32 := 0x20000613.
Lemma F_3d414 : fetch_word Asan.M.loaded_segments (0x3d414 : word) = Some W_3d414.
Proof. vm_refl. Qed.
Lemma D_3d414 : decode_any W_3d414 = Some (OpImm ALU_ADD 12 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d418 : bv 32 := 0x00090593.
Lemma F_3d418 : fetch_word Asan.M.loaded_segments (0x3d418 : word) = Some W_3d418.
Proof. vm_refl. Qed.
Lemma D_3d418 : decode_any W_3d418 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d41c : bv 32 := 0x00c96463.
Lemma F_3d41c : fetch_word Asan.M.loaded_segments (0x3d41c : word) = Some W_3d41c.
Proof. vm_refl. Qed.
Lemma D_3d41c : decode_any W_3d41c = Some (Branch BC_LTU 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d420 : bv 32 := 0x20000593.
Lemma F_3d420 : fetch_word Asan.M.loaded_segments (0x3d420 : word) = Some W_3d420.
Proof. vm_refl. Qed.
Lemma D_3d420 : decode_any W_3d420 = Some (OpImm ALU_ADD 11 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d424 : bv 32 := 0xfff58613.
Lemma F_3d424 : fetch_word Asan.M.loaded_segments (0x3d424 : word) = Some W_3d424.
Proof. vm_refl. Qed.
Lemma D_3d424 : decode_any W_3d424 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d428 : bv 32 := 0x00c5f633.
Lemma F_3d428 : fetch_word Asan.M.loaded_segments (0x3d428 : word) = Some W_3d428.
Proof. vm_refl. Qed.
Lemma D_3d428 : decode_any W_3d428 = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d42c : bv 32 := 0x040618e3.
Lemma F_3d42c : fetch_word Asan.M.loaded_segments (0x3d42c : word) = Some W_3d42c.
Proof. vm_refl. Qed.
Lemma D_3d42c : decode_any W_3d42c = Some (Branch BC_NE 12 0 2128, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d430 : bv 32 := 0xfffd3617.
Lemma F_3d430 : fetch_word Asan.M.loaded_segments (0x3d430 : word) = Some W_3d430.
Proof. vm_refl. Qed.
Lemma D_3d430 : decode_any W_3d430 = Some (Auipc 12 1048531, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d434 : bv 32 := 0xfb863603.
Lemma F_3d434 : fetch_word Asan.M.loaded_segments (0x3d434 : word) = Some W_3d434.
Proof. vm_refl. Qed.
Lemma D_3d434 : decode_any W_3d434 = Some (Load SZ8 true 12 12 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d438 : bv 32 := 0x40b006b3.
Lemma F_3d438 : fetch_word Asan.M.loaded_segments (0x3d438 : word) = Some W_3d438.
Proof. vm_refl. Qed.
Lemma D_3d438 : decode_any W_3d438 = Some (Op ALU_SUB 13 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d43c : bv 32 := 0x00d5f5b3.
Lemma F_3d43c : fetch_word Asan.M.loaded_segments (0x3d43c : word) = Some W_3d43c.
Proof. vm_refl. Qed.
Lemma D_3d43c : decode_any W_3d43c = Some (Op ALU_AND 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d440 : bv 32 := 0x02c585b3.
Lemma F_3d440 : fetch_word Asan.M.loaded_segments (0x3d440 : word) = Some W_3d440.
Proof. vm_refl. Qed.
Lemma D_3d440 : decode_any W_3d440 = Some (Mul M_MUL 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d444 : bv 32 := 0xfffd3617.
Lemma F_3d444 : fetch_word Asan.M.loaded_segments (0x3d444 : word) = Some W_3d444.
Proof. vm_refl. Qed.
Lemma D_3d444 : decode_any W_3d444 = Some (Auipc 12 1048531, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d448 : bv 32 := 0x03a5d593.
Lemma F_3d448 : fetch_word Asan.M.loaded_segments (0x3d448 : word) = Some W_3d448.
Proof. vm_refl. Qed.
Lemma D_3d448 : decode_any W_3d448 = Some (ShiftImm ALU_SRL 11 11 58, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d44c : bv 32 := 0x01460613.
Lemma F_3d44c : fetch_word Asan.M.loaded_segments (0x3d44c : word) = Some W_3d44c.
Proof. vm_refl. Qed.
Lemma D_3d44c : decode_any W_3d44c = Some (OpImm ALU_ADD 12 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d450 : bv 32 := 0x00b605b3.
Lemma F_3d450 : fetch_word Asan.M.loaded_segments (0x3d450 : word) = Some W_3d450.
Proof. vm_refl. Qed.
Lemma D_3d450 : decode_any W_3d450 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d454 : bv 32 := 0x0005c583.
Lemma F_3d454 : fetch_word Asan.M.loaded_segments (0x3d454 : word) = Some W_3d454.
Proof. vm_refl. Qed.
Lemma D_3d454 : decode_any W_3d454 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d458 : bv 32 := 0x00459593.
Lemma F_3d458 : fetch_word Asan.M.loaded_segments (0x3d458 : word) = Some W_3d458.
Proof. vm_refl. Qed.
Lemma D_3d458 : decode_any W_3d458 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d45c : bv 32 := 0x06058593.
Lemma F_3d45c : fetch_word Asan.M.loaded_segments (0x3d45c : word) = Some W_3d45c.
Proof. vm_refl. Qed.
Lemma D_3d45c : decode_any W_3d45c = Some (OpImm ALU_ADD 11 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d460 : bv 32 := 0x0705f593.
Lemma F_3d460 : fetch_word Asan.M.loaded_segments (0x3d460 : word) = Some W_3d460.
Proof. vm_refl. Qed.
Lemma D_3d460 : decode_any W_3d460 = Some (OpImm ALU_AND 11 11 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d464 : bv 32 := 0x00090413.
Lemma F_3d464 : fetch_word Asan.M.loaded_segments (0x3d464 : word) = Some W_3d464.
Proof. vm_refl. Qed.
Lemma D_3d464 : decode_any W_3d464 = Some (OpImm ALU_ADD 8 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d468 : bv 32 := 0xf92570e3.
Lemma F_3d468 : fetch_word Asan.M.loaded_segments (0x3d468 : word) = Some W_3d468.
Proof. vm_refl. Qed.
Lemma D_3d468 : decode_any W_3d468 = Some (Branch BC_GEU 10 18 8064, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d46c : bv 32 := 0xf81ff06f.
Lemma F_3d46c : fetch_word Asan.M.loaded_segments (0x3d46c : word) = Some W_3d46c.
Proof. vm_refl. Qed.
Lemma D_3d46c : decode_any W_3d46c = Some (Jal 0 2097024, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d470 : bv 32 := 0x06100513.
Lemma F_3d470 : fetch_word Asan.M.loaded_segments (0x3d470 : word) = Some W_3d470.
Proof. vm_refl. Qed.
Lemma D_3d470 : decode_any W_3d470 = Some (OpImm ALU_ADD 10 0 97, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d474 : bv 32 := 0x00aaf663.
Lemma F_3d474 : fetch_word Asan.M.loaded_segments (0x3d474 : word) = Some W_3d474.
Proof. vm_refl. Qed.
Lemma D_3d474 : decode_any W_3d474 = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d478 : bv 32 := 0x00100993.
Lemma F_3d478 : fetch_word Asan.M.loaded_segments (0x3d478 : word) = Some W_3d478.
Proof. vm_refl. Qed.
Lemma D_3d478 : decode_any W_3d478 = Some (OpImm ALU_ADD 19 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d47c : bv 32 := 0x0600006f.
Lemma F_3d47c : fetch_word Asan.M.loaded_segments (0x3d47c : word) = Some W_3d47c.
Proof. vm_refl. Qed.
Lemma D_3d47c : decode_any W_3d47c = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d480 : bv 32 := 0x1c100513.
Lemma F_3d480 : fetch_word Asan.M.loaded_segments (0x3d480 : word) = Some W_3d480.
Proof. vm_refl. Qed.
Lemma D_3d480 : decode_any W_3d480 = Some (OpImm ALU_ADD 10 0 449, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d484 : bv 32 := 0x00aaf663.
Lemma F_3d484 : fetch_word Asan.M.loaded_segments (0x3d484 : word) = Some W_3d484.
Proof. vm_refl. Qed.
Lemma D_3d484 : decode_any W_3d484 = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d488 : bv 32 := 0x00200993.
Lemma F_3d488 : fetch_word Asan.M.loaded_segments (0x3d488 : word) = Some W_3d488.
Proof. vm_refl. Qed.
Lemma D_3d488 : decode_any W_3d488 = Some (OpImm ALU_ADD 19 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d48c : bv 32 := 0x0500006f.
Lemma F_3d48c : fetch_word Asan.M.loaded_segments (0x3d48c : word) = Some W_3d48c.
Proof. vm_refl. Qed.
Lemma D_3d48c : decode_any W_3d48c = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d490 : bv 32 := 0x00001537.
Lemma F_3d490 : fetch_word Asan.M.loaded_segments (0x3d490 : word) = Some W_3d490.
Proof. vm_refl. Qed.
Lemma D_3d490 : decode_any W_3d490 = Some (Lui 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d494 : bv 32 := 0xf815051b.
Lemma F_3d494 : fetch_word Asan.M.loaded_segments (0x3d494 : word) = Some W_3d494.
Proof. vm_refl. Qed.
Lemma D_3d494 : decode_any W_3d494 = Some (OpImm32 10 10 3969, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d498 : bv 32 := 0x00aaf663.
Lemma F_3d498 : fetch_word Asan.M.loaded_segments (0x3d498 : word) = Some W_3d498.
Proof. vm_refl. Qed.
Lemma D_3d498 : decode_any W_3d498 = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d49c : bv 32 := 0x00300993.
Lemma F_3d49c : fetch_word Asan.M.loaded_segments (0x3d49c : word) = Some W_3d49c.
Proof. vm_refl. Qed.
Lemma D_3d49c : decode_any W_3d49c = Some (OpImm ALU_ADD 19 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4a0 : bv 32 := 0x03c0006f.
Lemma F_3d4a0 : fetch_word Asan.M.loaded_segments (0x3d4a0 : word) = Some W_3d4a0.
Proof. vm_refl. Qed.
Lemma D_3d4a0 : decode_any W_3d4a0 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4a4 : bv 32 := 0x00004537.
Lemma F_3d4a4 : fetch_word Asan.M.loaded_segments (0x3d4a4 : word) = Some W_3d4a4.
Proof. vm_refl. Qed.
Lemma D_3d4a4 : decode_any W_3d4a4 = Some (Lui 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4a8 : bv 32 := 0xf015051b.
Lemma F_3d4a8 : fetch_word Asan.M.loaded_segments (0x3d4a8 : word) = Some W_3d4a8.
Proof. vm_refl. Qed.
Lemma D_3d4a8 : decode_any W_3d4a8 = Some (OpImm32 10 10 3841, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4ac : bv 32 := 0x00aaf663.
Lemma F_3d4ac : fetch_word Asan.M.loaded_segments (0x3d4ac : word) = Some W_3d4ac.
Proof. vm_refl. Qed.
Lemma D_3d4ac : decode_any W_3d4ac = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4b0 : bv 32 := 0x00400993.
Lemma F_3d4b0 : fetch_word Asan.M.loaded_segments (0x3d4b0 : word) = Some W_3d4b0.
Proof. vm_refl. Qed.
Lemma D_3d4b0 : decode_any W_3d4b0 = Some (OpImm ALU_ADD 19 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4b4 : bv 32 := 0x0280006f.
Lemma F_3d4b4 : fetch_word Asan.M.loaded_segments (0x3d4b4 : word) = Some W_3d4b4.
Proof. vm_refl. Qed.
Lemma D_3d4b4 : decode_any W_3d4b4 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4b8 : bv 32 := 0x00008537.
Lemma F_3d4b8 : fetch_word Asan.M.loaded_segments (0x3d4b8 : word) = Some W_3d4b8.
Proof. vm_refl. Qed.
Lemma D_3d4b8 : decode_any W_3d4b8 = Some (Lui 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4bc : bv 32 := 0xe015051b.
Lemma F_3d4bc : fetch_word Asan.M.loaded_segments (0x3d4bc : word) = Some W_3d4bc.
Proof. vm_refl. Qed.
Lemma D_3d4bc : decode_any W_3d4bc = Some (OpImm32 10 10 3585, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4c0 : bv 32 := 0x00aaf663.
Lemma F_3d4c0 : fetch_word Asan.M.loaded_segments (0x3d4c0 : word) = Some W_3d4c0.
Proof. vm_refl. Qed.
Lemma D_3d4c0 : decode_any W_3d4c0 = Some (Branch BC_GEU 21 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4c4 : bv 32 := 0x00500993.
Lemma F_3d4c4 : fetch_word Asan.M.loaded_segments (0x3d4c4 : word) = Some W_3d4c4.
Proof. vm_refl. Qed.
Lemma D_3d4c4 : decode_any W_3d4c4 = Some (OpImm ALU_ADD 19 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4c8 : bv 32 := 0x0140006f.
Lemma F_3d4c8 : fetch_word Asan.M.loaded_segments (0x3d4c8 : word) = Some W_3d4c8.
Proof. vm_refl. Qed.
Lemma D_3d4c8 : decode_any W_3d4c8 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4cc : bv 32 := 0x00010537.
Lemma F_3d4cc : fetch_word Asan.M.loaded_segments (0x3d4cc : word) = Some W_3d4cc.
Proof. vm_refl. Qed.
Lemma D_3d4cc : decode_any W_3d4cc = Some (Lui 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4d0 : bv 32 := 0xc015051b.
Lemma F_3d4d0 : fetch_word Asan.M.loaded_segments (0x3d4d0 : word) = Some W_3d4d0.
Proof. vm_refl. Qed.
Lemma D_3d4d0 : decode_any W_3d4d0 = Some (OpImm32 10 10 3073, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4d4 : bv 32 := 0x00aab533.
Lemma F_3d4d4 : fetch_word Asan.M.loaded_segments (0x3d4d4 : word) = Some W_3d4d4.
Proof. vm_refl. Qed.
Lemma D_3d4d4 : decode_any W_3d4d4 = Some (Op ALU_SLTU 10 21 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4d8 : bv 32 := 0x00754993.
Lemma F_3d4d8 : fetch_word Asan.M.loaded_segments (0x3d4d8 : word) = Some W_3d4d8.
Proof. vm_refl. Qed.
Lemma D_3d4d8 : decode_any W_3d4d8 = Some (OpImm ALU_XOR 19 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4dc : bv 32 := 0x629d1503.
Lemma F_3d4dc : fetch_word Asan.M.loaded_segments (0x3d4dc : word) = Some W_3d4dc.
Proof. vm_refl. Qed.
Lemma D_3d4dc : decode_any W_3d4dc = Some (Load SZ2 true 10 26 1577, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4e0 : bv 32 := 0x0230000f.
Lemma F_3d4e0 : fetch_word Asan.M.loaded_segments (0x3d4e0 : word) = Some W_3d4e0.
Proof. vm_refl. Qed.
Lemma D_3d4e0 : decode_any W_3d4e0 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4e4 : bv 32 := 0x00010a37.
Lemma F_3d4e4 : fetch_word Asan.M.loaded_segments (0x3d4e4 : word) = Some W_3d4e4.
Proof. vm_refl. Qed.
Lemma D_3d4e4 : decode_any W_3d4e4 = Some (Lui 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4e8 : bv 32 := 0xfffa0c1b.
Lemma F_3d4e8 : fetch_word Asan.M.loaded_segments (0x3d4e8 : word) = Some W_3d4e8.
Proof. vm_refl. Qed.
Lemma D_3d4e8 : decode_any W_3d4e8 = Some (OpImm32 24 20 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4ec : bv 32 := 0x01857533.
Lemma F_3d4ec : fetch_word Asan.M.loaded_segments (0x3d4ec : word) = Some W_3d4ec.
Proof. vm_refl. Qed.
Lemma D_3d4ec : decode_any W_3d4ec = Some (Op ALU_AND 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4f0 : bv 32 := 0x4a0050ef.
Lemma F_3d4f0 : fetch_word Asan.M.loaded_segments (0x3d4f0 : word) = Some W_3d4f0.
Proof. vm_refl. Qed.
Lemma D_3d4f0 : decode_any W_3d4f0 = Some (Jal 1 21664, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4f4 : bv 32 := 0x00050493.
Lemma F_3d4f4 : fetch_word Asan.M.loaded_segments (0x3d4f4 : word) = Some W_3d4f4.
Proof. vm_refl. Qed.
Lemma D_3d4f4 : decode_any W_3d4f4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4f8 : bv 32 := 0x62bd1503.
Lemma F_3d4f8 : fetch_word Asan.M.loaded_segments (0x3d4f8 : word) = Some W_3d4f8.
Proof. vm_refl. Qed.
Lemma D_3d4f8 : decode_any W_3d4f8 = Some (Load SZ2 true 10 26 1579, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d4fc : bv 32 := 0x0230000f.
Lemma F_3d4fc : fetch_word Asan.M.loaded_segments (0x3d4fc : word) = Some W_3d4fc.
Proof. vm_refl. Qed.
Lemma D_3d4fc : decode_any W_3d4fc = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d500 : bv 32 := 0x01857533.
Lemma F_3d500 : fetch_word Asan.M.loaded_segments (0x3d500 : word) = Some W_3d500.
Proof. vm_refl. Qed.
Lemma D_3d500 : decode_any W_3d500 = Some (Op ALU_AND 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d504 : bv 32 := 0x48c050ef.
Lemma F_3d504 : fetch_word Asan.M.loaded_segments (0x3d504 : word) = Some W_3d504.
Proof. vm_refl. Qed.
Lemma D_3d504 : decode_any W_3d504 = Some (Jal 1 21644, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d508 : bv 32 := 0x0b34e663.
Lemma F_3d508 : fetch_word Asan.M.loaded_segments (0x3d508 : word) = Some W_3d508.
Proof. vm_refl. Qed.
Lemma D_3d508 : decode_any W_3d508 = Some (Branch BC_LTU 9 19 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d50c : bv 32 := 0x00048993.
Lemma F_3d50c : fetch_word Asan.M.loaded_segments (0x3d50c : word) = Some W_3d50c.
Proof. vm_refl. Qed.
Lemma D_3d50c : decode_any W_3d50c = Some (OpImm ALU_ADD 19 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d510 : bv 32 := 0x0aa4f463.
Lemma F_3d510 : fetch_word Asan.M.loaded_segments (0x3d510 : word) = Some W_3d510.
Proof. vm_refl. Qed.
Lemma D_3d510 : decode_any W_3d510 = Some (Branch BC_GEU 9 10 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d514 : bv 32 := 0x00800593.
Lemma F_3d514 : fetch_word Asan.M.loaded_segments (0x3d514 : word) = Some W_3d514.
Proof. vm_refl. Qed.
Lemma D_3d514 : decode_any W_3d514 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d518 : bv 32 := 0x000a8513.
Lemma F_3d518 : fetch_word Asan.M.loaded_segments (0x3d518 : word) = Some W_3d518.
Proof. vm_refl. Qed.
Lemma D_3d518 : decode_any W_3d518 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d51c : bv 32 := 0x0155e463.
Lemma F_3d51c : fetch_word Asan.M.loaded_segments (0x3d51c : word) = Some W_3d51c.
Proof. vm_refl. Qed.
Lemma D_3d51c : decode_any W_3d51c = Some (Branch BC_LTU 11 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d520 : bv 32 := 0x00800513.
Lemma F_3d520 : fetch_word Asan.M.loaded_segments (0x3d520 : word) = Some W_3d520.
Proof. vm_refl. Qed.
Lemma D_3d520 : decode_any W_3d520 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d524 : bv 32 := 0x00850533.
Lemma F_3d524 : fetch_word Asan.M.loaded_segments (0x3d524 : word) = Some W_3d524.
Proof. vm_refl. Qed.
Lemma D_3d524 : decode_any W_3d524 = Some (Op ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d528 : bv 32 := 0x40800c33.
Lemma F_3d528 : fetch_word Asan.M.loaded_segments (0x3d528 : word) = Some W_3d528.
Proof. vm_refl. Qed.
Lemma D_3d528 : decode_any W_3d528 = Some (Op ALU_SUB 24 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d52c : bv 32 := 0x00993593.
Lemma F_3d52c : fetch_word Asan.M.loaded_segments (0x3d52c : word) = Some W_3d52c.
Proof. vm_refl. Qed.
Lemma D_3d52c : decode_any W_3d52c = Some (OpImm ALU_SLTU 11 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d530 : bv 32 := 0xfff50513.
Lemma F_3d530 : fetch_word Asan.M.loaded_segments (0x3d530 : word) = Some W_3d530.
Proof. vm_refl. Qed.
Lemma D_3d530 : decode_any W_3d530 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d534 : bv 32 := 0xfff58593.
Lemma F_3d534 : fetch_word Asan.M.loaded_segments (0x3d534 : word) = Some W_3d534.
Proof. vm_refl. Qed.
Lemma D_3d534 : decode_any W_3d534 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d538 : bv 32 := 0x01857533.
Lemma F_3d538 : fetch_word Asan.M.loaded_segments (0x3d538 : word) = Some W_3d538.
Proof. vm_refl. Qed.
Lemma D_3d538 : decode_any W_3d538 = Some (Op ALU_AND 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d53c : bv 32 := 0x0085f5b3.
Lemma F_3d53c : fetch_word Asan.M.loaded_segments (0x3d53c : word) = Some W_3d53c.
Proof. vm_refl. Qed.
Lemma D_3d53c : decode_any W_3d53c = Some (Op ALU_AND 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d540 : bv 32 := 0x00b50533.
Lemma F_3d540 : fetch_word Asan.M.loaded_segments (0x3d540 : word) = Some W_3d540.
Proof. vm_refl. Qed.
Lemma D_3d540 : decode_any W_3d540 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d544 : bv 32 := 0x00757593.
Lemma F_3d544 : fetch_word Asan.M.loaded_segments (0x3d544 : word) = Some W_3d544.
Proof. vm_refl. Qed.
Lemma D_3d544 : decode_any W_3d544 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d548 : bv 32 := 0x6a059063.
Lemma F_3d548 : fetch_word Asan.M.loaded_segments (0x3d548 : word) = Some W_3d548.
Proof. vm_refl. Qed.
Lemma D_3d548 : decode_any W_3d548 = Some (Branch BC_NE 11 0 1696, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d54c : bv 32 := 0x01000593.
Lemma F_3d54c : fetch_word Asan.M.loaded_segments (0x3d54c : word) = Some W_3d54c.
Proof. vm_refl. Qed.
Lemma D_3d54c : decode_any W_3d54c = Some (OpImm ALU_ADD 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d550 : bv 32 := 0x001ab493.
Lemma F_3d550 : fetch_word Asan.M.loaded_segments (0x3d550 : word) = Some W_3d550.
Proof. vm_refl. Qed.
Lemma D_3d550 : decode_any W_3d550 = Some (OpImm ALU_SLTU 9 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d554 : bv 32 := 0x001a061b.
Lemma F_3d554 : fetch_word Asan.M.loaded_segments (0x3d554 : word) = Some W_3d554.
Proof. vm_refl. Qed.
Lemma D_3d554 : decode_any W_3d554 = Some (OpImm32 12 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d558 : bv 32 := 0x01359a3b.
Lemma F_3d558 : fetch_word Asan.M.loaded_segments (0x3d558 : word) = Some W_3d558.
Proof. vm_refl. Qed.
Lemma D_3d558 : decode_any W_3d558 = Some (Op32 ALU_SLL 20 11 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d55c : bv 32 := 0x00100593.
Lemma F_3d55c : fetch_word Asan.M.loaded_segments (0x3d55c : word) = Some W_3d55c.
Proof. vm_refl. Qed.
Lemma D_3d55c : decode_any W_3d55c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d560 : bv 32 := 0x009a84b3.
Lemma F_3d560 : fetch_word Asan.M.loaded_segments (0x3d560 : word) = Some W_3d560.
Proof. vm_refl. Qed.
Lemma D_3d560 : decode_any W_3d560 = Some (Op ALU_ADD 9 21 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d564 : bv 32 := 0x00c936b3.
Lemma F_3d564 : fetch_word Asan.M.loaded_segments (0x3d564 : word) = Some W_3d564.
Proof. vm_refl. Qed.
Lemma D_3d564 : decode_any W_3d564 = Some (Op ALU_SLTU 13 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d568 : bv 32 := 0x014509b3.
Lemma F_3d568 : fetch_word Asan.M.loaded_segments (0x3d568 : word) = Some W_3d568.
Proof. vm_refl. Qed.
Lemma D_3d568 : decode_any W_3d568 = Some (Op ALU_ADD 19 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d56c : bv 32 := 0x00c9b433.
Lemma F_3d56c : fetch_word Asan.M.loaded_segments (0x3d56c : word) = Some W_3d56c.
Proof. vm_refl. Qed.
Lemma D_3d56c : decode_any W_3d56c = Some (Op ALU_SLTU 8 19 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d570 : bv 32 := 0x0086f433.
Lemma F_3d570 : fetch_word Asan.M.loaded_segments (0x3d570 : word) = Some W_3d570.
Proof. vm_refl. Qed.
Lemma D_3d570 : decode_any W_3d570 = Some (Op ALU_AND 8 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d574 : bv 32 := 0xfff40513.
Lemma F_3d574 : fetch_word Asan.M.loaded_segments (0x3d574 : word) = Some W_3d574.
Proof. vm_refl. Qed.
Lemma D_3d574 : decode_any W_3d574 = Some (OpImm ALU_ADD 10 8 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d578 : bv 32 := 0x01457633.
Lemma F_3d578 : fetch_word Asan.M.loaded_segments (0x3d578 : word) = Some W_3d578.
Proof. vm_refl. Qed.
Lemma D_3d578 : decode_any W_3d578 = Some (Op ALU_AND 12 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d57c : bv 32 := 0x02859513.
Lemma F_3d57c : fetch_word Asan.M.loaded_segments (0x3d57c : word) = Some W_3d57c.
Proof. vm_refl. Qed.
Lemma D_3d57c : decode_any W_3d57c = Some (ShiftImm ALU_SLL 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d580 : bv 32 := 0x013609b3.
Lemma F_3d580 : fetch_word Asan.M.loaded_segments (0x3d580 : word) = Some W_3d580.
Proof. vm_refl. Qed.
Lemma D_3d580 : decode_any W_3d580 = Some (Op ALU_ADD 19 12 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d584 : bv 32 := 0x01556863.
Lemma F_3d584 : fetch_word Asan.M.loaded_segments (0x3d584 : word) = Some W_3d584.
Proof. vm_refl. Qed.
Lemma D_3d584 : decode_any W_3d584 = Some (Branch BC_LTU 10 21 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d588 : bv 32 := 0x01356663.
Lemma F_3d588 : fetch_word Asan.M.loaded_segments (0x3d588 : word) = Some W_3d588.
Proof. vm_refl. Qed.
Lemma D_3d588 : decode_any W_3d588 = Some (Branch BC_LTU 10 19 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d58c : bv 32 := 0x621d3503.
Lemma F_3d58c : fetch_word Asan.M.loaded_segments (0x3d58c : word) = Some W_3d58c.
Proof. vm_refl. Qed.
Lemma D_3d58c : decode_any W_3d58c = Some (Load SZ8 true 10 26 1569, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d590 : bv 32 := 0x06957063.
Lemma F_3d590 : fetch_word Asan.M.loaded_segments (0x3d590 : word) = Some W_3d590.
Proof. vm_refl. Qed.
Lemma D_3d590 : decode_any W_3d590 = Some (Branch BC_GEU 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d594 : bv 32 := 0x7e02e0ef.
Lemma F_3d594 : fetch_word Asan.M.loaded_segments (0x3d594 : word) = Some W_3d594.
Proof. vm_refl. Qed.
Lemma D_3d594 : decode_any W_3d594 = Some (Jal 1 190432, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d598 : bv 32 := 0x02050a63.
Lemma F_3d598 : fetch_word Asan.M.loaded_segments (0x3d598 : word) = Some W_3d598.
Proof. vm_refl. Qed.
Lemma D_3d598 : decode_any W_3d598 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d59c : bv 32 := 0xfffd4517.
Lemma F_3d59c : fetch_word Asan.M.loaded_segments (0x3d59c : word) = Some W_3d59c.
Proof. vm_refl. Qed.
Lemma D_3d59c : decode_any W_3d59c = Some (Auipc 10 1048532, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5a0 : bv 32 := 0x0f350513.
Lemma F_3d5a0 : fetch_word Asan.M.loaded_segments (0x3d5a0 : word) = Some W_3d5a0.
Proof. vm_refl. Qed.
Lemma D_3d5a0 : decode_any W_3d5a0 = Some (OpImm ALU_ADD 10 10 243, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5a4 : bv 32 := 0x00048593.
Lemma F_3d5a4 : fetch_word Asan.M.loaded_segments (0x3d5a4 : word) = Some W_3d5a4.
Proof. vm_refl. Qed.
Lemma D_3d5a4 : decode_any W_3d5a4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5a8 : bv 32 := 0x1e0370ef.
Lemma F_3d5a8 : fetch_word Asan.M.loaded_segments (0x3d5a8 : word) = Some W_3d5a8.
Proof. vm_refl. Qed.
Lemma D_3d5a8 : decode_any W_3d5a8 = Some (Jal 1 225760, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5ac : bv 32 := 0x00000a13.
Lemma F_3d5ac : fetch_word Asan.M.loaded_segments (0x3d5ac : word) = Some W_3d5ac.
Proof. vm_refl. Qed.
Lemma D_3d5ac : decode_any W_3d5ac = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5b0 : bv 32 := 0x4f40006f.
Lemma F_3d5b0 : fetch_word Asan.M.loaded_segments (0x3d5b0 : word) = Some W_3d5b0.
Proof. vm_refl. Qed.
Lemma D_3d5b0 : decode_any W_3d5b0 = Some (Jal 0 1268, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5b4 : bv 32 := 0xf6a9e0e3.
Lemma F_3d5b4 : fetch_word Asan.M.loaded_segments (0x3d5b4 : word) = Some W_3d5b4.
Proof. vm_refl. Qed.
Lemma D_3d5b4 : decode_any W_3d5b4 = Some (Branch BC_LTU 19 10 8032, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5b8 : bv 32 := 0x00050993.
Lemma F_3d5b8 : fetch_word Asan.M.loaded_segments (0x3d5b8 : word) = Some W_3d5b8.
Proof. vm_refl. Qed.
Lemma D_3d5b8 : decode_any W_3d5b8 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5bc : bv 32 := 0x00800593.
Lemma F_3d5bc : fetch_word Asan.M.loaded_segments (0x3d5bc : word) = Some W_3d5bc.
Proof. vm_refl. Qed.
Lemma D_3d5bc : decode_any W_3d5bc = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5c0 : bv 32 := 0x000a8513.
Lemma F_3d5c0 : fetch_word Asan.M.loaded_segments (0x3d5c0 : word) = Some W_3d5c0.
Proof. vm_refl. Qed.
Lemma D_3d5c0 : decode_any W_3d5c0 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5c4 : bv 32 := 0xf555fee3.
Lemma F_3d5c4 : fetch_word Asan.M.loaded_segments (0x3d5c4 : word) = Some W_3d5c4.
Proof. vm_refl. Qed.
Lemma D_3d5c4 : decode_any W_3d5c4 = Some (Branch BC_GEU 11 21 8028, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5c8 : bv 32 := 0xf5dff06f.
Lemma F_3d5c8 : fetch_word Asan.M.loaded_segments (0x3d5c8 : word) = Some W_3d5c8.
Proof. vm_refl. Qed.
Lemma D_3d5c8 : decode_any W_3d5c8 = Some (Jal 0 2096988, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5cc : bv 32 := 0x621d3603.
Lemma F_3d5cc : fetch_word Asan.M.loaded_segments (0x3d5cc : word) = Some W_3d5cc.
Proof. vm_refl. Qed.
Lemma D_3d5cc : decode_any W_3d5cc = Some (Load SZ8 true 12 26 1569, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5d0 : bv 32 := 0x00100513.
Lemma F_3d5d0 : fetch_word Asan.M.loaded_segments (0x3d5d0 : word) = Some W_3d5d0.
Proof. vm_refl. Qed.
Lemma D_3d5d0 : decode_any W_3d5d0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5d4 : bv 32 := 0x02851513.
Lemma F_3d5d4 : fetch_word Asan.M.loaded_segments (0x3d5d4 : word) = Some W_3d5d4.
Proof. vm_refl. Qed.
Lemma D_3d5d4 : decode_any W_3d5d4 = Some (ShiftImm ALU_SLL 10 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5d8 : bv 32 := 0x00a66463.
Lemma F_3d5d8 : fetch_word Asan.M.loaded_segments (0x3d5d8 : word) = Some W_3d5d8.
Proof. vm_refl. Qed.
Lemma D_3d5d8 : decode_any W_3d5d8 = Some (Branch BC_LTU 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5dc : bv 32 := 0x00050613.
Lemma F_3d5dc : fetch_word Asan.M.loaded_segments (0x3d5dc : word) = Some W_3d5dc.
Proof. vm_refl. Qed.
Lemma D_3d5dc : decode_any W_3d5dc = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5e0 : bv 32 := 0x00048513.
Lemma F_3d5e0 : fetch_word Asan.M.loaded_segments (0x3d5e0 : word) = Some W_3d5e0.
Proof. vm_refl. Qed.
Lemma D_3d5e0 : decode_any W_3d5e0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5e4 : bv 32 := 0x00098593.
Lemma F_3d5e4 : fetch_word Asan.M.loaded_segments (0x3d5e4 : word) = Some W_3d5e4.
Proof. vm_refl. Qed.
Lemma D_3d5e4 : decode_any W_3d5e4 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5e8 : bv 32 := 0x000b8693.
Lemma F_3d5e8 : fetch_word Asan.M.loaded_segments (0x3d5e8 : word) = Some W_3d5e8.
Proof. vm_refl. Qed.
Lemma D_3d5e8 : decode_any W_3d5e8 = Some (OpImm ALU_ADD 13 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5ec : bv 32 := 0x399260ef.
Lemma F_3d5ec : fetch_word Asan.M.loaded_segments (0x3d5ec : word) = Some W_3d5ec.
Proof. vm_refl. Qed.
Lemma D_3d5ec : decode_any W_3d5ec = Some (Jal 1 158616, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5f0 : bv 32 := 0x1f42c0ef.
Lemma F_3d5f0 : fetch_word Asan.M.loaded_segments (0x3d5f0 : word) = Some W_3d5f0.
Proof. vm_refl. Qed.
Lemma D_3d5f0 : decode_any W_3d5f0 = Some (Jal 1 180724, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5f4 : bv 32 := 0x00050d13.
Lemma F_3d5f4 : fetch_word Asan.M.loaded_segments (0x3d5f4 : word) = Some W_3d5f4.
Proof. vm_refl. Qed.
Lemma D_3d5f4 : decode_any W_3d5f4 = Some (OpImm ALU_ADD 26 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5f8 : bv 32 := 0x08050863.
Lemma F_3d5f8 : fetch_word Asan.M.loaded_segments (0x3d5f8 : word) = Some W_3d5f8.
Proof. vm_refl. Qed.
Lemma D_3d5f8 : decode_any W_3d5f8 = Some (Branch BC_EQ 10 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d5fc : bv 32 := 0x0d0d0593.
Lemma F_3d5fc : fetch_word Asan.M.loaded_segments (0x3d5fc : word) = Some W_3d5fc.
Proof. vm_refl. Qed.
Lemma D_3d5fc : decode_any W_3d5fc = Some (OpImm ALU_ADD 11 26 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d600 : bv 32 := 0x00800693.
Lemma F_3d600 : fetch_word Asan.M.loaded_segments (0x3d600 : word) = Some W_3d600.
Proof. vm_refl. Qed.
Lemma D_3d600 : decode_any W_3d600 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d604 : bv 32 := 0x000b0513.
Lemma F_3d604 : fetch_word Asan.M.loaded_segments (0x3d604 : word) = Some W_3d604.
Proof. vm_refl. Qed.
Lemma D_3d604 : decode_any W_3d604 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d608 : bv 32 := 0x00098613.
Lemma F_3d608 : fetch_word Asan.M.loaded_segments (0x3d608 : word) = Some W_3d608.
Proof. vm_refl. Qed.
Lemma D_3d608 : decode_any W_3d608 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d60c : bv 32 := 0x4bc040ef.
Lemma F_3d60c : fetch_word Asan.M.loaded_segments (0x3d60c : word) = Some W_3d60c.
Proof. vm_refl. Qed.
Lemma D_3d60c : decode_any W_3d60c = Some (Jal 1 17596, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d610 : bv 32 := 0x00050913.
Lemma F_3d610 : fetch_word Asan.M.loaded_segments (0x3d610 : word) = Some W_3d610.
Proof. vm_refl. Qed.
Lemma D_3d610 : decode_any W_3d610 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d614 : bv 32 := 0x0c050663.
Lemma F_3d614 : fetch_word Asan.M.loaded_segments (0x3d614 : word) = Some W_3d614.
Proof. vm_refl. Qed.
Lemma D_3d614 : decode_any W_3d614 = Some (Branch BC_EQ 10 0 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d618 : bv 32 := 0x01490a33.
Lemma F_3d618 : fetch_word Asan.M.loaded_segments (0x3d618 : word) = Some W_3d618.
Proof. vm_refl. Qed.
Lemma D_3d618 : decode_any W_3d618 = Some (Op ALU_ADD 20 18 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d61c : bv 32 := 0x019a7533.
Lemma F_3d61c : fetch_word Asan.M.loaded_segments (0x3d61c : word) = Some W_3d61c.
Proof. vm_refl. Qed.
Lemma D_3d61c : decode_any W_3d61c = Some (Op ALU_AND 10 20 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d620 : bv 32 := 0x01298733.
Lemma F_3d620 : fetch_word Asan.M.loaded_segments (0x3d620 : word) = Some W_3d620.
Proof. vm_refl. Qed.
Lemma D_3d620 : decode_any W_3d620 = Some (Op ALU_ADD 14 19 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d624 : bv 32 := 0x00050663.
Lemma F_3d624 : fetch_word Asan.M.loaded_segments (0x3d624 : word) = Some W_3d624.
Proof. vm_refl. Qed.
Lemma D_3d624 : decode_any W_3d624 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d628 : bv 32 := 0x014c8a33.
Lemma F_3d628 : fetch_word Asan.M.loaded_segments (0x3d628 : word) = Some W_3d628.
Proof. vm_refl. Qed.
Lemma D_3d628 : decode_any W_3d628 = Some (Op ALU_ADD 20 25 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d62c : bv 32 := 0x018a7a33.
Lemma F_3d62c : fetch_word Asan.M.loaded_segments (0x3d62c : word) = Some W_3d62c.
Proof. vm_refl. Qed.
Lemma D_3d62c : decode_any W_3d62c = Some (Op ALU_AND 20 20 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d630 : bv 32 := 0x009a0cb3.
Lemma F_3d630 : fetch_word Asan.M.loaded_segments (0x3d630 : word) = Some W_3d630.
Proof. vm_refl. Qed.
Lemma D_3d630 : decode_any W_3d630 = Some (Op ALU_ADD 25 20 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d634 : bv 32 := 0x5d976a63.
Lemma F_3d634 : fetch_word Asan.M.loaded_segments (0x3d634 : word) = Some W_3d634.
Proof. vm_refl. Qed.
Lemma D_3d634 : decode_any W_3d634 = Some (Branch BC_LTU 14 25 1492, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d638 : bv 32 := 0xff1a4503.
Lemma F_3d638 : fetch_word Asan.M.loaded_segments (0x3d638 : word) = Some W_3d638.
Proof. vm_refl. Qed.
Lemma D_3d638 : decode_any W_3d638 = Some (Load SZ1 false 10 20 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d63c : bv 32 := 0x003df593.
Lemma F_3d63c : fetch_word Asan.M.loaded_segments (0x3d63c : word) = Some W_3d63c.
Proof. vm_refl. Qed.
Lemma D_3d63c : decode_any W_3d63c = Some (OpImm ALU_AND 11 27 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d640 : bv 32 := 0xffc57513.
Lemma F_3d640 : fetch_word Asan.M.loaded_segments (0x3d640 : word) = Some W_3d640.
Proof. vm_refl. Qed.
Lemma D_3d640 : decode_any W_3d640 = Some (OpImm ALU_AND 10 10 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d644 : bv 32 := 0x00b56533.
Lemma F_3d644 : fetch_word Asan.M.loaded_segments (0x3d644 : word) = Some W_3d644.
Proof. vm_refl. Qed.
Lemma D_3d644 : decode_any W_3d644 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d648 : bv 32 := 0x0204d593.
Lemma F_3d648 : fetch_word Asan.M.loaded_segments (0x3d648 : word) = Some W_3d648.
Proof. vm_refl. Qed.
Lemma D_3d648 : decode_any W_3d648 = Some (ShiftImm ALU_SRL 11 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d64c : bv 32 := 0x030ad613.
Lemma F_3d64c : fetch_word Asan.M.loaded_segments (0x3d64c : word) = Some W_3d64c.
Proof. vm_refl. Qed.
Lemma D_3d64c : decode_any W_3d64c = Some (ShiftImm ALU_SRL 12 21 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d650 : bv 32 := 0xfeaa08a3.
Lemma F_3d650 : fetch_word Asan.M.loaded_segments (0x3d650 : word) = Some W_3d650.
Proof. vm_refl. Qed.
Lemma D_3d650 : decode_any W_3d650 = Some (Store SZ1 20 10 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d654 : bv 32 := 0xfeba1923.
Lemma F_3d654 : fetch_word Asan.M.loaded_segments (0x3d654 : word) = Some W_3d654.
Proof. vm_refl. Qed.
Lemma D_3d654 : decode_any W_3d654 = Some (Store SZ2 20 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d658 : bv 32 := 0xfe9a2a23.
Lemma F_3d658 : fetch_word Asan.M.loaded_segments (0x3d658 : word) = Some W_3d658.
Proof. vm_refl. Qed.
Lemma D_3d658 : decode_any W_3d658 = Some (Store SZ4 20 9 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d65c : bv 32 := 0x5c061463.
Lemma F_3d65c : fetch_word Asan.M.loaded_segments (0x3d65c : word) = Some W_3d65c.
Proof. vm_refl. Qed.
Lemma D_3d65c : decode_any W_3d65c = Some (Branch BC_NE 12 0 1480, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d660 : bv 32 := 0xff0a0a93.
Lemma F_3d660 : fetch_word Asan.M.loaded_segments (0x3d660 : word) = Some W_3d660.
Proof. vm_refl. Qed.
Lemma D_3d660 : decode_any W_3d660 = Some (OpImm ALU_ADD 21 20 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d664 : bv 32 := 0x08f57513.
Lemma F_3d664 : fetch_word Asan.M.loaded_segments (0x3d664 : word) = Some W_3d664.
Proof. vm_refl. Qed.
Lemma D_3d664 : decode_any W_3d664 = Some (OpImm ALU_AND 10 10 143, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d668 : bv 32 := 0x01013583.
Lemma F_3d668 : fetch_word Asan.M.loaded_segments (0x3d668 : word) = Some W_3d668.
Proof. vm_refl. Qed.
Lemma D_3d668 : decode_any W_3d668 = Some (Load SZ8 true 11 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d66c : bv 32 := 0x00b56533.
Lemma F_3d66c : fetch_word Asan.M.loaded_segments (0x3d66c : word) = Some W_3d66c.
Proof. vm_refl. Qed.
Lemma D_3d66c : decode_any W_3d66c = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d670 : bv 32 := 0x00aa80a3.
Lemma F_3d670 : fetch_word Asan.M.loaded_segments (0x3d670 : word) = Some W_3d670.
Proof. vm_refl. Qed.
Lemma D_3d670 : decode_any W_3d670 = Some (Store SZ1 21 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d674 : bv 32 := 0x080d0c63.
Lemma F_3d674 : fetch_word Asan.M.loaded_segments (0x3d674 : word) = Some W_3d674.
Proof. vm_refl. Qed.
Lemma D_3d674 : decode_any W_3d674 = Some (Branch BC_EQ 26 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d678 : bv 32 := 0x000d3503.
Lemma F_3d678 : fetch_word Asan.M.loaded_segments (0x3d678 : word) = Some W_3d678.
Proof. vm_refl. Qed.
Lemma D_3d678 : decode_any W_3d678 = Some (Load SZ8 true 10 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d67c : bv 32 := 0x00852c03.
Lemma F_3d67c : fetch_word Asan.M.loaded_segments (0x3d67c : word) = Some W_3d67c.
Proof. vm_refl. Qed.
Lemma D_3d67c : decode_any W_3d67c = Some (Load SZ4 true 24 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d680 : bv 32 := 0x020c1c13.
Lemma F_3d680 : fetch_word Asan.M.loaded_segments (0x3d680 : word) = Some W_3d680.
Proof. vm_refl. Qed.
Lemma D_3d680 : decode_any W_3d680 = Some (ShiftImm ALU_SLL 24 24 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d684 : bv 32 := 0x08c0006f.
Lemma F_3d684 : fetch_word Asan.M.loaded_segments (0x3d684 : word) = Some W_3d684.
Proof. vm_refl. Qed.
Lemma D_3d684 : decode_any W_3d684 = Some (Jal 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d688 : bv 32 := 0x3d8b0513.
Lemma F_3d688 : fetch_word Asan.M.loaded_segments (0x3d688 : word) = Some W_3d688.
Proof. vm_refl. Qed.
Lemma D_3d688 : decode_any W_3d688 = Some (OpImm ALU_ADD 10 22 984, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d68c : bv 32 := 0x0ff00593.
Lemma F_3d68c : fetch_word Asan.M.loaded_segments (0x3d68c : word) = Some W_3d68c.
Proof. vm_refl. Qed.
Lemma D_3d68c : decode_any W_3d68c = Some (OpImm ALU_ADD 11 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d690 : bv 32 := 0xffc57613.
Lemma F_3d690 : fetch_word Asan.M.loaded_segments (0x3d690 : word) = Some W_3d690.
Proof. vm_refl. Qed.
Lemma D_3d690 : decode_any W_3d690 = Some (OpImm ALU_AND 12 10 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d694 : bv 32 := 0x00100693.
Lemma F_3d694 : fetch_word Asan.M.loaded_segments (0x3d694 : word) = Some W_3d694.
Proof. vm_refl. Qed.
Lemma D_3d694 : decode_any W_3d694 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d698 : bv 32 := 0x1406272f.
Lemma F_3d698 : fetch_word Asan.M.loaded_segments (0x3d698 : word) = Some W_3d698.
Proof. vm_refl. Qed.
Lemma D_3d698 : decode_any W_3d698 = Some (Lr AW true false 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d69c : bv 32 := 0x00068793.
Lemma F_3d69c : fetch_word Asan.M.loaded_segments (0x3d69c : word) = Some W_3d69c.
Proof. vm_refl. Qed.
Lemma D_3d69c : decode_any W_3d69c = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6a0 : bv 32 := 0x00f747b3.
Lemma F_3d6a0 : fetch_word Asan.M.loaded_segments (0x3d6a0 : word) = Some W_3d6a0.
Proof. vm_refl. Qed.
Lemma D_3d6a0 : decode_any W_3d6a0 = Some (Op ALU_XOR 15 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6a4 : bv 32 := 0x00b7f7b3.
Lemma F_3d6a4 : fetch_word Asan.M.loaded_segments (0x3d6a4 : word) = Some W_3d6a4.
Proof. vm_refl. Qed.
Lemma D_3d6a4 : decode_any W_3d6a4 = Some (Op ALU_AND 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6a8 : bv 32 := 0x00f747b3.
Lemma F_3d6a8 : fetch_word Asan.M.loaded_segments (0x3d6a8 : word) = Some W_3d6a8.
Proof. vm_refl. Qed.
Lemma D_3d6a8 : decode_any W_3d6a8 = Some (Op ALU_XOR 15 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6ac : bv 32 := 0x18f627af.
Lemma F_3d6ac : fetch_word Asan.M.loaded_segments (0x3d6ac : word) = Some W_3d6ac.
Proof. vm_refl. Qed.
Lemma D_3d6ac : decode_any W_3d6ac = Some (Sc AW false false 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6b0 : bv 32 := 0xfe0794e3.
Lemma F_3d6b0 : fetch_word Asan.M.loaded_segments (0x3d6b0 : word) = Some W_3d6b0.
Proof. vm_refl. Qed.
Lemma D_3d6b0 : decode_any W_3d6b0 = Some (Branch BC_NE 15 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6b4 : bv 32 := 0x0ff77593.
Lemma F_3d6b4 : fetch_word Asan.M.loaded_segments (0x3d6b4 : word) = Some W_3d6b4.
Proof. vm_refl. Qed.
Lemma D_3d6b4 : decode_any W_3d6b4 = Some (OpImm ALU_AND 11 14 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6b8 : bv 32 := 0x60059063.
Lemma F_3d6b8 : fetch_word Asan.M.loaded_segments (0x3d6b8 : word) = Some W_3d6b8.
Proof. vm_refl. Qed.
Lemma D_3d6b8 : decode_any W_3d6b8 = Some (Branch BC_NE 11 0 1536, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6bc : bv 32 := 0x3e0b0593.
Lemma F_3d6bc : fetch_word Asan.M.loaded_segments (0x3d6bc : word) = Some W_3d6bc.
Proof. vm_refl. Qed.
Lemma D_3d6bc : decode_any W_3d6bc = Some (OpImm ALU_ADD 11 22 992, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6c0 : bv 32 := 0x00800693.
Lemma F_3d6c0 : fetch_word Asan.M.loaded_segments (0x3d6c0 : word) = Some W_3d6c0.
Proof. vm_refl. Qed.
Lemma D_3d6c0 : decode_any W_3d6c0 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6c4 : bv 32 := 0x000b0513.
Lemma F_3d6c4 : fetch_word Asan.M.loaded_segments (0x3d6c4 : word) = Some W_3d6c4.
Proof. vm_refl. Qed.
Lemma D_3d6c4 : decode_any W_3d6c4 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6c8 : bv 32 := 0x00098613.
Lemma F_3d6c8 : fetch_word Asan.M.loaded_segments (0x3d6c8 : word) = Some W_3d6c8.
Proof. vm_refl. Qed.
Lemma D_3d6c8 : decode_any W_3d6c8 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6cc : bv 32 := 0x3fc040ef.
Lemma F_3d6cc : fetch_word Asan.M.loaded_segments (0x3d6cc : word) = Some W_3d6cc.
Proof. vm_refl. Qed.
Lemma D_3d6cc : decode_any W_3d6cc = Some (Jal 1 17404, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6d0 : bv 32 := 0x00050913.
Lemma F_3d6d0 : fetch_word Asan.M.loaded_segments (0x3d6d0 : word) = Some W_3d6d0.
Proof. vm_refl. Qed.
Lemma D_3d6d0 : decode_any W_3d6d0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6d4 : bv 32 := 0x0310000f.
Lemma F_3d6d4 : fetch_word Asan.M.loaded_segments (0x3d6d4 : word) = Some W_3d6d4.
Proof. vm_refl. Qed.
Lemma D_3d6d4 : decode_any W_3d6d4 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6d8 : bv 32 := 0x3c0b0c23.
Lemma F_3d6d8 : fetch_word Asan.M.loaded_segments (0x3d6d8 : word) = Some W_3d6d8.
Proof. vm_refl. Qed.
Lemma D_3d6d8 : decode_any W_3d6d8 = Some (Store SZ1 22 0 984, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6dc : bv 32 := 0xf2051ee3.
Lemma F_3d6dc : fetch_word Asan.M.loaded_segments (0x3d6dc : word) = Some W_3d6dc.
Proof. vm_refl. Qed.
Lemma D_3d6dc : decode_any W_3d6dc = Some (Branch BC_NE 10 0 7996, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6e0 : bv 32 := 0x6842e0ef.
Lemma F_3d6e0 : fetch_word Asan.M.loaded_segments (0x3d6e0 : word) = Some W_3d6e0.
Proof. vm_refl. Qed.
Lemma D_3d6e0 : decode_any W_3d6e0 = Some (Jal 1 190084, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6e4 : bv 32 := 0x6902e0ef.
Lemma F_3d6e4 : fetch_word Asan.M.loaded_segments (0x3d6e4 : word) = Some W_3d6e4.
Proof. vm_refl. Qed.
Lemma D_3d6e4 : decode_any W_3d6e4 = Some (Jal 1 190096, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6e8 : bv 32 := 0x4c051c63.
Lemma F_3d6e8 : fetch_word Asan.M.loaded_segments (0x3d6e8 : word) = Some W_3d6e8.
Proof. vm_refl. Qed.
Lemma D_3d6e8 : decode_any W_3d6e8 = Some (Branch BC_NE 10 0 1240, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6ec : bv 32 := 0x00048513.
Lemma F_3d6ec : fetch_word Asan.M.loaded_segments (0x3d6ec : word) = Some W_3d6ec.
Proof. vm_refl. Qed.
Lemma D_3d6ec : decode_any W_3d6ec = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6f0 : bv 32 := 0x000b8593.
Lemma F_3d6f0 : fetch_word Asan.M.loaded_segments (0x3d6f0 : word) = Some W_3d6f0.
Proof. vm_refl. Qed.
Lemma D_3d6f0 : decode_any W_3d6f0 = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6f4 : bv 32 := 0x725260ef.
Lemma F_3d6f4 : fetch_word Asan.M.loaded_segments (0x3d6f4 : word) = Some W_3d6f4.
Proof. vm_refl. Qed.
Lemma D_3d6f4 : decode_any W_3d6f4 = Some (Jal 1 159524, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6f8 : bv 32 := 0x01490a33.
Lemma F_3d6f8 : fetch_word Asan.M.loaded_segments (0x3d6f8 : word) = Some W_3d6f8.
Proof. vm_refl. Qed.
Lemma D_3d6f8 : decode_any W_3d6f8 = Some (Op ALU_ADD 20 18 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d6fc : bv 32 := 0x019a7533.
Lemma F_3d6fc : fetch_word Asan.M.loaded_segments (0x3d6fc : word) = Some W_3d6fc.
Proof. vm_refl. Qed.
Lemma D_3d6fc : decode_any W_3d6fc = Some (Op ALU_AND 10 20 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d700 : bv 32 := 0x01298733.
Lemma F_3d700 : fetch_word Asan.M.loaded_segments (0x3d700 : word) = Some W_3d700.
Proof. vm_refl. Qed.
Lemma D_3d700 : decode_any W_3d700 = Some (Op ALU_ADD 14 19 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d704 : bv 32 := 0xf20512e3.
Lemma F_3d704 : fetch_word Asan.M.loaded_segments (0x3d704 : word) = Some W_3d704.
Proof. vm_refl. Qed.
Lemma D_3d704 : decode_any W_3d704 = Some (Branch BC_NE 10 0 7972, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d708 : bv 32 := 0xf29ff06f.
Lemma F_3d708 : fetch_word Asan.M.loaded_segments (0x3d708 : word) = Some W_3d708.
Proof. vm_refl. Qed.
Lemma D_3d708 : decode_any W_3d708 = Some (Jal 0 2096936, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d70c : bv 32 := 0x00000c13.
Lemma F_3d70c : fetch_word Asan.M.loaded_segments (0x3d70c : word) = Some W_3d70c.
Proof. vm_refl. Qed.
Lemma D_3d70c : decode_any W_3d70c = Some (OpImm ALU_ADD 24 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d710 : bv 32 := 0x000bb503.
Lemma F_3d710 : fetch_word Asan.M.loaded_segments (0x3d710 : word) = Some W_3d710.
Proof. vm_refl. Qed.
Lemma D_3d710 : decode_any W_3d710 = Some (Load SZ8 true 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d714 : bv 32 := 0x008bb583.
Lemma F_3d714 : fetch_word Asan.M.loaded_segments (0x3d714 : word) = Some W_3d714.
Proof. vm_refl. Qed.
Lemma D_3d714 : decode_any W_3d714 = Some (Load SZ8 true 11 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d718 : bv 32 := 0x790420ef.
Lemma F_3d718 : fetch_word Asan.M.loaded_segments (0x3d718 : word) = Some W_3d718.
Proof. vm_refl. Qed.
Lemma D_3d718 : decode_any W_3d718 = Some (Jal 1 272272, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d71c : bv 32 := 0x02051513.
Lemma F_3d71c : fetch_word Asan.M.loaded_segments (0x3d71c : word) = Some W_3d71c.
Proof. vm_refl. Qed.
Lemma D_3d71c : decode_any W_3d71c = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d720 : bv 32 := 0x02055513.
Lemma F_3d720 : fetch_word Asan.M.loaded_segments (0x3d720 : word) = Some W_3d720.
Proof. vm_refl. Qed.
Lemma D_3d720 : decode_any W_3d720 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d724 : bv 32 := 0x00ac6533.
Lemma F_3d724 : fetch_word Asan.M.loaded_segments (0x3d724 : word) = Some W_3d724.
Proof. vm_refl. Qed.
Lemma D_3d724 : decode_any W_3d724 = Some (Op ALU_OR 10 24 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d728 : bv 32 := 0x00aab423.
Lemma F_3d728 : fetch_word Asan.M.loaded_segments (0x3d728 : word) = Some W_3d728.
Proof. vm_refl. Qed.
Lemma D_3d728 : decode_any W_3d728 = Some (Store SZ8 21 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d72c : bv 32 := 0x02040063.
Lemma F_3d72c : fetch_word Asan.M.loaded_segments (0x3d72c : word) = Some W_3d72c.
Proof. vm_refl. Qed.
Lemma D_3d72c : decode_any W_3d72c = Some (Branch BC_EQ 8 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d730 : bv 32 := 0x00098517.
Lemma F_3d730 : fetch_word Asan.M.loaded_segments (0x3d730 : word) = Some W_3d730.
Proof. vm_refl. Qed.
Lemma D_3d730 : decode_any W_3d730 = Some (Auipc 10 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d734 : bv 32 := 0x18853503.
Lemma F_3d734 : fetch_word Asan.M.loaded_segments (0x3d734 : word) = Some W_3d734.
Proof. vm_refl. Qed.
Lemma D_3d734 : decode_any W_3d734 = Some (Load SZ8 true 10 10 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d738 : bv 32 := 0x00053503.
Lemma F_3d738 : fetch_word Asan.M.loaded_segments (0x3d738 : word) = Some W_3d738.
Proof. vm_refl. Qed.
Lemma D_3d738 : decode_any W_3d738 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d73c : bv 32 := 0x00395593.
Lemma F_3d73c : fetch_word Asan.M.loaded_segments (0x3d73c : word) = Some W_3d73c.
Proof. vm_refl. Qed.
Lemma D_3d73c : decode_any W_3d73c = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d740 : bv 32 := 0x00b50533.
Lemma F_3d740 : fetch_word Asan.M.loaded_segments (0x3d740 : word) = Some W_3d740.
Proof. vm_refl. Qed.
Lemma D_3d740 : decode_any W_3d740 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d744 : bv 32 := 0x00054503.
Lemma F_3d744 : fetch_word Asan.M.loaded_segments (0x3d744 : word) = Some W_3d744.
Proof. vm_refl. Qed.
Lemma D_3d744 : decode_any W_3d744 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d748 : bv 32 := 0x0c051063.
Lemma F_3d748 : fetch_word Asan.M.loaded_segments (0x3d748 : word) = Some W_3d748.
Proof. vm_refl. Qed.
Lemma D_3d748 : decode_any W_3d748 = Some (Branch BC_NE 10 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d74c : bv 32 := 0x020b3503.
Lemma F_3d74c : fetch_word Asan.M.loaded_segments (0x3d74c : word) = Some W_3d74c.
Proof. vm_refl. Qed.
Lemma D_3d74c : decode_any W_3d74c = Some (Load SZ8 true 10 22 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d750 : bv 32 := 0x02a96c63.
Lemma F_3d750 : fetch_word Asan.M.loaded_segments (0x3d750 : word) = Some W_3d750.
Proof. vm_refl. Qed.
Lemma D_3d750 : decode_any W_3d750 = Some (Branch BC_LTU 18 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d754 : bv 32 := 0x00100593.
Lemma F_3d754 : fetch_word Asan.M.loaded_segments (0x3d754 : word) = Some W_3d754.
Proof. vm_refl. Qed.
Lemma D_3d754 : decode_any W_3d754 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d758 : bv 32 := 0x02559593.
Lemma F_3d758 : fetch_word Asan.M.loaded_segments (0x3d758 : word) = Some W_3d758.
Proof. vm_refl. Qed.
Lemma D_3d758 : decode_any W_3d758 = Some (ShiftImm ALU_SLL 11 11 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d75c : bv 32 := 0x00b505b3.
Lemma F_3d75c : fetch_word Asan.M.loaded_segments (0x3d75c : word) = Some W_3d75c.
Proof. vm_refl. Qed.
Lemma D_3d75c : decode_any W_3d75c = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d760 : bv 32 := 0x02b97463.
Lemma F_3d760 : fetch_word Asan.M.loaded_segments (0x3d760 : word) = Some W_3d760.
Proof. vm_refl. Qed.
Lemma D_3d760 : decode_any W_3d760 = Some (Branch BC_GEU 18 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d764 : bv 32 := 0x40a90533.
Lemma F_3d764 : fetch_word Asan.M.loaded_segments (0x3d764 : word) = Some W_3d764.
Proof. vm_refl. Qed.
Lemma D_3d764 : decode_any W_3d764 = Some (Op ALU_SUB 10 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d768 : bv 32 := 0x02055513.
Lemma F_3d768 : fetch_word Asan.M.loaded_segments (0x3d768 : word) = Some W_3d768.
Proof. vm_refl. Qed.
Lemma D_3d768 : decode_any W_3d768 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d76c : bv 32 := 0x01f57413.
Lemma F_3d76c : fetch_word Asan.M.loaded_segments (0x3d76c : word) = Some W_3d76c.
Proof. vm_refl. Qed.
Lemma D_3d76c : decode_any W_3d76c = Some (OpImm ALU_AND 8 10 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d770 : bv 32 := 0x01f00593.
Lemma F_3d770 : fetch_word Asan.M.loaded_segments (0x3d770 : word) = Some W_3d770.
Proof. vm_refl. Qed.
Lemma D_3d770 : decode_any W_3d770 = Some (OpImm ALU_ADD 11 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d774 : bv 32 := 0x56b40663.
Lemma F_3d774 : fetch_word Asan.M.loaded_segments (0x3d774 : word) = Some W_3d774.
Proof. vm_refl. Qed.
Lemma D_3d774 : decode_any W_3d774 = Some (Branch BC_EQ 8 11 1388, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d778 : bv 32 := 0x01000593.
Lemma F_3d778 : fetch_word Asan.M.loaded_segments (0x3d778 : word) = Some W_3d778.
Proof. vm_refl. Qed.
Lemma D_3d778 : decode_any W_3d778 = Some (OpImm ALU_ADD 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d77c : bv 32 := 0x0285ee63.
Lemma F_3d77c : fetch_word Asan.M.loaded_segments (0x3d77c : word) = Some W_3d77c.
Proof. vm_refl. Qed.
Lemma D_3d77c : decode_any W_3d77c = Some (Branch BC_LTU 11 8 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d780 : bv 32 := 0x00541413.
Lemma F_3d780 : fetch_word Asan.M.loaded_segments (0x3d780 : word) = Some W_3d780.
Proof. vm_refl. Qed.
Lemma D_3d780 : decode_any W_3d780 = Some (ShiftImm ALU_SLL 8 8 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d784 : bv 32 := 0x0580006f.
Lemma F_3d784 : fetch_word Asan.M.loaded_segments (0x3d784 : word) = Some W_3d784.
Proof. vm_refl. Qed.
Lemma D_3d784 : decode_any W_3d784 = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d788 : bv 32 := 0x040b3503.
Lemma F_3d788 : fetch_word Asan.M.loaded_segments (0x3d788 : word) = Some W_3d788.
Proof. vm_refl. Qed.
Lemma D_3d788 : decode_any W_3d788 = Some (Load SZ8 true 10 22 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d78c : bv 32 := 0xfff50593.
Lemma F_3d78c : fetch_word Asan.M.loaded_segments (0x3d78c : word) = Some W_3d78c.
Proof. vm_refl. Qed.
Lemma D_3d78c : decode_any W_3d78c = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d790 : bv 32 := 0x0125f633.
Lemma F_3d790 : fetch_word Asan.M.loaded_segments (0x3d790 : word) = Some W_3d790.
Proof. vm_refl. Qed.
Lemma D_3d790 : decode_any W_3d790 = Some (Op ALU_AND 12 11 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d794 : bv 32 := 0x52061663.
Lemma F_3d794 : fetch_word Asan.M.loaded_segments (0x3d794 : word) = Some W_3d794.
Proof. vm_refl. Qed.
Lemma D_3d794 : decode_any W_3d794 = Some (Branch BC_NE 12 0 1324, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d798 : bv 32 := 0x00b57633.
Lemma F_3d798 : fetch_word Asan.M.loaded_segments (0x3d798 : word) = Some W_3d798.
Proof. vm_refl. Qed.
Lemma D_3d798 : decode_any W_3d798 = Some (Op ALU_AND 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d79c : bv 32 := 0x54061663.
Lemma F_3d79c : fetch_word Asan.M.loaded_segments (0x3d79c : word) = Some W_3d79c.
Proof. vm_refl. Qed.
Lemma D_3d79c : decode_any W_3d79c = Some (Branch BC_NE 12 0 1356, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7a0 : bv 32 := 0x40a90633.
Lemma F_3d7a0 : fetch_word Asan.M.loaded_segments (0x3d7a0 : word) = Some W_3d7a0.
Proof. vm_refl. Qed.
Lemma D_3d7a0 : decode_any W_3d7a0 = Some (Op ALU_SUB 12 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7a4 : bv 32 := 0x01063603.
Lemma F_3d7a4 : fetch_word Asan.M.loaded_segments (0x3d7a4 : word) = Some W_3d7a4.
Proof. vm_refl. Qed.
Lemma D_3d7a4 : decode_any W_3d7a4 = Some (Load SZ8 true 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7a8 : bv 32 := 0x00b605b3.
Lemma F_3d7a8 : fetch_word Asan.M.loaded_segments (0x3d7a8 : word) = Some W_3d7a8.
Proof. vm_refl. Qed.
Lemma D_3d7a8 : decode_any W_3d7a8 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7ac : bv 32 := 0x40a00433.
Lemma F_3d7ac : fetch_word Asan.M.loaded_segments (0x3d7ac : word) = Some W_3d7ac.
Proof. vm_refl. Qed.
Lemma D_3d7ac : decode_any W_3d7ac = Some (Op ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7b0 : bv 32 := 0x0085f433.
Lemma F_3d7b0 : fetch_word Asan.M.loaded_segments (0x3d7b0 : word) = Some W_3d7b0.
Proof. vm_refl. Qed.
Lemma D_3d7b0 : decode_any W_3d7b0 = Some (Op ALU_AND 8 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7b4 : bv 32 := 0x0280006f.
Lemma F_3d7b4 : fetch_word Asan.M.loaded_segments (0x3d7b4 : word) = Some W_3d7b4.
Proof. vm_refl. Qed.
Lemma D_3d7b4 : decode_any W_3d7b4 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7b8 : bv 32 := 0xff040413.
Lemma F_3d7b8 : fetch_word Asan.M.loaded_segments (0x3d7b8 : word) = Some W_3d7b8.
Proof. vm_refl. Qed.
Lemma D_3d7b8 : decode_any W_3d7b8 = Some (OpImm ALU_ADD 8 8 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7bc : bv 32 := 0x20000593.
Lemma F_3d7bc : fetch_word Asan.M.loaded_segments (0x3d7bc : word) = Some W_3d7bc.
Proof. vm_refl. Qed.
Lemma D_3d7bc : decode_any W_3d7bc = Some (OpImm ALU_ADD 11 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7c0 : bv 32 := 0x03f51513.
Lemma F_3d7c0 : fetch_word Asan.M.loaded_segments (0x3d7c0 : word) = Some W_3d7c0.
Proof. vm_refl. Qed.
Lemma D_3d7c0 : decode_any W_3d7c0 = Some (ShiftImm ALU_SLL 10 10 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7c4 : bv 32 := 0x00145413.
Lemma F_3d7c4 : fetch_word Asan.M.loaded_segments (0x3d7c4 : word) = Some W_3d7c4.
Proof. vm_refl. Qed.
Lemma D_3d7c4 : decode_any W_3d7c4 = Some (ShiftImm ALU_SRL 8 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7c8 : bv 32 := 0x00859433.
Lemma F_3d7c8 : fetch_word Asan.M.loaded_segments (0x3d7c8 : word) = Some W_3d7c8.
Proof. vm_refl. Qed.
Lemma D_3d7c8 : decode_any W_3d7c8 = Some (Op ALU_SLL 8 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7cc : bv 32 := 0x00145593.
Lemma F_3d7cc : fetch_word Asan.M.loaded_segments (0x3d7cc : word) = Some W_3d7cc.
Proof. vm_refl. Qed.
Lemma D_3d7cc : decode_any W_3d7cc = Some (ShiftImm ALU_SRL 11 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7d0 : bv 32 := 0x43f55513.
Lemma F_3d7d0 : fetch_word Asan.M.loaded_segments (0x3d7d0 : word) = Some W_3d7d0.
Proof. vm_refl. Qed.
Lemma D_3d7d0 : decode_any W_3d7d0 = Some (ShiftImm ALU_SRA 10 10 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7d4 : bv 32 := 0x00b57533.
Lemma F_3d7d4 : fetch_word Asan.M.loaded_segments (0x3d7d4 : word) = Some W_3d7d4.
Proof. vm_refl. Qed.
Lemma D_3d7d4 : decode_any W_3d7d4 = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7d8 : bv 32 := 0x00850433.
Lemma F_3d7d8 : fetch_word Asan.M.loaded_segments (0x3d7d8 : word) = Some W_3d7d8.
Proof. vm_refl. Qed.
Lemma D_3d7d8 : decode_any W_3d7d8 = Some (Op ALU_ADD 8 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7dc : bv 32 := 0x007c8c93.
Lemma F_3d7dc : fetch_word Asan.M.loaded_segments (0x3d7dc : word) = Some W_3d7dc.
Proof. vm_refl. Qed.
Lemma D_3d7dc : decode_any W_3d7dc = Some (OpImm ALU_ADD 25 25 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7e0 : bv 32 := 0xff8cfb13.
Lemma F_3d7e0 : fetch_word Asan.M.loaded_segments (0x3d7e0 : word) = Some W_3d7e0.
Proof. vm_refl. Qed.
Lemma D_3d7e0 : decode_any W_3d7e0 = Some (OpImm ALU_AND 22 25 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7e4 : bv 32 := 0x412a05b3.
Lemma F_3d7e4 : fetch_word Asan.M.loaded_segments (0x3d7e4 : word) = Some W_3d7e4.
Proof. vm_refl. Qed.
Lemma D_3d7e4 : decode_any W_3d7e4 = Some (Op ALU_SUB 11 20 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7e8 : bv 32 := 0x0fa00613.
Lemma F_3d7e8 : fetch_word Asan.M.loaded_segments (0x3d7e8 : word) = Some W_3d7e8.
Proof. vm_refl. Qed.
Lemma D_3d7e8 : decode_any W_3d7e8 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7ec : bv 32 := 0x00090513.
Lemma F_3d7ec : fetch_word Asan.M.loaded_segments (0x3d7ec : word) = Some W_3d7ec.
Proof. vm_refl. Qed.
Lemma D_3d7ec : decode_any W_3d7ec = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7f0 : bv 32 := 0x788230ef.
Lemma F_3d7f0 : fetch_word Asan.M.loaded_segments (0x3d7f0 : word) = Some W_3d7f0.
Proof. vm_refl. Qed.
Lemma D_3d7f0 : decode_any W_3d7f0 = Some (Jal 1 145288, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7f4 : bv 32 := 0x416905b3.
Lemma F_3d7f4 : fetch_word Asan.M.loaded_segments (0x3d7f4 : word) = Some W_3d7f4.
Proof. vm_refl. Qed.
Lemma D_3d7f4 : decode_any W_3d7f4 = Some (Op ALU_SUB 11 18 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7f8 : bv 32 := 0x008585b3.
Lemma F_3d7f8 : fetch_word Asan.M.loaded_segments (0x3d7f8 : word) = Some W_3d7f8.
Proof. vm_refl. Qed.
Lemma D_3d7f8 : decode_any W_3d7f8 = Some (Op ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d7fc : bv 32 := 0x0fa00613.
Lemma F_3d7fc : fetch_word Asan.M.loaded_segments (0x3d7fc : word) = Some W_3d7fc.
Proof. vm_refl. Qed.
Lemma D_3d7fc : decode_any W_3d7fc = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d800 : bv 32 := 0x000b0513.
Lemma F_3d800 : fetch_word Asan.M.loaded_segments (0x3d800 : word) = Some W_3d800.
Proof. vm_refl. Qed.
Lemma D_3d800 : decode_any W_3d800 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d804 : bv 32 := 0x774230ef.
Lemma F_3d804 : fetch_word Asan.M.loaded_segments (0x3d804 : word) = Some W_3d804.
Proof. vm_refl. Qed.
Lemma D_3d804 : decode_any W_3d804 = Some (Jal 1 145268, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d808 : bv 32 := 0xfff80537.
Lemma F_3d808 : fetch_word Asan.M.loaded_segments (0x3d808 : word) = Some W_3d808.
Proof. vm_refl. Qed.
Lemma D_3d808 : decode_any W_3d808 = Some (Lui 10 1048448, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d80c : bv 32 := 0x01055513.
Lemma F_3d80c : fetch_word Asan.M.loaded_segments (0x3d80c : word) = Some W_3d80c.
Proof. vm_refl. Qed.
Lemma D_3d80c : decode_any W_3d80c = Some (ShiftImm ALU_SRL 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d810 : bv 32 := 0x00a4fb33.
Lemma F_3d810 : fetch_word Asan.M.loaded_segments (0x3d810 : word) = Some W_3d810.
Proof. vm_refl. Qed.
Lemma D_3d810 : decode_any W_3d810 = Some (Op ALU_AND 22 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d814 : bv 32 := 0x000b0a63.
Lemma F_3d814 : fetch_word Asan.M.loaded_segments (0x3d814 : word) = Some W_3d814.
Proof. vm_refl. Qed.
Lemma D_3d814 : decode_any W_3d814 = Some (Branch BC_EQ 22 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d818 : bv 32 := 0x000a0513.
Lemma F_3d818 : fetch_word Asan.M.loaded_segments (0x3d818 : word) = Some W_3d818.
Proof. vm_refl. Qed.
Lemma D_3d818 : decode_any W_3d818 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d81c : bv 32 := 0x000b0593.
Lemma F_3d81c : fetch_word Asan.M.loaded_segments (0x3d81c : word) = Some W_3d81c.
Proof. vm_refl. Qed.
Lemma D_3d81c : decode_any W_3d81c = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d820 : bv 32 := 0x00000613.
Lemma F_3d820 : fetch_word Asan.M.loaded_segments (0x3d820 : word) = Some W_3d820.
Proof. vm_refl. Qed.
Lemma D_3d820 : decode_any W_3d820 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d824 : bv 32 := 0x754230ef.
Lemma F_3d824 : fetch_word Asan.M.loaded_segments (0x3d824 : word) = Some W_3d824.
Proof. vm_refl. Qed.
Lemma D_3d824 : decode_any W_3d824 = Some (Jal 1 145236, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d828 : bv 32 := 0x09648a63.
Lemma F_3d828 : fetch_word Asan.M.loaded_segments (0x3d828 : word) = Some W_3d828.
Proof. vm_refl. Qed.
Lemma D_3d828 : decode_any W_3d828 = Some (Branch BC_EQ 9 22 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d82c : bv 32 := 0x738230ef.
Lemma F_3d82c : fetch_word Asan.M.loaded_segments (0x3d82c : word) = Some W_3d82c.
Proof. vm_refl. Qed.
Lemma D_3d82c : decode_any W_3d82c = Some (Jal 1 145208, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d830 : bv 32 := 0x08050663.
Lemma F_3d830 : fetch_word Asan.M.loaded_segments (0x3d830 : word) = Some W_3d830.
Proof. vm_refl. Qed.
Lemma D_3d830 : decode_any W_3d830 = Some (Branch BC_EQ 10 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d834 : bv 32 := 0x00098517.
Lemma F_3d834 : fetch_word Asan.M.loaded_segments (0x3d834 : word) = Some W_3d834.
Proof. vm_refl. Qed.
Lemma D_3d834 : decode_any W_3d834 = Some (Auipc 10 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d838 : bv 32 := 0x08453503.
Lemma F_3d838 : fetch_word Asan.M.loaded_segments (0x3d838 : word) = Some W_3d838.
Proof. vm_refl. Qed.
Lemma D_3d838 : decode_any W_3d838 = Some (Load SZ8 true 10 10 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d83c : bv 32 := 0x00053503.
Lemma F_3d83c : fetch_word Asan.M.loaded_segments (0x3d83c : word) = Some W_3d83c.
Proof. vm_refl. Qed.
Lemma D_3d83c : decode_any W_3d83c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d840 : bv 32 := 0x016a0b33.
Lemma F_3d840 : fetch_word Asan.M.loaded_segments (0x3d840 : word) = Some W_3d840.
Proof. vm_refl. Qed.
Lemma D_3d840 : decode_any W_3d840 = Some (Op ALU_ADD 22 20 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d844 : bv 32 := 0xfff50593.
Lemma F_3d844 : fetch_word Asan.M.loaded_segments (0x3d844 : word) = Some W_3d844.
Proof. vm_refl. Qed.
Lemma D_3d844 : decode_any W_3d844 = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d848 : bv 32 := 0x00b53633.
Lemma F_3d848 : fetch_word Asan.M.loaded_segments (0x3d848 : word) = Some W_3d848.
Proof. vm_refl. Qed.
Lemma D_3d848 : decode_any W_3d848 = Some (Op ALU_SLTU 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d84c : bv 32 := 0xfff60613.
Lemma F_3d84c : fetch_word Asan.M.loaded_segments (0x3d84c : word) = Some W_3d84c.
Proof. vm_refl. Qed.
Lemma D_3d84c : decode_any W_3d84c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d850 : bv 32 := 0x00b67633.
Lemma F_3d850 : fetch_word Asan.M.loaded_segments (0x3d850 : word) = Some W_3d850.
Proof. vm_refl. Qed.
Lemma D_3d850 : decode_any W_3d850 = Some (Op ALU_AND 12 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d854 : bv 32 := 0x05667263.
Lemma F_3d854 : fetch_word Asan.M.loaded_segments (0x3d854 : word) = Some W_3d854.
Proof. vm_refl. Qed.
Lemma D_3d854 : decode_any W_3d854 = Some (Branch BC_GEU 12 22 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d858 : bv 32 := 0x00098617.
Lemma F_3d858 : fetch_word Asan.M.loaded_segments (0x3d858 : word) = Some W_3d858.
Proof. vm_refl. Qed.
Lemma D_3d858 : decode_any W_3d858 = Some (Auipc 12 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d85c : bv 32 := 0x06863603.
Lemma F_3d85c : fetch_word Asan.M.loaded_segments (0x3d85c : word) = Some W_3d85c.
Proof. vm_refl. Qed.
Lemma D_3d85c : decode_any W_3d85c = Some (Load SZ8 true 12 12 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d860 : bv 32 := 0x00098697.
Lemma F_3d860 : fetch_word Asan.M.loaded_segments (0x3d860 : word) = Some W_3d860.
Proof. vm_refl. Qed.
Lemma D_3d860 : decode_any W_3d860 = Some (Auipc 13 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d864 : bv 32 := 0x0686b683.
Lemma F_3d864 : fetch_word Asan.M.loaded_segments (0x3d864 : word) = Some W_3d864.
Proof. vm_refl. Qed.
Lemma D_3d864 : decode_any W_3d864 = Some (Load SZ8 true 13 13 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d868 : bv 32 := 0x00063783.
Lemma F_3d868 : fetch_word Asan.M.loaded_segments (0x3d868 : word) = Some W_3d868.
Proof. vm_refl. Qed.
Lemma D_3d868 : decode_any W_3d868 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d86c : bv 32 := 0x0006b603.
Lemma F_3d86c : fetch_word Asan.M.loaded_segments (0x3d86c : word) = Some W_3d86c.
Proof. vm_refl. Qed.
Lemma D_3d86c : decode_any W_3d86c = Some (Load SZ8 true 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d870 : bv 32 := 0xfff78713.
Lemma F_3d870 : fetch_word Asan.M.loaded_segments (0x3d870 : word) = Some W_3d870.
Proof. vm_refl. Qed.
Lemma D_3d870 : decode_any W_3d870 = Some (OpImm ALU_ADD 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d874 : bv 32 := 0x01677463.
Lemma F_3d874 : fetch_word Asan.M.loaded_segments (0x3d874 : word) = Some W_3d874.
Proof. vm_refl. Qed.
Lemma D_3d874 : decode_any W_3d874 = Some (Branch BC_GEU 14 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d878 : bv 32 := 0x03667063.
Lemma F_3d878 : fetch_word Asan.M.loaded_segments (0x3d878 : word) = Some W_3d878.
Proof. vm_refl. Qed.
Lemma D_3d878 : decode_any W_3d878 = Some (Branch BC_GEU 12 22 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d87c : bv 32 := 0x00098697.
Lemma F_3d87c : fetch_word Asan.M.loaded_segments (0x3d87c : word) = Some W_3d87c.
Proof. vm_refl. Qed.
Lemma D_3d87c : decode_any W_3d87c = Some (Auipc 13 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d880 : bv 32 := 0x0546b683.
Lemma F_3d880 : fetch_word Asan.M.loaded_segments (0x3d880 : word) = Some W_3d880.
Proof. vm_refl. Qed.
Lemma D_3d880 : decode_any W_3d880 = Some (Load SZ8 true 13 13 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d884 : bv 32 := 0x0006b883.
Lemma F_3d884 : fetch_word Asan.M.loaded_segments (0x3d884 : word) = Some W_3d884.
Proof. vm_refl. Qed.
Lemma D_3d884 : decode_any W_3d884 = Some (Load SZ8 true 17 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d888 : bv 32 := 0x0038d693.
Lemma F_3d888 : fetch_word Asan.M.loaded_segments (0x3d888 : word) = Some W_3d888.
Proof. vm_refl. Qed.
Lemma D_3d888 : decode_any W_3d888 = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d88c : bv 32 := 0x00a68833.
Lemma F_3d88c : fetch_word Asan.M.loaded_segments (0x3d88c : word) = Some W_3d88c.
Proof. vm_refl. Qed.
Lemma D_3d88c : decode_any W_3d88c = Some (Op ALU_ADD 16 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d890 : bv 32 := 0x2568ea63.
Lemma F_3d890 : fetch_word Asan.M.loaded_segments (0x3d890 : word) = Some W_3d890.
Proof. vm_refl. Qed.
Lemma D_3d890 : decode_any W_3d890 = Some (Branch BC_LTU 17 22 596, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d894 : bv 32 := 0x25687863.
Lemma F_3d894 : fetch_word Asan.M.loaded_segments (0x3d894 : word) = Some W_3d894.
Proof. vm_refl. Qed.
Lemma D_3d894 : decode_any W_3d894 = Some (Branch BC_GEU 16 22 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d898 : bv 32 := 0x00098597.
Lemma F_3d898 : fetch_word Asan.M.loaded_segments (0x3d898 : word) = Some W_3d898.
Proof. vm_refl. Qed.
Lemma D_3d898 : decode_any W_3d898 = Some (Auipc 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d89c : bv 32 := 0x0185b583.
Lemma F_3d89c : fetch_word Asan.M.loaded_segments (0x3d89c : word) = Some W_3d89c.
Proof. vm_refl. Qed.
Lemma D_3d89c : decode_any W_3d89c = Some (Load SZ8 true 11 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8a0 : bv 32 := 0x0555c583.
Lemma F_3d8a0 : fetch_word Asan.M.loaded_segments (0x3d8a0 : word) = Some W_3d8a0.
Proof. vm_refl. Qed.
Lemma D_3d8a0 : decode_any W_3d8a0 = Some (Load SZ1 false 11 11 85, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8a4 : bv 32 := 0x003b5613.
Lemma F_3d8a4 : fetch_word Asan.M.loaded_segments (0x3d8a4 : word) = Some W_3d8a4.
Proof. vm_refl. Qed.
Lemma D_3d8a4 : decode_any W_3d8a4 = Some (ShiftImm ALU_SRL 12 22 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8a8 : bv 32 := 0x00c50533.
Lemma F_3d8a8 : fetch_word Asan.M.loaded_segments (0x3d8a8 : word) = Some W_3d8a8.
Proof. vm_refl. Qed.
Lemma D_3d8a8 : decode_any W_3d8a8 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8ac : bv 32 := 0x40b005bb.
Lemma F_3d8ac : fetch_word Asan.M.loaded_segments (0x3d8ac : word) = Some W_3d8ac.
Proof. vm_refl. Qed.
Lemma D_3d8ac : decode_any W_3d8ac = Some (Op32 ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8b0 : bv 32 := 0x00b4f5b3.
Lemma F_3d8b0 : fetch_word Asan.M.loaded_segments (0x3d8b0 : word) = Some W_3d8b0.
Proof. vm_refl. Qed.
Lemma D_3d8b0 : decode_any W_3d8b0 = Some (Op ALU_AND 11 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8b4 : bv 32 := 0x0075f593.
Lemma F_3d8b4 : fetch_word Asan.M.loaded_segments (0x3d8b4 : word) = Some W_3d8b4.
Proof. vm_refl. Qed.
Lemma D_3d8b4 : decode_any W_3d8b4 = Some (OpImm ALU_AND 11 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8b8 : bv 32 := 0x00b50023.
Lemma F_3d8b8 : fetch_word Asan.M.loaded_segments (0x3d8b8 : word) = Some W_3d8b8.
Proof. vm_refl. Qed.
Lemma D_3d8b8 : decode_any W_3d8b8 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8bc : bv 32 := 0x0f42b0ef.
Lemma F_3d8bc : fetch_word Asan.M.loaded_segments (0x3d8bc : word) = Some W_3d8bc.
Proof. vm_refl. Qed.
Lemma D_3d8bc : decode_any W_3d8bc = Some (Jal 1 176372, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8c0 : bv 32 := 0x01053583.
Lemma F_3d8c0 : fetch_word Asan.M.loaded_segments (0x3d8c0 : word) = Some W_3d8c0.
Proof. vm_refl. Qed.
Lemma D_3d8c0 : decode_any W_3d8c0 = Some (Load SZ8 true 11 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8c4 : bv 32 := 0x00053603.
Lemma F_3d8c4 : fetch_word Asan.M.loaded_segments (0x3d8c4 : word) = Some W_3d8c4.
Proof. vm_refl. Qed.
Lemma D_3d8c4 : decode_any W_3d8c4 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8c8 : bv 32 := 0x00853683.
Lemma F_3d8c8 : fetch_word Asan.M.loaded_segments (0x3d8c8 : word) = Some W_3d8c8.
Proof. vm_refl. Qed.
Lemma D_3d8c8 : decode_any W_3d8c8 = Some (Load SZ8 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8cc : bv 32 := 0x40998733.
Lemma F_3d8cc : fetch_word Asan.M.loaded_segments (0x3d8cc : word) = Some W_3d8cc.
Proof. vm_refl. Qed.
Lemma D_3d8cc : decode_any W_3d8cc = Some (Op ALU_SUB 14 19 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8d0 : bv 32 := 0x00b705b3.
Lemma F_3d8d0 : fetch_word Asan.M.loaded_segments (0x3d8d0 : word) = Some W_3d8d0.
Proof. vm_refl. Qed.
Lemma D_3d8d0 : decode_any W_3d8d0 = Some (Op ALU_ADD 11 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8d4 : bv 32 := 0x00010737.
Lemma F_3d8d4 : fetch_word Asan.M.loaded_segments (0x3d8d4 : word) = Some W_3d8d4.
Proof. vm_refl. Qed.
Lemma D_3d8d4 : decode_any W_3d8d4 = Some (Lui 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8d8 : bv 32 := 0x0017071b.
Lemma F_3d8d8 : fetch_word Asan.M.loaded_segments (0x3d8d8 : word) = Some W_3d8d8.
Proof. vm_refl. Qed.
Lemma D_3d8d8 : decode_any W_3d8d8 = Some (OpImm32 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8dc : bv 32 := 0x00160613.
Lemma F_3d8dc : fetch_word Asan.M.loaded_segments (0x3d8dc : word) = Some W_3d8dc.
Proof. vm_refl. Qed.
Lemma D_3d8dc : decode_any W_3d8dc = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8e0 : bv 32 := 0x009686b3.
Lemma F_3d8e0 : fetch_word Asan.M.loaded_segments (0x3d8e0 : word) = Some W_3d8e0.
Proof. vm_refl. Qed.
Lemma D_3d8e0 : decode_any W_3d8e0 = Some (Op ALU_ADD 13 13 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8e4 : bv 32 := 0x00c53023.
Lemma F_3d8e4 : fetch_word Asan.M.loaded_segments (0x3d8e4 : word) = Some W_3d8e4.
Proof. vm_refl. Qed.
Lemma D_3d8e4 : decode_any W_3d8e4 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8e8 : bv 32 := 0x00d53423.
Lemma F_3d8e8 : fetch_word Asan.M.loaded_segments (0x3d8e8 : word) = Some W_3d8e8.
Proof. vm_refl. Qed.
Lemma D_3d8e8 : decode_any W_3d8e8 = Some (Store SZ8 10 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8ec : bv 32 := 0x00b53823.
Lemma F_3d8ec : fetch_word Asan.M.loaded_segments (0x3d8ec : word) = Some W_3d8ec.
Proof. vm_refl. Qed.
Lemma D_3d8ec : decode_any W_3d8ec = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8f0 : bv 32 := 0x00e9ee63.
Lemma F_3d8f0 : fetch_word Asan.M.loaded_segments (0x3d8f0 : word) = Some W_3d8f0.
Proof. vm_refl. Qed.
Lemma D_3d8f0 : decode_any W_3d8f0 = Some (Branch BC_LTU 19 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8f4 : bv 32 := 0x06853583.
Lemma F_3d8f4 : fetch_word Asan.M.loaded_segments (0x3d8f4 : word) = Some W_3d8f4.
Proof. vm_refl. Qed.
Lemma D_3d8f4 : decode_any W_3d8f4 = Some (Load SZ8 true 11 10 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8f8 : bv 32 := 0x00158593.
Lemma F_3d8f8 : fetch_word Asan.M.loaded_segments (0x3d8f8 : word) = Some W_3d8f8.
Proof. vm_refl. Qed.
Lemma D_3d8f8 : decode_any W_3d8f8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d8fc : bv 32 := 0x06b53423.
Lemma F_3d8fc : fetch_word Asan.M.loaded_segments (0x3d8fc : word) = Some W_3d8fc.
Proof. vm_refl. Qed.
Lemma D_3d8fc : decode_any W_3d8fc = Some (Store SZ8 10 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d900 : bv 32 := 0x00813503.
Lemma F_3d900 : fetch_word Asan.M.loaded_segments (0x3d900 : word) = Some W_3d900.
Proof. vm_refl. Qed.
Lemma D_3d900 : decode_any W_3d900 = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d904 : bv 32 := 0x10051c63.
Lemma F_3d904 : fetch_word Asan.M.loaded_segments (0x3d904 : word) = Some W_3d904.
Proof. vm_refl. Qed.
Lemma D_3d904 : decode_any W_3d904 = Some (Branch BC_NE 10 0 280, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d908 : bv 32 := 0x1480006f.
Lemma F_3d908 : fetch_word Asan.M.loaded_segments (0x3d908 : word) = Some W_3d908.
Proof. vm_refl. Qed.
Lemma D_3d908 : decode_any W_3d908 = Some (Jal 0 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d90c : bv 32 := 0x20000593.
Lemma F_3d90c : fetch_word Asan.M.loaded_segments (0x3d90c : word) = Some W_3d90c.
Proof. vm_refl. Qed.
Lemma D_3d90c : decode_any W_3d90c = Some (OpImm ALU_ADD 11 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d910 : bv 32 := 0x07050513.
Lemma F_3d910 : fetch_word Asan.M.loaded_segments (0x3d910 : word) = Some W_3d910.
Proof. vm_refl. Qed.
Lemma D_3d910 : decode_any W_3d910 = Some (OpImm ALU_ADD 10 10 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d914 : bv 32 := 0x0135e863.
Lemma F_3d914 : fetch_word Asan.M.loaded_segments (0x3d914 : word) = Some W_3d914.
Proof. vm_refl. Qed.
Lemma D_3d914 : decode_any W_3d914 = Some (Branch BC_LTU 11 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d918 : bv 32 := 0x01f98593.
Lemma F_3d918 : fetch_word Asan.M.loaded_segments (0x3d918 : word) = Some W_3d918.
Proof. vm_refl. Qed.
Lemma D_3d918 : decode_any W_3d918 = Some (OpImm ALU_ADD 11 19 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d91c : bv 32 := 0x0055d593.
Lemma F_3d91c : fetch_word Asan.M.loaded_segments (0x3d91c : word) = Some W_3d91c.
Proof. vm_refl. Qed.
Lemma D_3d91c : decode_any W_3d91c = Some (ShiftImm ALU_SRL 11 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d920 : bv 32 := 0x0e00006f.
Lemma F_3d920 : fetch_word Asan.M.loaded_segments (0x3d920 : word) = Some W_3d920.
Proof. vm_refl. Qed.
Lemma D_3d920 : decode_any W_3d920 = Some (Jal 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d924 : bv 32 := 0x0019d593.
Lemma F_3d924 : fetch_word Asan.M.loaded_segments (0x3d924 : word) = Some W_3d924.
Proof. vm_refl. Qed.
Lemma D_3d924 : decode_any W_3d924 = Some (ShiftImm ALU_SRL 11 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d928 : bv 32 := 0x55555637.
Lemma F_3d928 : fetch_word Asan.M.loaded_segments (0x3d928 : word) = Some W_3d928.
Proof. vm_refl. Qed.
Lemma D_3d928 : decode_any W_3d928 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d92c : bv 32 := 0x333336b7.
Lemma F_3d92c : fetch_word Asan.M.loaded_segments (0x3d92c : word) = Some W_3d92c.
Proof. vm_refl. Qed.
Lemma D_3d92c : decode_any W_3d92c = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d930 : bv 32 := 0x0f0f1737.
Lemma F_3d930 : fetch_word Asan.M.loaded_segments (0x3d930 : word) = Some W_3d930.
Proof. vm_refl. Qed.
Lemma D_3d930 : decode_any W_3d930 = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d934 : bv 32 := 0x010107b7.
Lemma F_3d934 : fetch_word Asan.M.loaded_segments (0x3d934 : word) = Some W_3d934.
Proof. vm_refl. Qed.
Lemma D_3d934 : decode_any W_3d934 = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d938 : bv 32 := 0x00b9e5b3.
Lemma F_3d938 : fetch_word Asan.M.loaded_segments (0x3d938 : word) = Some W_3d938.
Proof. vm_refl. Qed.
Lemma D_3d938 : decode_any W_3d938 = Some (Op ALU_OR 11 19 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d93c : bv 32 := 0x5556061b.
Lemma F_3d93c : fetch_word Asan.M.loaded_segments (0x3d93c : word) = Some W_3d93c.
Proof. vm_refl. Qed.
Lemma D_3d93c : decode_any W_3d93c = Some (OpImm32 12 12 1365, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d940 : bv 32 := 0x3336869b.
Lemma F_3d940 : fetch_word Asan.M.loaded_segments (0x3d940 : word) = Some W_3d940.
Proof. vm_refl. Qed.
Lemma D_3d940 : decode_any W_3d940 = Some (OpImm32 13 13 819, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d944 : bv 32 := 0xf0f7071b.
Lemma F_3d944 : fetch_word Asan.M.loaded_segments (0x3d944 : word) = Some W_3d944.
Proof. vm_refl. Qed.
Lemma D_3d944 : decode_any W_3d944 = Some (OpImm32 14 14 3855, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d948 : bv 32 := 0x1017879b.
Lemma F_3d948 : fetch_word Asan.M.loaded_segments (0x3d948 : word) = Some W_3d948.
Proof. vm_refl. Qed.
Lemma D_3d948 : decode_any W_3d948 = Some (OpImm32 15 15 257, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d94c : bv 32 := 0x0025d813.
Lemma F_3d94c : fetch_word Asan.M.loaded_segments (0x3d94c : word) = Some W_3d94c.
Proof. vm_refl. Qed.
Lemma D_3d94c : decode_any W_3d94c = Some (ShiftImm ALU_SRL 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d950 : bv 32 := 0x0105e5b3.
Lemma F_3d950 : fetch_word Asan.M.loaded_segments (0x3d950 : word) = Some W_3d950.
Proof. vm_refl. Qed.
Lemma D_3d950 : decode_any W_3d950 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d954 : bv 32 := 0x02061813.
Lemma F_3d954 : fetch_word Asan.M.loaded_segments (0x3d954 : word) = Some W_3d954.
Proof. vm_refl. Qed.
Lemma D_3d954 : decode_any W_3d954 = Some (ShiftImm ALU_SLL 16 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d958 : bv 32 := 0x01060633.
Lemma F_3d958 : fetch_word Asan.M.loaded_segments (0x3d958 : word) = Some W_3d958.
Proof. vm_refl. Qed.
Lemma D_3d958 : decode_any W_3d958 = Some (Op ALU_ADD 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d95c : bv 32 := 0x02069813.
Lemma F_3d95c : fetch_word Asan.M.loaded_segments (0x3d95c : word) = Some W_3d95c.
Proof. vm_refl. Qed.
Lemma D_3d95c : decode_any W_3d95c = Some (ShiftImm ALU_SLL 16 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d960 : bv 32 := 0x010686b3.
Lemma F_3d960 : fetch_word Asan.M.loaded_segments (0x3d960 : word) = Some W_3d960.
Proof. vm_refl. Qed.
Lemma D_3d960 : decode_any W_3d960 = Some (Op ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d964 : bv 32 := 0x02071813.
Lemma F_3d964 : fetch_word Asan.M.loaded_segments (0x3d964 : word) = Some W_3d964.
Proof. vm_refl. Qed.
Lemma D_3d964 : decode_any W_3d964 = Some (ShiftImm ALU_SLL 16 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d968 : bv 32 := 0x01070733.
Lemma F_3d968 : fetch_word Asan.M.loaded_segments (0x3d968 : word) = Some W_3d968.
Proof. vm_refl. Qed.
Lemma D_3d968 : decode_any W_3d968 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d96c : bv 32 := 0x02079813.
Lemma F_3d96c : fetch_word Asan.M.loaded_segments (0x3d96c : word) = Some W_3d96c.
Proof. vm_refl. Qed.
Lemma D_3d96c : decode_any W_3d96c = Some (ShiftImm ALU_SLL 16 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d970 : bv 32 := 0x010787b3.
Lemma F_3d970 : fetch_word Asan.M.loaded_segments (0x3d970 : word) = Some W_3d970.
Proof. vm_refl. Qed.
Lemma D_3d970 : decode_any W_3d970 = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d974 : bv 32 := 0x0045d813.
Lemma F_3d974 : fetch_word Asan.M.loaded_segments (0x3d974 : word) = Some W_3d974.
Proof. vm_refl. Qed.
Lemma D_3d974 : decode_any W_3d974 = Some (ShiftImm ALU_SRL 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d978 : bv 32 := 0x0105e5b3.
Lemma F_3d978 : fetch_word Asan.M.loaded_segments (0x3d978 : word) = Some W_3d978.
Proof. vm_refl. Qed.
Lemma D_3d978 : decode_any W_3d978 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d97c : bv 32 := 0x0085d813.
Lemma F_3d97c : fetch_word Asan.M.loaded_segments (0x3d97c : word) = Some W_3d97c.
Proof. vm_refl. Qed.
Lemma D_3d97c : decode_any W_3d97c = Some (ShiftImm ALU_SRL 16 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d980 : bv 32 := 0x0105e5b3.
Lemma F_3d980 : fetch_word Asan.M.loaded_segments (0x3d980 : word) = Some W_3d980.
Proof. vm_refl. Qed.
Lemma D_3d980 : decode_any W_3d980 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d984 : bv 32 := 0x0105d813.
Lemma F_3d984 : fetch_word Asan.M.loaded_segments (0x3d984 : word) = Some W_3d984.
Proof. vm_refl. Qed.
Lemma D_3d984 : decode_any W_3d984 = Some (ShiftImm ALU_SRL 16 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d988 : bv 32 := 0x0105e5b3.
Lemma F_3d988 : fetch_word Asan.M.loaded_segments (0x3d988 : word) = Some W_3d988.
Proof. vm_refl. Qed.
Lemma D_3d988 : decode_any W_3d988 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d98c : bv 32 := 0x0205d813.
Lemma F_3d98c : fetch_word Asan.M.loaded_segments (0x3d98c : word) = Some W_3d98c.
Proof. vm_refl. Qed.
Lemma D_3d98c : decode_any W_3d98c = Some (ShiftImm ALU_SRL 16 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d990 : bv 32 := 0x0105e5b3.
Lemma F_3d990 : fetch_word Asan.M.loaded_segments (0x3d990 : word) = Some W_3d990.
Proof. vm_refl. Qed.
Lemma D_3d990 : decode_any W_3d990 = Some (Op ALU_OR 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d994 : bv 32 := 0xfff5c593.
Lemma F_3d994 : fetch_word Asan.M.loaded_segments (0x3d994 : word) = Some W_3d994.
Proof. vm_refl. Qed.
Lemma D_3d994 : decode_any W_3d994 = Some (OpImm ALU_XOR 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d998 : bv 32 := 0x0015d813.
Lemma F_3d998 : fetch_word Asan.M.loaded_segments (0x3d998 : word) = Some W_3d998.
Proof. vm_refl. Qed.
Lemma D_3d998 : decode_any W_3d998 = Some (ShiftImm ALU_SRL 16 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d99c : bv 32 := 0x00c87633.
Lemma F_3d99c : fetch_word Asan.M.loaded_segments (0x3d99c : word) = Some W_3d99c.
Proof. vm_refl. Qed.
Lemma D_3d99c : decode_any W_3d99c = Some (Op ALU_AND 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9a0 : bv 32 := 0x40c585b3.
Lemma F_3d9a0 : fetch_word Asan.M.loaded_segments (0x3d9a0 : word) = Some W_3d9a0.
Proof. vm_refl. Qed.
Lemma D_3d9a0 : decode_any W_3d9a0 = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9a4 : bv 32 := 0x00d5f633.
Lemma F_3d9a4 : fetch_word Asan.M.loaded_segments (0x3d9a4 : word) = Some W_3d9a4.
Proof. vm_refl. Qed.
Lemma D_3d9a4 : decode_any W_3d9a4 = Some (Op ALU_AND 12 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9a8 : bv 32 := 0x0025d593.
Lemma F_3d9a8 : fetch_word Asan.M.loaded_segments (0x3d9a8 : word) = Some W_3d9a8.
Proof. vm_refl. Qed.
Lemma D_3d9a8 : decode_any W_3d9a8 = Some (ShiftImm ALU_SRL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9ac : bv 32 := 0x00d5f5b3.
Lemma F_3d9ac : fetch_word Asan.M.loaded_segments (0x3d9ac : word) = Some W_3d9ac.
Proof. vm_refl. Qed.
Lemma D_3d9ac : decode_any W_3d9ac = Some (Op ALU_AND 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9b0 : bv 32 := 0x00b605b3.
Lemma F_3d9b0 : fetch_word Asan.M.loaded_segments (0x3d9b0 : word) = Some W_3d9b0.
Proof. vm_refl. Qed.
Lemma D_3d9b0 : decode_any W_3d9b0 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9b4 : bv 32 := 0x0045d613.
Lemma F_3d9b4 : fetch_word Asan.M.loaded_segments (0x3d9b4 : word) = Some W_3d9b4.
Proof. vm_refl. Qed.
Lemma D_3d9b4 : decode_any W_3d9b4 = Some (ShiftImm ALU_SRL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9b8 : bv 32 := 0x00c585b3.
Lemma F_3d9b8 : fetch_word Asan.M.loaded_segments (0x3d9b8 : word) = Some W_3d9b8.
Proof. vm_refl. Qed.
Lemma D_3d9b8 : decode_any W_3d9b8 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9bc : bv 32 := 0x03e00613.
Lemma F_3d9bc : fetch_word Asan.M.loaded_segments (0x3d9bc : word) = Some W_3d9bc.
Proof. vm_refl. Qed.
Lemma D_3d9bc : decode_any W_3d9bc = Some (OpImm ALU_ADD 12 0 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9c0 : bv 32 := 0x00e5f5b3.
Lemma F_3d9c0 : fetch_word Asan.M.loaded_segments (0x3d9c0 : word) = Some W_3d9c0.
Proof. vm_refl. Qed.
Lemma D_3d9c0 : decode_any W_3d9c0 = Some (Op ALU_AND 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9c4 : bv 32 := 0xfff00693.
Lemma F_3d9c4 : fetch_word Asan.M.loaded_segments (0x3d9c4 : word) = Some W_3d9c4.
Proof. vm_refl. Qed.
Lemma D_3d9c4 : decode_any W_3d9c4 = Some (OpImm ALU_ADD 13 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9c8 : bv 32 := 0x02f585b3.
Lemma F_3d9c8 : fetch_word Asan.M.loaded_segments (0x3d9c8 : word) = Some W_3d9c8.
Proof. vm_refl. Qed.
Lemma D_3d9c8 : decode_any W_3d9c8 = Some (Mul M_MUL 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9cc : bv 32 := 0x0385d593.
Lemma F_3d9cc : fetch_word Asan.M.loaded_segments (0x3d9cc : word) = Some W_3d9cc.
Proof. vm_refl. Qed.
Lemma D_3d9cc : decode_any W_3d9cc = Some (ShiftImm ALU_SRL 11 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9d0 : bv 32 := 0x40b6063b.
Lemma F_3d9d0 : fetch_word Asan.M.loaded_segments (0x3d9d0 : word) = Some W_3d9d0.
Proof. vm_refl. Qed.
Lemma D_3d9d0 : decode_any W_3d9d0 = Some (Op32 ALU_SUB 12 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9d4 : bv 32 := 0x00159593.
Lemma F_3d9d4 : fetch_word Asan.M.loaded_segments (0x3d9d4 : word) = Some W_3d9d4.
Proof. vm_refl. Qed.
Lemma D_3d9d4 : decode_any W_3d9d4 = Some (ShiftImm ALU_SLL 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9d8 : bv 32 := 0x00c9d733.
Lemma F_3d9d8 : fetch_word Asan.M.loaded_segments (0x3d9d8 : word) = Some W_3d9d8.
Proof. vm_refl. Qed.
Lemma D_3d9d8 : decode_any W_3d9d8 = Some (Op ALU_SRL 14 19 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9dc : bv 32 := 0x00c6963b.
Lemma F_3d9dc : fetch_word Asan.M.loaded_segments (0x3d9dc : word) = Some W_3d9dc.
Proof. vm_refl. Qed.
Lemma D_3d9dc : decode_any W_3d9dc = Some (Op32 ALU_SLL 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9e0 : bv 32 := 0x07e5c593.
Lemma F_3d9e0 : fetch_word Asan.M.loaded_segments (0x3d9e0 : word) = Some W_3d9e0.
Proof. vm_refl. Qed.
Lemma D_3d9e0 : decode_any W_3d9e0 = Some (OpImm ALU_XOR 11 11 126, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9e4 : bv 32 := 0x00177713.
Lemma F_3d9e4 : fetch_word Asan.M.loaded_segments (0x3d9e4 : word) = Some W_3d9e4.
Proof. vm_refl. Qed.
Lemma D_3d9e4 : decode_any W_3d9e4 = Some (OpImm ALU_AND 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9e8 : bv 32 := 0xfff64613.
Lemma F_3d9e8 : fetch_word Asan.M.loaded_segments (0x3d9e8 : word) = Some W_3d9e8.
Proof. vm_refl. Qed.
Lemma D_3d9e8 : decode_any W_3d9e8 = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9ec : bv 32 := 0x00c9f633.
Lemma F_3d9ec : fetch_word Asan.M.loaded_segments (0x3d9ec : word) = Some W_3d9ec.
Proof. vm_refl. Qed.
Lemma D_3d9ec : decode_any W_3d9ec = Some (Op ALU_AND 12 19 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9f0 : bv 32 := 0x00e5e5b3.
Lemma F_3d9f0 : fetch_word Asan.M.loaded_segments (0x3d9f0 : word) = Some W_3d9f0.
Proof. vm_refl. Qed.
Lemma D_3d9f0 : decode_any W_3d9f0 = Some (Op ALU_OR 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9f4 : bv 32 := 0x00c03633.
Lemma F_3d9f4 : fetch_word Asan.M.loaded_segments (0x3d9f4 : word) = Some W_3d9f4.
Proof. vm_refl. Qed.
Lemma D_3d9f4 : decode_any W_3d9f4 = Some (Op ALU_SLTU 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9f8 : bv 32 := 0x00c585b3.
Lemma F_3d9f8 : fetch_word Asan.M.loaded_segments (0x3d9f8 : word) = Some W_3d9f8.
Proof. vm_refl. Qed.
Lemma D_3d9f8 : decode_any W_3d9f8 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3d9fc : bv 32 := 0xffe58593.
Lemma F_3d9fc : fetch_word Asan.M.loaded_segments (0x3d9fc : word) = Some W_3d9fc.
Proof. vm_refl. Qed.
Lemma D_3d9fc : decode_any W_3d9fc = Some (OpImm ALU_ADD 11 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da00 : bv 32 := 0x00359593.
Lemma F_3da00 : fetch_word Asan.M.loaded_segments (0x3da00 : word) = Some W_3da00.
Proof. vm_refl. Qed.
Lemma D_3da00 : decode_any W_3da00 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da04 : bv 32 := 0x00b50533.
Lemma F_3da04 : fetch_word Asan.M.loaded_segments (0x3da04 : word) = Some W_3da04.
Proof. vm_refl. Qed.
Lemma D_3da04 : decode_any W_3da04 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da08 : bv 32 := 0x00053583.
Lemma F_3da08 : fetch_word Asan.M.loaded_segments (0x3da08 : word) = Some W_3da08.
Proof. vm_refl. Qed.
Lemma D_3da08 : decode_any W_3da08 = Some (Load SZ8 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da0c : bv 32 := 0x00158593.
Lemma F_3da0c : fetch_word Asan.M.loaded_segments (0x3da0c : word) = Some W_3da0c.
Proof. vm_refl. Qed.
Lemma D_3da0c : decode_any W_3da0c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da10 : bv 32 := 0x00b53023.
Lemma F_3da10 : fetch_word Asan.M.loaded_segments (0x3da10 : word) = Some W_3da10.
Proof. vm_refl. Qed.
Lemma D_3da10 : decode_any W_3da10 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da14 : bv 32 := 0x00813503.
Lemma F_3da14 : fetch_word Asan.M.loaded_segments (0x3da14 : word) = Some W_3da14.
Proof. vm_refl. Qed.
Lemma D_3da14 : decode_any W_3da14 = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da18 : bv 32 := 0x02050c63.
Lemma F_3da18 : fetch_word Asan.M.loaded_segments (0x3da18 : word) = Some W_3da18.
Proof. vm_refl. Qed.
Lemma D_3da18 : decode_any W_3da18 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da1c : bv 32 := 0x00098517.
Lemma F_3da1c : fetch_word Asan.M.loaded_segments (0x3da1c : word) = Some W_3da1c.
Proof. vm_refl. Qed.
Lemma D_3da1c : decode_any W_3da1c = Some (Auipc 10 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da20 : bv 32 := 0xe9453503.
Lemma F_3da20 : fetch_word Asan.M.loaded_segments (0x3da20 : word) = Some W_3da20.
Proof. vm_refl. Qed.
Lemma D_3da20 : decode_any W_3da20 = Some (Load SZ8 true 10 10 3732, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da24 : bv 32 := 0x02c52583.
Lemma F_3da24 : fetch_word Asan.M.loaded_segments (0x3da24 : word) = Some W_3da24.
Proof. vm_refl. Qed.
Lemma D_3da24 : decode_any W_3da24 = Some (Load SZ4 true 11 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da28 : bv 32 := 0x02058463.
Lemma F_3da28 : fetch_word Asan.M.loaded_segments (0x3da28 : word) = Some W_3da28.
Proof. vm_refl. Qed.
Lemma D_3da28 : decode_any W_3da28 = Some (Branch BC_EQ 11 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da2c : bv 32 := 0x00048613.
Lemma F_3da2c : fetch_word Asan.M.loaded_segments (0x3da2c : word) = Some W_3da2c.
Proof. vm_refl. Qed.
Lemma D_3da2c : decode_any W_3da2c = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da30 : bv 32 := 0x00b4e463.
Lemma F_3da30 : fetch_word Asan.M.loaded_segments (0x3da30 : word) = Some W_3da30.
Proof. vm_refl. Qed.
Lemma D_3da30 : decode_any W_3da30 = Some (Branch BC_LTU 9 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da34 : bv 32 := 0x00058613.
Lemma F_3da34 : fetch_word Asan.M.loaded_segments (0x3da34 : word) = Some W_3da34.
Proof. vm_refl. Qed.
Lemma D_3da34 : decode_any W_3da34 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da38 : bv 32 := 0x00098597.
Lemma F_3da38 : fetch_word Asan.M.loaded_segments (0x3da38 : word) = Some W_3da38.
Proof. vm_refl. Qed.
Lemma D_3da38 : decode_any W_3da38 = Some (Auipc 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da3c : bv 32 := 0xea05b583.
Lemma F_3da3c : fetch_word Asan.M.loaded_segments (0x3da3c : word) = Some W_3da3c.
Proof. vm_refl. Qed.
Lemma D_3da3c : decode_any W_3da3c = Some (Load SZ8 true 11 11 3744, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da40 : bv 32 := 0x0005b683.
Lemma F_3da40 : fetch_word Asan.M.loaded_segments (0x3da40 : word) = Some W_3da40.
Proof. vm_refl. Qed.
Lemma D_3da40 : decode_any W_3da40 = Some (Load SZ8 true 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da44 : bv 32 := 0x03452583.
Lemma F_3da44 : fetch_word Asan.M.loaded_segments (0x3da44 : word) = Some W_3da44.
Proof. vm_refl. Qed.
Lemma D_3da44 : decode_any W_3da44 = Some (Load SZ4 true 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da48 : bv 32 := 0x000a0513.
Lemma F_3da48 : fetch_word Asan.M.loaded_segments (0x3da48 : word) = Some W_3da48.
Proof. vm_refl. Qed.
Lemma D_3da48 : decode_any W_3da48 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da4c : bv 32 := 0x000680e7.
Lemma F_3da4c : fetch_word Asan.M.loaded_segments (0x3da4c : word) = Some W_3da4c.
Proof. vm_refl. Qed.
Lemma D_3da4c : decode_any W_3da4c = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da50 : bv 32 := 0x1594f0ef.
Lemma F_3da50 : fetch_word Asan.M.loaded_segments (0x3da50 : word) = Some W_3da50.
Proof. vm_refl. Qed.
Lemma D_3da50 : decode_any W_3da50 = Some (Jal 1 325976, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da54 : bv 32 := 0x001ac583.
Lemma F_3da54 : fetch_word Asan.M.loaded_segments (0x3da54 : word) = Some W_3da54.
Proof. vm_refl. Qed.
Lemma D_3da54 : decode_any W_3da54 = Some (Load SZ1 false 11 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da58 : bv 32 := 0x40a0053b.
Lemma F_3da58 : fetch_word Asan.M.loaded_segments (0x3da58 : word) = Some W_3da58.
Proof. vm_refl. Qed.
Lemma D_3da58 : decode_any W_3da58 = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da5c : bv 32 := 0x00c57513.
Lemma F_3da5c : fetch_word Asan.M.loaded_segments (0x3da5c : word) = Some W_3da5c.
Proof. vm_refl. Qed.
Lemma D_3da5c : decode_any W_3da5c = Some (OpImm ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da60 : bv 32 := 0x0f35f593.
Lemma F_3da60 : fetch_word Asan.M.loaded_segments (0x3da60 : word) = Some W_3da60.
Proof. vm_refl. Qed.
Lemma D_3da60 : decode_any W_3da60 = Some (OpImm ALU_AND 11 11 243, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da64 : bv 32 := 0x00a5e533.
Lemma F_3da64 : fetch_word Asan.M.loaded_segments (0x3da64 : word) = Some W_3da64.
Proof. vm_refl. Qed.
Lemma D_3da64 : decode_any W_3da64 = Some (Op ALU_OR 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da68 : bv 32 := 0x00200593.
Lemma F_3da68 : fetch_word Asan.M.loaded_segments (0x3da68 : word) = Some W_3da68.
Proof. vm_refl. Qed.
Lemma D_3da68 : decode_any W_3da68 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da6c : bv 32 := 0x00aa80a3.
Lemma F_3da6c : fetch_word Asan.M.loaded_segments (0x3da6c : word) = Some W_3da6c.
Proof. vm_refl. Qed.
Lemma D_3da6c : decode_any W_3da6c = Some (Store SZ1 21 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da70 : bv 32 := 0x0310000f.
Lemma F_3da70 : fetch_word Asan.M.loaded_segments (0x3da70 : word) = Some W_3da70.
Proof. vm_refl. Qed.
Lemma D_3da70 : decode_any W_3da70 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da74 : bv 32 := 0x00ba8023.
Lemma F_3da74 : fetch_word Asan.M.loaded_segments (0x3da74 : word) = Some W_3da74.
Proof. vm_refl. Qed.
Lemma D_3da74 : decode_any W_3da74 = Some (Store SZ1 21 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da78 : bv 32 := 0x032a8063.
Lemma F_3da78 : fetch_word Asan.M.loaded_segments (0x3da78 : word) = Some W_3da78.
Proof. vm_refl. Qed.
Lemma D_3da78 : decode_any W_3da78 = Some (Branch BC_EQ 21 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da7c : bv 32 := 0x01090693.
Lemma F_3da7c : fetch_word Asan.M.loaded_segments (0x3da7c : word) = Some W_3da7c.
Proof. vm_refl. Qed.
Lemma D_3da7c : decode_any W_3da7c = Some (OpImm ALU_ADD 13 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da80 : bv 32 := 0x20daee63.
Lemma F_3da80 : fetch_word Asan.M.loaded_segments (0x3da80 : word) = Some W_3da80.
Proof. vm_refl. Qed.
Lemma D_3da80 : decode_any W_3da80 = Some (Branch BC_LTU 21 13 540, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da84 : bv 32 := 0xfffd3517.
Lemma F_3da84 : fetch_word Asan.M.loaded_segments (0x3da84 : word) = Some W_3da84.
Proof. vm_refl. Qed.
Lemma D_3da84 : decode_any W_3da84 = Some (Auipc 10 1048531, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da88 : bv 32 := 0x8bc53503.
Lemma F_3da88 : fetch_word Asan.M.loaded_segments (0x3da88 : word) = Some W_3da88.
Proof. vm_refl. Qed.
Lemma D_3da88 : decode_any W_3da88 = Some (Load SZ8 true 10 10 2236, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da8c : bv 32 := 0x01593423.
Lemma F_3da8c : fetch_word Asan.M.loaded_segments (0x3da8c : word) = Some W_3da8c.
Proof. vm_refl. Qed.
Lemma D_3da8c : decode_any W_3da8c = Some (Store SZ8 18 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da90 : bv 32 := 0x0310000f.
Lemma F_3da90 : fetch_word Asan.M.loaded_segments (0x3da90 : word) = Some W_3da90.
Proof. vm_refl. Qed.
Lemma D_3da90 : decode_any W_3da90 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da94 : bv 32 := 0x00a93023.
Lemma F_3da94 : fetch_word Asan.M.loaded_segments (0x3da94 : word) = Some W_3da94.
Proof. vm_refl. Qed.
Lemma D_3da94 : decode_any W_3da94 = Some (Store SZ8 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da98 : bv 32 := 0x000a0513.
Lemma F_3da98 : fetch_word Asan.M.loaded_segments (0x3da98 : word) = Some W_3da98.
Proof. vm_refl. Qed.
Lemma D_3da98 : decode_any W_3da98 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3da9c : bv 32 := 0x00048593.
Lemma F_3da9c : fetch_word Asan.M.loaded_segments (0x3da9c : word) = Some W_3da9c.
Proof. vm_refl. Qed.
Lemma D_3da9c : decode_any W_3da9c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3daa0 : bv 32 := 0x518300ef.
Lemma F_3daa0 : fetch_word Asan.M.loaded_segments (0x3daa0 : word) = Some W_3daa0.
Proof. vm_refl. Qed.
Lemma D_3daa0 : decode_any W_3daa0 = Some (Jal 1 197912, 4%Z).
Proof. vm_refl. Qed.

Definition W_3daa4 : bv 32 := 0x000a0513.
Lemma F_3daa4 : fetch_word Asan.M.loaded_segments (0x3daa4 : word) = Some W_3daa4.
Proof. vm_refl. Qed.
Lemma D_3daa4 : decode_any W_3daa4 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3daa8 : bv 32 := 0x07813083.
Lemma F_3daa8 : fetch_word Asan.M.loaded_segments (0x3daa8 : word) = Some W_3daa8.
Proof. vm_refl. Qed.
Lemma D_3daa8 : decode_any W_3daa8 = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_3daac : bv 32 := 0x07013403.
Lemma F_3daac : fetch_word Asan.M.loaded_segments (0x3daac : word) = Some W_3daac.
Proof. vm_refl. Qed.
Lemma D_3daac : decode_any W_3daac = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dab0 : bv 32 := 0x06813483.
Lemma F_3dab0 : fetch_word Asan.M.loaded_segments (0x3dab0 : word) = Some W_3dab0.
Proof. vm_refl. Qed.
Lemma D_3dab0 : decode_any W_3dab0 = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dab4 : bv 32 := 0x06013903.
Lemma F_3dab4 : fetch_word Asan.M.loaded_segments (0x3dab4 : word) = Some W_3dab4.
Proof. vm_refl. Qed.
Lemma D_3dab4 : decode_any W_3dab4 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dab8 : bv 32 := 0x05813983.
Lemma F_3dab8 : fetch_word Asan.M.loaded_segments (0x3dab8 : word) = Some W_3dab8.
Proof. vm_refl. Qed.
Lemma D_3dab8 : decode_any W_3dab8 = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dabc : bv 32 := 0x05013a03.
Lemma F_3dabc : fetch_word Asan.M.loaded_segments (0x3dabc : word) = Some W_3dabc.
Proof. vm_refl. Qed.
Lemma D_3dabc : decode_any W_3dabc = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dac0 : bv 32 := 0x04813a83.
Lemma F_3dac0 : fetch_word Asan.M.loaded_segments (0x3dac0 : word) = Some W_3dac0.
Proof. vm_refl. Qed.
Lemma D_3dac0 : decode_any W_3dac0 = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dac4 : bv 32 := 0x04013b03.
Lemma F_3dac4 : fetch_word Asan.M.loaded_segments (0x3dac4 : word) = Some W_3dac4.
Proof. vm_refl. Qed.
Lemma D_3dac4 : decode_any W_3dac4 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dac8 : bv 32 := 0x03813b83.
Lemma F_3dac8 : fetch_word Asan.M.loaded_segments (0x3dac8 : word) = Some W_3dac8.
Proof. vm_refl. Qed.
Lemma D_3dac8 : decode_any W_3dac8 = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dacc : bv 32 := 0x03013c03.
Lemma F_3dacc : fetch_word Asan.M.loaded_segments (0x3dacc : word) = Some W_3dacc.
Proof. vm_refl. Qed.
Lemma D_3dacc : decode_any W_3dacc = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dad0 : bv 32 := 0x02813c83.
Lemma F_3dad0 : fetch_word Asan.M.loaded_segments (0x3dad0 : word) = Some W_3dad0.
Proof. vm_refl. Qed.
Lemma D_3dad0 : decode_any W_3dad0 = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dad4 : bv 32 := 0x02013d03.
Lemma F_3dad4 : fetch_word Asan.M.loaded_segments (0x3dad4 : word) = Some W_3dad4.
Proof. vm_refl. Qed.
Lemma D_3dad4 : decode_any W_3dad4 = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dad8 : bv 32 := 0x01813d83.
Lemma F_3dad8 : fetch_word Asan.M.loaded_segments (0x3dad8 : word) = Some W_3dad8.
Proof. vm_refl. Qed.
Lemma D_3dad8 : decode_any W_3dad8 = Some (Load SZ8 true 27 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dadc : bv 32 := 0x08010113.
Lemma F_3dadc : fetch_word Asan.M.loaded_segments (0x3dadc : word) = Some W_3dadc.
Proof. vm_refl. Qed.
Lemma D_3dadc : decode_any W_3dadc = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dae0 : bv 32 := 0x00008067.
Lemma F_3dae0 : fetch_word Asan.M.loaded_segments (0x3dae0 : word) = Some W_3dae0.
Proof. vm_refl. Qed.
Lemma D_3dae0 : decode_any W_3dae0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dae4 : bv 32 := 0x00098897.
Lemma F_3dae4 : fetch_word Asan.M.loaded_segments (0x3dae4 : word) = Some W_3dae4.
Proof. vm_refl. Qed.
Lemma D_3dae4 : decode_any W_3dae4 = Some (Auipc 17 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dae8 : bv 32 := 0xdcc8b883.
Lemma F_3dae8 : fetch_word Asan.M.loaded_segments (0x3dae8 : word) = Some W_3dae8.
Proof. vm_refl. Qed.
Lemma D_3dae8 : decode_any W_3dae8 = Some (Load SZ8 true 17 17 3532, 4%Z).
Proof. vm_refl. Qed.

Definition W_3daec : bv 32 := 0x04e8c883.
Lemma F_3daec : fetch_word Asan.M.loaded_segments (0x3daec : word) = Some W_3daec.
Proof. vm_refl. Qed.
Lemma D_3daec : decode_any W_3daec = Some (Load SZ1 false 17 17 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_3daf0 : bv 32 := 0x08089e63.
Lemma F_3daf0 : fetch_word Asan.M.loaded_segments (0x3daf0 : word) = Some W_3daf0.
Proof. vm_refl. Qed.
Lemma D_3daf0 : decode_any W_3daf0 = Some (Branch BC_NE 17 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_3daf4 : bv 32 := 0x04078063.
Lemma F_3daf4 : fetch_word Asan.M.loaded_segments (0x3daf4 : word) = Some W_3daf4.
Proof. vm_refl. Qed.
Lemma D_3daf4 : decode_any W_3daf4 = Some (Branch BC_EQ 15 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3daf8 : bv 32 := 0x0037d793.
Lemma F_3daf8 : fetch_word Asan.M.loaded_segments (0x3daf8 : word) = Some W_3daf8.
Proof. vm_refl. Qed.
Lemma D_3daf8 : decode_any W_3daf8 = Some (ShiftImm ALU_SRL 15 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dafc : bv 32 := 0x00b787b3.
Lemma F_3dafc : fetch_word Asan.M.loaded_segments (0x3dafc : word) = Some W_3dafc.
Proof. vm_refl. Qed.
Lemma D_3dafc : decode_any W_3dafc = Some (Op ALU_ADD 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db00 : bv 32 := 0x0767f063.
Lemma F_3db00 : fetch_word Asan.M.loaded_segments (0x3db00 : word) = Some W_3db00.
Proof. vm_refl. Qed.
Lemma D_3db00 : decode_any W_3db00 = Some (Branch BC_GEU 15 22 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db04 : bv 32 := 0x00150793.
Lemma F_3db04 : fetch_word Asan.M.loaded_segments (0x3db04 : word) = Some W_3db04.
Proof. vm_refl. Qed.
Lemma D_3db04 : decode_any W_3db04 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db08 : bv 32 := 0x01676863.
Lemma F_3db08 : fetch_word Asan.M.loaded_segments (0x3db08 : word) = Some W_3db08.
Proof. vm_refl. Qed.
Lemma D_3db08 : decode_any W_3db08 = Some (Branch BC_LTU 14 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db0c : bv 32 := 0x00365713.
Lemma F_3db0c : fetch_word Asan.M.loaded_segments (0x3db0c : word) = Some W_3db0c.
Proof. vm_refl. Qed.
Lemma D_3db0c : decode_any W_3db0c = Some (ShiftImm ALU_SRL 14 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db10 : bv 32 := 0x00f70733.
Lemma F_3db10 : fetch_word Asan.M.loaded_segments (0x3db10 : word) = Some W_3db10.
Proof. vm_refl. Qed.
Lemma D_3db10 : decode_any W_3db10 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db14 : bv 32 := 0xd8eb72e3.
Lemma F_3db14 : fetch_word Asan.M.loaded_segments (0x3db14 : word) = Some W_3db14.
Proof. vm_refl. Qed.
Lemma D_3db14 : decode_any W_3db14 = Some (Branch BC_GEU 22 14 7556, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db18 : bv 32 := 0x00160613.
Lemma F_3db18 : fetch_word Asan.M.loaded_segments (0x3db18 : word) = Some W_3db18.
Proof. vm_refl. Qed.
Lemma D_3db18 : decode_any W_3db18 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db1c : bv 32 := 0x06cb6863.
Lemma F_3db1c : fetch_word Asan.M.loaded_segments (0x3db1c : word) = Some W_3db1c.
Proof. vm_refl. Qed.
Lemma D_3db1c : decode_any W_3db1c = Some (Branch BC_LTU 22 12 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db20 : bv 32 := 0x00f686b3.
Lemma F_3db20 : fetch_word Asan.M.loaded_segments (0x3db20 : word) = Some W_3db20.
Proof. vm_refl. Qed.
Lemma D_3db20 : decode_any W_3db20 = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db24 : bv 32 := 0x0036d693.
Lemma F_3db24 : fetch_word Asan.M.loaded_segments (0x3db24 : word) = Some W_3db24.
Proof. vm_refl. Qed.
Lemma D_3db24 : decode_any W_3db24 = Some (ShiftImm ALU_SRL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db28 : bv 32 := 0x00b685b3.
Lemma F_3db28 : fetch_word Asan.M.loaded_segments (0x3db28 : word) = Some W_3db28.
Proof. vm_refl. Qed.
Lemma D_3db28 : decode_any W_3db28 = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db2c : bv 32 := 0xd765f6e3.
Lemma F_3db2c : fetch_word Asan.M.loaded_segments (0x3db2c : word) = Some W_3db2c.
Proof. vm_refl. Qed.
Lemma D_3db2c : decode_any W_3db2c = Some (Branch BC_GEU 11 22 7532, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db30 : bv 32 := 0x05c0006f.
Lemma F_3db30 : fetch_word Asan.M.loaded_segments (0x3db30 : word) = Some W_3db30.
Proof. vm_refl. Qed.
Lemma D_3db30 : decode_any W_3db30 = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db34 : bv 32 := 0x04050463.
Lemma F_3db34 : fetch_word Asan.M.loaded_segments (0x3db34 : word) = Some W_3db34.
Proof. vm_refl. Qed.
Lemma D_3db34 : decode_any W_3db34 = Some (Branch BC_EQ 10 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db38 : bv 32 := 0x0035d613.
Lemma F_3db38 : fetch_word Asan.M.loaded_segments (0x3db38 : word) = Some W_3db38.
Proof. vm_refl. Qed.
Lemma D_3db38 : decode_any W_3db38 = Some (ShiftImm ALU_SRL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db3c : bv 32 := 0x00a60633.
Lemma F_3db3c : fetch_word Asan.M.loaded_segments (0x3db3c : word) = Some W_3db3c.
Proof. vm_refl. Qed.
Lemma D_3db3c : decode_any W_3db3c = Some (Op ALU_ADD 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db40 : bv 32 := 0x00060663.
Lemma F_3db40 : fetch_word Asan.M.loaded_segments (0x3db40 : word) = Some W_3db40.
Proof. vm_refl. Qed.
Lemma D_3db40 : decode_any W_3db40 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db44 : bv 32 := 0x00160613.
Lemma F_3db44 : fetch_word Asan.M.loaded_segments (0x3db44 : word) = Some W_3db44.
Proof. vm_refl. Qed.
Lemma D_3db44 : decode_any W_3db44 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db48 : bv 32 := 0x04cb6263.
Lemma F_3db48 : fetch_word Asan.M.loaded_segments (0x3db48 : word) = Some W_3db48.
Proof. vm_refl. Qed.
Lemma D_3db48 : decode_any W_3db48 = Some (Branch BC_LTU 22 12 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db4c : bv 32 := 0x00180813.
Lemma F_3db4c : fetch_word Asan.M.loaded_segments (0x3db4c : word) = Some W_3db4c.
Proof. vm_refl. Qed.
Lemma D_3db4c : decode_any W_3db4c = Some (OpImm ALU_ADD 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db50 : bv 32 := 0x00385613.
Lemma F_3db50 : fetch_word Asan.M.loaded_segments (0x3db50 : word) = Some W_3db50.
Proof. vm_refl. Qed.
Lemma D_3db50 : decode_any W_3db50 = Some (ShiftImm ALU_SRL 12 16 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db54 : bv 32 := 0x00b605b3.
Lemma F_3db54 : fetch_word Asan.M.loaded_segments (0x3db54 : word) = Some W_3db54.
Proof. vm_refl. Qed.
Lemma D_3db54 : decode_any W_3db54 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db58 : bv 32 := 0xd565f0e3.
Lemma F_3db58 : fetch_word Asan.M.loaded_segments (0x3db58 : word) = Some W_3db58.
Proof. vm_refl. Qed.
Lemma D_3db58 : decode_any W_3db58 = Some (Branch BC_GEU 11 22 7488, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db5c : bv 32 := 0x0300006f.
Lemma F_3db5c : fetch_word Asan.M.loaded_segments (0x3db5c : word) = Some W_3db5c.
Proof. vm_refl. Qed.
Lemma D_3db5c : decode_any W_3db5c = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db60 : bv 32 := 0xd2050ce3.
Lemma F_3db60 : fetch_word Asan.M.loaded_segments (0x3db60 : word) = Some W_3db60.
Proof. vm_refl. Qed.
Lemma D_3db60 : decode_any W_3db60 = Some (Branch BC_EQ 10 0 7480, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db64 : bv 32 := 0x0035d593.
Lemma F_3db64 : fetch_word Asan.M.loaded_segments (0x3db64 : word) = Some W_3db64.
Proof. vm_refl. Qed.
Lemma D_3db64 : decode_any W_3db64 = Some (ShiftImm ALU_SRL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db68 : bv 32 := 0x00a585b3.
Lemma F_3db68 : fetch_word Asan.M.loaded_segments (0x3db68 : word) = Some W_3db68.
Proof. vm_refl. Qed.
Lemma D_3db68 : decode_any W_3db68 = Some (Op ALU_ADD 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db6c : bv 32 := 0xd20586e3.
Lemma F_3db6c : fetch_word Asan.M.loaded_segments (0x3db6c : word) = Some W_3db6c.
Proof. vm_refl. Qed.
Lemma D_3db6c : decode_any W_3db6c = Some (Branch BC_EQ 11 0 7468, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db70 : bv 32 := 0x00158593.
Lemma F_3db70 : fetch_word Asan.M.loaded_segments (0x3db70 : word) = Some W_3db70.
Proof. vm_refl. Qed.
Lemma D_3db70 : decode_any W_3db70 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db74 : bv 32 := 0xd2bb72e3.
Lemma F_3db74 : fetch_word Asan.M.loaded_segments (0x3db74 : word) = Some W_3db74.
Proof. vm_refl. Qed.
Lemma D_3db74 : decode_any W_3db74 = Some (Branch BC_GEU 22 11 7460, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db78 : bv 32 := 0x0140006f.
Lemma F_3db78 : fetch_word Asan.M.loaded_segments (0x3db78 : word) = Some W_3db78.
Proof. vm_refl. Qed.
Lemma D_3db78 : decode_any W_3db78 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db7c : bv 32 := 0x00168693.
Lemma F_3db7c : fetch_word Asan.M.loaded_segments (0x3db7c : word) = Some W_3db7c.
Proof. vm_refl. Qed.
Lemma D_3db7c : decode_any W_3db7c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db80 : bv 32 := 0x0036d693.
Lemma F_3db80 : fetch_word Asan.M.loaded_segments (0x3db80 : word) = Some W_3db80.
Proof. vm_refl. Qed.
Lemma D_3db80 : decode_any W_3db80 = Some (ShiftImm ALU_SRL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db84 : bv 32 := 0xfff68693.
Lemma F_3db84 : fetch_word Asan.M.loaded_segments (0x3db84 : word) = Some W_3db84.
Proof. vm_refl. Qed.
Lemma D_3db84 : decode_any W_3db84 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db88 : bv 32 := 0xd166f8e3.
Lemma F_3db88 : fetch_word Asan.M.loaded_segments (0x3db88 : word) = Some W_3db88.
Proof. vm_refl. Qed.
Lemma D_3db88 : decode_any W_3db88 = Some (Branch BC_GEU 13 22 7440, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db8c : bv 32 := 0xfffe4517.
Lemma F_3db8c : fetch_word Asan.M.loaded_segments (0x3db8c : word) = Some W_3db8c.
Proof. vm_refl. Qed.
Lemma D_3db8c : decode_any W_3db8c = Some (Auipc 10 1048548, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db90 : bv 32 := 0xfffda597.
Lemma F_3db90 : fetch_word Asan.M.loaded_segments (0x3db90 : word) = Some W_3db90.
Proof. vm_refl. Qed.
Lemma D_3db90 : decode_any W_3db90 = Some (Auipc 11 1048538, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db94 : bv 32 := 0x80150513.
Lemma F_3db94 : fetch_word Asan.M.loaded_segments (0x3db94 : word) = Some W_3db94.
Proof. vm_refl. Qed.
Lemma D_3db94 : decode_any W_3db94 = Some (OpImm ALU_ADD 10 10 2049, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db98 : bv 32 := 0xd5b58613.
Lemma F_3db98 : fetch_word Asan.M.loaded_segments (0x3db98 : word) = Some W_3db98.
Proof. vm_refl. Qed.
Lemma D_3db98 : decode_any W_3db98 = Some (OpImm ALU_ADD 12 11 3419, 4%Z).
Proof. vm_refl. Qed.

Definition W_3db9c : bv 32 := 0x17700593.
Lemma F_3db9c : fetch_word Asan.M.loaded_segments (0x3db9c : word) = Some W_3db9c.
Proof. vm_refl. Qed.
Lemma D_3db9c : decode_any W_3db9c = Some (OpImm ALU_ADD 11 0 375, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dba0 : bv 32 := 0x00000693.
Lemma F_3dba0 : fetch_word Asan.M.loaded_segments (0x3dba0 : word) = Some W_3dba0.
Proof. vm_refl. Qed.
Lemma D_3dba0 : decode_any W_3dba0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dba4 : bv 32 := 0x00000713.
Lemma F_3dba4 : fetch_word Asan.M.loaded_segments (0x3dba4 : word) = Some W_3dba4.
Proof. vm_refl. Qed.
Lemma D_3dba4 : decode_any W_3dba4 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dba8 : bv 32 := 0x4c03b0ef.
Lemma F_3dba8 : fetch_word Asan.M.loaded_segments (0x3dba8 : word) = Some W_3dba8.
Proof. vm_refl. Qed.
Lemma D_3dba8 : decode_any W_3dba8 = Some (Jal 1 242880, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dbac : bv 32 := 0x0f4290ef.
Lemma F_3dbac : fetch_word Asan.M.loaded_segments (0x3dbac : word) = Some W_3dbac.
Proof. vm_refl. Qed.
Lemma D_3dbac : decode_any W_3dbac = Some (Jal 1 168180, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dbb0 : bv 32 := 0x1ec2e0ef.
Lemma F_3dbb0 : fetch_word Asan.M.loaded_segments (0x3dbb0 : word) = Some W_3dbb0.
Proof. vm_refl. Qed.
Lemma D_3dbb0 : decode_any W_3dbb0 = Some (Jal 1 188908, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dbb4 : bv 32 := 0x80050ee3.
Lemma F_3dbb4 : fetch_word Asan.M.loaded_segments (0x3dbb4 : word) = Some W_3dbb4.
Proof. vm_refl. Qed.
Lemma D_3dbb4 : decode_any W_3dbb4 = Some (Branch BC_EQ 10 0 6172, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dbb8 : bv 32 := 0x1bc2e0ef.
Lemma F_3dbb8 : fetch_word Asan.M.loaded_segments (0x3dbb8 : word) = Some W_3dbb8.
Proof. vm_refl. Qed.
Lemma D_3dbb8 : decode_any W_3dbb8 = Some (Jal 1 188860, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dbbc : bv 32 := 0x08050a63.
Lemma F_3dbbc : fetch_word Asan.M.loaded_segments (0x3dbbc : word) = Some W_3dbbc.
Proof. vm_refl. Qed.
Lemma D_3dbbc : decode_any W_3dbbc = Some (Branch BC_EQ 10 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dbc0 : bv 32 := 0x00000a13.
Lemma F_3dbc0 : fetch_word Asan.M.loaded_segments (0x3dbc0 : word) = Some W_3dbc0.
Proof. vm_refl. Qed.
Lemma D_3dbc0 : decode_any W_3dbc0 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dbc4 : bv 32 := 0xee1ff06f.
Lemma F_3dbc4 : fetch_word Asan.M.loaded_segments (0x3dbc4 : word) = Some W_3dbc4.
Proof. vm_refl. Qed.
Lemma D_3dbc4 : decode_any W_3dbc4 = Some (Jal 0 2096864, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dbc8 : bv 32 := 0xfffd8517.
Lemma F_3dbc8 : fetch_word Asan.M.loaded_segments (0x3dbc8 : word) = Some W_3dbc8.
Proof. vm_refl. Qed.
Lemma D_3dbc8 : decode_any W_3dbc8 = Some (Auipc 10 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dbcc : bv 32 := 0xfffde597.
Lemma F_3dbcc : fetch_word Asan.M.loaded_segments (0x3dbcc : word) = Some W_3dbcc.
Proof. vm_refl. Qed.
Lemma D_3dbcc : decode_any W_3dbcc = Some (Auipc 11 1048542, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dbd0 : bv 32 := 0xb3f50513.
Lemma F_3dbd0 : fetch_word Asan.M.loaded_segments (0x3dbd0 : word) = Some W_3dbd0.
Proof. vm_refl. Qed.
Lemma D_3dbd0 : decode_any W_3dbd0 = Some (OpImm ALU_ADD 10 10 2879, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dbd4 : bv 32 := 0xb1358613.
Lemma F_3dbd4 : fetch_word Asan.M.loaded_segments (0x3dbd4 : word) = Some W_3dbd4.
Proof. vm_refl. Qed.
Lemma D_3dbd4 : decode_any W_3dbd4 = Some (OpImm ALU_ADD 12 11 2835, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dbd8 : bv 32 := 0x23200593.
Lemma F_3dbd8 : fetch_word Asan.M.loaded_segments (0x3dbd8 : word) = Some W_3dbd8.
Proof. vm_refl. Qed.
Lemma D_3dbd8 : decode_any W_3dbd8 = Some (OpImm ALU_ADD 11 0 562, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dbdc : bv 32 := 0x00000693.
Lemma F_3dbdc : fetch_word Asan.M.loaded_segments (0x3dbdc : word) = Some W_3dbdc.
Proof. vm_refl. Qed.
Lemma D_3dbdc : decode_any W_3dbdc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dbe0 : bv 32 := 0x00000713.
Lemma F_3dbe0 : fetch_word Asan.M.loaded_segments (0x3dbe0 : word) = Some W_3dbe0.
Proof. vm_refl. Qed.
Lemma D_3dbe0 : decode_any W_3dbe0 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dbe4 : bv 32 := 0x4843b0ef.
Lemma F_3dbe4 : fetch_word Asan.M.loaded_segments (0x3dbe4 : word) = Some W_3dbe4.
Proof. vm_refl. Qed.
Lemma D_3dbe4 : decode_any W_3dbe4 = Some (Jal 1 242820, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dbe8 : bv 32 := 0xfffd8517.
Lemma F_3dbe8 : fetch_word Asan.M.loaded_segments (0x3dbe8 : word) = Some W_3dbe8.
Proof. vm_refl. Qed.
Lemma D_3dbe8 : decode_any W_3dbe8 = Some (Auipc 10 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dbec : bv 32 := 0xfffd3597.
Lemma F_3dbec : fetch_word Asan.M.loaded_segments (0x3dbec : word) = Some W_3dbec.
Proof. vm_refl. Qed.
Lemma D_3dbec : decode_any W_3dbec = Some (Auipc 11 1048531, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dbf0 : bv 32 := 0xb1f50513.
Lemma F_3dbf0 : fetch_word Asan.M.loaded_segments (0x3dbf0 : word) = Some W_3dbf0.
Proof. vm_refl. Qed.
Lemma D_3dbf0 : decode_any W_3dbf0 = Some (OpImm ALU_ADD 10 10 2847, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dbf4 : bv 32 := 0x1e458613.
Lemma F_3dbf4 : fetch_word Asan.M.loaded_segments (0x3dbf4 : word) = Some W_3dbf4.
Proof. vm_refl. Qed.
Lemma D_3dbf4 : decode_any W_3dbf4 = Some (OpImm ALU_ADD 12 11 484, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dbf8 : bv 32 := 0x23e00593.
Lemma F_3dbf8 : fetch_word Asan.M.loaded_segments (0x3dbf8 : word) = Some W_3dbf8.
Proof. vm_refl. Qed.
Lemma D_3dbf8 : decode_any W_3dbf8 = Some (OpImm ALU_ADD 11 0 574, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dbfc : bv 32 := 0x00000693.
Lemma F_3dbfc : fetch_word Asan.M.loaded_segments (0x3dbfc : word) = Some W_3dbfc.
Proof. vm_refl. Qed.
Lemma D_3dbfc : decode_any W_3dbfc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc00 : bv 32 := 0x00000713.
Lemma F_3dc00 : fetch_word Asan.M.loaded_segments (0x3dc00 : word) = Some W_3dc00.
Proof. vm_refl. Qed.
Lemma D_3dc00 : decode_any W_3dc00 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc04 : bv 32 := 0x4643b0ef.
Lemma F_3dc04 : fetch_word Asan.M.loaded_segments (0x3dc04 : word) = Some W_3dc04.
Proof. vm_refl. Qed.
Lemma D_3dc04 : decode_any W_3dc04 = Some (Jal 1 242788, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc08 : bv 32 := 0xfffd8517.
Lemma F_3dc08 : fetch_word Asan.M.loaded_segments (0x3dc08 : word) = Some W_3dc08.
Proof. vm_refl. Qed.
Lemma D_3dc08 : decode_any W_3dc08 = Some (Auipc 10 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc0c : bv 32 := 0xfffe3597.
Lemma F_3dc0c : fetch_word Asan.M.loaded_segments (0x3dc0c : word) = Some W_3dc0c.
Proof. vm_refl. Qed.
Lemma D_3dc0c : decode_any W_3dc0c = Some (Auipc 11 1048547, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc10 : bv 32 := 0xaff50513.
Lemma F_3dc10 : fetch_word Asan.M.loaded_segments (0x3dc10 : word) = Some W_3dc10.
Proof. vm_refl. Qed.
Lemma D_3dc10 : decode_any W_3dc10 = Some (OpImm ALU_ADD 10 10 2815, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc14 : bv 32 := 0xd6b58613.
Lemma F_3dc14 : fetch_word Asan.M.loaded_segments (0x3dc14 : word) = Some W_3dc14.
Proof. vm_refl. Qed.
Lemma D_3dc14 : decode_any W_3dc14 = Some (OpImm ALU_ADD 12 11 3435, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc18 : bv 32 := 0x26200593.
Lemma F_3dc18 : fetch_word Asan.M.loaded_segments (0x3dc18 : word) = Some W_3dc18.
Proof. vm_refl. Qed.
Lemma D_3dc18 : decode_any W_3dc18 = Some (OpImm ALU_ADD 11 0 610, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc1c : bv 32 := 0x000c8693.
Lemma F_3dc1c : fetch_word Asan.M.loaded_segments (0x3dc1c : word) = Some W_3dc1c.
Proof. vm_refl. Qed.
Lemma D_3dc1c : decode_any W_3dc1c = Some (OpImm ALU_ADD 13 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc20 : bv 32 := 0x4483b0ef.
Lemma F_3dc20 : fetch_word Asan.M.loaded_segments (0x3dc20 : word) = Some W_3dc20.
Proof. vm_refl. Qed.
Lemma D_3dc20 : decode_any W_3dc20 = Some (Jal 1 242760, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc24 : bv 32 := 0xfff80537.
Lemma F_3dc24 : fetch_word Asan.M.loaded_segments (0x3dc24 : word) = Some W_3dc24.
Proof. vm_refl. Qed.
Lemma D_3dc24 : decode_any W_3dc24 = Some (Lui 10 1048448, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc28 : bv 32 := 0x01055513.
Lemma F_3dc28 : fetch_word Asan.M.loaded_segments (0x3dc28 : word) = Some W_3dc28.
Proof. vm_refl. Qed.
Lemma D_3dc28 : decode_any W_3dc28 = Some (ShiftImm ALU_SRL 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc2c : bv 32 := 0x00750513.
Lemma F_3dc2c : fetch_word Asan.M.loaded_segments (0x3dc2c : word) = Some W_3dc2c.
Proof. vm_refl. Qed.
Lemma D_3dc2c : decode_any W_3dc2c = Some (OpImm ALU_ADD 10 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc30 : bv 32 := 0x00a4f6b3.
Lemma F_3dc30 : fetch_word Asan.M.loaded_segments (0x3dc30 : word) = Some W_3dc30.
Proof. vm_refl. Qed.
Lemma D_3dc30 : decode_any W_3dc30 = Some (Op ALU_AND 13 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc34 : bv 32 := 0xfffd8517.
Lemma F_3dc34 : fetch_word Asan.M.loaded_segments (0x3dc34 : word) = Some W_3dc34.
Proof. vm_refl. Qed.
Lemma D_3dc34 : decode_any W_3dc34 = Some (Auipc 10 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc38 : bv 32 := 0xfffdb597.
Lemma F_3dc38 : fetch_word Asan.M.loaded_segments (0x3dc38 : word) = Some W_3dc38.
Proof. vm_refl. Qed.
Lemma D_3dc38 : decode_any W_3dc38 = Some (Auipc 11 1048539, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc3c : bv 32 := 0xad350513.
Lemma F_3dc3c : fetch_word Asan.M.loaded_segments (0x3dc3c : word) = Some W_3dc3c.
Proof. vm_refl. Qed.
Lemma D_3dc3c : decode_any W_3dc3c = Some (OpImm ALU_ADD 10 10 2771, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc40 : bv 32 := 0xff158613.
Lemma F_3dc40 : fetch_word Asan.M.loaded_segments (0x3dc40 : word) = Some W_3dc40.
Proof. vm_refl. Qed.
Lemma D_3dc40 : decode_any W_3dc40 = Some (OpImm ALU_ADD 12 11 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc44 : bv 32 := 0x07800593.
Lemma F_3dc44 : fetch_word Asan.M.loaded_segments (0x3dc44 : word) = Some W_3dc44.
Proof. vm_refl. Qed.
Lemma D_3dc44 : decode_any W_3dc44 = Some (OpImm ALU_ADD 11 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc48 : bv 32 := 0x00048713.
Lemma F_3dc48 : fetch_word Asan.M.loaded_segments (0x3dc48 : word) = Some W_3dc48.
Proof. vm_refl. Qed.
Lemma D_3dc48 : decode_any W_3dc48 = Some (OpImm ALU_ADD 14 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc4c : bv 32 := 0x41c3b0ef.
Lemma F_3dc4c : fetch_word Asan.M.loaded_segments (0x3dc4c : word) = Some W_3dc4c.
Proof. vm_refl. Qed.
Lemma D_3dc4c : decode_any W_3dc4c = Some (Jal 1 242716, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc50 : bv 32 := 0x000b8513.
Lemma F_3dc50 : fetch_word Asan.M.loaded_segments (0x3dc50 : word) = Some W_3dc50.
Proof. vm_refl. Qed.
Lemma D_3dc50 : decode_any W_3dc50 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc54 : bv 32 := 0x78c260ef.
Lemma F_3dc54 : fetch_word Asan.M.loaded_segments (0x3dc54 : word) = Some W_3dc54.
Proof. vm_refl. Qed.
Lemma D_3dc54 : decode_any W_3dc54 = Some (Jal 1 157580, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc58 : bv 32 := 0xf60b9e63.
Lemma F_3dc58 : fetch_word Asan.M.loaded_segments (0x3dc58 : word) = Some W_3dc58.
Proof. vm_refl. Qed.
Lemma D_3dc58 : decode_any W_3dc58 = Some (Branch BC_NE 23 0 6012, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc5c : bv 32 := 0xfffd8517.
Lemma F_3dc5c : fetch_word Asan.M.loaded_segments (0x3dc5c : word) = Some W_3dc5c.
Proof. vm_refl. Qed.
Lemma D_3dc5c : decode_any W_3dc5c = Some (Auipc 10 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc60 : bv 32 := 0xfffd5597.
Lemma F_3dc60 : fetch_word Asan.M.loaded_segments (0x3dc60 : word) = Some W_3dc60.
Proof. vm_refl. Qed.
Lemma D_3dc60 : decode_any W_3dc60 = Some (Auipc 11 1048533, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc64 : bv 32 := 0xaab50513.
Lemma F_3dc64 : fetch_word Asan.M.loaded_segments (0x3dc64 : word) = Some W_3dc64.
Proof. vm_refl. Qed.
Lemma D_3dc64 : decode_any W_3dc64 = Some (OpImm ALU_ADD 10 10 2731, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc68 : bv 32 := 0x60d58613.
Lemma F_3dc68 : fetch_word Asan.M.loaded_segments (0x3dc68 : word) = Some W_3dc68.
Proof. vm_refl. Qed.
Lemma D_3dc68 : decode_any W_3dc68 = Some (OpImm ALU_ADD 12 11 1549, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc6c : bv 32 := 0x22300593.
Lemma F_3dc6c : fetch_word Asan.M.loaded_segments (0x3dc6c : word) = Some W_3dc6c.
Proof. vm_refl. Qed.
Lemma D_3dc6c : decode_any W_3dc6c = Some (OpImm ALU_ADD 11 0 547, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc70 : bv 32 := 0x00000693.
Lemma F_3dc70 : fetch_word Asan.M.loaded_segments (0x3dc70 : word) = Some W_3dc70.
Proof. vm_refl. Qed.
Lemma D_3dc70 : decode_any W_3dc70 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc74 : bv 32 := 0x00000713.
Lemma F_3dc74 : fetch_word Asan.M.loaded_segments (0x3dc74 : word) = Some W_3dc74.
Proof. vm_refl. Qed.
Lemma D_3dc74 : decode_any W_3dc74 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc78 : bv 32 := 0x3f03b0ef.
Lemma F_3dc78 : fetch_word Asan.M.loaded_segments (0x3dc78 : word) = Some W_3dc78.
Proof. vm_refl. Qed.
Lemma D_3dc78 : decode_any W_3dc78 = Some (Jal 1 242672, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc7c : bv 32 := 0xfffe2517.
Lemma F_3dc7c : fetch_word Asan.M.loaded_segments (0x3dc7c : word) = Some W_3dc7c.
Proof. vm_refl. Qed.
Lemma D_3dc7c : decode_any W_3dc7c = Some (Auipc 10 1048546, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc80 : bv 32 := 0xfffd6597.
Lemma F_3dc80 : fetch_word Asan.M.loaded_segments (0x3dc80 : word) = Some W_3dc80.
Proof. vm_refl. Qed.
Lemma D_3dc80 : decode_any W_3dc80 = Some (Auipc 11 1048534, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc84 : bv 32 := 0x81b50513.
Lemma F_3dc84 : fetch_word Asan.M.loaded_segments (0x3dc84 : word) = Some W_3dc84.
Proof. vm_refl. Qed.
Lemma D_3dc84 : decode_any W_3dc84 = Some (OpImm ALU_ADD 10 10 2075, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc88 : bv 32 := 0x69658613.
Lemma F_3dc88 : fetch_word Asan.M.loaded_segments (0x3dc88 : word) = Some W_3dc88.
Proof. vm_refl. Qed.
Lemma D_3dc88 : decode_any W_3dc88 = Some (OpImm ALU_ADD 12 11 1686, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc8c : bv 32 := 0x1e300593.
Lemma F_3dc8c : fetch_word Asan.M.loaded_segments (0x3dc8c : word) = Some W_3dc8c.
Proof. vm_refl. Qed.
Lemma D_3dc8c : decode_any W_3dc8c = Some (OpImm ALU_ADD 11 0 483, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc90 : bv 32 := 0x00000693.
Lemma F_3dc90 : fetch_word Asan.M.loaded_segments (0x3dc90 : word) = Some W_3dc90.
Proof. vm_refl. Qed.
Lemma D_3dc90 : decode_any W_3dc90 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc94 : bv 32 := 0x00000713.
Lemma F_3dc94 : fetch_word Asan.M.loaded_segments (0x3dc94 : word) = Some W_3dc94.
Proof. vm_refl. Qed.
Lemma D_3dc94 : decode_any W_3dc94 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc98 : bv 32 := 0x3d03b0ef.
Lemma F_3dc98 : fetch_word Asan.M.loaded_segments (0x3dc98 : word) = Some W_3dc98.
Proof. vm_refl. Qed.
Lemma D_3dc98 : decode_any W_3dc98 = Some (Jal 1 242640, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dc9c : bv 32 := 0xfffd8517.
Lemma F_3dc9c : fetch_word Asan.M.loaded_segments (0x3dc9c : word) = Some W_3dc9c.
Proof. vm_refl. Qed.
Lemma D_3dc9c : decode_any W_3dc9c = Some (Auipc 10 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dca0 : bv 32 := 0xfffd4597.
Lemma F_3dca0 : fetch_word Asan.M.loaded_segments (0x3dca0 : word) = Some W_3dca0.
Proof. vm_refl. Qed.
Lemma D_3dca0 : decode_any W_3dca0 = Some (Auipc 11 1048532, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dca4 : bv 32 := 0xa6b50513.
Lemma F_3dca4 : fetch_word Asan.M.loaded_segments (0x3dca4 : word) = Some W_3dca4.
Proof. vm_refl. Qed.
Lemma D_3dca4 : decode_any W_3dca4 = Some (OpImm ALU_ADD 10 10 2667, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dca8 : bv 32 := 0x26f58613.
Lemma F_3dca8 : fetch_word Asan.M.loaded_segments (0x3dca8 : word) = Some W_3dca8.
Proof. vm_refl. Qed.
Lemma D_3dca8 : decode_any W_3dca8 = Some (OpImm ALU_ADD 12 11 623, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dcac : bv 32 := 0x29800593.
Lemma F_3dcac : fetch_word Asan.M.loaded_segments (0x3dcac : word) = Some W_3dcac.
Proof. vm_refl. Qed.
Lemma D_3dcac : decode_any W_3dcac = Some (OpImm ALU_ADD 11 0 664, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dcb0 : bv 32 := 0x000a8713.
Lemma F_3dcb0 : fetch_word Asan.M.loaded_segments (0x3dcb0 : word) = Some W_3dcb0.
Proof. vm_refl. Qed.
Lemma D_3dcb0 : decode_any W_3dcb0 = Some (OpImm ALU_ADD 14 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dcb4 : bv 32 := 0x3b43b0ef.
Lemma F_3dcb4 : fetch_word Asan.M.loaded_segments (0x3dcb4 : word) = Some W_3dcb4.
Proof. vm_refl. Qed.
Lemma D_3dcb4 : decode_any W_3dcb4 = Some (Jal 1 242612, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dcb8 : bv 32 := 0x424350ef.
Lemma F_3dcb8 : fetch_word Asan.M.loaded_segments (0x3dcb8 : word) = Some W_3dcb8.
Proof. vm_refl. Qed.
Lemma D_3dcb8 : decode_any W_3dcb8 = Some (Jal 1 218148, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dcbc : bv 32 := 0xa01ff06f.
Lemma F_3dcbc : fetch_word Asan.M.loaded_segments (0x3dcbc : word) = Some W_3dcbc.
Proof. vm_refl. Qed.
Lemma D_3dcbc : decode_any W_3dcbc = Some (Jal 0 2095616, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dcc0 : bv 32 := 0xfffd6517.
Lemma F_3dcc0 : fetch_word Asan.M.loaded_segments (0x3dcc0 : word) = Some W_3dcc0.
Proof. vm_refl. Qed.
Lemma D_3dcc0 : decode_any W_3dcc0 = Some (Auipc 10 1048534, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dcc4 : bv 32 := 0xfffde597.
Lemma F_3dcc4 : fetch_word Asan.M.loaded_segments (0x3dcc4 : word) = Some W_3dcc4.
Proof. vm_refl. Qed.
Lemma D_3dcc4 : decode_any W_3dcc4 = Some (Auipc 11 1048542, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dcc8 : bv 32 := 0x5ff50513.
Lemma F_3dcc8 : fetch_word Asan.M.loaded_segments (0x3dcc8 : word) = Some W_3dcc8.
Proof. vm_refl. Qed.
Lemma D_3dcc8 : decode_any W_3dcc8 = Some (OpImm ALU_ADD 10 10 1535, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dccc : bv 32 := 0x9bf58613.
Lemma F_3dccc : fetch_word Asan.M.loaded_segments (0x3dccc : word) = Some W_3dccc.
Proof. vm_refl. Qed.
Lemma D_3dccc : decode_any W_3dccc = Some (OpImm ALU_ADD 12 11 2495, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dcd0 : bv 32 := 0x12900593.
Lemma F_3dcd0 : fetch_word Asan.M.loaded_segments (0x3dcd0 : word) = Some W_3dcd0.
Proof. vm_refl. Qed.
Lemma D_3dcd0 : decode_any W_3dcd0 = Some (OpImm ALU_ADD 11 0 297, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dcd4 : bv 32 := 0x00000693.
Lemma F_3dcd4 : fetch_word Asan.M.loaded_segments (0x3dcd4 : word) = Some W_3dcd4.
Proof. vm_refl. Qed.
Lemma D_3dcd4 : decode_any W_3dcd4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dcd8 : bv 32 := 0x00000713.
Lemma F_3dcd8 : fetch_word Asan.M.loaded_segments (0x3dcd8 : word) = Some W_3dcd8.
Proof. vm_refl. Qed.
Lemma D_3dcd8 : decode_any W_3dcd8 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dcdc : bv 32 := 0x38c3b0ef.
Lemma F_3dcdc : fetch_word Asan.M.loaded_segments (0x3dcdc : word) = Some W_3dcdc.
Proof. vm_refl. Qed.
Lemma D_3dcdc : decode_any W_3dcdc = Some (Jal 1 242572, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dce0 : bv 32 := 0x04000413.
Lemma F_3dce0 : fetch_word Asan.M.loaded_segments (0x3dce0 : word) = Some W_3dce0.
Proof. vm_refl. Qed.
Lemma D_3dce0 : decode_any W_3dce0 = Some (OpImm ALU_ADD 8 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dce4 : bv 32 := 0xaf9ff06f.
Lemma F_3dce4 : fetch_word Asan.M.loaded_segments (0x3dce4 : word) = Some W_3dce4.
Proof. vm_refl. Qed.
Lemma D_3dce4 : decode_any W_3dce4 = Some (Jal 0 2095864, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dce8 : bv 32 := 0xfffd5517.
Lemma F_3dce8 : fetch_word Asan.M.loaded_segments (0x3dce8 : word) = Some W_3dce8.
Proof. vm_refl. Qed.
Lemma D_3dce8 : decode_any W_3dce8 = Some (Auipc 10 1048533, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dcec : bv 32 := 0xa8250513.
Lemma F_3dcec : fetch_word Asan.M.loaded_segments (0x3dcec : word) = Some W_3dcec.
Proof. vm_refl. Qed.
Lemma D_3dcec : decode_any W_3dcec = Some (OpImm ALU_ADD 10 10 2690, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dcf0 : bv 32 := 0x524300ef.
Lemma F_3dcf0 : fetch_word Asan.M.loaded_segments (0x3dcf0 : word) = Some W_3dcf0.
Proof. vm_refl. Qed.
Lemma D_3dcf0 : decode_any W_3dcf0 = Some (Jal 1 197924, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dcf4 : bv 32 := 0x2a83b0ef.
Lemma F_3dcf4 : fetch_word Asan.M.loaded_segments (0x3dcf4 : word) = Some W_3dcf4.
Proof. vm_refl. Qed.
Lemma D_3dcf4 : decode_any W_3dcf4 = Some (Jal 1 242344, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dcf8 : bv 32 := 0xff010113.
Lemma F_3dcf8 : fetch_word Asan.M.loaded_segments (0x3dcf8 : word) = Some W_3dcf8.
Proof. vm_refl. Qed.
Lemma D_3dcf8 : decode_any W_3dcf8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dcfc : bv 32 := 0x00113423.
Lemma F_3dcfc : fetch_word Asan.M.loaded_segments (0x3dcfc : word) = Some W_3dcfc.
Proof. vm_refl. Qed.
Lemma D_3dcfc : decode_any W_3dcfc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd00 : bv 32 := 0x00060813.
Lemma F_3dd00 : fetch_word Asan.M.loaded_segments (0x3dd00 : word) = Some W_3dd00.
Proof. vm_refl. Qed.
Lemma D_3dd00 : decode_any W_3dd00 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd04 : bv 32 := 0x00058693.
Lemma F_3dd04 : fetch_word Asan.M.loaded_segments (0x3dd04 : word) = Some W_3dd04.
Proof. vm_refl. Qed.
Lemma D_3dd04 : decode_any W_3dd04 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd08 : bv 32 := 0x04050463.
Lemma F_3dd08 : fetch_word Asan.M.loaded_segments (0x3dd08 : word) = Some W_3dd08.
Proof. vm_refl. Qed.
Lemma D_3dd08 : decode_any W_3dd08 = Some (Branch BC_EQ 10 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd0c : bv 32 := 0x00050593.
Lemma F_3dd0c : fetch_word Asan.M.loaded_segments (0x3dd0c : word) = Some W_3dd0c.
Proof. vm_refl. Qed.
Lemma D_3dd0c : decode_any W_3dd0c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd10 : bv 32 := 0x06069863.
Lemma F_3dd10 : fetch_word Asan.M.loaded_segments (0x3dd10 : word) = Some W_3dd10.
Proof. vm_refl. Qed.
Lemma D_3dd10 : decode_any W_3dd10 = Some (Branch BC_NE 13 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd14 : bv 32 := 0x00098517.
Lemma F_3dd14 : fetch_word Asan.M.loaded_segments (0x3dd14 : word) = Some W_3dd14.
Proof. vm_refl. Qed.
Lemma D_3dd14 : decode_any W_3dd14 = Some (Auipc 10 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd18 : bv 32 := 0xb9c53503.
Lemma F_3dd18 : fetch_word Asan.M.loaded_segments (0x3dd18 : word) = Some W_3dd18.
Proof. vm_refl. Qed.
Lemma D_3dd18 : decode_any W_3dd18 = Some (Load SZ8 true 10 10 2972, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd1c : bv 32 := 0x07154503.
Lemma F_3dd1c : fetch_word Asan.M.loaded_segments (0x3dd1c : word) = Some W_3dd1c.
Proof. vm_refl. Qed.
Lemma D_3dd1c : decode_any W_3dd1c = Some (Load SZ1 false 10 10 113, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd20 : bv 32 := 0x04050e63.
Lemma F_3dd20 : fetch_word Asan.M.loaded_segments (0x3dd20 : word) = Some W_3dd20.
Proof. vm_refl. Qed.
Lemma D_3dd20 : decode_any W_3dd20 = Some (Branch BC_EQ 10 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd24 : bv 32 := 0x0009c517.
Lemma F_3dd24 : fetch_word Asan.M.loaded_segments (0x3dd24 : word) = Some W_3dd24.
Proof. vm_refl. Qed.
Lemma D_3dd24 : decode_any W_3dd24 = Some (Auipc 10 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd28 : bv 32 := 0x7b450513.
Lemma F_3dd28 : fetch_word Asan.M.loaded_segments (0x3dd28 : word) = Some W_3dd28.
Proof. vm_refl. Qed.
Lemma D_3dd28 : decode_any W_3dd28 = Some (OpImm ALU_ADD 10 10 1972, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd2c : bv 32 := 0x00100793.
Lemma F_3dd2c : fetch_word Asan.M.loaded_segments (0x3dd2c : word) = Some W_3dd2c.
Proof. vm_refl. Qed.
Lemma D_3dd2c : decode_any W_3dd2c = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd30 : bv 32 := 0x00000613.
Lemma F_3dd30 : fetch_word Asan.M.loaded_segments (0x3dd30 : word) = Some W_3dd30.
Proof. vm_refl. Qed.
Lemma D_3dd30 : decode_any W_3dd30 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd34 : bv 32 := 0x00000693.
Lemma F_3dd34 : fetch_word Asan.M.loaded_segments (0x3dd34 : word) = Some W_3dd34.
Proof. vm_refl. Qed.
Lemma D_3dd34 : decode_any W_3dd34 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd38 : bv 32 := 0x00080713.
Lemma F_3dd38 : fetch_word Asan.M.loaded_segments (0x3dd38 : word) = Some W_3dd38.
Proof. vm_refl. Qed.
Lemma D_3dd38 : decode_any W_3dd38 = Some (OpImm ALU_ADD 14 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd3c : bv 32 := 0xb20ff0ef.
Lemma F_3dd3c : fetch_word Asan.M.loaded_segments (0x3dd3c : word) = Some W_3dd3c.
Proof. vm_refl. Qed.
Lemma D_3dd3c : decode_any W_3dd3c = Some (Jal 1 2093856, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd40 : bv 32 := 0x00000513.
Lemma F_3dd40 : fetch_word Asan.M.loaded_segments (0x3dd40 : word) = Some W_3dd40.
Proof. vm_refl. Qed.
Lemma D_3dd40 : decode_any W_3dd40 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd44 : bv 32 := 0x00813083.
Lemma F_3dd44 : fetch_word Asan.M.loaded_segments (0x3dd44 : word) = Some W_3dd44.
Proof. vm_refl. Qed.
Lemma D_3dd44 : decode_any W_3dd44 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd48 : bv 32 := 0x01010113.
Lemma F_3dd48 : fetch_word Asan.M.loaded_segments (0x3dd48 : word) = Some W_3dd48.
Proof. vm_refl. Qed.
Lemma D_3dd48 : decode_any W_3dd48 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd4c : bv 32 := 0x00008067.
Lemma F_3dd4c : fetch_word Asan.M.loaded_segments (0x3dd4c : word) = Some W_3dd4c.
Proof. vm_refl. Qed.
Lemma D_3dd4c : decode_any W_3dd4c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd50 : bv 32 := 0x0009c517.
Lemma F_3dd50 : fetch_word Asan.M.loaded_segments (0x3dd50 : word) = Some W_3dd50.
Proof. vm_refl. Qed.
Lemma D_3dd50 : decode_any W_3dd50 = Some (Auipc 10 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd54 : bv 32 := 0x00800613.
Lemma F_3dd54 : fetch_word Asan.M.loaded_segments (0x3dd54 : word) = Some W_3dd54.
Proof. vm_refl. Qed.
Lemma D_3dd54 : decode_any W_3dd54 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd58 : bv 32 := 0x00100713.
Lemma F_3dd58 : fetch_word Asan.M.loaded_segments (0x3dd58 : word) = Some W_3dd58.
Proof. vm_refl. Qed.
Lemma D_3dd58 : decode_any W_3dd58 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd5c : bv 32 := 0x78850513.
Lemma F_3dd5c : fetch_word Asan.M.loaded_segments (0x3dd5c : word) = Some W_3dd5c.
Proof. vm_refl. Qed.
Lemma D_3dd5c : decode_any W_3dd5c = Some (OpImm ALU_ADD 10 10 1928, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd60 : bv 32 := 0x00100793.
Lemma F_3dd60 : fetch_word Asan.M.loaded_segments (0x3dd60 : word) = Some W_3dd60.
Proof. vm_refl. Qed.
Lemma D_3dd60 : decode_any W_3dd60 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd64 : bv 32 := 0x00068593.
Lemma F_3dd64 : fetch_word Asan.M.loaded_segments (0x3dd64 : word) = Some W_3dd64.
Proof. vm_refl. Qed.
Lemma D_3dd64 : decode_any W_3dd64 = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd68 : bv 32 := 0x00080693.
Lemma F_3dd68 : fetch_word Asan.M.loaded_segments (0x3dd68 : word) = Some W_3dd68.
Proof. vm_refl. Qed.
Lemma D_3dd68 : decode_any W_3dd68 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd6c : bv 32 := 0xe04ff0ef.
Lemma F_3dd6c : fetch_word Asan.M.loaded_segments (0x3dd6c : word) = Some W_3dd6c.
Proof. vm_refl. Qed.
Lemma D_3dd6c : decode_any W_3dd6c = Some (Jal 1 2094596, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd70 : bv 32 := 0x02051463.
Lemma F_3dd70 : fetch_word Asan.M.loaded_segments (0x3dd70 : word) = Some W_3dd70.
Proof. vm_refl. Qed.
Lemma D_3dd70 : decode_any W_3dd70 = Some (Branch BC_NE 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd74 : bv 32 := 0x6cd3b0ef.
Lemma F_3dd74 : fetch_word Asan.M.loaded_segments (0x3dd74 : word) = Some W_3dd74.
Proof. vm_refl. Qed.
Lemma D_3dd74 : decode_any W_3dd74 = Some (Jal 1 245452, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd78 : bv 32 := 0xfc9ff06f.
Lemma F_3dd78 : fetch_word Asan.M.loaded_segments (0x3dd78 : word) = Some W_3dd78.
Proof. vm_refl. Qed.
Lemma D_3dd78 : decode_any W_3dd78 = Some (Jal 0 2097096, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd7c : bv 32 := 0x00100693.
Lemma F_3dd7c : fetch_word Asan.M.loaded_segments (0x3dd7c : word) = Some W_3dd7c.
Proof. vm_refl. Qed.
Lemma D_3dd7c : decode_any W_3dd7c = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd80 : bv 32 := 0x0009c517.
Lemma F_3dd80 : fetch_word Asan.M.loaded_segments (0x3dd80 : word) = Some W_3dd80.
Proof. vm_refl. Qed.
Lemma D_3dd80 : decode_any W_3dd80 = Some (Auipc 10 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd84 : bv 32 := 0x75850513.
Lemma F_3dd84 : fetch_word Asan.M.loaded_segments (0x3dd84 : word) = Some W_3dd84.
Proof. vm_refl. Qed.
Lemma D_3dd84 : decode_any W_3dd84 = Some (OpImm ALU_ADD 10 10 1880, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd88 : bv 32 := 0x00068613.
Lemma F_3dd88 : fetch_word Asan.M.loaded_segments (0x3dd88 : word) = Some W_3dd88.
Proof. vm_refl. Qed.
Lemma D_3dd88 : decode_any W_3dd88 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd8c : bv 32 := 0x00080693.
Lemma F_3dd8c : fetch_word Asan.M.loaded_segments (0x3dd8c : word) = Some W_3dd8c.
Proof. vm_refl. Qed.
Lemma D_3dd8c : decode_any W_3dd8c = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd90 : bv 32 := 0x014000ef.
Lemma F_3dd90 : fetch_word Asan.M.loaded_segments (0x3dd90 : word) = Some W_3dd90.
Proof. vm_refl. Qed.
Lemma D_3dd90 : decode_any W_3dd90 = Some (Jal 1 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd94 : bv 32 := 0xfe0500e3.
Lemma F_3dd94 : fetch_word Asan.M.loaded_segments (0x3dd94 : word) = Some W_3dd94.
Proof. vm_refl. Qed.
Lemma D_3dd94 : decode_any W_3dd94 = Some (Branch BC_EQ 10 0 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd98 : bv 32 := 0x00813083.
Lemma F_3dd98 : fetch_word Asan.M.loaded_segments (0x3dd98 : word) = Some W_3dd98.
Proof. vm_refl. Qed.
Lemma D_3dd98 : decode_any W_3dd98 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dd9c : bv 32 := 0x01010113.
Lemma F_3dd9c : fetch_word Asan.M.loaded_segments (0x3dd9c : word) = Some W_3dd9c.
Proof. vm_refl. Qed.
Lemma D_3dd9c : decode_any W_3dd9c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dda0 : bv 32 := 0x00008067.
Lemma F_3dda0 : fetch_word Asan.M.loaded_segments (0x3dda0 : word) = Some W_3dda0.
Proof. vm_refl. Qed.
Lemma D_3dda0 : decode_any W_3dda0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dda4 : bv 32 := 0xfd010113.
Lemma F_3dda4 : fetch_word Asan.M.loaded_segments (0x3dda4 : word) = Some W_3dda4.
Proof. vm_refl. Qed.
Lemma D_3dda4 : decode_any W_3dda4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dda8 : bv 32 := 0x02113423.
Lemma F_3dda8 : fetch_word Asan.M.loaded_segments (0x3dda8 : word) = Some W_3dda8.
Proof. vm_refl. Qed.
Lemma D_3dda8 : decode_any W_3dda8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ddac : bv 32 := 0x02813023.
Lemma F_3ddac : fetch_word Asan.M.loaded_segments (0x3ddac : word) = Some W_3ddac.
Proof. vm_refl. Qed.
Lemma D_3ddac : decode_any W_3ddac = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ddb0 : bv 32 := 0x00913c23.
Lemma F_3ddb0 : fetch_word Asan.M.loaded_segments (0x3ddb0 : word) = Some W_3ddb0.
Proof. vm_refl. Qed.
Lemma D_3ddb0 : decode_any W_3ddb0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ddb4 : bv 32 := 0x01213823.
Lemma F_3ddb4 : fetch_word Asan.M.loaded_segments (0x3ddb4 : word) = Some W_3ddb4.
Proof. vm_refl. Qed.
Lemma D_3ddb4 : decode_any W_3ddb4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ddb8 : bv 32 := 0x01313423.
Lemma F_3ddb8 : fetch_word Asan.M.loaded_segments (0x3ddb8 : word) = Some W_3ddb8.
Proof. vm_refl. Qed.
Lemma D_3ddb8 : decode_any W_3ddb8 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ddbc : bv 32 := 0x01413023.
Lemma F_3ddbc : fetch_word Asan.M.loaded_segments (0x3ddbc : word) = Some W_3ddbc.
Proof. vm_refl. Qed.
Lemma D_3ddbc : decode_any W_3ddbc = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ddc0 : bv 32 := 0x10058463.
Lemma F_3ddc0 : fetch_word Asan.M.loaded_segments (0x3ddc0 : word) = Some W_3ddc0.
Proof. vm_refl. Qed.
Lemma D_3ddc0 : decode_any W_3ddc0 = Some (Branch BC_EQ 11 0 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ddc4 : bv 32 := 0x00060993.
Lemma F_3ddc4 : fetch_word Asan.M.loaded_segments (0x3ddc4 : word) = Some W_3ddc4.
Proof. vm_refl. Qed.
Lemma D_3ddc4 : decode_any W_3ddc4 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ddc8 : bv 32 := 0x10060063.
Lemma F_3ddc8 : fetch_word Asan.M.loaded_segments (0x3ddc8 : word) = Some W_3ddc8.
Proof. vm_refl. Qed.
Lemma D_3ddc8 : decode_any W_3ddc8 = Some (Branch BC_EQ 12 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ddcc : bv 32 := 0x00068413.
Lemma F_3ddcc : fetch_word Asan.M.loaded_segments (0x3ddcc : word) = Some W_3ddcc.
Proof. vm_refl. Qed.
Lemma D_3ddcc : decode_any W_3ddcc = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ddd0 : bv 32 := 0x00058493.
Lemma F_3ddd0 : fetch_word Asan.M.loaded_segments (0x3ddd0 : word) = Some W_3ddd0.
Proof. vm_refl. Qed.
Lemma D_3ddd0 : decode_any W_3ddd0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ddd4 : bv 32 := 0x00050913.
Lemma F_3ddd4 : fetch_word Asan.M.loaded_segments (0x3ddd4 : word) = Some W_3ddd4.
Proof. vm_refl. Qed.
Lemma D_3ddd4 : decode_any W_3ddd4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ddd8 : bv 32 := 0x3d92a0ef.
Lemma F_3ddd8 : fetch_word Asan.M.loaded_segments (0x3ddd8 : word) = Some W_3ddd8.
Proof. vm_refl. Qed.
Lemma D_3ddd8 : decode_any W_3ddd8 = Some (Jal 1 175064, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dddc : bv 32 := 0x03853583.
Lemma F_3dddc : fetch_word Asan.M.loaded_segments (0x3dddc : word) = Some W_3dddc.
Proof. vm_refl. Qed.
Lemma D_3dddc : decode_any W_3dddc = Some (Load SZ8 true 11 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dde0 : bv 32 := 0x04053603.
Lemma F_3dde0 : fetch_word Asan.M.loaded_segments (0x3dde0 : word) = Some W_3dde0.
Proof. vm_refl. Qed.
Lemma D_3dde0 : decode_any W_3dde0 = Some (Load SZ8 true 12 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dde4 : bv 32 := 0x00158593.
Lemma F_3dde4 : fetch_word Asan.M.loaded_segments (0x3dde4 : word) = Some W_3dde4.
Proof. vm_refl. Qed.
Lemma D_3dde4 : decode_any W_3dde4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dde8 : bv 32 := 0x01360633.
Lemma F_3dde8 : fetch_word Asan.M.loaded_segments (0x3dde8 : word) = Some W_3dde8.
Proof. vm_refl. Qed.
Lemma D_3dde8 : decode_any W_3dde8 = Some (Op ALU_ADD 12 12 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ddec : bv 32 := 0x02b53c23.
Lemma F_3ddec : fetch_word Asan.M.loaded_segments (0x3ddec : word) = Some W_3ddec.
Proof. vm_refl. Qed.
Lemma D_3ddec : decode_any W_3ddec = Some (Store SZ8 10 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ddf0 : bv 32 := 0x04c53023.
Lemma F_3ddf0 : fetch_word Asan.M.loaded_segments (0x3ddf0 : word) = Some W_3ddf0.
Proof. vm_refl. Qed.
Lemma D_3ddf0 : decode_any W_3ddf0 = Some (Store SZ8 10 12 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ddf4 : bv 32 := 0x00800613.
Lemma F_3ddf4 : fetch_word Asan.M.loaded_segments (0x3ddf4 : word) = Some W_3ddf4.
Proof. vm_refl. Qed.
Lemma D_3ddf4 : decode_any W_3ddf4 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ddf8 : bv 32 := 0x00100713.
Lemma F_3ddf8 : fetch_word Asan.M.loaded_segments (0x3ddf8 : word) = Some W_3ddf8.
Proof. vm_refl. Qed.
Lemma D_3ddf8 : decode_any W_3ddf8 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ddfc : bv 32 := 0x00100793.
Lemma F_3ddfc : fetch_word Asan.M.loaded_segments (0x3ddfc : word) = Some W_3ddfc.
Proof. vm_refl. Qed.
Lemma D_3ddfc : decode_any W_3ddfc = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de00 : bv 32 := 0x00090513.
Lemma F_3de00 : fetch_word Asan.M.loaded_segments (0x3de00 : word) = Some W_3de00.
Proof. vm_refl. Qed.
Lemma D_3de00 : decode_any W_3de00 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de04 : bv 32 := 0x00098593.
Lemma F_3de04 : fetch_word Asan.M.loaded_segments (0x3de04 : word) = Some W_3de04.
Proof. vm_refl. Qed.
Lemma D_3de04 : decode_any W_3de04 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de08 : bv 32 := 0x00040693.
Lemma F_3de08 : fetch_word Asan.M.loaded_segments (0x3de08 : word) = Some W_3de08.
Proof. vm_refl. Qed.
Lemma D_3de08 : decode_any W_3de08 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de0c : bv 32 := 0xd64ff0ef.
Lemma F_3de0c : fetch_word Asan.M.loaded_segments (0x3de0c : word) = Some W_3de0c.
Proof. vm_refl. Qed.
Lemma D_3de0c : decode_any W_3de0c = Some (Jal 1 2094436, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de10 : bv 32 := 0x00050a13.
Lemma F_3de10 : fetch_word Asan.M.loaded_segments (0x3de10 : word) = Some W_3de10.
Proof. vm_refl. Qed.
Lemma D_3de10 : decode_any W_3de10 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de14 : bv 32 := 0x08050863.
Lemma F_3de14 : fetch_word Asan.M.loaded_segments (0x3de14 : word) = Some W_3de14.
Proof. vm_refl. Qed.
Lemma D_3de14 : decode_any W_3de14 = Some (Branch BC_EQ 10 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de18 : bv 32 := 0xff048503.
Lemma F_3de18 : fetch_word Asan.M.loaded_segments (0x3de18 : word) = Some W_3de18.
Proof. vm_refl. Qed.
Lemma D_3de18 : decode_any W_3de18 = Some (Load SZ1 true 10 9 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de1c : bv 32 := 0x00200593.
Lemma F_3de1c : fetch_word Asan.M.loaded_segments (0x3de1c : word) = Some W_3de1c.
Proof. vm_refl. Qed.
Lemma D_3de1c : decode_any W_3de1c = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de20 : bv 32 := 0x0230000f.
Lemma F_3de20 : fetch_word Asan.M.loaded_segments (0x3de20 : word) = Some W_3de20.
Proof. vm_refl. Qed.
Lemma D_3de20 : decode_any W_3de20 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de24 : bv 32 := 0x02b50663.
Lemma F_3de24 : fetch_word Asan.M.loaded_segments (0x3de24 : word) = Some W_3de24.
Proof. vm_refl. Qed.
Lemma D_3de24 : decode_any W_3de24 = Some (Branch BC_EQ 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de28 : bv 32 := 0x0ff57513.
Lemma F_3de28 : fetch_word Asan.M.loaded_segments (0x3de28 : word) = Some W_3de28.
Proof. vm_refl. Qed.
Lemma D_3de28 : decode_any W_3de28 = Some (OpImm ALU_AND 10 10 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de2c : bv 32 := 0x00300593.
Lemma F_3de2c : fetch_word Asan.M.loaded_segments (0x3de2c : word) = Some W_3de2c.
Proof. vm_refl. Qed.
Lemma D_3de2c : decode_any W_3de2c = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de30 : bv 32 := 0x00b51a63.
Lemma F_3de30 : fetch_word Asan.M.loaded_segments (0x3de30 : word) = Some W_3de30.
Proof. vm_refl. Qed.
Lemma D_3de30 : decode_any W_3de30 = Some (Branch BC_NE 10 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de34 : bv 32 := 0x00048513.
Lemma F_3de34 : fetch_word Asan.M.loaded_segments (0x3de34 : word) = Some W_3de34.
Proof. vm_refl. Qed.
Lemma D_3de34 : decode_any W_3de34 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de38 : bv 32 := 0x00040593.
Lemma F_3de38 : fetch_word Asan.M.loaded_segments (0x3de38 : word) = Some W_3de38.
Proof. vm_refl. Qed.
Lemma D_3de38 : decode_any W_3de38 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de3c : bv 32 := 0x494250ef.
Lemma F_3de3c : fetch_word Asan.M.loaded_segments (0x3de3c : word) = Some W_3de3c.
Proof. vm_refl. Qed.
Lemma D_3de3c : decode_any W_3de3c = Some (Jal 1 152724, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de40 : bv 32 := 0x0100006f.
Lemma F_3de40 : fetch_word Asan.M.loaded_segments (0x3de40 : word) = Some W_3de40.
Proof. vm_refl. Qed.
Lemma D_3de40 : decode_any W_3de40 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de44 : bv 32 := 0x00048513.
Lemma F_3de44 : fetch_word Asan.M.loaded_segments (0x3de44 : word) = Some W_3de44.
Proof. vm_refl. Qed.
Lemma D_3de44 : decode_any W_3de44 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de48 : bv 32 := 0x00040593.
Lemma F_3de48 : fetch_word Asan.M.loaded_segments (0x3de48 : word) = Some W_3de48.
Proof. vm_refl. Qed.
Lemma D_3de48 : decode_any W_3de48 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de4c : bv 32 := 0x191250ef.
Lemma F_3de4c : fetch_word Asan.M.loaded_segments (0x3de4c : word) = Some W_3de4c.
Proof. vm_refl. Qed.
Lemma D_3de4c : decode_any W_3de4c = Some (Jal 1 154000, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de50 : bv 32 := 0x00098517.
Lemma F_3de50 : fetch_word Asan.M.loaded_segments (0x3de50 : word) = Some W_3de50.
Proof. vm_refl. Qed.
Lemma D_3de50 : decode_any W_3de50 = Some (Auipc 10 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de54 : bv 32 := 0xa9053503.
Lemma F_3de54 : fetch_word Asan.M.loaded_segments (0x3de54 : word) = Some W_3de54.
Proof. vm_refl. Qed.
Lemma D_3de54 : decode_any W_3de54 = Some (Load SZ8 true 10 10 2704, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de58 : bv 32 := 0x00053683.
Lemma F_3de58 : fetch_word Asan.M.loaded_segments (0x3de58 : word) = Some W_3de58.
Proof. vm_refl. Qed.
Lemma D_3de58 : decode_any W_3de58 = Some (Load SZ8 true 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de5c : bv 32 := 0x08068663.
Lemma F_3de5c : fetch_word Asan.M.loaded_segments (0x3de5c : word) = Some W_3de5c.
Proof. vm_refl. Qed.
Lemma D_3de5c : decode_any W_3de5c = Some (Branch BC_EQ 13 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de60 : bv 32 := 0xff24d503.
Lemma F_3de60 : fetch_word Asan.M.loaded_segments (0x3de60 : word) = Some W_3de60.
Proof. vm_refl. Qed.
Lemma D_3de60 : decode_any W_3de60 = Some (Load SZ2 false 10 9 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de64 : bv 32 := 0xff44e583.
Lemma F_3de64 : fetch_word Asan.M.loaded_segments (0x3de64 : word) = Some W_3de64.
Proof. vm_refl. Qed.
Lemma D_3de64 : decode_any W_3de64 = Some (Load SZ4 false 11 9 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de68 : bv 32 := 0x02051513.
Lemma F_3de68 : fetch_word Asan.M.loaded_segments (0x3de68 : word) = Some W_3de68.
Proof. vm_refl. Qed.
Lemma D_3de68 : decode_any W_3de68 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de6c : bv 32 := 0x00b56533.
Lemma F_3de6c : fetch_word Asan.M.loaded_segments (0x3de6c : word) = Some W_3de6c.
Proof. vm_refl. Qed.
Lemma D_3de6c : decode_any W_3de6c = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de70 : bv 32 := 0x00a9e463.
Lemma F_3de70 : fetch_word Asan.M.loaded_segments (0x3de70 : word) = Some W_3de70.
Proof. vm_refl. Qed.
Lemma D_3de70 : decode_any W_3de70 = Some (Branch BC_LTU 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de74 : bv 32 := 0x00050993.
Lemma F_3de74 : fetch_word Asan.M.loaded_segments (0x3de74 : word) = Some W_3de74.
Proof. vm_refl. Qed.
Lemma D_3de74 : decode_any W_3de74 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de78 : bv 32 := 0x000a0513.
Lemma F_3de78 : fetch_word Asan.M.loaded_segments (0x3de78 : word) = Some W_3de78.
Proof. vm_refl. Qed.
Lemma D_3de78 : decode_any W_3de78 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de7c : bv 32 := 0x00048593.
Lemma F_3de7c : fetch_word Asan.M.loaded_segments (0x3de7c : word) = Some W_3de7c.
Proof. vm_refl. Qed.
Lemma D_3de7c : decode_any W_3de7c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de80 : bv 32 := 0x00098613.
Lemma F_3de80 : fetch_word Asan.M.loaded_segments (0x3de80 : word) = Some W_3de80.
Proof. vm_refl. Qed.
Lemma D_3de80 : decode_any W_3de80 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de84 : bv 32 := 0x000680e7.
Lemma F_3de84 : fetch_word Asan.M.loaded_segments (0x3de84 : word) = Some W_3de84.
Proof. vm_refl. Qed.
Lemma D_3de84 : decode_any W_3de84 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de88 : bv 32 := 0x00100793.
Lemma F_3de88 : fetch_word Asan.M.loaded_segments (0x3de88 : word) = Some W_3de88.
Proof. vm_refl. Qed.
Lemma D_3de88 : decode_any W_3de88 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de8c : bv 32 := 0x00090513.
Lemma F_3de8c : fetch_word Asan.M.loaded_segments (0x3de8c : word) = Some W_3de8c.
Proof. vm_refl. Qed.
Lemma D_3de8c : decode_any W_3de8c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de90 : bv 32 := 0x00048593.
Lemma F_3de90 : fetch_word Asan.M.loaded_segments (0x3de90 : word) = Some W_3de90.
Proof. vm_refl. Qed.
Lemma D_3de90 : decode_any W_3de90 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de94 : bv 32 := 0x00000613.
Lemma F_3de94 : fetch_word Asan.M.loaded_segments (0x3de94 : word) = Some W_3de94.
Proof. vm_refl. Qed.
Lemma D_3de94 : decode_any W_3de94 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de98 : bv 32 := 0x00000693.
Lemma F_3de98 : fetch_word Asan.M.loaded_segments (0x3de98 : word) = Some W_3de98.
Proof. vm_refl. Qed.
Lemma D_3de98 : decode_any W_3de98 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3de9c : bv 32 := 0x00040713.
Lemma F_3de9c : fetch_word Asan.M.loaded_segments (0x3de9c : word) = Some W_3de9c.
Proof. vm_refl. Qed.
Lemma D_3de9c : decode_any W_3de9c = Some (OpImm ALU_ADD 14 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dea0 : bv 32 := 0x9bcff0ef.
Lemma F_3dea0 : fetch_word Asan.M.loaded_segments (0x3dea0 : word) = Some W_3dea0.
Proof. vm_refl. Qed.
Lemma D_3dea0 : decode_any W_3dea0 = Some (Jal 1 2093500, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dea4 : bv 32 := 0x000a0513.
Lemma F_3dea4 : fetch_word Asan.M.loaded_segments (0x3dea4 : word) = Some W_3dea4.
Proof. vm_refl. Qed.
Lemma D_3dea4 : decode_any W_3dea4 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dea8 : bv 32 := 0x02813083.
Lemma F_3dea8 : fetch_word Asan.M.loaded_segments (0x3dea8 : word) = Some W_3dea8.
Proof. vm_refl. Qed.
Lemma D_3dea8 : decode_any W_3dea8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_3deac : bv 32 := 0x02013403.
Lemma F_3deac : fetch_word Asan.M.loaded_segments (0x3deac : word) = Some W_3deac.
Proof. vm_refl. Qed.
Lemma D_3deac : decode_any W_3deac = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3deb0 : bv 32 := 0x01813483.
Lemma F_3deb0 : fetch_word Asan.M.loaded_segments (0x3deb0 : word) = Some W_3deb0.
Proof. vm_refl. Qed.
Lemma D_3deb0 : decode_any W_3deb0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3deb4 : bv 32 := 0x01013903.
Lemma F_3deb4 : fetch_word Asan.M.loaded_segments (0x3deb4 : word) = Some W_3deb4.
Proof. vm_refl. Qed.
Lemma D_3deb4 : decode_any W_3deb4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3deb8 : bv 32 := 0x00813983.
Lemma F_3deb8 : fetch_word Asan.M.loaded_segments (0x3deb8 : word) = Some W_3deb8.
Proof. vm_refl. Qed.
Lemma D_3deb8 : decode_any W_3deb8 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3debc : bv 32 := 0x00013a03.
Lemma F_3debc : fetch_word Asan.M.loaded_segments (0x3debc : word) = Some W_3debc.
Proof. vm_refl. Qed.
Lemma D_3debc : decode_any W_3debc = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dec0 : bv 32 := 0x03010113.
Lemma F_3dec0 : fetch_word Asan.M.loaded_segments (0x3dec0 : word) = Some W_3dec0.
Proof. vm_refl. Qed.
Lemma D_3dec0 : decode_any W_3dec0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dec4 : bv 32 := 0x00008067.
Lemma F_3dec4 : fetch_word Asan.M.loaded_segments (0x3dec4 : word) = Some W_3dec4.
Proof. vm_refl. Qed.
Lemma D_3dec4 : decode_any W_3dec4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dec8 : bv 32 := 0xfffd8517.
Lemma F_3dec8 : fetch_word Asan.M.loaded_segments (0x3dec8 : word) = Some W_3dec8.
Proof. vm_refl. Qed.
Lemma D_3dec8 : decode_any W_3dec8 = Some (Auipc 10 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_3decc : bv 32 := 0xfffd3597.
Lemma F_3decc : fetch_word Asan.M.loaded_segments (0x3decc : word) = Some W_3decc.
Proof. vm_refl. Qed.
Lemma D_3decc : decode_any W_3decc = Some (Auipc 11 1048531, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ded0 : bv 32 := 0x83f50513.
Lemma F_3ded0 : fetch_word Asan.M.loaded_segments (0x3ded0 : word) = Some W_3ded0.
Proof. vm_refl. Qed.
Lemma D_3ded0 : decode_any W_3ded0 = Some (OpImm ALU_ADD 10 10 2111, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ded4 : bv 32 := 0x7fd58613.
Lemma F_3ded4 : fetch_word Asan.M.loaded_segments (0x3ded4 : word) = Some W_3ded4.
Proof. vm_refl. Qed.
Lemma D_3ded4 : decode_any W_3ded4 = Some (OpImm ALU_ADD 12 11 2045, 4%Z).
Proof. vm_refl. Qed.

Definition W_3ded8 : bv 32 := 0x2ff00593.
Lemma F_3ded8 : fetch_word Asan.M.loaded_segments (0x3ded8 : word) = Some W_3ded8.
Proof. vm_refl. Qed.
Lemma D_3ded8 : decode_any W_3ded8 = Some (OpImm ALU_ADD 11 0 767, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dedc : bv 32 := 0x00000693.
Lemma F_3dedc : fetch_word Asan.M.loaded_segments (0x3dedc : word) = Some W_3dedc.
Proof. vm_refl. Qed.
Lemma D_3dedc : decode_any W_3dedc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dee0 : bv 32 := 0x00000713.
Lemma F_3dee0 : fetch_word Asan.M.loaded_segments (0x3dee0 : word) = Some W_3dee0.
Proof. vm_refl. Qed.
Lemma D_3dee0 : decode_any W_3dee0 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dee4 : bv 32 := 0x1843b0ef.
Lemma F_3dee4 : fetch_word Asan.M.loaded_segments (0x3dee4 : word) = Some W_3dee4.
Proof. vm_refl. Qed.
Lemma D_3dee4 : decode_any W_3dee4 = Some (Jal 1 242052, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dee8 : bv 32 := 0xfffd8517.
Lemma F_3dee8 : fetch_word Asan.M.loaded_segments (0x3dee8 : word) = Some W_3dee8.
Proof. vm_refl. Qed.
Lemma D_3dee8 : decode_any W_3dee8 = Some (Auipc 10 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_3deec : bv 32 := 0xfffdf597.
Lemma F_3deec : fetch_word Asan.M.loaded_segments (0x3deec : word) = Some W_3deec.
Proof. vm_refl. Qed.
Lemma D_3deec : decode_any W_3deec = Some (Auipc 11 1048543, 4%Z).
Proof. vm_refl. Qed.

Definition W_3def0 : bv 32 := 0x81f50513.
Lemma F_3def0 : fetch_word Asan.M.loaded_segments (0x3def0 : word) = Some W_3def0.
Proof. vm_refl. Qed.
Lemma D_3def0 : decode_any W_3def0 = Some (OpImm ALU_ADD 10 10 2079, 4%Z).
Proof. vm_refl. Qed.

Definition W_3def4 : bv 32 := 0x55c58613.
Lemma F_3def4 : fetch_word Asan.M.loaded_segments (0x3def4 : word) = Some W_3def4.
Proof. vm_refl. Qed.
Lemma D_3def4 : decode_any W_3def4 = Some (OpImm ALU_ADD 12 11 1372, 4%Z).
Proof. vm_refl. Qed.

Definition W_3def8 : bv 32 := 0x30d00593.
Lemma F_3def8 : fetch_word Asan.M.loaded_segments (0x3def8 : word) = Some W_3def8.
Proof. vm_refl. Qed.
Lemma D_3def8 : decode_any W_3def8 = Some (OpImm ALU_ADD 11 0 781, 4%Z).
Proof. vm_refl. Qed.

Definition W_3defc : bv 32 := 0x00000713.
Lemma F_3defc : fetch_word Asan.M.loaded_segments (0x3defc : word) = Some W_3defc.
Proof. vm_refl. Qed.
Lemma D_3defc : decode_any W_3defc = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df00 : bv 32 := 0x1683b0ef.
Lemma F_3df00 : fetch_word Asan.M.loaded_segments (0x3df00 : word) = Some W_3df00.
Proof. vm_refl. Qed.
Lemma D_3df00 : decode_any W_3df00 = Some (Jal 1 242024, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df04 : bv 32 := 0xfe010113.
Lemma F_3df04 : fetch_word Asan.M.loaded_segments (0x3df04 : word) = Some W_3df04.
Proof. vm_refl. Qed.
Lemma D_3df04 : decode_any W_3df04 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df08 : bv 32 := 0x00113c23.
Lemma F_3df08 : fetch_word Asan.M.loaded_segments (0x3df08 : word) = Some W_3df08.
Proof. vm_refl. Qed.
Lemma D_3df08 : decode_any W_3df08 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df0c : bv 32 := 0x00813823.
Lemma F_3df0c : fetch_word Asan.M.loaded_segments (0x3df0c : word) = Some W_3df0c.
Proof. vm_refl. Qed.
Lemma D_3df0c : decode_any W_3df0c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df10 : bv 32 := 0x00913423.
Lemma F_3df10 : fetch_word Asan.M.loaded_segments (0x3df10 : word) = Some W_3df10.
Proof. vm_refl. Qed.
Lemma D_3df10 : decode_any W_3df10 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df14 : bv 32 := 0x01213023.
Lemma F_3df14 : fetch_word Asan.M.loaded_segments (0x3df14 : word) = Some W_3df14.
Proof. vm_refl. Qed.
Lemma D_3df14 : decode_any W_3df14 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df18 : bv 32 := 0x00060413.
Lemma F_3df18 : fetch_word Asan.M.loaded_segments (0x3df18 : word) = Some W_3df18.
Proof. vm_refl. Qed.
Lemma D_3df18 : decode_any W_3df18 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df1c : bv 32 := 0x00050493.
Lemma F_3df1c : fetch_word Asan.M.loaded_segments (0x3df1c : word) = Some W_3df1c.
Proof. vm_refl. Qed.
Lemma D_3df1c : decode_any W_3df1c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df20 : bv 32 := 0xfff50513.
Lemma F_3df20 : fetch_word Asan.M.loaded_segments (0x3df20 : word) = Some W_3df20.
Proof. vm_refl. Qed.
Lemma D_3df20 : decode_any W_3df20 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df24 : bv 32 := 0x00a4c633.
Lemma F_3df24 : fetch_word Asan.M.loaded_segments (0x3df24 : word) = Some W_3df24.
Proof. vm_refl. Qed.
Lemma D_3df24 : decode_any W_3df24 = Some (Op ALU_XOR 12 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df28 : bv 32 := 0x04c57263.
Lemma F_3df28 : fetch_word Asan.M.loaded_segments (0x3df28 : word) = Some W_3df28.
Proof. vm_refl. Qed.
Lemma D_3df28 : decode_any W_3df28 = Some (Branch BC_GEU 10 12 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df2c : bv 32 := 0x00a5f533.
Lemma F_3df2c : fetch_word Asan.M.loaded_segments (0x3df2c : word) = Some W_3df2c.
Proof. vm_refl. Qed.
Lemma D_3df2c : decode_any W_3df2c = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df30 : bv 32 := 0x02051e63.
Lemma F_3df30 : fetch_word Asan.M.loaded_segments (0x3df30 : word) = Some W_3df30.
Proof. vm_refl. Qed.
Lemma D_3df30 : decode_any W_3df30 = Some (Branch BC_NE 10 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df34 : bv 32 := 0x0009c517.
Lemma F_3df34 : fetch_word Asan.M.loaded_segments (0x3df34 : word) = Some W_3df34.
Proof. vm_refl. Qed.
Lemma D_3df34 : decode_any W_3df34 = Some (Auipc 10 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df38 : bv 32 := 0x00100713.
Lemma F_3df38 : fetch_word Asan.M.loaded_segments (0x3df38 : word) = Some W_3df38.
Proof. vm_refl. Qed.
Lemma D_3df38 : decode_any W_3df38 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df3c : bv 32 := 0x5a450513.
Lemma F_3df3c : fetch_word Asan.M.loaded_segments (0x3df3c : word) = Some W_3df3c.
Proof. vm_refl. Qed.
Lemma D_3df3c : decode_any W_3df3c = Some (OpImm ALU_ADD 10 10 1444, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df40 : bv 32 := 0x00100793.
Lemma F_3df40 : fetch_word Asan.M.loaded_segments (0x3df40 : word) = Some W_3df40.
Proof. vm_refl. Qed.
Lemma D_3df40 : decode_any W_3df40 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df44 : bv 32 := 0x00048613.
Lemma F_3df44 : fetch_word Asan.M.loaded_segments (0x3df44 : word) = Some W_3df44.
Proof. vm_refl. Qed.
Lemma D_3df44 : decode_any W_3df44 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df48 : bv 32 := 0x00040693.
Lemma F_3df48 : fetch_word Asan.M.loaded_segments (0x3df48 : word) = Some W_3df48.
Proof. vm_refl. Qed.
Lemma D_3df48 : decode_any W_3df48 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df4c : bv 32 := 0xc24ff0ef.
Lemma F_3df4c : fetch_word Asan.M.loaded_segments (0x3df4c : word) = Some W_3df4c.
Proof. vm_refl. Qed.
Lemma D_3df4c : decode_any W_3df4c = Some (Jal 1 2094116, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df50 : bv 32 := 0x04050663.
Lemma F_3df50 : fetch_word Asan.M.loaded_segments (0x3df50 : word) = Some W_3df50.
Proof. vm_refl. Qed.
Lemma D_3df50 : decode_any W_3df50 = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df54 : bv 32 := 0x01813083.
Lemma F_3df54 : fetch_word Asan.M.loaded_segments (0x3df54 : word) = Some W_3df54.
Proof. vm_refl. Qed.
Lemma D_3df54 : decode_any W_3df54 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df58 : bv 32 := 0x01013403.
Lemma F_3df58 : fetch_word Asan.M.loaded_segments (0x3df58 : word) = Some W_3df58.
Proof. vm_refl. Qed.
Lemma D_3df58 : decode_any W_3df58 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df5c : bv 32 := 0x00813483.
Lemma F_3df5c : fetch_word Asan.M.loaded_segments (0x3df5c : word) = Some W_3df5c.
Proof. vm_refl. Qed.
Lemma D_3df5c : decode_any W_3df5c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df60 : bv 32 := 0x00013903.
Lemma F_3df60 : fetch_word Asan.M.loaded_segments (0x3df60 : word) = Some W_3df60.
Proof. vm_refl. Qed.
Lemma D_3df60 : decode_any W_3df60 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df64 : bv 32 := 0x02010113.
Lemma F_3df64 : fetch_word Asan.M.loaded_segments (0x3df64 : word) = Some W_3df64.
Proof. vm_refl. Qed.
Lemma D_3df64 : decode_any W_3df64 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df68 : bv 32 := 0x00008067.
Lemma F_3df68 : fetch_word Asan.M.loaded_segments (0x3df68 : word) = Some W_3df68.
Proof. vm_refl. Qed.
Lemma D_3df68 : decode_any W_3df68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df6c : bv 32 := 0x00058913.
Lemma F_3df6c : fetch_word Asan.M.loaded_segments (0x3df6c : word) = Some W_3df6c.
Proof. vm_refl. Qed.
Lemma D_3df6c : decode_any W_3df6c = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df70 : bv 32 := 0x1e87f0ef.
Lemma F_3df70 : fetch_word Asan.M.loaded_segments (0x3df70 : word) = Some W_3df70.
Proof. vm_refl. Qed.
Lemma D_3df70 : decode_any W_3df70 = Some (Jal 1 520680, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df74 : bv 32 := 0x01600593.
Lemma F_3df74 : fetch_word Asan.M.loaded_segments (0x3df74 : word) = Some W_3df74.
Proof. vm_refl. Qed.
Lemma D_3df74 : decode_any W_3df74 = Some (OpImm ALU_ADD 11 0 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df78 : bv 32 := 0x00b52023.
Lemma F_3df78 : fetch_word Asan.M.loaded_segments (0x3df78 : word) = Some W_3df78.
Proof. vm_refl. Qed.
Lemma D_3df78 : decode_any W_3df78 = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df7c : bv 32 := 0x5f92d0ef.
Lemma F_3df7c : fetch_word Asan.M.loaded_segments (0x3df7c : word) = Some W_3df7c.
Proof. vm_refl. Qed.
Lemma D_3df7c : decode_any W_3df7c = Some (Jal 1 187896, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df80 : bv 32 := 0x02051063.
Lemma F_3df80 : fetch_word Asan.M.loaded_segments (0x3df80 : word) = Some W_3df80.
Proof. vm_refl. Qed.
Lemma D_3df80 : decode_any W_3df80 = Some (Branch BC_NE 10 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df84 : bv 32 := 0x00090513.
Lemma F_3df84 : fetch_word Asan.M.loaded_segments (0x3df84 : word) = Some W_3df84.
Proof. vm_refl. Qed.
Lemma D_3df84 : decode_any W_3df84 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df88 : bv 32 := 0x00048593.
Lemma F_3df88 : fetch_word Asan.M.loaded_segments (0x3df88 : word) = Some W_3df88.
Proof. vm_refl. Qed.
Lemma D_3df88 : decode_any W_3df88 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df8c : bv 32 := 0x00040613.
Lemma F_3df8c : fetch_word Asan.M.loaded_segments (0x3df8c : word) = Some W_3df8c.
Proof. vm_refl. Qed.
Lemma D_3df8c : decode_any W_3df8c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df90 : bv 32 := 0x7a5250ef.
Lemma F_3df90 : fetch_word Asan.M.loaded_segments (0x3df90 : word) = Some W_3df90.
Proof. vm_refl. Qed.
Lemma D_3df90 : decode_any W_3df90 = Some (Jal 1 155556, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df94 : bv 32 := 0x00090593.
Lemma F_3df94 : fetch_word Asan.M.loaded_segments (0x3df94 : word) = Some W_3df94.
Proof. vm_refl. Qed.
Lemma D_3df94 : decode_any W_3df94 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df98 : bv 32 := 0xf9dff06f.
Lemma F_3df98 : fetch_word Asan.M.loaded_segments (0x3df98 : word) = Some W_3df98.
Proof. vm_refl. Qed.
Lemma D_3df98 : decode_any W_3df98 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

Definition W_3df9c : bv 32 := 0x4a53b0ef.
Lemma F_3df9c : fetch_word Asan.M.loaded_segments (0x3df9c : word) = Some W_3df9c.
Proof. vm_refl. Qed.
Lemma D_3df9c : decode_any W_3df9c = Some (Jal 1 244900, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dfa0 : bv 32 := 0x00000513.
Lemma F_3dfa0 : fetch_word Asan.M.loaded_segments (0x3dfa0 : word) = Some W_3dfa0.
Proof. vm_refl. Qed.
Lemma D_3dfa0 : decode_any W_3dfa0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dfa4 : bv 32 := 0x01813083.
Lemma F_3dfa4 : fetch_word Asan.M.loaded_segments (0x3dfa4 : word) = Some W_3dfa4.
Proof. vm_refl. Qed.
Lemma D_3dfa4 : decode_any W_3dfa4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dfa8 : bv 32 := 0x01013403.
Lemma F_3dfa8 : fetch_word Asan.M.loaded_segments (0x3dfa8 : word) = Some W_3dfa8.
Proof. vm_refl. Qed.
Lemma D_3dfa8 : decode_any W_3dfa8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dfac : bv 32 := 0x00813483.
Lemma F_3dfac : fetch_word Asan.M.loaded_segments (0x3dfac : word) = Some W_3dfac.
Proof. vm_refl. Qed.
Lemma D_3dfac : decode_any W_3dfac = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dfb0 : bv 32 := 0x00013903.
Lemma F_3dfb0 : fetch_word Asan.M.loaded_segments (0x3dfb0 : word) = Some W_3dfb0.
Proof. vm_refl. Qed.
Lemma D_3dfb0 : decode_any W_3dfb0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dfb4 : bv 32 := 0x02010113.
Lemma F_3dfb4 : fetch_word Asan.M.loaded_segments (0x3dfb4 : word) = Some W_3dfb4.
Proof. vm_refl. Qed.
Lemma D_3dfb4 : decode_any W_3dfb4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3dfb8 : bv 32 := 0x00008067.
Lemma F_3dfb8 : fetch_word Asan.M.loaded_segments (0x3dfb8 : word) = Some W_3dfb8.
Proof. vm_refl. Qed.
Lemma D_3dfb8 : decode_any W_3dfb8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
