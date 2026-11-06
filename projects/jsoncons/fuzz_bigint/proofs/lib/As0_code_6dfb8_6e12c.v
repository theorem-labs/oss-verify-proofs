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

Definition W_6dfb8 : bv 32 := 0xfe010113.
Lemma F_6dfb8 : fetch_word Asan.M.loaded_segments (0x6dfb8 : word) = Some W_6dfb8.
Proof. vm_refl. Qed.
Lemma D_6dfb8 : decode_any W_6dfb8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfbc : bv 32 := 0x00113c23.
Lemma F_6dfbc : fetch_word Asan.M.loaded_segments (0x6dfbc : word) = Some W_6dfbc.
Proof. vm_refl. Qed.
Lemma D_6dfbc : decode_any W_6dfbc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfc0 : bv 32 := 0x00813823.
Lemma F_6dfc0 : fetch_word Asan.M.loaded_segments (0x6dfc0 : word) = Some W_6dfc0.
Proof. vm_refl. Qed.
Lemma D_6dfc0 : decode_any W_6dfc0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfc4 : bv 32 := 0x00913423.
Lemma F_6dfc4 : fetch_word Asan.M.loaded_segments (0x6dfc4 : word) = Some W_6dfc4.
Proof. vm_refl. Qed.
Lemma D_6dfc4 : decode_any W_6dfc4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfc8 : bv 32 := 0x01213023.
Lemma F_6dfc8 : fetch_word Asan.M.loaded_segments (0x6dfc8 : word) = Some W_6dfc8.
Proof. vm_refl. Qed.
Lemma D_6dfc8 : decode_any W_6dfc8 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfcc : bv 32 := 0x00058413.
Lemma F_6dfcc : fetch_word Asan.M.loaded_segments (0x6dfcc : word) = Some W_6dfcc.
Proof. vm_refl. Qed.
Lemma D_6dfcc : decode_any W_6dfcc = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfd0 : bv 32 := 0x00050493.
Lemma F_6dfd0 : fetch_word Asan.M.loaded_segments (0x6dfd0 : word) = Some W_6dfd0.
Proof. vm_refl. Qed.
Lemma D_6dfd0 : decode_any W_6dfd0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfd4 : bv 32 := 0x09c000ef.
Lemma F_6dfd4 : fetch_word Asan.M.loaded_segments (0x6dfd4 : word) = Some W_6dfd4.
Proof. vm_refl. Qed.
Lemma D_6dfd4 : decode_any W_6dfd4 = Some (Jal 1 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfd8 : bv 32 := 0x00101517.
Lemma F_6dfd8 : fetch_word Asan.M.loaded_segments (0x6dfd8 : word) = Some W_6dfd8.
Proof. vm_refl. Qed.
Lemma D_6dfd8 : decode_any W_6dfd8 = Some (Auipc 10 257, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfdc : bv 32 := 0x62850913.
Lemma F_6dfdc : fetch_word Asan.M.loaded_segments (0x6dfdc : word) = Some W_6dfdc.
Proof. vm_refl. Qed.
Lemma D_6dfdc : decode_any W_6dfdc = Some (OpImm ALU_ADD 18 10 1576, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfe0 : bv 32 := 0x00093603.
Lemma F_6dfe0 : fetch_word Asan.M.loaded_segments (0x6dfe0 : word) = Some W_6dfe0.
Proof. vm_refl. Qed.
Lemma D_6dfe0 : decode_any W_6dfe0 = Some (Load SZ8 true 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfe4 : bv 32 := 0x06060a63.
Lemma F_6dfe4 : fetch_word Asan.M.loaded_segments (0x6dfe4 : word) = Some W_6dfe4.
Proof. vm_refl. Qed.
Lemma D_6dfe4 : decode_any W_6dfe4 = Some (Branch BC_EQ 12 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfe8 : bv 32 := 0x00048513.
Lemma F_6dfe8 : fetch_word Asan.M.loaded_segments (0x6dfe8 : word) = Some W_6dfe8.
Proof. vm_refl. Qed.
Lemma D_6dfe8 : decode_any W_6dfe8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dfec : bv 32 := 0x00040593.
Lemma F_6dfec : fetch_word Asan.M.loaded_segments (0x6dfec : word) = Some W_6dfec.
Proof. vm_refl. Qed.
Lemma D_6dfec : decode_any W_6dfec = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dff0 : bv 32 := 0x000600e7.
Lemma F_6dff0 : fetch_word Asan.M.loaded_segments (0x6dff0 : word) = Some W_6dff0.
Proof. vm_refl. Qed.
Lemma D_6dff0 : decode_any W_6dff0 = Some (Jalr 1 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dff4 : bv 32 := 0x01093603.
Lemma F_6dff4 : fetch_word Asan.M.loaded_segments (0x6dff4 : word) = Some W_6dff4.
Proof. vm_refl. Qed.
Lemma D_6dff4 : decode_any W_6dff4 = Some (Load SZ8 true 12 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dff8 : bv 32 := 0x06060063.
Lemma F_6dff8 : fetch_word Asan.M.loaded_segments (0x6dff8 : word) = Some W_6dff8.
Proof. vm_refl. Qed.
Lemma D_6dff8 : decode_any W_6dff8 = Some (Branch BC_EQ 12 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_6dffc : bv 32 := 0x00048513.
Lemma F_6dffc : fetch_word Asan.M.loaded_segments (0x6dffc : word) = Some W_6dffc.
Proof. vm_refl. Qed.
Lemma D_6dffc : decode_any W_6dffc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e000 : bv 32 := 0x00040593.
Lemma F_6e000 : fetch_word Asan.M.loaded_segments (0x6e000 : word) = Some W_6e000.
Proof. vm_refl. Qed.
Lemma D_6e000 : decode_any W_6e000 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e004 : bv 32 := 0x000600e7.
Lemma F_6e004 : fetch_word Asan.M.loaded_segments (0x6e004 : word) = Some W_6e004.
Proof. vm_refl. Qed.
Lemma D_6e004 : decode_any W_6e004 = Some (Jalr 1 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e008 : bv 32 := 0x02093603.
Lemma F_6e008 : fetch_word Asan.M.loaded_segments (0x6e008 : word) = Some W_6e008.
Proof. vm_refl. Qed.
Lemma D_6e008 : decode_any W_6e008 = Some (Load SZ8 true 12 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e00c : bv 32 := 0x04060663.
Lemma F_6e00c : fetch_word Asan.M.loaded_segments (0x6e00c : word) = Some W_6e00c.
Proof. vm_refl. Qed.
Lemma D_6e00c : decode_any W_6e00c = Some (Branch BC_EQ 12 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e010 : bv 32 := 0x00048513.
Lemma F_6e010 : fetch_word Asan.M.loaded_segments (0x6e010 : word) = Some W_6e010.
Proof. vm_refl. Qed.
Lemma D_6e010 : decode_any W_6e010 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e014 : bv 32 := 0x00040593.
Lemma F_6e014 : fetch_word Asan.M.loaded_segments (0x6e014 : word) = Some W_6e014.
Proof. vm_refl. Qed.
Lemma D_6e014 : decode_any W_6e014 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e018 : bv 32 := 0x000600e7.
Lemma F_6e018 : fetch_word Asan.M.loaded_segments (0x6e018 : word) = Some W_6e018.
Proof. vm_refl. Qed.
Lemma D_6e018 : decode_any W_6e018 = Some (Jalr 1 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e01c : bv 32 := 0x03093603.
Lemma F_6e01c : fetch_word Asan.M.loaded_segments (0x6e01c : word) = Some W_6e01c.
Proof. vm_refl. Qed.
Lemma D_6e01c : decode_any W_6e01c = Some (Load SZ8 true 12 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e020 : bv 32 := 0x02060c63.
Lemma F_6e020 : fetch_word Asan.M.loaded_segments (0x6e020 : word) = Some W_6e020.
Proof. vm_refl. Qed.
Lemma D_6e020 : decode_any W_6e020 = Some (Branch BC_EQ 12 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e024 : bv 32 := 0x00048513.
Lemma F_6e024 : fetch_word Asan.M.loaded_segments (0x6e024 : word) = Some W_6e024.
Proof. vm_refl. Qed.
Lemma D_6e024 : decode_any W_6e024 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e028 : bv 32 := 0x00040593.
Lemma F_6e028 : fetch_word Asan.M.loaded_segments (0x6e028 : word) = Some W_6e028.
Proof. vm_refl. Qed.
Lemma D_6e028 : decode_any W_6e028 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e02c : bv 32 := 0x000600e7.
Lemma F_6e02c : fetch_word Asan.M.loaded_segments (0x6e02c : word) = Some W_6e02c.
Proof. vm_refl. Qed.
Lemma D_6e02c : decode_any W_6e02c = Some (Jalr 1 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e030 : bv 32 := 0x04093303.
Lemma F_6e030 : fetch_word Asan.M.loaded_segments (0x6e030 : word) = Some W_6e030.
Proof. vm_refl. Qed.
Lemma D_6e030 : decode_any W_6e030 = Some (Load SZ8 true 6 18 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e034 : bv 32 := 0x02030263.
Lemma F_6e034 : fetch_word Asan.M.loaded_segments (0x6e034 : word) = Some W_6e034.
Proof. vm_refl. Qed.
Lemma D_6e034 : decode_any W_6e034 = Some (Branch BC_EQ 6 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e038 : bv 32 := 0x00048513.
Lemma F_6e038 : fetch_word Asan.M.loaded_segments (0x6e038 : word) = Some W_6e038.
Proof. vm_refl. Qed.
Lemma D_6e038 : decode_any W_6e038 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e03c : bv 32 := 0x00040593.
Lemma F_6e03c : fetch_word Asan.M.loaded_segments (0x6e03c : word) = Some W_6e03c.
Proof. vm_refl. Qed.
Lemma D_6e03c : decode_any W_6e03c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e040 : bv 32 := 0x01813083.
Lemma F_6e040 : fetch_word Asan.M.loaded_segments (0x6e040 : word) = Some W_6e040.
Proof. vm_refl. Qed.
Lemma D_6e040 : decode_any W_6e040 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e044 : bv 32 := 0x01013403.
Lemma F_6e044 : fetch_word Asan.M.loaded_segments (0x6e044 : word) = Some W_6e044.
Proof. vm_refl. Qed.
Lemma D_6e044 : decode_any W_6e044 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e048 : bv 32 := 0x00813483.
Lemma F_6e048 : fetch_word Asan.M.loaded_segments (0x6e048 : word) = Some W_6e048.
Proof. vm_refl. Qed.
Lemma D_6e048 : decode_any W_6e048 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e04c : bv 32 := 0x00013903.
Lemma F_6e04c : fetch_word Asan.M.loaded_segments (0x6e04c : word) = Some W_6e04c.
Proof. vm_refl. Qed.
Lemma D_6e04c : decode_any W_6e04c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e050 : bv 32 := 0x02010113.
Lemma F_6e050 : fetch_word Asan.M.loaded_segments (0x6e050 : word) = Some W_6e050.
Proof. vm_refl. Qed.
Lemma D_6e050 : decode_any W_6e050 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e054 : bv 32 := 0x00030067.
Lemma F_6e054 : fetch_word Asan.M.loaded_segments (0x6e054 : word) = Some W_6e054.
Proof. vm_refl. Qed.
Lemma D_6e054 : decode_any W_6e054 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e058 : bv 32 := 0x01813083.
Lemma F_6e058 : fetch_word Asan.M.loaded_segments (0x6e058 : word) = Some W_6e058.
Proof. vm_refl. Qed.
Lemma D_6e058 : decode_any W_6e058 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e05c : bv 32 := 0x01013403.
Lemma F_6e05c : fetch_word Asan.M.loaded_segments (0x6e05c : word) = Some W_6e05c.
Proof. vm_refl. Qed.
Lemma D_6e05c : decode_any W_6e05c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e060 : bv 32 := 0x00813483.
Lemma F_6e060 : fetch_word Asan.M.loaded_segments (0x6e060 : word) = Some W_6e060.
Proof. vm_refl. Qed.
Lemma D_6e060 : decode_any W_6e060 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e064 : bv 32 := 0x00013903.
Lemma F_6e064 : fetch_word Asan.M.loaded_segments (0x6e064 : word) = Some W_6e064.
Proof. vm_refl. Qed.
Lemma D_6e064 : decode_any W_6e064 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e068 : bv 32 := 0x02010113.
Lemma F_6e068 : fetch_word Asan.M.loaded_segments (0x6e068 : word) = Some W_6e068.
Proof. vm_refl. Qed.
Lemma D_6e068 : decode_any W_6e068 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e06c : bv 32 := 0x00008067.
Lemma F_6e06c : fetch_word Asan.M.loaded_segments (0x6e06c : word) = Some W_6e06c.
Proof. vm_refl. Qed.
Lemma D_6e06c : decode_any W_6e06c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e070 : bv 32 := 0x00008067.
Lemma F_6e070 : fetch_word Asan.M.loaded_segments (0x6e070 : word) = Some W_6e070.
Proof. vm_refl. Qed.
Lemma D_6e070 : decode_any W_6e070 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e074 : bv 32 := 0xfe010113.
Lemma F_6e074 : fetch_word Asan.M.loaded_segments (0x6e074 : word) = Some W_6e074.
Proof. vm_refl. Qed.
Lemma D_6e074 : decode_any W_6e074 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e078 : bv 32 := 0x00113c23.
Lemma F_6e078 : fetch_word Asan.M.loaded_segments (0x6e078 : word) = Some W_6e078.
Proof. vm_refl. Qed.
Lemma D_6e078 : decode_any W_6e078 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e07c : bv 32 := 0x00813823.
Lemma F_6e07c : fetch_word Asan.M.loaded_segments (0x6e07c : word) = Some W_6e07c.
Proof. vm_refl. Qed.
Lemma D_6e07c : decode_any W_6e07c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e080 : bv 32 := 0x00913423.
Lemma F_6e080 : fetch_word Asan.M.loaded_segments (0x6e080 : word) = Some W_6e080.
Proof. vm_refl. Qed.
Lemma D_6e080 : decode_any W_6e080 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e084 : bv 32 := 0x00050413.
Lemma F_6e084 : fetch_word Asan.M.loaded_segments (0x6e084 : word) = Some W_6e084.
Proof. vm_refl. Qed.
Lemma D_6e084 : decode_any W_6e084 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e088 : bv 32 := 0x098000ef.
Lemma F_6e088 : fetch_word Asan.M.loaded_segments (0x6e088 : word) = Some W_6e088.
Proof. vm_refl. Qed.
Lemma D_6e088 : decode_any W_6e088 = Some (Jal 1 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e08c : bv 32 := 0x00050e63.
Lemma F_6e08c : fetch_word Asan.M.loaded_segments (0x6e08c : word) = Some W_6e08c.
Proof. vm_refl. Qed.
Lemma D_6e08c : decode_any W_6e08c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e090 : bv 32 := 0x00100513.
Lemma F_6e090 : fetch_word Asan.M.loaded_segments (0x6e090 : word) = Some W_6e090.
Proof. vm_refl. Qed.
Lemma D_6e090 : decode_any W_6e090 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e094 : bv 32 := 0x01813083.
Lemma F_6e094 : fetch_word Asan.M.loaded_segments (0x6e094 : word) = Some W_6e094.
Proof. vm_refl. Qed.
Lemma D_6e094 : decode_any W_6e094 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e098 : bv 32 := 0x01013403.
Lemma F_6e098 : fetch_word Asan.M.loaded_segments (0x6e098 : word) = Some W_6e098.
Proof. vm_refl. Qed.
Lemma D_6e098 : decode_any W_6e098 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e09c : bv 32 := 0x00813483.
Lemma F_6e09c : fetch_word Asan.M.loaded_segments (0x6e09c : word) = Some W_6e09c.
Proof. vm_refl. Qed.
Lemma D_6e09c : decode_any W_6e09c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0a0 : bv 32 := 0x02010113.
Lemma F_6e0a0 : fetch_word Asan.M.loaded_segments (0x6e0a0 : word) = Some W_6e0a0.
Proof. vm_refl. Qed.
Lemma D_6e0a0 : decode_any W_6e0a0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0a4 : bv 32 := 0x00008067.
Lemma F_6e0a4 : fetch_word Asan.M.loaded_segments (0x6e0a4 : word) = Some W_6e0a4.
Proof. vm_refl. Qed.
Lemma D_6e0a4 : decode_any W_6e0a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0a8 : bv 32 := 0x00040513.
Lemma F_6e0a8 : fetch_word Asan.M.loaded_segments (0x6e0a8 : word) = Some W_6e0a8.
Proof. vm_refl. Qed.
Lemma D_6e0a8 : decode_any W_6e0a8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0ac : bv 32 := 0x07c000ef.
Lemma F_6e0ac : fetch_word Asan.M.loaded_segments (0x6e0ac : word) = Some W_6e0ac.
Proof. vm_refl. Qed.
Lemma D_6e0ac : decode_any W_6e0ac = Some (Jal 1 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0b0 : bv 32 := 0x00101517.
Lemma F_6e0b0 : fetch_word Asan.M.loaded_segments (0x6e0b0 : word) = Some W_6e0b0.
Proof. vm_refl. Qed.
Lemma D_6e0b0 : decode_any W_6e0b0 = Some (Auipc 10 257, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0b4 : bv 32 := 0x55050493.
Lemma F_6e0b4 : fetch_word Asan.M.loaded_segments (0x6e0b4 : word) = Some W_6e0b4.
Proof. vm_refl. Qed.
Lemma D_6e0b4 : decode_any W_6e0b4 = Some (OpImm ALU_ADD 9 10 1360, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0b8 : bv 32 := 0x0084b583.
Lemma F_6e0b8 : fetch_word Asan.M.loaded_segments (0x6e0b8 : word) = Some W_6e0b8.
Proof. vm_refl. Qed.
Lemma D_6e0b8 : decode_any W_6e0b8 = Some (Load SZ8 true 11 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0bc : bv 32 := 0x04058663.
Lemma F_6e0bc : fetch_word Asan.M.loaded_segments (0x6e0bc : word) = Some W_6e0bc.
Proof. vm_refl. Qed.
Lemma D_6e0bc : decode_any W_6e0bc = Some (Branch BC_EQ 11 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0c0 : bv 32 := 0x00040513.
Lemma F_6e0c0 : fetch_word Asan.M.loaded_segments (0x6e0c0 : word) = Some W_6e0c0.
Proof. vm_refl. Qed.
Lemma D_6e0c0 : decode_any W_6e0c0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0c4 : bv 32 := 0x000580e7.
Lemma F_6e0c4 : fetch_word Asan.M.loaded_segments (0x6e0c4 : word) = Some W_6e0c4.
Proof. vm_refl. Qed.
Lemma D_6e0c4 : decode_any W_6e0c4 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0c8 : bv 32 := 0x0184b583.
Lemma F_6e0c8 : fetch_word Asan.M.loaded_segments (0x6e0c8 : word) = Some W_6e0c8.
Proof. vm_refl. Qed.
Lemma D_6e0c8 : decode_any W_6e0c8 = Some (Load SZ8 true 11 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0cc : bv 32 := 0x02058e63.
Lemma F_6e0cc : fetch_word Asan.M.loaded_segments (0x6e0cc : word) = Some W_6e0cc.
Proof. vm_refl. Qed.
Lemma D_6e0cc : decode_any W_6e0cc = Some (Branch BC_EQ 11 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0d0 : bv 32 := 0x00040513.
Lemma F_6e0d0 : fetch_word Asan.M.loaded_segments (0x6e0d0 : word) = Some W_6e0d0.
Proof. vm_refl. Qed.
Lemma D_6e0d0 : decode_any W_6e0d0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0d4 : bv 32 := 0x000580e7.
Lemma F_6e0d4 : fetch_word Asan.M.loaded_segments (0x6e0d4 : word) = Some W_6e0d4.
Proof. vm_refl. Qed.
Lemma D_6e0d4 : decode_any W_6e0d4 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0d8 : bv 32 := 0x0284b583.
Lemma F_6e0d8 : fetch_word Asan.M.loaded_segments (0x6e0d8 : word) = Some W_6e0d8.
Proof. vm_refl. Qed.
Lemma D_6e0d8 : decode_any W_6e0d8 = Some (Load SZ8 true 11 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0dc : bv 32 := 0x02058663.
Lemma F_6e0dc : fetch_word Asan.M.loaded_segments (0x6e0dc : word) = Some W_6e0dc.
Proof. vm_refl. Qed.
Lemma D_6e0dc : decode_any W_6e0dc = Some (Branch BC_EQ 11 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0e0 : bv 32 := 0x00040513.
Lemma F_6e0e0 : fetch_word Asan.M.loaded_segments (0x6e0e0 : word) = Some W_6e0e0.
Proof. vm_refl. Qed.
Lemma D_6e0e0 : decode_any W_6e0e0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0e4 : bv 32 := 0x000580e7.
Lemma F_6e0e4 : fetch_word Asan.M.loaded_segments (0x6e0e4 : word) = Some W_6e0e4.
Proof. vm_refl. Qed.
Lemma D_6e0e4 : decode_any W_6e0e4 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0e8 : bv 32 := 0x0384b583.
Lemma F_6e0e8 : fetch_word Asan.M.loaded_segments (0x6e0e8 : word) = Some W_6e0e8.
Proof. vm_refl. Qed.
Lemma D_6e0e8 : decode_any W_6e0e8 = Some (Load SZ8 true 11 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0ec : bv 32 := 0x00058e63.
Lemma F_6e0ec : fetch_word Asan.M.loaded_segments (0x6e0ec : word) = Some W_6e0ec.
Proof. vm_refl. Qed.
Lemma D_6e0ec : decode_any W_6e0ec = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0f0 : bv 32 := 0x00040513.
Lemma F_6e0f0 : fetch_word Asan.M.loaded_segments (0x6e0f0 : word) = Some W_6e0f0.
Proof. vm_refl. Qed.
Lemma D_6e0f0 : decode_any W_6e0f0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0f4 : bv 32 := 0x000580e7.
Lemma F_6e0f4 : fetch_word Asan.M.loaded_segments (0x6e0f4 : word) = Some W_6e0f4.
Proof. vm_refl. Qed.
Lemma D_6e0f4 : decode_any W_6e0f4 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0f8 : bv 32 := 0x0484b583.
Lemma F_6e0f8 : fetch_word Asan.M.loaded_segments (0x6e0f8 : word) = Some W_6e0f8.
Proof. vm_refl. Qed.
Lemma D_6e0f8 : decode_any W_6e0f8 = Some (Load SZ8 true 11 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e0fc : bv 32 := 0x00058663.
Lemma F_6e0fc : fetch_word Asan.M.loaded_segments (0x6e0fc : word) = Some W_6e0fc.
Proof. vm_refl. Qed.
Lemma D_6e0fc : decode_any W_6e0fc = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e100 : bv 32 := 0x00040513.
Lemma F_6e100 : fetch_word Asan.M.loaded_segments (0x6e100 : word) = Some W_6e100.
Proof. vm_refl. Qed.
Lemma D_6e100 : decode_any W_6e100 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e104 : bv 32 := 0x000580e7.
Lemma F_6e104 : fetch_word Asan.M.loaded_segments (0x6e104 : word) = Some W_6e104.
Proof. vm_refl. Qed.
Lemma D_6e104 : decode_any W_6e104 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e108 : bv 32 := 0x00000513.
Lemma F_6e108 : fetch_word Asan.M.loaded_segments (0x6e108 : word) = Some W_6e108.
Proof. vm_refl. Qed.
Lemma D_6e108 : decode_any W_6e108 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e10c : bv 32 := 0x01813083.
Lemma F_6e10c : fetch_word Asan.M.loaded_segments (0x6e10c : word) = Some W_6e10c.
Proof. vm_refl. Qed.
Lemma D_6e10c : decode_any W_6e10c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e110 : bv 32 := 0x01013403.
Lemma F_6e110 : fetch_word Asan.M.loaded_segments (0x6e110 : word) = Some W_6e110.
Proof. vm_refl. Qed.
Lemma D_6e110 : decode_any W_6e110 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e114 : bv 32 := 0x00813483.
Lemma F_6e114 : fetch_word Asan.M.loaded_segments (0x6e114 : word) = Some W_6e114.
Proof. vm_refl. Qed.
Lemma D_6e114 : decode_any W_6e114 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e118 : bv 32 := 0x02010113.
Lemma F_6e118 : fetch_word Asan.M.loaded_segments (0x6e118 : word) = Some W_6e118.
Proof. vm_refl. Qed.
Lemma D_6e118 : decode_any W_6e118 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e11c : bv 32 := 0x00008067.
Lemma F_6e11c : fetch_word Asan.M.loaded_segments (0x6e11c : word) = Some W_6e11c.
Proof. vm_refl. Qed.
Lemma D_6e11c : decode_any W_6e11c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e120 : bv 32 := 0x00000513.
Lemma F_6e120 : fetch_word Asan.M.loaded_segments (0x6e120 : word) = Some W_6e120.
Proof. vm_refl. Qed.
Lemma D_6e120 : decode_any W_6e120 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e124 : bv 32 := 0x00008067.
Lemma F_6e124 : fetch_word Asan.M.loaded_segments (0x6e124 : word) = Some W_6e124.
Proof. vm_refl. Qed.
Lemma D_6e124 : decode_any W_6e124 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6e128 : bv 32 := 0x00008067.
Lemma F_6e128 : fetch_word Asan.M.loaded_segments (0x6e128 : word) = Some W_6e128.
Proof. vm_refl. Qed.
Lemma D_6e128 : decode_any W_6e128 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
