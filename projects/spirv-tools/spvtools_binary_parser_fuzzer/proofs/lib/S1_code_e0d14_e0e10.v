(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_e0d14 : bv 32 := 0x0ff5f593.
Lemma F_e0d14 : fetch_word Plain.M.loaded_segments (0xe0d48 : word) = Some W_e0d14.
Proof. vm_refl. Qed.
Lemma D_e0d14 : decode_any W_e0d14 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d18 : bv 32 := 0x00757693.
Lemma F_e0d18 : fetch_word Plain.M.loaded_segments (0xe0d4c : word) = Some W_e0d18.
Proof. vm_refl. Qed.
Lemma D_e0d18 : decode_any W_e0d18 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d1c : bv 32 := 0x00c03733.
Lemma F_e0d1c : fetch_word Plain.M.loaded_segments (0xe0d50 : word) = Some W_e0d1c.
Proof. vm_refl. Qed.
Lemma D_e0d1c : decode_any W_e0d1c = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d20 : bv 32 := 0x02068c63.
Lemma F_e0d20 : fetch_word Plain.M.loaded_segments (0xe0d54 : word) = Some W_e0d20.
Proof. vm_refl. Qed.
Lemma D_e0d20 : decode_any W_e0d20 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d24 : bv 32 := 0x02060a63.
Lemma F_e0d24 : fetch_word Plain.M.loaded_segments (0xe0d58 : word) = Some W_e0d24.
Proof. vm_refl. Qed.
Lemma D_e0d24 : decode_any W_e0d24 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d28 : bv 32 := 0x00150793.
Lemma F_e0d28 : fetch_word Plain.M.loaded_segments (0xe0d5c : word) = Some W_e0d28.
Proof. vm_refl. Qed.
Lemma D_e0d28 : decode_any W_e0d28 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d2c : bv 32 := 0x00100813.
Lemma F_e0d2c : fetch_word Plain.M.loaded_segments (0xe0d60 : word) = Some W_e0d2c.
Proof. vm_refl. Qed.
Lemma D_e0d2c : decode_any W_e0d2c = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d30 : bv 32 := 0x00054703.
Lemma F_e0d30 : fetch_word Plain.M.loaded_segments (0xe0d64 : word) = Some W_e0d30.
Proof. vm_refl. Qed.
Lemma D_e0d30 : decode_any W_e0d30 = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d34 : bv 32 := 0x00060693.
Lemma F_e0d34 : fetch_word Plain.M.loaded_segments (0xe0d68 : word) = Some W_e0d34.
Proof. vm_refl. Qed.
Lemma D_e0d34 : decode_any W_e0d34 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d38 : bv 32 := 0x06b70e63.
Lemma F_e0d38 : fetch_word Plain.M.loaded_segments (0xe0d6c : word) = Some W_e0d38.
Proof. vm_refl. Qed.
Lemma D_e0d38 : decode_any W_e0d38 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d3c : bv 32 := 0x00150513.
Lemma F_e0d3c : fetch_word Plain.M.loaded_segments (0xe0d70 : word) = Some W_e0d3c.
Proof. vm_refl. Qed.
Lemma D_e0d3c : decode_any W_e0d3c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d40 : bv 32 := 0xfff68613.
Lemma F_e0d40 : fetch_word Plain.M.loaded_segments (0xe0d74 : word) = Some W_e0d40.
Proof. vm_refl. Qed.
Lemma D_e0d40 : decode_any W_e0d40 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d44 : bv 32 := 0x0077f893.
Lemma F_e0d44 : fetch_word Plain.M.loaded_segments (0xe0d78 : word) = Some W_e0d44.
Proof. vm_refl. Qed.
Lemma D_e0d44 : decode_any W_e0d44 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d48 : bv 32 := 0x00c03733.
Lemma F_e0d48 : fetch_word Plain.M.loaded_segments (0xe0d7c : word) = Some W_e0d48.
Proof. vm_refl. Qed.
Lemma D_e0d48 : decode_any W_e0d48 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d4c : bv 32 := 0x00088663.
Lemma F_e0d4c : fetch_word Plain.M.loaded_segments (0xe0d80 : word) = Some W_e0d4c.
Proof. vm_refl. Qed.
Lemma D_e0d4c : decode_any W_e0d4c = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d50 : bv 32 := 0x00178793.
Lemma F_e0d50 : fetch_word Plain.M.loaded_segments (0xe0d84 : word) = Some W_e0d50.
Proof. vm_refl. Qed.
Lemma D_e0d50 : decode_any W_e0d50 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d54 : bv 32 := 0xfd069ee3.
Lemma F_e0d54 : fetch_word Plain.M.loaded_segments (0xe0d88 : word) = Some W_e0d54.
Proof. vm_refl. Qed.
Lemma D_e0d54 : decode_any W_e0d54 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d58 : bv 32 := 0x06070863.
Lemma F_e0d58 : fetch_word Plain.M.loaded_segments (0xe0d8c : word) = Some W_e0d58.
Proof. vm_refl. Qed.
Lemma D_e0d58 : decode_any W_e0d58 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d5c : bv 32 := 0x00054683.
Lemma F_e0d5c : fetch_word Plain.M.loaded_segments (0xe0d90 : word) = Some W_e0d5c.
Proof. vm_refl. Qed.
Lemma D_e0d5c : decode_any W_e0d5c = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d60 : bv 32 := 0x04b68663.
Lemma F_e0d60 : fetch_word Plain.M.loaded_segments (0xe0d94 : word) = Some W_e0d60.
Proof. vm_refl. Qed.
Lemma D_e0d60 : decode_any W_e0d60 = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d64 : bv 32 := 0x00800693.
Lemma F_e0d64 : fetch_word Plain.M.loaded_segments (0xe0d98 : word) = Some W_e0d64.
Proof. vm_refl. Qed.
Lemma D_e0d64 : decode_any W_e0d64 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d68 : bv 32 := 0x04d66263.
Lemma F_e0d68 : fetch_word Plain.M.loaded_segments (0xe0d9c : word) = Some W_e0d68.
Proof. vm_refl. Qed.
Lemma D_e0d68 : decode_any W_e0d68 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d6c : bv 32 := 0xfff34697.
Lemma F_e0d6c : fetch_word Plain.M.loaded_segments (0xe0da0 : word) = Some W_e0d6c.
Proof. vm_refl. Qed.
Lemma D_e0d6c : decode_any W_e0d6c = Some (Auipc 13 1048372, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d70 : bv 32 := 0xc306b683.
Lemma F_e0d70 : fetch_word Plain.M.loaded_segments (0xe0da4 : word) = Some W_e0d70.
Proof. vm_refl. Qed.
Lemma D_e0d70 : decode_any W_e0d70 = Some (Load SZ8 true 13 13 3120, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d74 : bv 32 := 0xfff34717.
Lemma F_e0d74 : fetch_word Plain.M.loaded_segments (0xe0da8 : word) = Some W_e0d74.
Proof. vm_refl. Qed.
Lemma D_e0d74 : decode_any W_e0d74 = Some (Auipc 14 1048372, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d78 : bv 32 := 0xc1873703.
Lemma F_e0d78 : fetch_word Plain.M.loaded_segments (0xe0dac : word) = Some W_e0d78.
Proof. vm_refl. Qed.
Lemma D_e0d78 : decode_any W_e0d78 = Some (Load SZ8 true 14 14 3096, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d7c : bv 32 := 0x00168793.
Lemma F_e0d7c : fetch_word Plain.M.loaded_segments (0xe0db0 : word) = Some W_e0d7c.
Proof. vm_refl. Qed.
Lemma D_e0d7c : decode_any W_e0d7c = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d80 : bv 32 := 0x02f587b3.
Lemma F_e0d80 : fetch_word Plain.M.loaded_segments (0xe0db4 : word) = Some W_e0d80.
Proof. vm_refl. Qed.
Lemma D_e0d80 : decode_any W_e0d80 = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d84 : bv 32 := 0x00700813.
Lemma F_e0d84 : fetch_word Plain.M.loaded_segments (0xe0db8 : word) = Some W_e0d84.
Proof. vm_refl. Qed.
Lemma D_e0d84 : decode_any W_e0d84 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d88 : bv 32 := 0x00053883.
Lemma F_e0d88 : fetch_word Plain.M.loaded_segments (0xe0dbc : word) = Some W_e0d88.
Proof. vm_refl. Qed.
Lemma D_e0d88 : decode_any W_e0d88 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d8c : bv 32 := 0x00f8c8b3.
Lemma F_e0d8c : fetch_word Plain.M.loaded_segments (0xe0dc0 : word) = Some W_e0d8c.
Proof. vm_refl. Qed.
Lemma D_e0d8c : decode_any W_e0d8c = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d90 : bv 32 := 0x411682b3.
Lemma F_e0d90 : fetch_word Plain.M.loaded_segments (0xe0dc4 : word) = Some W_e0d90.
Proof. vm_refl. Qed.
Lemma D_e0d90 : decode_any W_e0d90 = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d94 : bv 32 := 0x0112e8b3.
Lemma F_e0d94 : fetch_word Plain.M.loaded_segments (0xe0dc8 : word) = Some W_e0d94.
Proof. vm_refl. Qed.
Lemma D_e0d94 : decode_any W_e0d94 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d98 : bv 32 := 0x00e8f8b3.
Lemma F_e0d98 : fetch_word Plain.M.loaded_segments (0xe0dcc : word) = Some W_e0d98.
Proof. vm_refl. Qed.
Lemma D_e0d98 : decode_any W_e0d98 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0d9c : bv 32 := 0x02e89a63.
Lemma F_e0d9c : fetch_word Plain.M.loaded_segments (0xe0dd0 : word) = Some W_e0d9c.
Proof. vm_refl. Qed.
Lemma D_e0d9c : decode_any W_e0d9c = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0da0 : bv 32 := 0xff860613.
Lemma F_e0da0 : fetch_word Plain.M.loaded_segments (0xe0dd4 : word) = Some W_e0da0.
Proof. vm_refl. Qed.
Lemma D_e0da0 : decode_any W_e0da0 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0da4 : bv 32 := 0x00850513.
Lemma F_e0da4 : fetch_word Plain.M.loaded_segments (0xe0dd8 : word) = Some W_e0da4.
Proof. vm_refl. Qed.
Lemma D_e0da4 : decode_any W_e0da4 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0da8 : bv 32 := 0xfec860e3.
Lemma F_e0da8 : fetch_word Plain.M.loaded_segments (0xe0ddc : word) = Some W_e0da8.
Proof. vm_refl. Qed.
Lemma D_e0da8 : decode_any W_e0da8 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0dac : bv 32 := 0x00060693.
Lemma F_e0dac : fetch_word Plain.M.loaded_segments (0xe0de0 : word) = Some W_e0dac.
Proof. vm_refl. Qed.
Lemma D_e0dac : decode_any W_e0dac = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0db0 : bv 32 := 0x00060c63.
Lemma F_e0db0 : fetch_word Plain.M.loaded_segments (0xe0de4 : word) = Some W_e0db0.
Proof. vm_refl. Qed.
Lemma D_e0db0 : decode_any W_e0db0 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0db4 : bv 32 := 0x00054603.
Lemma F_e0db4 : fetch_word Plain.M.loaded_segments (0xe0de8 : word) = Some W_e0db4.
Proof. vm_refl. Qed.
Lemma D_e0db4 : decode_any W_e0db4 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0db8 : bv 32 := 0x00b60a63.
Lemma F_e0db8 : fetch_word Plain.M.loaded_segments (0xe0dec : word) = Some W_e0db8.
Proof. vm_refl. Qed.
Lemma D_e0db8 : decode_any W_e0db8 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0dbc : bv 32 := 0xfff68693.
Lemma F_e0dbc : fetch_word Plain.M.loaded_segments (0xe0df0 : word) = Some W_e0dbc.
Proof. vm_refl. Qed.
Lemma D_e0dbc : decode_any W_e0dbc = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0dc0 : bv 32 := 0x00150513.
Lemma F_e0dc0 : fetch_word Plain.M.loaded_segments (0xe0df4 : word) = Some W_e0dc0.
Proof. vm_refl. Qed.
Lemma D_e0dc0 : decode_any W_e0dc0 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0dc4 : bv 32 := 0xfe0698e3.
Lemma F_e0dc4 : fetch_word Plain.M.loaded_segments (0xe0df8 : word) = Some W_e0dc4.
Proof. vm_refl. Qed.
Lemma D_e0dc4 : decode_any W_e0dc4 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0dcc : bv 32 := 0x00008067.
Lemma F_e0dcc : fetch_word Plain.M.loaded_segments (0xe0e00 : word) = Some W_e0dcc.
Proof. vm_refl. Qed.
Lemma D_e0dcc : decode_any W_e0dcc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0dd0 : bv 32 := 0x00060693.
Lemma F_e0dd0 : fetch_word Plain.M.loaded_segments (0xe0e04 : word) = Some W_e0dd0.
Proof. vm_refl. Qed.
Lemma D_e0dd0 : decode_any W_e0dd0 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0dd4 : bv 32 := 0x00054603.
Lemma F_e0dd4 : fetch_word Plain.M.loaded_segments (0xe0e08 : word) = Some W_e0dd4.
Proof. vm_refl. Qed.
Lemma D_e0dd4 : decode_any W_e0dd4 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0dd8 : bv 32 := 0xfeb612e3.
Lemma F_e0dd8 : fetch_word Plain.M.loaded_segments (0xe0e0c : word) = Some W_e0dd8.
Proof. vm_refl. Qed.
Lemma D_e0dd8 : decode_any W_e0dd8 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0ddc : bv 32 := 0xff1ff06f.
Lemma F_e0ddc : fetch_word Plain.M.loaded_segments (0xe0e10 : word) = Some W_e0ddc.
Proof. vm_refl. Qed.
Lemma D_e0ddc : decode_any W_e0ddc = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.
