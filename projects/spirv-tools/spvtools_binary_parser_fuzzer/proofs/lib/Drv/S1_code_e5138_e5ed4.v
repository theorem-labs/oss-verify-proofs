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

Definition W_e5288 : bv 32 := 0x00e13423.

Definition W_e528c : bv 32 := 0x0015c683.

Definition W_e5290 : bv 32 := 0xfd068793.

Definition W_e5d08 : bv 32 := 0xff010113.

Definition W_e5d0c : bv 32 := 0x00113423.

Definition W_e5d10 : bv 32 := 0x8c0ea0ef.

Definition W_e5d14 : bv 32 := 0xff010113.
Lemma F_e5d14 : fetch_word Plain.M.loaded_segments (0xe5d48 : word) = Some W_e5d14.
Proof. vm_refl. Qed.
Lemma D_e5d14 : decode_any W_e5d14 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d18 : bv 32 := 0x00113423.
Lemma F_e5d18 : fetch_word Plain.M.loaded_segments (0xe5d4c : word) = Some W_e5d18.
Proof. vm_refl. Qed.
Lemma D_e5d18 : decode_any W_e5d18 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d1c : bv 32 := 0xfc4ef0ef.
Lemma F_e5d1c : fetch_word Plain.M.loaded_segments (0xe5d50 : word) = Some W_e5d1c.
Proof. vm_refl. Qed.
Lemma D_e5d1c : decode_any W_e5d1c = Some (Jal 1 2029508, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d20 : bv 32 := 0x00050593.
Lemma F_e5d20 : fetch_word Plain.M.loaded_segments (0xe5d54 : word) = Some W_e5d20.
Proof. vm_refl. Qed.
Lemma D_e5d20 : decode_any W_e5d20 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d24 : bv 32 := 0x03900513.
Lemma F_e5d24 : fetch_word Plain.M.loaded_segments (0xe5d58 : word) = Some W_e5d24.
Proof. vm_refl. Qed.
Lemma D_e5d24 : decode_any W_e5d24 = Some (OpImm ALU_ADD 10 0 57, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d28 : bv 32 := 0x00000613.
Lemma F_e5d28 : fetch_word Plain.M.loaded_segments (0xe5d5c : word) = Some W_e5d28.
Proof. vm_refl. Qed.
Lemma D_e5d28 : decode_any W_e5d28 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d2c : bv 32 := 0x00000693.
Lemma F_e5d2c : fetch_word Plain.M.loaded_segments (0xe5d60 : word) = Some W_e5d2c.
Proof. vm_refl. Qed.
Lemma D_e5d2c : decode_any W_e5d2c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d30 : bv 32 := 0x00000713.
Lemma F_e5d30 : fetch_word Plain.M.loaded_segments (0xe5d64 : word) = Some W_e5d30.
Proof. vm_refl. Qed.
Lemma D_e5d30 : decode_any W_e5d30 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d34 : bv 32 := 0x00000793.
Lemma F_e5d34 : fetch_word Plain.M.loaded_segments (0xe5d68 : word) = Some W_e5d34.
Proof. vm_refl. Qed.
Lemma D_e5d34 : decode_any W_e5d34 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d38 : bv 32 := 0x00000813.
Lemma F_e5d38 : fetch_word Plain.M.loaded_segments (0xe5d6c : word) = Some W_e5d38.
Proof. vm_refl. Qed.
Lemma D_e5d38 : decode_any W_e5d38 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d3c : bv 32 := 0x8e4fc0ef.
Lemma F_e5d3c : fetch_word Plain.M.loaded_segments (0xe5d70 : word) = Some W_e5d3c.
Proof. vm_refl. Qed.
Lemma D_e5d3c : decode_any W_e5d3c = Some (Jal 1 2080996, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d40 : bv 32 := 0x0005051b.
Lemma F_e5d40 : fetch_word Plain.M.loaded_segments (0xe5d74 : word) = Some W_e5d40.
Proof. vm_refl. Qed.
Lemma D_e5d40 : decode_any W_e5d40 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d44 : bv 32 := 0x00450593.
Lemma F_e5d44 : fetch_word Plain.M.loaded_segments (0xe5d78 : word) = Some W_e5d44.
Proof. vm_refl. Qed.
Lemma D_e5d44 : decode_any W_e5d44 = Some (OpImm ALU_ADD 11 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d48 : bv 32 := 0x0015b593.
Lemma F_e5d48 : fetch_word Plain.M.loaded_segments (0xe5d7c : word) = Some W_e5d48.
Proof. vm_refl. Qed.
Lemma D_e5d48 : decode_any W_e5d48 = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d4c : bv 32 := 0xfff58593.
Lemma F_e5d4c : fetch_word Plain.M.loaded_segments (0xe5d80 : word) = Some W_e5d4c.
Proof. vm_refl. Qed.
Lemma D_e5d4c : decode_any W_e5d4c = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d50 : bv 32 := 0x00a5f533.
Lemma F_e5d50 : fetch_word Plain.M.loaded_segments (0xe5d84 : word) = Some W_e5d50.
Proof. vm_refl. Qed.
Lemma D_e5d50 : decode_any W_e5d50 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d54 : bv 32 := 0xd34ea0ef.
Lemma F_e5d54 : fetch_word Plain.M.loaded_segments (0xe5d88 : word) = Some W_e5d54.
Proof. vm_refl. Qed.
Lemma D_e5d54 : decode_any W_e5d54 = Some (Jal 1 2008372, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d58 : bv 32 := 0x0005051b.
Lemma F_e5d58 : fetch_word Plain.M.loaded_segments (0xe5d8c : word) = Some W_e5d58.
Proof. vm_refl. Qed.
Lemma D_e5d58 : decode_any W_e5d58 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d5c : bv 32 := 0x00813083.
Lemma F_e5d5c : fetch_word Plain.M.loaded_segments (0xe5d90 : word) = Some W_e5d5c.
Proof. vm_refl. Qed.
Lemma D_e5d5c : decode_any W_e5d5c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d60 : bv 32 := 0x01010113.
Lemma F_e5d60 : fetch_word Plain.M.loaded_segments (0xe5d94 : word) = Some W_e5d60.
Proof. vm_refl. Qed.
Lemma D_e5d60 : decode_any W_e5d60 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d64 : bv 32 := 0x00008067.
Lemma F_e5d64 : fetch_word Plain.M.loaded_segments (0xe5d98 : word) = Some W_e5d64.
Proof. vm_refl. Qed.
Lemma D_e5d64 : decode_any W_e5d64 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d74 : bv 32 := 0xff010113.
Lemma F_e5d74 : fetch_word Plain.M.loaded_segments (0xe5da8 : word) = Some W_e5d74.
Proof. vm_refl. Qed.
Lemma D_e5d74 : decode_any W_e5d74 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d78 : bv 32 := 0x00113423.
Lemma F_e5d78 : fetch_word Plain.M.loaded_segments (0xe5dac : word) = Some W_e5d78.
Proof. vm_refl. Qed.
Lemma D_e5d78 : decode_any W_e5d78 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d7c : bv 32 := 0x00060693.
Lemma F_e5d7c : fetch_word Plain.M.loaded_segments (0xe5db0 : word) = Some W_e5d7c.
Proof. vm_refl. Qed.
Lemma D_e5d7c : decode_any W_e5d7c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d80 : bv 32 := 0x00058613.
Lemma F_e5d80 : fetch_word Plain.M.loaded_segments (0xe5db4 : word) = Some W_e5d80.
Proof. vm_refl. Qed.
Lemma D_e5d80 : decode_any W_e5d80 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d84 : bv 32 := 0x00050593.
Lemma F_e5d84 : fetch_word Plain.M.loaded_segments (0xe5db8 : word) = Some W_e5d84.
Proof. vm_refl. Qed.
Lemma D_e5d84 : decode_any W_e5d84 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d88 : bv 32 := 0x03f00513.
Lemma F_e5d88 : fetch_word Plain.M.loaded_segments (0xe5dbc : word) = Some W_e5d88.
Proof. vm_refl. Qed.
Lemma D_e5d88 : decode_any W_e5d88 = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d8c : bv 32 := 0x00000713.
Lemma F_e5d8c : fetch_word Plain.M.loaded_segments (0xe5dc0 : word) = Some W_e5d8c.
Proof. vm_refl. Qed.
Lemma D_e5d8c : decode_any W_e5d8c = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d90 : bv 32 := 0x00000793.
Lemma F_e5d90 : fetch_word Plain.M.loaded_segments (0xe5dc4 : word) = Some W_e5d90.
Proof. vm_refl. Qed.
Lemma D_e5d90 : decode_any W_e5d90 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d94 : bv 32 := 0x00000813.
Lemma F_e5d94 : fetch_word Plain.M.loaded_segments (0xe5dc8 : word) = Some W_e5d94.
Proof. vm_refl. Qed.
Lemma D_e5d94 : decode_any W_e5d94 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d98 : bv 32 := 0x888fc0ef.
Lemma F_e5d98 : fetch_word Plain.M.loaded_segments (0xe5dcc : word) = Some W_e5d98.
Proof. vm_refl. Qed.
Lemma D_e5d98 : decode_any W_e5d98 = Some (Jal 1 2080904, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5d9c : bv 32 := 0x00813083.
Lemma F_e5d9c : fetch_word Plain.M.loaded_segments (0xe5dd0 : word) = Some W_e5d9c.
Proof. vm_refl. Qed.
Lemma D_e5d9c : decode_any W_e5d9c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5da0 : bv 32 := 0x01010113.
Lemma F_e5da0 : fetch_word Plain.M.loaded_segments (0xe5dd4 : word) = Some W_e5da0.
Proof. vm_refl. Qed.
Lemma D_e5da0 : decode_any W_e5da0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5da4 : bv 32 := 0xce4ea06f.
Lemma F_e5da4 : fetch_word Plain.M.loaded_segments (0xe5dd8 : word) = Some W_e5da4.
Proof. vm_refl. Qed.
Lemma D_e5da4 : decode_any W_e5da4 = Some (Jal 0 2008292, 4%Z).
Proof. vm_refl. Qed.

Definition W_e5da8 : bv 32 := 0xff010113.

Definition W_e5dac : bv 32 := 0x00113423.

Definition W_e5db0 : bv 32 := 0x00813023.

Definition W_e5db4 : bv 32 := 0x00153413.

Definition W_e5db8 : bv 32 := 0x00850433.

Definition W_e5dbc : bv 32 := 0x00040513.

Definition W_e5dc0 : bv 32 := 0xaecec0ef.

Definition W_e5dc4 : bv 32 := 0x00051e63.

Definition W_e5de0 : bv 32 := 0x00813083.

Definition W_e5de4 : bv 32 := 0x00013403.

Definition W_e5de8 : bv 32 := 0x01010113.

Definition W_e5dec : bv 32 := 0x00008067.

