(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_121d50 : bv 32 := 0x0284b503.
Lemma F_121d50 : fetch_word Asan.M.loaded_segments (0x121d94 : word) = Some W_121d50.
Proof. vm_refl. Qed.
Lemma D_121d50 : decode_any W_121d50 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_121d54 : bv 32 := 0x0384b603.
Lemma F_121d54 : fetch_word Asan.M.loaded_segments (0x121d98 : word) = Some W_121d54.
Proof. vm_refl. Qed.
Lemma D_121d54 : decode_any W_121d54 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_121d58 : bv 32 := 0x40c50b33.
Lemma F_121d58 : fetch_word Asan.M.loaded_segments (0x121d9c : word) = Some W_121d58.
Proof. vm_refl. Qed.
Lemma D_121d58 : decode_any W_121d58 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_121d5c : bv 32 := 0x00c546b3.
Lemma F_121d5c : fetch_word Asan.M.loaded_segments (0x121da0 : word) = Some W_121d5c.
Proof. vm_refl. Qed.
Lemma D_121d5c : decode_any W_121d5c = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_121d60 : bv 32 := 0x00c13423.
Lemma F_121d60 : fetch_word Asan.M.loaded_segments (0x121da4 : word) = Some W_121d60.
Proof. vm_refl. Qed.
Lemma D_121d60 : decode_any W_121d60 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_121d64 : bv 32 := 0x01613823.
Lemma F_121d64 : fetch_word Asan.M.loaded_segments (0x121da8 : word) = Some W_121d64.
Proof. vm_refl. Qed.
Lemma D_121d64 : decode_any W_121d64 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_121d68 : bv 32 := 0x00b13c23.
Lemma F_121d68 : fetch_word Asan.M.loaded_segments (0x121dac : word) = Some W_121d68.
Proof. vm_refl. Qed.
Lemma D_121d68 : decode_any W_121d68 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_121d6c : bv 32 := 0x02813023.
Lemma F_121d6c : fetch_word Asan.M.loaded_segments (0x121db0 : word) = Some W_121d6c.
Proof. vm_refl. Qed.
Lemma D_121d6c : decode_any W_121d6c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_121d70 : bv 32 := 0x008b0b33.
Lemma F_121d70 : fetch_word Asan.M.loaded_segments (0x121db4 : word) = Some W_121d70.
Proof. vm_refl. Qed.
Lemma D_121d70 : decode_any W_121d70 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_121d74 : bv 32 := 0x00d03933.
Lemma F_121d74 : fetch_word Asan.M.loaded_segments (0x121db8 : word) = Some W_121d74.
Proof. vm_refl. Qed.
Lemma D_121d74 : decode_any W_121d74 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_121d78 : bv 32 := 0x00c50663.
Lemma F_121d78 : fetch_word Asan.M.loaded_segments (0x121dbc : word) = Some W_121d78.
Proof. vm_refl. Qed.
Lemma D_121d78 : decode_any W_121d78 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_121d7c : bv 32 := 0x00810993.
Lemma F_121d7c : fetch_word Asan.M.loaded_segments (0x121dc0 : word) = Some W_121d7c.
Proof. vm_refl. Qed.
Lemma D_121d7c : decode_any W_121d7c = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_121d80 : bv 32 := 0x0080006f.
Lemma F_121d80 : fetch_word Asan.M.loaded_segments (0x121dc4 : word) = Some W_121d80.
Proof. vm_refl. Qed.
Lemma D_121d80 : decode_any W_121d80 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_121d84 : bv 32 := 0x01810993.
Lemma F_121d84 : fetch_word Asan.M.loaded_segments (0x121dc8 : word) = Some W_121d84.
Proof. vm_refl. Qed.
Lemma D_121d84 : decode_any W_121d84 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_121d88 : bv 32 := 0x0784a503.
Lemma F_121d88 : fetch_word Asan.M.loaded_segments (0x121dcc : word) = Some W_121d88.
Proof. vm_refl. Qed.
Lemma D_121d88 : decode_any W_121d88 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_121d8c : bv 32 := 0x00190913.
Lemma F_121d8c : fetch_word Asan.M.loaded_segments (0x121dd0 : word) = Some W_121d8c.
Proof. vm_refl. Qed.
Lemma D_121d8c : decode_any W_121d8c = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_121d90 : bv 32 := 0x04200893.
Lemma F_121d90 : fetch_word Asan.M.loaded_segments (0x121dd4 : word) = Some W_121d90.
Proof. vm_refl. Qed.
Lemma D_121d90 : decode_any W_121d90 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_121d94 : bv 32 := 0x00098593.
Lemma F_121d94 : fetch_word Asan.M.loaded_segments (0x121dd8 : word) = Some W_121d94.
Proof. vm_refl. Qed.
Lemma D_121d94 : decode_any W_121d94 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_121d98 : bv 32 := 0x00090613.
Lemma F_121d98 : fetch_word Asan.M.loaded_segments (0x121ddc : word) = Some W_121d98.
Proof. vm_refl. Qed.
Lemma D_121d98 : decode_any W_121d98 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_121da0 : bv 32 := 0x971f80ef.
Lemma F_121da0 : fetch_word Asan.M.loaded_segments (0x121de4 : word) = Some W_121da0.
Proof. vm_refl. Qed.
Lemma D_121da0 : decode_any W_121da0 = Some (Jal 1 2066800, 4%Z).
Proof. vm_refl. Qed.

Definition W_121da4 : bv 32 := 0x09651863.
Lemma F_121da4 : fetch_word Asan.M.loaded_segments (0x121de8 : word) = Some W_121da4.
Proof. vm_refl. Qed.
Lemma D_121da4 : decode_any W_121da4 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_121df8 : bv 32 := 0x00800713.
Lemma F_121df8 : fetch_word Asan.M.loaded_segments (0x121e3c : word) = Some W_121df8.
Proof. vm_refl. Qed.
Lemma D_121df8 : decode_any W_121df8 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_121dfc : bv 32 := 0x000a0593.
Lemma F_121dfc : fetch_word Asan.M.loaded_segments (0x121e40 : word) = Some W_121dfc.
Proof. vm_refl. Qed.
Lemma D_121dfc : decode_any W_121dfc = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e00 : bv 32 := 0x00e98733.
Lemma F_121e00 : fetch_word Asan.M.loaded_segments (0x121e44 : word) = Some W_121e00.
Proof. vm_refl. Qed.
Lemma D_121e00 : decode_any W_121e00 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e04 : bv 32 := 0x00073783.
Lemma F_121e04 : fetch_word Asan.M.loaded_segments (0x121e48 : word) = Some W_121e04.
Proof. vm_refl. Qed.
Lemma D_121e04 : decode_any W_121e04 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e08 : bv 32 := 0x40ab0b33.
Lemma F_121e08 : fetch_word Asan.M.loaded_segments (0x121e4c : word) = Some W_121e08.
Proof. vm_refl. Qed.
Lemma D_121e08 : decode_any W_121e08 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e0c : bv 32 := 0x0784a503.
Lemma F_121e0c : fetch_word Asan.M.loaded_segments (0x121e50 : word) = Some W_121e0c.
Proof. vm_refl. Qed.
Lemma D_121e0c : decode_any W_121e0c = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e10 : bv 32 := 0x40c9093b.
Lemma F_121e10 : fetch_word Asan.M.loaded_segments (0x121e54 : word) = Some W_121e10.
Proof. vm_refl. Qed.
Lemma D_121e10 : decode_any W_121e10 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e14 : bv 32 := 0x40d787b3.
Lemma F_121e14 : fetch_word Asan.M.loaded_segments (0x121e58 : word) = Some W_121e14.
Proof. vm_refl. Qed.
Lemma D_121e14 : decode_any W_121e14 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e18 : bv 32 := 0x00f73023.
Lemma F_121e18 : fetch_word Asan.M.loaded_segments (0x121e5c : word) = Some W_121e18.
Proof. vm_refl. Qed.
Lemma D_121e18 : decode_any W_121e18 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e1c : bv 32 := 0x04200893.
Lemma F_121e1c : fetch_word Asan.M.loaded_segments (0x121e60 : word) = Some W_121e1c.
Proof. vm_refl. Qed.
Lemma D_121e1c : decode_any W_121e1c = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e20 : bv 32 := 0x00090613.
Lemma F_121e20 : fetch_word Asan.M.loaded_segments (0x121e64 : word) = Some W_121e20.
Proof. vm_refl. Qed.
Lemma D_121e20 : decode_any W_121e20 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e28 : bv 32 := 0x8e9f80ef.
Lemma F_121e28 : fetch_word Asan.M.loaded_segments (0x121e6c : word) = Some W_121e28.
Proof. vm_refl. Qed.
Lemma D_121e28 : decode_any W_121e28 = Some (Jal 1 2066664, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e2c : bv 32 := 0x000a0993.
Lemma F_121e2c : fetch_word Asan.M.loaded_segments (0x121e70 : word) = Some W_121e2c.
Proof. vm_refl. Qed.
Lemma D_121e2c : decode_any W_121e2c = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e30 : bv 32 := 0xf7650ce3.
Lemma F_121e30 : fetch_word Asan.M.loaded_segments (0x121e74 : word) = Some W_121e30.
Proof. vm_refl. Qed.
Lemma D_121e30 : decode_any W_121e30 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e34 : bv 32 := 0x02054c63.
Lemma F_121e34 : fetch_word Asan.M.loaded_segments (0x121e78 : word) = Some W_121e34.
Proof. vm_refl. Qed.
Lemma D_121e34 : decode_any W_121e34 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e38 : bv 32 := 0x0089b583.
Lemma F_121e38 : fetch_word Asan.M.loaded_segments (0x121e7c : word) = Some W_121e38.
Proof. vm_refl. Qed.
Lemma D_121e38 : decode_any W_121e38 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e3c : bv 32 := 0x00a5b633.
Lemma F_121e3c : fetch_word Asan.M.loaded_segments (0x121e80 : word) = Some W_121e3c.
Proof. vm_refl. Qed.
Lemma D_121e3c : decode_any W_121e3c = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e40 : bv 32 := 0x00461a13.
Lemma F_121e40 : fetch_word Asan.M.loaded_segments (0x121e84 : word) = Some W_121e40.
Proof. vm_refl. Qed.
Lemma D_121e40 : decode_any W_121e40 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e44 : bv 32 := 0x01498a33.
Lemma F_121e44 : fetch_word Asan.M.loaded_segments (0x121e88 : word) = Some W_121e44.
Proof. vm_refl. Qed.
Lemma D_121e44 : decode_any W_121e44 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e48 : bv 32 := 0x000a3703.
Lemma F_121e48 : fetch_word Asan.M.loaded_segments (0x121e8c : word) = Some W_121e48.
Proof. vm_refl. Qed.
Lemma D_121e48 : decode_any W_121e48 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e4c : bv 32 := 0x40c006b3.
Lemma F_121e4c : fetch_word Asan.M.loaded_segments (0x121e90 : word) = Some W_121e4c.
Proof. vm_refl. Qed.
Lemma D_121e4c : decode_any W_121e4c = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e50 : bv 32 := 0x00b6f6b3.
Lemma F_121e50 : fetch_word Asan.M.loaded_segments (0x121e94 : word) = Some W_121e50.
Proof. vm_refl. Qed.
Lemma D_121e50 : decode_any W_121e50 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e54 : bv 32 := 0x40d506b3.
Lemma F_121e54 : fetch_word Asan.M.loaded_segments (0x121e98 : word) = Some W_121e54.
Proof. vm_refl. Qed.
Lemma D_121e54 : decode_any W_121e54 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e58 : bv 32 := 0x00d70733.
Lemma F_121e58 : fetch_word Asan.M.loaded_segments (0x121e9c : word) = Some W_121e58.
Proof. vm_refl. Qed.
Lemma D_121e58 : decode_any W_121e58 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e5c : bv 32 := 0x00ea3023.
Lemma F_121e5c : fetch_word Asan.M.loaded_segments (0x121ea0 : word) = Some W_121e5c.
Proof. vm_refl. Qed.
Lemma D_121e5c : decode_any W_121e5c = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e60 : bv 32 := 0xf8a5fce3.
Lemma F_121e60 : fetch_word Asan.M.loaded_segments (0x121ea4 : word) = Some W_121e60.
Proof. vm_refl. Qed.
Lemma D_121e60 : decode_any W_121e60 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e64 : bv 32 := 0x01800713.
Lemma F_121e64 : fetch_word Asan.M.loaded_segments (0x121ea8 : word) = Some W_121e64.
Proof. vm_refl. Qed.
Lemma D_121e64 : decode_any W_121e64 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_121e68 : bv 32 := 0xf95ff06f.
Lemma F_121e68 : fetch_word Asan.M.loaded_segments (0x121eac : word) = Some W_121e68.
Proof. vm_refl. Qed.
Lemma D_121e68 : decode_any W_121e68 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.
