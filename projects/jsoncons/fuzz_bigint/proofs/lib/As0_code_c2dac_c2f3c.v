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

Definition W_c2dac : bv 32 := 0xf9010113.
Lemma F_c2dac : fetch_word Asan.M.loaded_segments (0xc2dac : word) = Some W_c2dac.
Proof. vm_refl. Qed.
Lemma D_c2dac : decode_any W_c2dac = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2db0 : bv 32 := 0x06113423.
Lemma F_c2db0 : fetch_word Asan.M.loaded_segments (0xc2db0 : word) = Some W_c2db0.
Proof. vm_refl. Qed.
Lemma D_c2db0 : decode_any W_c2db0 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2db4 : bv 32 := 0x06813023.
Lemma F_c2db4 : fetch_word Asan.M.loaded_segments (0xc2db4 : word) = Some W_c2db4.
Proof. vm_refl. Qed.
Lemma D_c2db4 : decode_any W_c2db4 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2db8 : bv 32 := 0x04913c23.
Lemma F_c2db8 : fetch_word Asan.M.loaded_segments (0xc2db8 : word) = Some W_c2db8.
Proof. vm_refl. Qed.
Lemma D_c2db8 : decode_any W_c2db8 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2dbc : bv 32 := 0x05213823.
Lemma F_c2dbc : fetch_word Asan.M.loaded_segments (0xc2dbc : word) = Some W_c2dbc.
Proof. vm_refl. Qed.
Lemma D_c2dbc : decode_any W_c2dbc = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2dc0 : bv 32 := 0x05313423.
Lemma F_c2dc0 : fetch_word Asan.M.loaded_segments (0xc2dc0 : word) = Some W_c2dc0.
Proof. vm_refl. Qed.
Lemma D_c2dc0 : decode_any W_c2dc0 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2dc4 : bv 32 := 0x05413023.
Lemma F_c2dc4 : fetch_word Asan.M.loaded_segments (0xc2dc4 : word) = Some W_c2dc4.
Proof. vm_refl. Qed.
Lemma D_c2dc4 : decode_any W_c2dc4 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2dc8 : bv 32 := 0x03513c23.
Lemma F_c2dc8 : fetch_word Asan.M.loaded_segments (0xc2dc8 : word) = Some W_c2dc8.
Proof. vm_refl. Qed.
Lemma D_c2dc8 : decode_any W_c2dc8 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2dcc : bv 32 := 0x03613823.
Lemma F_c2dcc : fetch_word Asan.M.loaded_segments (0xc2dcc : word) = Some W_c2dcc.
Proof. vm_refl. Qed.
Lemma D_c2dcc : decode_any W_c2dcc = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2dd0 : bv 32 := 0x00060413.
Lemma F_c2dd0 : fetch_word Asan.M.loaded_segments (0xc2dd0 : word) = Some W_c2dd0.
Proof. vm_refl. Qed.
Lemma D_c2dd0 : decode_any W_c2dd0 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2dd4 : bv 32 := 0x00050493.
Lemma F_c2dd4 : fetch_word Asan.M.loaded_segments (0xc2dd4 : word) = Some W_c2dd4.
Proof. vm_refl. Qed.
Lemma D_c2dd4 : decode_any W_c2dd4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2dd8 : bv 32 := 0x00014517.
Lemma F_c2dd8 : fetch_word Asan.M.loaded_segments (0xc2dd8 : word) = Some W_c2dd8.
Proof. vm_refl. Qed.
Lemma D_c2dd8 : decode_any W_c2dd8 = Some (Auipc 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2ddc : bv 32 := 0x84053a83.
Lemma F_c2ddc : fetch_word Asan.M.loaded_segments (0xc2ddc : word) = Some W_c2ddc.
Proof. vm_refl. Qed.
Lemma D_c2ddc : decode_any W_c2ddc = Some (Load SZ8 true 21 10 2112, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2de0 : bv 32 := 0x000ab503.
Lemma F_c2de0 : fetch_word Asan.M.loaded_segments (0xc2de0 : word) = Some W_c2de0.
Proof. vm_refl. Qed.
Lemma D_c2de0 : decode_any W_c2de0 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2de4 : bv 32 := 0x02a13423.
Lemma F_c2de4 : fetch_word Asan.M.loaded_segments (0xc2de4 : word) = Some W_c2de4.
Proof. vm_refl. Qed.
Lemma D_c2de4 : decode_any W_c2de4 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2de8 : bv 32 := 0x0284b503.
Lemma F_c2de8 : fetch_word Asan.M.loaded_segments (0xc2de8 : word) = Some W_c2de8.
Proof. vm_refl. Qed.
Lemma D_c2de8 : decode_any W_c2de8 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2dec : bv 32 := 0x0384b603.
Lemma F_c2dec : fetch_word Asan.M.loaded_segments (0xc2dec : word) = Some W_c2dec.
Proof. vm_refl. Qed.
Lemma D_c2dec : decode_any W_c2dec = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2df0 : bv 32 := 0x40c50b33.
Lemma F_c2df0 : fetch_word Asan.M.loaded_segments (0xc2df0 : word) = Some W_c2df0.
Proof. vm_refl. Qed.
Lemma D_c2df0 : decode_any W_c2df0 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2df4 : bv 32 := 0x00c546b3.
Lemma F_c2df4 : fetch_word Asan.M.loaded_segments (0xc2df4 : word) = Some W_c2df4.
Proof. vm_refl. Qed.
Lemma D_c2df4 : decode_any W_c2df4 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2df8 : bv 32 := 0x00c13423.
Lemma F_c2df8 : fetch_word Asan.M.loaded_segments (0xc2df8 : word) = Some W_c2df8.
Proof. vm_refl. Qed.
Lemma D_c2df8 : decode_any W_c2df8 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2dfc : bv 32 := 0x01613823.
Lemma F_c2dfc : fetch_word Asan.M.loaded_segments (0xc2dfc : word) = Some W_c2dfc.
Proof. vm_refl. Qed.
Lemma D_c2dfc : decode_any W_c2dfc = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e00 : bv 32 := 0x00b13c23.
Lemma F_c2e00 : fetch_word Asan.M.loaded_segments (0xc2e00 : word) = Some W_c2e00.
Proof. vm_refl. Qed.
Lemma D_c2e00 : decode_any W_c2e00 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e04 : bv 32 := 0x02813023.
Lemma F_c2e04 : fetch_word Asan.M.loaded_segments (0xc2e04 : word) = Some W_c2e04.
Proof. vm_refl. Qed.
Lemma D_c2e04 : decode_any W_c2e04 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e08 : bv 32 := 0x008b0b33.
Lemma F_c2e08 : fetch_word Asan.M.loaded_segments (0xc2e08 : word) = Some W_c2e08.
Proof. vm_refl. Qed.
Lemma D_c2e08 : decode_any W_c2e08 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e0c : bv 32 := 0x00d03933.
Lemma F_c2e0c : fetch_word Asan.M.loaded_segments (0xc2e0c : word) = Some W_c2e0c.
Proof. vm_refl. Qed.
Lemma D_c2e0c : decode_any W_c2e0c = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e10 : bv 32 := 0x00c50663.
Lemma F_c2e10 : fetch_word Asan.M.loaded_segments (0xc2e10 : word) = Some W_c2e10.
Proof. vm_refl. Qed.
Lemma D_c2e10 : decode_any W_c2e10 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e14 : bv 32 := 0x00810993.
Lemma F_c2e14 : fetch_word Asan.M.loaded_segments (0xc2e14 : word) = Some W_c2e14.
Proof. vm_refl. Qed.
Lemma D_c2e14 : decode_any W_c2e14 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e18 : bv 32 := 0x0080006f.
Lemma F_c2e18 : fetch_word Asan.M.loaded_segments (0xc2e18 : word) = Some W_c2e18.
Proof. vm_refl. Qed.
Lemma D_c2e18 : decode_any W_c2e18 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e1c : bv 32 := 0x01810993.
Lemma F_c2e1c : fetch_word Asan.M.loaded_segments (0xc2e1c : word) = Some W_c2e1c.
Proof. vm_refl. Qed.
Lemma D_c2e1c : decode_any W_c2e1c = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e20 : bv 32 := 0x0784a503.
Lemma F_c2e20 : fetch_word Asan.M.loaded_segments (0xc2e20 : word) = Some W_c2e20.
Proof. vm_refl. Qed.
Lemma D_c2e20 : decode_any W_c2e20 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e24 : bv 32 := 0x00190913.
Lemma F_c2e24 : fetch_word Asan.M.loaded_segments (0xc2e24 : word) = Some W_c2e24.
Proof. vm_refl. Qed.
Lemma D_c2e24 : decode_any W_c2e24 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e28 : bv 32 := 0x04200893.
Lemma F_c2e28 : fetch_word Asan.M.loaded_segments (0xc2e28 : word) = Some W_c2e28.
Proof. vm_refl. Qed.
Lemma D_c2e28 : decode_any W_c2e28 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e2c : bv 32 := 0x00098593.
Lemma F_c2e2c : fetch_word Asan.M.loaded_segments (0xc2e2c : word) = Some W_c2e2c.
Proof. vm_refl. Qed.
Lemma D_c2e2c : decode_any W_c2e2c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e30 : bv 32 := 0x00090613.
Lemma F_c2e30 : fetch_word Asan.M.loaded_segments (0xc2e30 : word) = Some W_c2e30.
Proof. vm_refl. Qed.
Lemma D_c2e30 : decode_any W_c2e30 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e34 : bv 32 := 0x00000073.
Lemma F_c2e34 : fetch_word Asan.M.loaded_segments (0xc2e34 : word) = Some W_c2e34.
Proof. vm_refl. Qed.
Lemma D_c2e34 : decode_any W_c2e34 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_c2e34 : is_ecall W_c2e34 = true.
Proof. reflexivity. Qed.

Definition W_c2e38 : bv 32 := 0x985fa0ef.
Lemma F_c2e38 : fetch_word Asan.M.loaded_segments (0xc2e38 : word) = Some W_c2e38.
Proof. vm_refl. Qed.
Lemma D_c2e38 : decode_any W_c2e38 = Some (Jal 1 2075012, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e3c : bv 32 := 0x09651863.
Lemma F_c2e3c : fetch_word Asan.M.loaded_segments (0xc2e3c : word) = Some W_c2e3c.
Proof. vm_refl. Qed.
Lemma D_c2e3c : decode_any W_c2e3c = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e40 : bv 32 := 0x0584b503.
Lemma F_c2e40 : fetch_word Asan.M.loaded_segments (0xc2e40 : word) = Some W_c2e40.
Proof. vm_refl. Qed.
Lemma D_c2e40 : decode_any W_c2e40 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e44 : bv 32 := 0x0604b583.
Lemma F_c2e44 : fetch_word Asan.M.loaded_segments (0xc2e44 : word) = Some W_c2e44.
Proof. vm_refl. Qed.
Lemma D_c2e44 : decode_any W_c2e44 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e48 : bv 32 := 0x00b505b3.
Lemma F_c2e48 : fetch_word Asan.M.loaded_segments (0xc2e48 : word) = Some W_c2e48.
Proof. vm_refl. Qed.
Lemma D_c2e48 : decode_any W_c2e48 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e4c : bv 32 := 0x02b4b023.
Lemma F_c2e4c : fetch_word Asan.M.loaded_segments (0xc2e4c : word) = Some W_c2e4c.
Proof. vm_refl. Qed.
Lemma D_c2e4c : decode_any W_c2e4c = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e50 : bv 32 := 0x02a4b423.
Lemma F_c2e50 : fetch_word Asan.M.loaded_segments (0xc2e50 : word) = Some W_c2e50.
Proof. vm_refl. Qed.
Lemma D_c2e50 : decode_any W_c2e50 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e54 : bv 32 := 0x02a4bc23.
Lemma F_c2e54 : fetch_word Asan.M.loaded_segments (0xc2e54 : word) = Some W_c2e54.
Proof. vm_refl. Qed.
Lemma D_c2e54 : decode_any W_c2e54 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e58 : bv 32 := 0x00040513.
Lemma F_c2e58 : fetch_word Asan.M.loaded_segments (0xc2e58 : word) = Some W_c2e58.
Proof. vm_refl. Qed.
Lemma D_c2e58 : decode_any W_c2e58 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e5c : bv 32 := 0x000ab583.
Lemma F_c2e5c : fetch_word Asan.M.loaded_segments (0xc2e5c : word) = Some W_c2e5c.
Proof. vm_refl. Qed.
Lemma D_c2e5c : decode_any W_c2e5c = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e60 : bv 32 := 0x02813603.
Lemma F_c2e60 : fetch_word Asan.M.loaded_segments (0xc2e60 : word) = Some W_c2e60.
Proof. vm_refl. Qed.
Lemma D_c2e60 : decode_any W_c2e60 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e64 : bv 32 := 0x0cc59a63.
Lemma F_c2e64 : fetch_word Asan.M.loaded_segments (0xc2e64 : word) = Some W_c2e64.
Proof. vm_refl. Qed.
Lemma D_c2e64 : decode_any W_c2e64 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e68 : bv 32 := 0x06813083.
Lemma F_c2e68 : fetch_word Asan.M.loaded_segments (0xc2e68 : word) = Some W_c2e68.
Proof. vm_refl. Qed.
Lemma D_c2e68 : decode_any W_c2e68 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e6c : bv 32 := 0x06013403.
Lemma F_c2e6c : fetch_word Asan.M.loaded_segments (0xc2e6c : word) = Some W_c2e6c.
Proof. vm_refl. Qed.
Lemma D_c2e6c : decode_any W_c2e6c = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e70 : bv 32 := 0x05813483.
Lemma F_c2e70 : fetch_word Asan.M.loaded_segments (0xc2e70 : word) = Some W_c2e70.
Proof. vm_refl. Qed.
Lemma D_c2e70 : decode_any W_c2e70 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e74 : bv 32 := 0x05013903.
Lemma F_c2e74 : fetch_word Asan.M.loaded_segments (0xc2e74 : word) = Some W_c2e74.
Proof. vm_refl. Qed.
Lemma D_c2e74 : decode_any W_c2e74 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e78 : bv 32 := 0x04813983.
Lemma F_c2e78 : fetch_word Asan.M.loaded_segments (0xc2e78 : word) = Some W_c2e78.
Proof. vm_refl. Qed.
Lemma D_c2e78 : decode_any W_c2e78 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e7c : bv 32 := 0x04013a03.
Lemma F_c2e7c : fetch_word Asan.M.loaded_segments (0xc2e7c : word) = Some W_c2e7c.
Proof. vm_refl. Qed.
Lemma D_c2e7c : decode_any W_c2e7c = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e80 : bv 32 := 0x03813a83.
Lemma F_c2e80 : fetch_word Asan.M.loaded_segments (0xc2e80 : word) = Some W_c2e80.
Proof. vm_refl. Qed.
Lemma D_c2e80 : decode_any W_c2e80 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e84 : bv 32 := 0x03013b03.
Lemma F_c2e84 : fetch_word Asan.M.loaded_segments (0xc2e84 : word) = Some W_c2e84.
Proof. vm_refl. Qed.
Lemma D_c2e84 : decode_any W_c2e84 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e88 : bv 32 := 0x07010113.
Lemma F_c2e88 : fetch_word Asan.M.loaded_segments (0xc2e88 : word) = Some W_c2e88.
Proof. vm_refl. Qed.
Lemma D_c2e88 : decode_any W_c2e88 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e8c : bv 32 := 0x00008067.
Lemma F_c2e8c : fetch_word Asan.M.loaded_segments (0xc2e8c : word) = Some W_c2e8c.
Proof. vm_refl. Qed.
Lemma D_c2e8c : decode_any W_c2e8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e90 : bv 32 := 0x00800713.
Lemma F_c2e90 : fetch_word Asan.M.loaded_segments (0xc2e90 : word) = Some W_c2e90.
Proof. vm_refl. Qed.
Lemma D_c2e90 : decode_any W_c2e90 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e94 : bv 32 := 0x000a0593.
Lemma F_c2e94 : fetch_word Asan.M.loaded_segments (0xc2e94 : word) = Some W_c2e94.
Proof. vm_refl. Qed.
Lemma D_c2e94 : decode_any W_c2e94 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e98 : bv 32 := 0x00e98733.
Lemma F_c2e98 : fetch_word Asan.M.loaded_segments (0xc2e98 : word) = Some W_c2e98.
Proof. vm_refl. Qed.
Lemma D_c2e98 : decode_any W_c2e98 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2e9c : bv 32 := 0x00073783.
Lemma F_c2e9c : fetch_word Asan.M.loaded_segments (0xc2e9c : word) = Some W_c2e9c.
Proof. vm_refl. Qed.
Lemma D_c2e9c : decode_any W_c2e9c = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2ea0 : bv 32 := 0x40ab0b33.
Lemma F_c2ea0 : fetch_word Asan.M.loaded_segments (0xc2ea0 : word) = Some W_c2ea0.
Proof. vm_refl. Qed.
Lemma D_c2ea0 : decode_any W_c2ea0 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2ea4 : bv 32 := 0x0784a503.
Lemma F_c2ea4 : fetch_word Asan.M.loaded_segments (0xc2ea4 : word) = Some W_c2ea4.
Proof. vm_refl. Qed.
Lemma D_c2ea4 : decode_any W_c2ea4 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2ea8 : bv 32 := 0x40c9093b.
Lemma F_c2ea8 : fetch_word Asan.M.loaded_segments (0xc2ea8 : word) = Some W_c2ea8.
Proof. vm_refl. Qed.
Lemma D_c2ea8 : decode_any W_c2ea8 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2eac : bv 32 := 0x40d787b3.
Lemma F_c2eac : fetch_word Asan.M.loaded_segments (0xc2eac : word) = Some W_c2eac.
Proof. vm_refl. Qed.
Lemma D_c2eac : decode_any W_c2eac = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2eb0 : bv 32 := 0x00f73023.
Lemma F_c2eb0 : fetch_word Asan.M.loaded_segments (0xc2eb0 : word) = Some W_c2eb0.
Proof. vm_refl. Qed.
Lemma D_c2eb0 : decode_any W_c2eb0 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2eb4 : bv 32 := 0x04200893.
Lemma F_c2eb4 : fetch_word Asan.M.loaded_segments (0xc2eb4 : word) = Some W_c2eb4.
Proof. vm_refl. Qed.
Lemma D_c2eb4 : decode_any W_c2eb4 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2eb8 : bv 32 := 0x00090613.
Lemma F_c2eb8 : fetch_word Asan.M.loaded_segments (0xc2eb8 : word) = Some W_c2eb8.
Proof. vm_refl. Qed.
Lemma D_c2eb8 : decode_any W_c2eb8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2ebc : bv 32 := 0x00000073.
Lemma F_c2ebc : fetch_word Asan.M.loaded_segments (0xc2ebc : word) = Some W_c2ebc.
Proof. vm_refl. Qed.
Lemma D_c2ebc : decode_any W_c2ebc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_c2ebc : is_ecall W_c2ebc = true.
Proof. reflexivity. Qed.

Definition W_c2ec0 : bv 32 := 0x8fdfa0ef.
Lemma F_c2ec0 : fetch_word Asan.M.loaded_segments (0xc2ec0 : word) = Some W_c2ec0.
Proof. vm_refl. Qed.
Lemma D_c2ec0 : decode_any W_c2ec0 = Some (Jal 1 2074876, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2ec4 : bv 32 := 0x000a0993.
Lemma F_c2ec4 : fetch_word Asan.M.loaded_segments (0xc2ec4 : word) = Some W_c2ec4.
Proof. vm_refl. Qed.
Lemma D_c2ec4 : decode_any W_c2ec4 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2ec8 : bv 32 := 0xf7650ce3.
Lemma F_c2ec8 : fetch_word Asan.M.loaded_segments (0xc2ec8 : word) = Some W_c2ec8.
Proof. vm_refl. Qed.
Lemma D_c2ec8 : decode_any W_c2ec8 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2ecc : bv 32 := 0x02054c63.
Lemma F_c2ecc : fetch_word Asan.M.loaded_segments (0xc2ecc : word) = Some W_c2ecc.
Proof. vm_refl. Qed.
Lemma D_c2ecc : decode_any W_c2ecc = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2ed0 : bv 32 := 0x0089b583.
Lemma F_c2ed0 : fetch_word Asan.M.loaded_segments (0xc2ed0 : word) = Some W_c2ed0.
Proof. vm_refl. Qed.
Lemma D_c2ed0 : decode_any W_c2ed0 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2ed4 : bv 32 := 0x00a5b633.
Lemma F_c2ed4 : fetch_word Asan.M.loaded_segments (0xc2ed4 : word) = Some W_c2ed4.
Proof. vm_refl. Qed.
Lemma D_c2ed4 : decode_any W_c2ed4 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2ed8 : bv 32 := 0x00461a13.
Lemma F_c2ed8 : fetch_word Asan.M.loaded_segments (0xc2ed8 : word) = Some W_c2ed8.
Proof. vm_refl. Qed.
Lemma D_c2ed8 : decode_any W_c2ed8 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2edc : bv 32 := 0x01498a33.
Lemma F_c2edc : fetch_word Asan.M.loaded_segments (0xc2edc : word) = Some W_c2edc.
Proof. vm_refl. Qed.
Lemma D_c2edc : decode_any W_c2edc = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2ee0 : bv 32 := 0x000a3703.
Lemma F_c2ee0 : fetch_word Asan.M.loaded_segments (0xc2ee0 : word) = Some W_c2ee0.
Proof. vm_refl. Qed.
Lemma D_c2ee0 : decode_any W_c2ee0 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2ee4 : bv 32 := 0x40c006b3.
Lemma F_c2ee4 : fetch_word Asan.M.loaded_segments (0xc2ee4 : word) = Some W_c2ee4.
Proof. vm_refl. Qed.
Lemma D_c2ee4 : decode_any W_c2ee4 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2ee8 : bv 32 := 0x00b6f6b3.
Lemma F_c2ee8 : fetch_word Asan.M.loaded_segments (0xc2ee8 : word) = Some W_c2ee8.
Proof. vm_refl. Qed.
Lemma D_c2ee8 : decode_any W_c2ee8 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2eec : bv 32 := 0x40d506b3.
Lemma F_c2eec : fetch_word Asan.M.loaded_segments (0xc2eec : word) = Some W_c2eec.
Proof. vm_refl. Qed.
Lemma D_c2eec : decode_any W_c2eec = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2ef0 : bv 32 := 0x00d70733.
Lemma F_c2ef0 : fetch_word Asan.M.loaded_segments (0xc2ef0 : word) = Some W_c2ef0.
Proof. vm_refl. Qed.
Lemma D_c2ef0 : decode_any W_c2ef0 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2ef4 : bv 32 := 0x00ea3023.
Lemma F_c2ef4 : fetch_word Asan.M.loaded_segments (0xc2ef4 : word) = Some W_c2ef4.
Proof. vm_refl. Qed.
Lemma D_c2ef4 : decode_any W_c2ef4 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2ef8 : bv 32 := 0xf8a5fce3.
Lemma F_c2ef8 : fetch_word Asan.M.loaded_segments (0xc2ef8 : word) = Some W_c2ef8.
Proof. vm_refl. Qed.
Lemma D_c2ef8 : decode_any W_c2ef8 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2efc : bv 32 := 0x01800713.
Lemma F_c2efc : fetch_word Asan.M.loaded_segments (0xc2efc : word) = Some W_c2efc.
Proof. vm_refl. Qed.
Lemma D_c2efc : decode_any W_c2efc = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2f00 : bv 32 := 0xf95ff06f.
Lemma F_c2f00 : fetch_word Asan.M.loaded_segments (0xc2f00 : word) = Some W_c2f00.
Proof. vm_refl. Qed.
Lemma D_c2f00 : decode_any W_c2f00 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2f04 : bv 32 := 0x00000513.
Lemma F_c2f04 : fetch_word Asan.M.loaded_segments (0xc2f04 : word) = Some W_c2f04.
Proof. vm_refl. Qed.
Lemma D_c2f04 : decode_any W_c2f04 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2f08 : bv 32 := 0x0004a583.
Lemma F_c2f08 : fetch_word Asan.M.loaded_segments (0xc2f08 : word) = Some W_c2f08.
Proof. vm_refl. Qed.
Lemma D_c2f08 : decode_any W_c2f08 = Some (Load SZ4 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2f0c : bv 32 := 0x0009091b.
Lemma F_c2f0c : fetch_word Asan.M.loaded_segments (0xc2f0c : word) = Some W_c2f0c.
Proof. vm_refl. Qed.
Lemma D_c2f0c : decode_any W_c2f0c = Some (OpImm32 18 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2f10 : bv 32 := 0x00200613.
Lemma F_c2f10 : fetch_word Asan.M.loaded_segments (0xc2f10 : word) = Some W_c2f10.
Proof. vm_refl. Qed.
Lemma D_c2f10 : decode_any W_c2f10 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2f14 : bv 32 := 0x0205e593.
Lemma F_c2f14 : fetch_word Asan.M.loaded_segments (0xc2f14 : word) = Some W_c2f14.
Proof. vm_refl. Qed.
Lemma D_c2f14 : decode_any W_c2f14 = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2f18 : bv 32 := 0x00b4a023.
Lemma F_c2f18 : fetch_word Asan.M.loaded_segments (0xc2f18 : word) = Some W_c2f18.
Proof. vm_refl. Qed.
Lemma D_c2f18 : decode_any W_c2f18 = Some (Store SZ4 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2f1c : bv 32 := 0x0204b023.
Lemma F_c2f1c : fetch_word Asan.M.loaded_segments (0xc2f1c : word) = Some W_c2f1c.
Proof. vm_refl. Qed.
Lemma D_c2f1c : decode_any W_c2f1c = Some (Store SZ8 9 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2f20 : bv 32 := 0x0204b423.
Lemma F_c2f20 : fetch_word Asan.M.loaded_segments (0xc2f20 : word) = Some W_c2f20.
Proof. vm_refl. Qed.
Lemma D_c2f20 : decode_any W_c2f20 = Some (Store SZ8 9 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2f24 : bv 32 := 0x0204bc23.
Lemma F_c2f24 : fetch_word Asan.M.loaded_segments (0xc2f24 : word) = Some W_c2f24.
Proof. vm_refl. Qed.
Lemma D_c2f24 : decode_any W_c2f24 = Some (Store SZ8 9 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2f28 : bv 32 := 0xf2c90ae3.
Lemma F_c2f28 : fetch_word Asan.M.loaded_segments (0xc2f28 : word) = Some W_c2f28.
Proof. vm_refl. Qed.
Lemma D_c2f28 : decode_any W_c2f28 = Some (Branch BC_EQ 18 12 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2f2c : bv 32 := 0x0089b503.
Lemma F_c2f2c : fetch_word Asan.M.loaded_segments (0xc2f2c : word) = Some W_c2f2c.
Proof. vm_refl. Qed.
Lemma D_c2f2c : decode_any W_c2f2c = Some (Load SZ8 true 10 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2f30 : bv 32 := 0x40a40533.
Lemma F_c2f30 : fetch_word Asan.M.loaded_segments (0xc2f30 : word) = Some W_c2f30.
Proof. vm_refl. Qed.
Lemma D_c2f30 : decode_any W_c2f30 = Some (Op ALU_SUB 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2f34 : bv 32 := 0xf29ff06f.
Lemma F_c2f34 : fetch_word Asan.M.loaded_segments (0xc2f34 : word) = Some W_c2f34.
Proof. vm_refl. Qed.
Lemma D_c2f34 : decode_any W_c2f34 = Some (Jal 0 2096936, 4%Z).
Proof. vm_refl. Qed.

Definition W_c2f38 : bv 32 := 0xa18fa0ef.
Lemma F_c2f38 : fetch_word Asan.M.loaded_segments (0xc2f38 : word) = Some W_c2f38.
Proof. vm_refl. Qed.
Lemma D_c2f38 : decode_any W_c2f38 = Some (Jal 1 2073112, 4%Z).
Proof. vm_refl. Qed.
