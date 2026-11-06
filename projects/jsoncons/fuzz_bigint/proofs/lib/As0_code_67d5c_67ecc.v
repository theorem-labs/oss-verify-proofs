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

Definition W_67d5c : bv 32 := 0x0310000f.
Lemma F_67d5c : fetch_word Asan.M.loaded_segments (0x67d5c : word) = Some W_67d5c.
Proof. vm_refl. Qed.
Lemma D_67d5c : decode_any W_67d5c = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67d60 : bv 32 := 0x00077597.
Lemma F_67d60 : fetch_word Asan.M.loaded_segments (0x67d60 : word) = Some W_67d60.
Proof. vm_refl. Qed.
Lemma D_67d60 : decode_any W_67d60 = Some (Auipc 11 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_67d64 : bv 32 := 0xaca5ae23.
Lemma F_67d64 : fetch_word Asan.M.loaded_segments (0x67d64 : word) = Some W_67d64.
Proof. vm_refl. Qed.
Lemma D_67d64 : decode_any W_67d64 = Some (Store SZ4 11 10 2780, 4%Z).
Proof. vm_refl. Qed.

Definition W_67d68 : bv 32 := 0x00008067.
Lemma F_67d68 : fetch_word Asan.M.loaded_segments (0x67d68 : word) = Some W_67d68.
Proof. vm_refl. Qed.
Lemma D_67d68 : decode_any W_67d68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67d6c : bv 32 := 0x00077517.
Lemma F_67d6c : fetch_word Asan.M.loaded_segments (0x67d6c : word) = Some W_67d6c.
Proof. vm_refl. Qed.
Lemma D_67d6c : decode_any W_67d6c = Some (Auipc 10 119, 4%Z).
Proof. vm_refl. Qed.

Definition W_67d70 : bv 32 := 0xad052503.
Lemma F_67d70 : fetch_word Asan.M.loaded_segments (0x67d70 : word) = Some W_67d70.
Proof. vm_refl. Qed.
Lemma D_67d70 : decode_any W_67d70 = Some (Load SZ4 true 10 10 2768, 4%Z).
Proof. vm_refl. Qed.

Definition W_67d74 : bv 32 := 0x0230000f.
Lemma F_67d74 : fetch_word Asan.M.loaded_segments (0x67d74 : word) = Some W_67d74.
Proof. vm_refl. Qed.
Lemma D_67d74 : decode_any W_67d74 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67d78 : bv 32 := 0x00008067.
Lemma F_67d78 : fetch_word Asan.M.loaded_segments (0x67d78 : word) = Some W_67d78.
Proof. vm_refl. Qed.
Lemma D_67d78 : decode_any W_67d78 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67d7c : bv 32 := 0xfb010113.
Lemma F_67d7c : fetch_word Asan.M.loaded_segments (0x67d7c : word) = Some W_67d7c.
Proof. vm_refl. Qed.
Lemma D_67d7c : decode_any W_67d7c = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_67d80 : bv 32 := 0x04113423.
Lemma F_67d80 : fetch_word Asan.M.loaded_segments (0x67d80 : word) = Some W_67d80.
Proof. vm_refl. Qed.
Lemma D_67d80 : decode_any W_67d80 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_67d84 : bv 32 := 0x04813023.
Lemma F_67d84 : fetch_word Asan.M.loaded_segments (0x67d84 : word) = Some W_67d84.
Proof. vm_refl. Qed.
Lemma D_67d84 : decode_any W_67d84 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_67d88 : bv 32 := 0x02913c23.
Lemma F_67d88 : fetch_word Asan.M.loaded_segments (0x67d88 : word) = Some W_67d88.
Proof. vm_refl. Qed.
Lemma D_67d88 : decode_any W_67d88 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_67d8c : bv 32 := 0x03213823.
Lemma F_67d8c : fetch_word Asan.M.loaded_segments (0x67d8c : word) = Some W_67d8c.
Proof. vm_refl. Qed.
Lemma D_67d8c : decode_any W_67d8c = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_67d90 : bv 32 := 0x03313423.
Lemma F_67d90 : fetch_word Asan.M.loaded_segments (0x67d90 : word) = Some W_67d90.
Proof. vm_refl. Qed.
Lemma D_67d90 : decode_any W_67d90 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_67d94 : bv 32 := 0x03413023.
Lemma F_67d94 : fetch_word Asan.M.loaded_segments (0x67d94 : word) = Some W_67d94.
Proof. vm_refl. Qed.
Lemma D_67d94 : decode_any W_67d94 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_67d98 : bv 32 := 0x01513c23.
Lemma F_67d98 : fetch_word Asan.M.loaded_segments (0x67d98 : word) = Some W_67d98.
Proof. vm_refl. Qed.
Lemma D_67d98 : decode_any W_67d98 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_67d9c : bv 32 := 0x01613823.
Lemma F_67d9c : fetch_word Asan.M.loaded_segments (0x67d9c : word) = Some W_67d9c.
Proof. vm_refl. Qed.
Lemma D_67d9c : decode_any W_67d9c = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_67da0 : bv 32 := 0x01713423.
Lemma F_67da0 : fetch_word Asan.M.loaded_segments (0x67da0 : word) = Some W_67da0.
Proof. vm_refl. Qed.
Lemma D_67da0 : decode_any W_67da0 = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_67da4 : bv 32 := 0x01813023.
Lemma F_67da4 : fetch_word Asan.M.loaded_segments (0x67da4 : word) = Some W_67da4.
Proof. vm_refl. Qed.
Lemma D_67da4 : decode_any W_67da4 = Some (Store SZ8 2 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67da8 : bv 32 := 0x00078493.
Lemma F_67da8 : fetch_word Asan.M.loaded_segments (0x67da8 : word) = Some W_67da8.
Proof. vm_refl. Qed.
Lemma D_67da8 : decode_any W_67da8 = Some (OpImm ALU_ADD 9 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67dac : bv 32 := 0x00070a93.
Lemma F_67dac : fetch_word Asan.M.loaded_segments (0x67dac : word) = Some W_67dac.
Proof. vm_refl. Qed.
Lemma D_67dac : decode_any W_67dac = Some (OpImm ALU_ADD 21 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67db0 : bv 32 := 0x00068a13.
Lemma F_67db0 : fetch_word Asan.M.loaded_segments (0x67db0 : word) = Some W_67db0.
Proof. vm_refl. Qed.
Lemma D_67db0 : decode_any W_67db0 = Some (OpImm ALU_ADD 20 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67db4 : bv 32 := 0x00060413.
Lemma F_67db4 : fetch_word Asan.M.loaded_segments (0x67db4 : word) = Some W_67db4.
Proof. vm_refl. Qed.
Lemma D_67db4 : decode_any W_67db4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67db8 : bv 32 := 0x00058913.
Lemma F_67db8 : fetch_word Asan.M.loaded_segments (0x67db8 : word) = Some W_67db8.
Proof. vm_refl. Qed.
Lemma D_67db8 : decode_any W_67db8 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67dbc : bv 32 := 0x00050993.
Lemma F_67dbc : fetch_word Asan.M.loaded_segments (0x67dbc : word) = Some W_67dbc.
Proof. vm_refl. Qed.
Lemma D_67dbc : decode_any W_67dbc = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67dc0 : bv 32 := 0x00052423.
Lemma F_67dc0 : fetch_word Asan.M.loaded_segments (0x67dc0 : word) = Some W_67dc0.
Proof. vm_refl. Qed.
Lemma D_67dc0 : decode_any W_67dc0 = Some (Store SZ4 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_67dc4 : bv 32 := 0xb10fe0ef.
Lemma F_67dc4 : fetch_word Asan.M.loaded_segments (0x67dc4 : word) = Some W_67dc4.
Proof. vm_refl. Qed.
Lemma D_67dc4 : decode_any W_67dc4 = Some (Jal 1 2089744, 4%Z).
Proof. vm_refl. Qed.

Definition W_67dc8 : bv 32 := 0x0c050a63.
Lemma F_67dc8 : fetch_word Asan.M.loaded_segments (0x67dc8 : word) = Some W_67dc8.
Proof. vm_refl. Qed.
Lemma D_67dc8 : decode_any W_67dc8 = Some (Branch BC_EQ 10 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_67dcc : bv 32 := 0x219010ef.
Lemma F_67dcc : fetch_word Asan.M.loaded_segments (0x67dcc : word) = Some W_67dcc.
Proof. vm_refl. Qed.
Lemma D_67dcc : decode_any W_67dcc = Some (Jal 1 6680, 4%Z).
Proof. vm_refl. Qed.

Definition W_67dd0 : bv 32 := 0x04050a63.
Lemma F_67dd0 : fetch_word Asan.M.loaded_segments (0x67dd0 : word) = Some W_67dd0.
Proof. vm_refl. Qed.
Lemma D_67dd0 : decode_any W_67dd0 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_67dd4 : bv 32 := 0x7ff50c13.
Lemma F_67dd4 : fetch_word Asan.M.loaded_segments (0x67dd4 : word) = Some W_67dd4.
Proof. vm_refl. Qed.
Lemma D_67dd4 : decode_any W_67dd4 = Some (OpImm ALU_ADD 24 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_67dd8 : bv 32 := 0x461c4583.
Lemma F_67dd8 : fetch_word Asan.M.loaded_segments (0x67dd8 : word) = Some W_67dd8.
Proof. vm_refl. Qed.
Lemma D_67dd8 : decode_any W_67dd8 = Some (Load SZ1 false 11 24 1121, 4%Z).
Proof. vm_refl. Qed.

Definition W_67ddc : bv 32 := 0x00100613.
Lemma F_67ddc : fetch_word Asan.M.loaded_segments (0x67ddc : word) = Some W_67ddc.
Proof. vm_refl. Qed.
Lemma D_67ddc : decode_any W_67ddc = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_67de0 : bv 32 := 0x46cc00a3.
Lemma F_67de0 : fetch_word Asan.M.loaded_segments (0x67de0 : word) = Some W_67de0.
Proof. vm_refl. Qed.
Lemma D_67de0 : decode_any W_67de0 = Some (Store SZ1 24 12 1121, 4%Z).
Proof. vm_refl. Qed.

Definition W_67de4 : bv 32 := 0x0a059a63.
Lemma F_67de4 : fetch_word Asan.M.loaded_segments (0x67de4 : word) = Some W_67de4.
Proof. vm_refl. Qed.
Lemma D_67de4 : decode_any W_67de4 = Some (Branch BC_NE 11 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_67de8 : bv 32 := 0x00050b93.
Lemma F_67de8 : fetch_word Asan.M.loaded_segments (0x67de8 : word) = Some W_67de8.
Proof. vm_refl. Qed.
Lemma D_67de8 : decode_any W_67de8 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67dec : bv 32 := 0x3bd010ef.
Lemma F_67dec : fetch_word Asan.M.loaded_segments (0x67dec : word) = Some W_67dec.
Proof. vm_refl. Qed.
Lemma D_67dec : decode_any W_67dec = Some (Jal 1 7100, 4%Z).
Proof. vm_refl. Qed.

Definition W_67df0 : bv 32 := 0x00050b13.
Lemma F_67df0 : fetch_word Asan.M.loaded_segments (0x67df0 : word) = Some W_67df0.
Proof. vm_refl. Qed.
Lemma D_67df0 : decode_any W_67df0 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67df4 : bv 32 := 0x000b8513.
Lemma F_67df4 : fetch_word Asan.M.loaded_segments (0x67df4 : word) = Some W_67df4.
Proof. vm_refl. Qed.
Lemma D_67df4 : decode_any W_67df4 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67df8 : bv 32 := 0x409010ef.
Lemma F_67df8 : fetch_word Asan.M.loaded_segments (0x67df8 : word) = Some W_67df8.
Proof. vm_refl. Qed.
Lemma D_67df8 : decode_any W_67df8 = Some (Jal 1 7176, 4%Z).
Proof. vm_refl. Qed.

Definition W_67dfc : bv 32 := 0x00050813.
Lemma F_67dfc : fetch_word Asan.M.loaded_segments (0x67dfc : word) = Some W_67dfc.
Proof. vm_refl. Qed.
Lemma D_67dfc : decode_any W_67dfc = Some (OpImm ALU_ADD 16 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e00 : bv 32 := 0x060a8c63.
Lemma F_67e00 : fetch_word Asan.M.loaded_segments (0x67e00 : word) = Some W_67e00.
Proof. vm_refl. Qed.
Lemma D_67e00 : decode_any W_67e00 = Some (Branch BC_EQ 21 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e04 : bv 32 := 0x00100893.
Lemma F_67e04 : fetch_word Asan.M.loaded_segments (0x67e04 : word) = Some W_67e04.
Proof. vm_refl. Qed.
Lemma D_67e04 : decode_any W_67e04 = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e08 : bv 32 := 0x00098513.
Lemma F_67e08 : fetch_word Asan.M.loaded_segments (0x67e08 : word) = Some W_67e08.
Proof. vm_refl. Qed.
Lemma D_67e08 : decode_any W_67e08 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e0c : bv 32 := 0x00048593.
Lemma F_67e0c : fetch_word Asan.M.loaded_segments (0x67e0c : word) = Some W_67e0c.
Proof. vm_refl. Qed.
Lemma D_67e0c : decode_any W_67e0c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e10 : bv 32 := 0x00090613.
Lemma F_67e10 : fetch_word Asan.M.loaded_segments (0x67e10 : word) = Some W_67e10.
Proof. vm_refl. Qed.
Lemma D_67e10 : decode_any W_67e10 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e14 : bv 32 := 0x00040693.
Lemma F_67e14 : fetch_word Asan.M.loaded_segments (0x67e14 : word) = Some W_67e14.
Proof. vm_refl. Qed.
Lemma D_67e14 : decode_any W_67e14 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e18 : bv 32 := 0x00000713.
Lemma F_67e18 : fetch_word Asan.M.loaded_segments (0x67e18 : word) = Some W_67e18.
Proof. vm_refl. Qed.
Lemma D_67e18 : decode_any W_67e18 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e1c : bv 32 := 0x000b0793.
Lemma F_67e1c : fetch_word Asan.M.loaded_segments (0x67e1c : word) = Some W_67e1c.
Proof. vm_refl. Qed.
Lemma D_67e1c : decode_any W_67e1c = Some (OpImm ALU_ADD 15 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e20 : bv 32 := 0x0740006f.
Lemma F_67e20 : fetch_word Asan.M.loaded_segments (0x67e20 : word) = Some W_67e20.
Proof. vm_refl. Qed.
Lemma D_67e20 : decode_any W_67e20 = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e24 : bv 32 := 0x060a9c63.
Lemma F_67e24 : fetch_word Asan.M.loaded_segments (0x67e24 : word) = Some W_67e24.
Proof. vm_refl. Qed.
Lemma D_67e24 : decode_any W_67e24 = Some (Branch BC_NE 21 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e28 : bv 32 := 0x00098513.
Lemma F_67e28 : fetch_word Asan.M.loaded_segments (0x67e28 : word) = Some W_67e28.
Proof. vm_refl. Qed.
Lemma D_67e28 : decode_any W_67e28 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e2c : bv 32 := 0x00048593.
Lemma F_67e2c : fetch_word Asan.M.loaded_segments (0x67e2c : word) = Some W_67e2c.
Proof. vm_refl. Qed.
Lemma D_67e2c : decode_any W_67e2c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e30 : bv 32 := 0x00090613.
Lemma F_67e30 : fetch_word Asan.M.loaded_segments (0x67e30 : word) = Some W_67e30.
Proof. vm_refl. Qed.
Lemma D_67e30 : decode_any W_67e30 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e34 : bv 32 := 0x00040693.
Lemma F_67e34 : fetch_word Asan.M.loaded_segments (0x67e34 : word) = Some W_67e34.
Proof. vm_refl. Qed.
Lemma D_67e34 : decode_any W_67e34 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e38 : bv 32 := 0x000a0713.
Lemma F_67e38 : fetch_word Asan.M.loaded_segments (0x67e38 : word) = Some W_67e38.
Proof. vm_refl. Qed.
Lemma D_67e38 : decode_any W_67e38 = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e3c : bv 32 := 0x00000793.
Lemma F_67e3c : fetch_word Asan.M.loaded_segments (0x67e3c : word) = Some W_67e3c.
Proof. vm_refl. Qed.
Lemma D_67e3c : decode_any W_67e3c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e40 : bv 32 := 0x00000813.
Lemma F_67e40 : fetch_word Asan.M.loaded_segments (0x67e40 : word) = Some W_67e40.
Proof. vm_refl. Qed.
Lemma D_67e40 : decode_any W_67e40 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e44 : bv 32 := 0x00000893.
Lemma F_67e44 : fetch_word Asan.M.loaded_segments (0x67e44 : word) = Some W_67e44.
Proof. vm_refl. Qed.
Lemma D_67e44 : decode_any W_67e44 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e48 : bv 32 := 0x04813083.
Lemma F_67e48 : fetch_word Asan.M.loaded_segments (0x67e48 : word) = Some W_67e48.
Proof. vm_refl. Qed.
Lemma D_67e48 : decode_any W_67e48 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e4c : bv 32 := 0x04013403.
Lemma F_67e4c : fetch_word Asan.M.loaded_segments (0x67e4c : word) = Some W_67e4c.
Proof. vm_refl. Qed.
Lemma D_67e4c : decode_any W_67e4c = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e50 : bv 32 := 0x03813483.
Lemma F_67e50 : fetch_word Asan.M.loaded_segments (0x67e50 : word) = Some W_67e50.
Proof. vm_refl. Qed.
Lemma D_67e50 : decode_any W_67e50 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e54 : bv 32 := 0x03013903.
Lemma F_67e54 : fetch_word Asan.M.loaded_segments (0x67e54 : word) = Some W_67e54.
Proof. vm_refl. Qed.
Lemma D_67e54 : decode_any W_67e54 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e58 : bv 32 := 0x02813983.
Lemma F_67e58 : fetch_word Asan.M.loaded_segments (0x67e58 : word) = Some W_67e58.
Proof. vm_refl. Qed.
Lemma D_67e58 : decode_any W_67e58 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e5c : bv 32 := 0x02013a03.
Lemma F_67e5c : fetch_word Asan.M.loaded_segments (0x67e5c : word) = Some W_67e5c.
Proof. vm_refl. Qed.
Lemma D_67e5c : decode_any W_67e5c = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e60 : bv 32 := 0x01813a83.
Lemma F_67e60 : fetch_word Asan.M.loaded_segments (0x67e60 : word) = Some W_67e60.
Proof. vm_refl. Qed.
Lemma D_67e60 : decode_any W_67e60 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e64 : bv 32 := 0x01013b03.
Lemma F_67e64 : fetch_word Asan.M.loaded_segments (0x67e64 : word) = Some W_67e64.
Proof. vm_refl. Qed.
Lemma D_67e64 : decode_any W_67e64 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e68 : bv 32 := 0x00813b83.
Lemma F_67e68 : fetch_word Asan.M.loaded_segments (0x67e68 : word) = Some W_67e68.
Proof. vm_refl. Qed.
Lemma D_67e68 : decode_any W_67e68 = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e6c : bv 32 := 0x00013c03.
Lemma F_67e6c : fetch_word Asan.M.loaded_segments (0x67e6c : word) = Some W_67e6c.
Proof. vm_refl. Qed.
Lemma D_67e6c : decode_any W_67e6c = Some (Load SZ8 true 24 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e70 : bv 32 := 0x05010113.
Lemma F_67e70 : fetch_word Asan.M.loaded_segments (0x67e70 : word) = Some W_67e70.
Proof. vm_refl. Qed.
Lemma D_67e70 : decode_any W_67e70 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e74 : bv 32 := 0x01c1906f.
Lemma F_67e74 : fetch_word Asan.M.loaded_segments (0x67e74 : word) = Some W_67e74.
Proof. vm_refl. Qed.
Lemma D_67e74 : decode_any W_67e74 = Some (Jal 0 102428, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e78 : bv 32 := 0x00098513.
Lemma F_67e78 : fetch_word Asan.M.loaded_segments (0x67e78 : word) = Some W_67e78.
Proof. vm_refl. Qed.
Lemma D_67e78 : decode_any W_67e78 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e7c : bv 32 := 0x00048593.
Lemma F_67e7c : fetch_word Asan.M.loaded_segments (0x67e7c : word) = Some W_67e7c.
Proof. vm_refl. Qed.
Lemma D_67e7c : decode_any W_67e7c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e80 : bv 32 := 0x00090613.
Lemma F_67e80 : fetch_word Asan.M.loaded_segments (0x67e80 : word) = Some W_67e80.
Proof. vm_refl. Qed.
Lemma D_67e80 : decode_any W_67e80 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e84 : bv 32 := 0x00040693.
Lemma F_67e84 : fetch_word Asan.M.loaded_segments (0x67e84 : word) = Some W_67e84.
Proof. vm_refl. Qed.
Lemma D_67e84 : decode_any W_67e84 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e88 : bv 32 := 0x000a0713.
Lemma F_67e88 : fetch_word Asan.M.loaded_segments (0x67e88 : word) = Some W_67e88.
Proof. vm_refl. Qed.
Lemma D_67e88 : decode_any W_67e88 = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e8c : bv 32 := 0x000b0793.
Lemma F_67e8c : fetch_word Asan.M.loaded_segments (0x67e8c : word) = Some W_67e8c.
Proof. vm_refl. Qed.
Lemma D_67e8c : decode_any W_67e8c = Some (OpImm ALU_ADD 15 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e90 : bv 32 := 0x00000893.
Lemma F_67e90 : fetch_word Asan.M.loaded_segments (0x67e90 : word) = Some W_67e90.
Proof. vm_refl. Qed.
Lemma D_67e90 : decode_any W_67e90 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e94 : bv 32 := 0x7fd180ef.
Lemma F_67e94 : fetch_word Asan.M.loaded_segments (0x67e94 : word) = Some W_67e94.
Proof. vm_refl. Qed.
Lemma D_67e94 : decode_any W_67e94 = Some (Jal 1 102396, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e98 : bv 32 := 0x460c00a3.
Lemma F_67e98 : fetch_word Asan.M.loaded_segments (0x67e98 : word) = Some W_67e98.
Proof. vm_refl. Qed.
Lemma D_67e98 : decode_any W_67e98 = Some (Store SZ1 24 0 1121, 4%Z).
Proof. vm_refl. Qed.

Definition W_67e9c : bv 32 := 0x04813083.
Lemma F_67e9c : fetch_word Asan.M.loaded_segments (0x67e9c : word) = Some W_67e9c.
Proof. vm_refl. Qed.
Lemma D_67e9c : decode_any W_67e9c = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_67ea0 : bv 32 := 0x04013403.
Lemma F_67ea0 : fetch_word Asan.M.loaded_segments (0x67ea0 : word) = Some W_67ea0.
Proof. vm_refl. Qed.
Lemma D_67ea0 : decode_any W_67ea0 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_67ea4 : bv 32 := 0x03813483.
Lemma F_67ea4 : fetch_word Asan.M.loaded_segments (0x67ea4 : word) = Some W_67ea4.
Proof. vm_refl. Qed.
Lemma D_67ea4 : decode_any W_67ea4 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_67ea8 : bv 32 := 0x03013903.
Lemma F_67ea8 : fetch_word Asan.M.loaded_segments (0x67ea8 : word) = Some W_67ea8.
Proof. vm_refl. Qed.
Lemma D_67ea8 : decode_any W_67ea8 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_67eac : bv 32 := 0x02813983.
Lemma F_67eac : fetch_word Asan.M.loaded_segments (0x67eac : word) = Some W_67eac.
Proof. vm_refl. Qed.
Lemma D_67eac : decode_any W_67eac = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_67eb0 : bv 32 := 0x02013a03.
Lemma F_67eb0 : fetch_word Asan.M.loaded_segments (0x67eb0 : word) = Some W_67eb0.
Proof. vm_refl. Qed.
Lemma D_67eb0 : decode_any W_67eb0 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_67eb4 : bv 32 := 0x01813a83.
Lemma F_67eb4 : fetch_word Asan.M.loaded_segments (0x67eb4 : word) = Some W_67eb4.
Proof. vm_refl. Qed.
Lemma D_67eb4 : decode_any W_67eb4 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_67eb8 : bv 32 := 0x01013b03.
Lemma F_67eb8 : fetch_word Asan.M.loaded_segments (0x67eb8 : word) = Some W_67eb8.
Proof. vm_refl. Qed.
Lemma D_67eb8 : decode_any W_67eb8 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_67ebc : bv 32 := 0x00813b83.
Lemma F_67ebc : fetch_word Asan.M.loaded_segments (0x67ebc : word) = Some W_67ebc.
Proof. vm_refl. Qed.
Lemma D_67ebc : decode_any W_67ebc = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_67ec0 : bv 32 := 0x00013c03.
Lemma F_67ec0 : fetch_word Asan.M.loaded_segments (0x67ec0 : word) = Some W_67ec0.
Proof. vm_refl. Qed.
Lemma D_67ec0 : decode_any W_67ec0 = Some (Load SZ8 true 24 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_67ec4 : bv 32 := 0x05010113.
Lemma F_67ec4 : fetch_word Asan.M.loaded_segments (0x67ec4 : word) = Some W_67ec4.
Proof. vm_refl. Qed.
Lemma D_67ec4 : decode_any W_67ec4 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_67ec8 : bv 32 := 0x00008067.
Lemma F_67ec8 : fetch_word Asan.M.loaded_segments (0x67ec8 : word) = Some W_67ec8.
Proof. vm_refl. Qed.
Lemma D_67ec8 : decode_any W_67ec8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
