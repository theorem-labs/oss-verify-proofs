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

Definition W_63d84 : bv 32 := 0x81010113.
Lemma F_63d84 : fetch_word Asan.M.loaded_segments (0x63dd4 : word) = Some W_63d84.
Proof. vm_refl. Qed.
Lemma D_63d84 : decode_any W_63d84 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_63d88 : bv 32 := 0x7e113423.
Lemma F_63d88 : fetch_word Asan.M.loaded_segments (0x63dd8 : word) = Some W_63d88.
Proof. vm_refl. Qed.
Lemma D_63d88 : decode_any W_63d88 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_63d8c : bv 32 := 0x7e813023.
Lemma F_63d8c : fetch_word Asan.M.loaded_segments (0x63ddc : word) = Some W_63d8c.
Proof. vm_refl. Qed.
Lemma D_63d8c : decode_any W_63d8c = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_63d90 : bv 32 := 0x7c913c23.
Lemma F_63d90 : fetch_word Asan.M.loaded_segments (0x63de0 : word) = Some W_63d90.
Proof. vm_refl. Qed.
Lemma D_63d90 : decode_any W_63d90 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_63d94 : bv 32 := 0x7d213823.
Lemma F_63d94 : fetch_word Asan.M.loaded_segments (0x63de4 : word) = Some W_63d94.
Proof. vm_refl. Qed.
Lemma D_63d94 : decode_any W_63d94 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_63d98 : bv 32 := 0x7d313423.
Lemma F_63d98 : fetch_word Asan.M.loaded_segments (0x63de8 : word) = Some W_63d98.
Proof. vm_refl. Qed.
Lemma D_63d98 : decode_any W_63d98 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_63d9c : bv 32 := 0x7d413023.
Lemma F_63d9c : fetch_word Asan.M.loaded_segments (0x63dec : word) = Some W_63d9c.
Proof. vm_refl. Qed.
Lemma D_63d9c : decode_any W_63d9c = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_63da0 : bv 32 := 0x7b513c23.
Lemma F_63da0 : fetch_word Asan.M.loaded_segments (0x63df0 : word) = Some W_63da0.
Proof. vm_refl. Qed.
Lemma D_63da0 : decode_any W_63da0 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_63da4 : bv 32 := 0x7b613823.
Lemma F_63da4 : fetch_word Asan.M.loaded_segments (0x63df4 : word) = Some W_63da4.
Proof. vm_refl. Qed.
Lemma D_63da4 : decode_any W_63da4 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_63da8 : bv 32 := 0x7f010413.
Lemma F_63da8 : fetch_word Asan.M.loaded_segments (0x63df8 : word) = Some W_63da8.
Proof. vm_refl. Qed.
Lemma D_63da8 : decode_any W_63da8 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_63dac : bv 32 := 0xf9010113.
Lemma F_63dac : fetch_word Asan.M.loaded_segments (0x63dfc : word) = Some W_63dac.
Proof. vm_refl. Qed.
Lemma D_63dac : decode_any W_63dac = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_63db0 : bv 32 := 0x00050913.
Lemma F_63db0 : fetch_word Asan.M.loaded_segments (0x63e00 : word) = Some W_63db0.
Proof. vm_refl. Qed.
Lemma D_63db0 : decode_any W_63db0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63db4 : bv 32 := 0x5551c0ef.
Lemma F_63db4 : fetch_word Asan.M.loaded_segments (0x63e04 : word) = Some W_63db4.
Proof. vm_refl. Qed.
Lemma D_63db4 : decode_any W_63db4 = Some (Jal 1 118100, 4%Z).
Proof. vm_refl. Qed.

Definition W_63db8 : bv 32 := 0x0a050863.
Lemma F_63db8 : fetch_word Asan.M.loaded_segments (0x63e08 : word) = Some W_63db8.
Proof. vm_refl. Qed.
Lemma D_63db8 : decode_any W_63db8 = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_63dbc : bv 32 := 0x45d1d0ef.
Lemma F_63dbc : fetch_word Asan.M.loaded_segments (0x63e0c : word) = Some W_63dbc.
Proof. vm_refl. Qed.
Lemma D_63dbc : decode_any W_63dbc = Some (Jal 1 121948, 4%Z).
Proof. vm_refl. Qed.

Definition W_63dc0 : bv 32 := 0x000d7597.
Lemma F_63dc0 : fetch_word Asan.M.loaded_segments (0x63e10 : word) = Some W_63dc0.
Proof. vm_refl. Qed.
Lemma D_63dc0 : decode_any W_63dc0 = Some (Auipc 11 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_63dc4 : bv 32 := 0x1c05b583.
Lemma F_63dc4 : fetch_word Asan.M.loaded_segments (0x63e14 : word) = Some W_63dc4.
Proof. vm_refl. Qed.
Lemma D_63dc4 : decode_any W_63dc4 = Some (Load SZ8 true 11 11 448, 4%Z).
Proof. vm_refl. Qed.

Definition W_63dc8 : bv 32 := 0x00050493.
Lemma F_63dc8 : fetch_word Asan.M.loaded_segments (0x63e18 : word) = Some W_63dc8.
Proof. vm_refl. Qed.
Lemma D_63dc8 : decode_any W_63dc8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63dcc : bv 32 := 0x00090513.
Lemma F_63dcc : fetch_word Asan.M.loaded_segments (0x63e1c : word) = Some W_63dcc.
Proof. vm_refl. Qed.
Lemma D_63dcc : decode_any W_63dcc = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63dd0 : bv 32 := 0x000580e7.
Lemma F_63dd0 : fetch_word Asan.M.loaded_segments (0x63e20 : word) = Some W_63dd0.
Proof. vm_refl. Qed.
Lemma D_63dd0 : decode_any W_63dd0 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63dd4 : bv 32 := 0x06048463.
Lemma F_63dd4 : fetch_word Asan.M.loaded_segments (0x63e24 : word) = Some W_63dd4.
Proof. vm_refl. Qed.
Lemma D_63dd4 : decode_any W_63dd4 = Some (Branch BC_EQ 9 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_63dd8 : bv 32 := 0x000d5597.
Lemma F_63dd8 : fetch_word Asan.M.loaded_segments (0x63e28 : word) = Some W_63dd8.
Proof. vm_refl. Qed.
Lemma D_63dd8 : decode_any W_63dd8 = Some (Auipc 11 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ddc : bv 32 := 0x3805b983.
Lemma F_63ddc : fetch_word Asan.M.loaded_segments (0x63e2c : word) = Some W_63ddc.
Proof. vm_refl. Qed.
Lemma D_63ddc : decode_any W_63ddc = Some (Load SZ8 true 19 11 896, 4%Z).
Proof. vm_refl. Qed.

Definition W_63de0 : bv 32 := 0x0fb9c583.
Lemma F_63de0 : fetch_word Asan.M.loaded_segments (0x63e30 : word) = Some W_63de0.
Proof. vm_refl. Qed.
Lemma D_63de0 : decode_any W_63de0 = Some (Load SZ1 false 11 19 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_63de4 : bv 32 := 0x04058c63.
Lemma F_63de4 : fetch_word Asan.M.loaded_segments (0x63e34 : word) = Some W_63de4.
Proof. vm_refl. Qed.
Lemma D_63de4 : decode_any W_63de4 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_63de8 : bv 32 := 0x00150493.
Lemma F_63de8 : fetch_word Asan.M.loaded_segments (0x63e38 : word) = Some W_63de8.
Proof. vm_refl. Qed.
Lemma D_63de8 : decode_any W_63de8 = Some (OpImm ALU_ADD 9 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_63dec : bv 32 := 0xfff94593.
Lemma F_63dec : fetch_word Asan.M.loaded_segments (0x63e3c : word) = Some W_63dec.
Proof. vm_refl. Qed.
Lemma D_63dec : decode_any W_63dec = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_63df0 : bv 32 := 0x80040a13.
Lemma F_63df0 : fetch_word Asan.M.loaded_segments (0x63e40 : word) = Some W_63df0.
Proof. vm_refl. Qed.
Lemma D_63df0 : decode_any W_63df0 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_63df4 : bv 32 := 0xfa8a0a13.
Lemma F_63df4 : fetch_word Asan.M.loaded_segments (0x63e44 : word) = Some W_63df4.
Proof. vm_refl. Qed.
Lemma D_63df4 : decode_any W_63df4 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_63df8 : bv 32 := 0x0a95e063.
Lemma F_63df8 : fetch_word Asan.M.loaded_segments (0x63e48 : word) = Some W_63df8.
Proof. vm_refl. Qed.
Lemma D_63df8 : decode_any W_63df8 = Some (Branch BC_LTU 11 9 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_63dfc : bv 32 := 0x04000593.
Lemma F_63dfc : fetch_word Asan.M.loaded_segments (0x63e4c : word) = Some W_63dfc.
Proof. vm_refl. Qed.
Lemma D_63dfc : decode_any W_63dfc = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e00 : bv 32 := 0x10b57263.
Lemma F_63e00 : fetch_word Asan.M.loaded_segments (0x63e50 : word) = Some W_63e00.
Proof. vm_refl. Qed.
Lemma D_63e00 : decode_any W_63e00 = Some (Branch BC_GEU 10 11 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e04 : bv 32 := 0x000d5597.
Lemma F_63e04 : fetch_word Asan.M.loaded_segments (0x63e54 : word) = Some W_63e04.
Proof. vm_refl. Qed.
Lemma D_63e04 : decode_any W_63e04 = Some (Auipc 11 213, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e08 : bv 32 := 0x3645b583.
Lemma F_63e08 : fetch_word Asan.M.loaded_segments (0x63e58 : word) = Some W_63e08.
Proof. vm_refl. Qed.
Lemma D_63e08 : decode_any W_63e08 = Some (Load SZ8 true 11 11 868, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e0c : bv 32 := 0x0005b603.
Lemma F_63e0c : fetch_word Asan.M.loaded_segments (0x63e5c : word) = Some W_63e0c.
Proof. vm_refl. Qed.
Lemma D_63e0c : decode_any W_63e0c = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e10 : bv 32 := 0x012506b3.
Lemma F_63e10 : fetch_word Asan.M.loaded_segments (0x63e60 : word) = Some W_63e10.
Proof. vm_refl. Qed.
Lemma D_63e10 : decode_any W_63e10 = Some (Op ALU_ADD 13 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e14 : bv 32 := 0x00395593.
Lemma F_63e14 : fetch_word Asan.M.loaded_segments (0x63e64 : word) = Some W_63e14.
Proof. vm_refl. Qed.
Lemma D_63e14 : decode_any W_63e14 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e18 : bv 32 := 0x0036d713.
Lemma F_63e18 : fetch_word Asan.M.loaded_segments (0x63e68 : word) = Some W_63e18.
Proof. vm_refl. Qed.
Lemma D_63e18 : decode_any W_63e18 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e1c : bv 32 := 0x00b605b3.
Lemma F_63e1c : fetch_word Asan.M.loaded_segments (0x63e6c : word) = Some W_63e1c.
Proof. vm_refl. Qed.
Lemma D_63e1c : decode_any W_63e1c = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e20 : bv 32 := 0x00e60633.
Lemma F_63e20 : fetch_word Asan.M.loaded_segments (0x63e70 : word) = Some W_63e20.
Proof. vm_refl. Qed.
Lemma D_63e20 : decode_any W_63e20 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e24 : bv 32 := 0xff85f713.
Lemma F_63e24 : fetch_word Asan.M.loaded_segments (0x63e74 : word) = Some W_63e24.
Proof. vm_refl. Qed.
Lemma D_63e24 : decode_any W_63e24 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e28 : bv 32 := 0xff867793.
Lemma F_63e28 : fetch_word Asan.M.loaded_segments (0x63e78 : word) = Some W_63e28.
Proof. vm_refl. Qed.
Lemma D_63e28 : decode_any W_63e28 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e2c : bv 32 := 0x00073703.
Lemma F_63e2c : fetch_word Asan.M.loaded_segments (0x63e7c : word) = Some W_63e2c.
Proof. vm_refl. Qed.
Lemma D_63e2c : decode_any W_63e2c = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e30 : bv 32 := 0x0007b783.
Lemma F_63e30 : fetch_word Asan.M.loaded_segments (0x63e80 : word) = Some W_63e30.
Proof. vm_refl. Qed.
Lemma D_63e30 : decode_any W_63e30 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e34 : bv 32 := 0x00e7e733.
Lemma F_63e34 : fetch_word Asan.M.loaded_segments (0x63e84 : word) = Some W_63e34.
Proof. vm_refl. Qed.
Lemma D_63e34 : decode_any W_63e34 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e38 : bv 32 := 0x0c071e63.
Lemma F_63e38 : fetch_word Asan.M.loaded_segments (0x63e88 : word) = Some W_63e38.
Proof. vm_refl. Qed.
Lemma D_63e38 : decode_any W_63e38 = Some (Branch BC_NE 14 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e3c : bv 32 := 0x07010113.
Lemma F_63e3c : fetch_word Asan.M.loaded_segments (0x63e8c : word) = Some W_63e3c.
Proof. vm_refl. Qed.
Lemma D_63e3c : decode_any W_63e3c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e40 : bv 32 := 0x7e813083.
Lemma F_63e40 : fetch_word Asan.M.loaded_segments (0x63e90 : word) = Some W_63e40.
Proof. vm_refl. Qed.
Lemma D_63e40 : decode_any W_63e40 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e44 : bv 32 := 0x7e013403.
Lemma F_63e44 : fetch_word Asan.M.loaded_segments (0x63e94 : word) = Some W_63e44.
Proof. vm_refl. Qed.
Lemma D_63e44 : decode_any W_63e44 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e48 : bv 32 := 0x7d813483.
Lemma F_63e48 : fetch_word Asan.M.loaded_segments (0x63e98 : word) = Some W_63e48.
Proof. vm_refl. Qed.
Lemma D_63e48 : decode_any W_63e48 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e4c : bv 32 := 0x7d013903.
Lemma F_63e4c : fetch_word Asan.M.loaded_segments (0x63e9c : word) = Some W_63e4c.
Proof. vm_refl. Qed.
Lemma D_63e4c : decode_any W_63e4c = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e50 : bv 32 := 0x7c813983.
Lemma F_63e50 : fetch_word Asan.M.loaded_segments (0x63ea0 : word) = Some W_63e50.
Proof. vm_refl. Qed.
Lemma D_63e50 : decode_any W_63e50 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e54 : bv 32 := 0x7c013a03.
Lemma F_63e54 : fetch_word Asan.M.loaded_segments (0x63ea4 : word) = Some W_63e54.
Proof. vm_refl. Qed.
Lemma D_63e54 : decode_any W_63e54 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e58 : bv 32 := 0x7b813a83.
Lemma F_63e58 : fetch_word Asan.M.loaded_segments (0x63ea8 : word) = Some W_63e58.
Proof. vm_refl. Qed.
Lemma D_63e58 : decode_any W_63e58 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e5c : bv 32 := 0x7b013b03.
Lemma F_63e5c : fetch_word Asan.M.loaded_segments (0x63eac : word) = Some W_63e5c.
Proof. vm_refl. Qed.
Lemma D_63e5c : decode_any W_63e5c = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e60 : bv 32 := 0x7f010113.
Lemma F_63e60 : fetch_word Asan.M.loaded_segments (0x63eb0 : word) = Some W_63e60.
Proof. vm_refl. Qed.
Lemma D_63e60 : decode_any W_63e60 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e64 : bv 32 := 0x00008067.
Lemma F_63e64 : fetch_word Asan.M.loaded_segments (0x63eb4 : word) = Some W_63e64.
Proof. vm_refl. Qed.
Lemma D_63e64 : decode_any W_63e64 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f04 : bv 32 := 0x00050a93.
Lemma F_63f04 : fetch_word Asan.M.loaded_segments (0x63f54 : word) = Some W_63f04.
Proof. vm_refl. Qed.
Lemma D_63f04 : decode_any W_63f04 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f08 : bv 32 := 0x04049263.
Lemma F_63f08 : fetch_word Asan.M.loaded_segments (0x63f58 : word) = Some W_63f08.
Proof. vm_refl. Qed.
Lemma D_63f08 : decode_any W_63f08 = Some (Branch BC_NE 9 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f14 : bv 32 := 0x00050a93.
Lemma F_63f14 : fetch_word Asan.M.loaded_segments (0x63f64 : word) = Some W_63f14.
Proof. vm_refl. Qed.
Lemma D_63f14 : decode_any W_63f14 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f18 : bv 32 := 0x00060503.
Lemma F_63f18 : fetch_word Asan.M.loaded_segments (0x63f68 : word) = Some W_63f18.
Proof. vm_refl. Qed.
Lemma D_63f18 : decode_any W_63f18 = Some (Load SZ1 true 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f1c : bv 32 := 0x0076f693.
Lemma F_63f1c : fetch_word Asan.M.loaded_segments (0x63f6c : word) = Some W_63f1c.
Proof. vm_refl. Qed.
Lemma D_63f1c : decode_any W_63f1c = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f20 : bv 32 := 0x00a03733.
Lemma F_63f20 : fetch_word Asan.M.loaded_segments (0x63f70 : word) = Some W_63f20.
Proof. vm_refl. Qed.
Lemma D_63f20 : decode_any W_63f20 = Some (Op ALU_SLTU 14 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f24 : bv 32 := 0x00a6a533.
Lemma F_63f24 : fetch_word Asan.M.loaded_segments (0x63f74 : word) = Some W_63f24.
Proof. vm_refl. Qed.
Lemma D_63f24 : decode_any W_63f24 = Some (Op ALU_SLT 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f28 : bv 32 := 0x00154513.
Lemma F_63f28 : fetch_word Asan.M.loaded_segments (0x63f78 : word) = Some W_63f28.
Proof. vm_refl. Qed.
Lemma D_63f28 : decode_any W_63f28 = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f2c : bv 32 := 0x00a77533.
Lemma F_63f2c : fetch_word Asan.M.loaded_segments (0x63f7c : word) = Some W_63f2c.
Proof. vm_refl. Qed.
Lemma D_63f2c : decode_any W_63f2c = Some (Op ALU_AND 10 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f30 : bv 32 := 0x00c5fa63.
Lemma F_63f30 : fetch_word Asan.M.loaded_segments (0x63f80 : word) = Some W_63f30.
Proof. vm_refl. Qed.
Lemma D_63f30 : decode_any W_63f30 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f34 : bv 32 := 0x0005c683.
Lemma F_63f34 : fetch_word Asan.M.loaded_segments (0x63f84 : word) = Some W_63f34.
Proof. vm_refl. Qed.
Lemma D_63f34 : decode_any W_63f34 = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f38 : bv 32 := 0x00158593.
Lemma F_63f38 : fetch_word Asan.M.loaded_segments (0x63f88 : word) = Some W_63f38.
Proof. vm_refl. Qed.
Lemma D_63f38 : decode_any W_63f38 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f3c : bv 32 := 0x00a6e533.
Lemma F_63f3c : fetch_word Asan.M.loaded_segments (0x63f8c : word) = Some W_63f3c.
Proof. vm_refl. Qed.
Lemma D_63f3c : decode_any W_63f3c = Some (Op ALU_OR 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f40 : bv 32 := 0xfec59ae3.
Lemma F_63f40 : fetch_word Asan.M.loaded_segments (0x63f90 : word) = Some W_63f40.
Proof. vm_refl. Qed.
Lemma D_63f40 : decode_any W_63f40 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f44 : bv 32 := 0x0ff57513.
Lemma F_63f44 : fetch_word Asan.M.loaded_segments (0x63f94 : word) = Some W_63f44.
Proof. vm_refl. Qed.
Lemma D_63f44 : decode_any W_63f44 = Some (OpImm ALU_AND 10 10 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f48 : bv 32 := 0x0c050463.
Lemma F_63f48 : fetch_word Asan.M.loaded_segments (0x63f98 : word) = Some W_63f48.
Proof. vm_refl. Qed.
Lemma D_63f48 : decode_any W_63f48 = Some (Branch BC_EQ 10 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f4c : bv 32 := 0x00090513.
Lemma F_63f4c : fetch_word Asan.M.loaded_segments (0x63f9c : word) = Some W_63f4c.
Proof. vm_refl. Qed.
Lemma D_63f4c : decode_any W_63f4c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f50 : bv 32 := 0x00048593.
Lemma F_63f50 : fetch_word Asan.M.loaded_segments (0x63fa0 : word) = Some W_63f50.
Proof. vm_refl. Qed.
Lemma D_63f50 : decode_any W_63f50 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f54 : bv 32 := 0x6a1170ef.
Lemma F_63f54 : fetch_word Asan.M.loaded_segments (0x63fa4 : word) = Some W_63f54.
Proof. vm_refl. Qed.
Lemma D_63f54 : decode_any W_63f54 = Some (Jal 1 97952, 4%Z).
Proof. vm_refl. Qed.

Definition W_63f58 : bv 32 := 0x0a050c63.
Lemma F_63f58 : fetch_word Asan.M.loaded_segments (0x63fa8 : word) = Some W_63f58.
Proof. vm_refl. Qed.
Lemma D_63f58 : decode_any W_63f58 = Some (Branch BC_EQ 10 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_64010 : bv 32 := 0x000a8513.
Lemma F_64010 : fetch_word Asan.M.loaded_segments (0x64060 : word) = Some W_64010.
Proof. vm_refl. Qed.
Lemma D_64010 : decode_any W_64010 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64014 : bv 32 := 0xe29ff06f.
Lemma F_64014 : fetch_word Asan.M.loaded_segments (0x64064 : word) = Some W_64014.
Proof. vm_refl. Qed.
Lemma D_64014 : decode_any W_64014 = Some (Jal 0 2096680, 4%Z).
Proof. vm_refl. Qed.
