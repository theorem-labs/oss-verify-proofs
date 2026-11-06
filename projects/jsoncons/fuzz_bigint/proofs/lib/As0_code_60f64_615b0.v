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

Definition W_60f64 : bv 32 := 0x0007c517.
Lemma F_60f64 : fetch_word Asan.M.loaded_segments (0x60f64 : word) = Some W_60f64.
Proof. vm_refl. Qed.
Lemma D_60f64 : decode_any W_60f64 = Some (Auipc 10 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_60f68 : bv 32 := 0x43850503.
Lemma F_60f68 : fetch_word Asan.M.loaded_segments (0x60f68 : word) = Some W_60f68.
Proof. vm_refl. Qed.
Lemma D_60f68 : decode_any W_60f68 = Some (Load SZ1 true 10 10 1080, 4%Z).
Proof. vm_refl. Qed.

Definition W_60f6c : bv 32 := 0x0230000f.
Lemma F_60f6c : fetch_word Asan.M.loaded_segments (0x60f6c : word) = Some W_60f6c.
Proof. vm_refl. Qed.
Lemma D_60f6c : decode_any W_60f6c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60f70 : bv 32 := 0x00a03533.
Lemma F_60f70 : fetch_word Asan.M.loaded_segments (0x60f70 : word) = Some W_60f70.
Proof. vm_refl. Qed.
Lemma D_60f70 : decode_any W_60f70 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_60f74 : bv 32 := 0x00008067.
Lemma F_60f74 : fetch_word Asan.M.loaded_segments (0x60f74 : word) = Some W_60f74.
Proof. vm_refl. Qed.
Lemma D_60f74 : decode_any W_60f74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60f78 : bv 32 := 0xfc010113.
Lemma F_60f78 : fetch_word Asan.M.loaded_segments (0x60f78 : word) = Some W_60f78.
Proof. vm_refl. Qed.
Lemma D_60f78 : decode_any W_60f78 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_60f7c : bv 32 := 0x02113c23.
Lemma F_60f7c : fetch_word Asan.M.loaded_segments (0x60f7c : word) = Some W_60f7c.
Proof. vm_refl. Qed.
Lemma D_60f7c : decode_any W_60f7c = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_60f80 : bv 32 := 0x02813823.
Lemma F_60f80 : fetch_word Asan.M.loaded_segments (0x60f80 : word) = Some W_60f80.
Proof. vm_refl. Qed.
Lemma D_60f80 : decode_any W_60f80 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_60f84 : bv 32 := 0x02913423.
Lemma F_60f84 : fetch_word Asan.M.loaded_segments (0x60f84 : word) = Some W_60f84.
Proof. vm_refl. Qed.
Lemma D_60f84 : decode_any W_60f84 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_60f88 : bv 32 := 0x03213023.
Lemma F_60f88 : fetch_word Asan.M.loaded_segments (0x60f88 : word) = Some W_60f88.
Proof. vm_refl. Qed.
Lemma D_60f88 : decode_any W_60f88 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_60f8c : bv 32 := 0x01313c23.
Lemma F_60f8c : fetch_word Asan.M.loaded_segments (0x60f8c : word) = Some W_60f8c.
Proof. vm_refl. Qed.
Lemma D_60f8c : decode_any W_60f8c = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_60f90 : bv 32 := 0x01413823.
Lemma F_60f90 : fetch_word Asan.M.loaded_segments (0x60f90 : word) = Some W_60f90.
Proof. vm_refl. Qed.
Lemma D_60f90 : decode_any W_60f90 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_60f94 : bv 32 := 0x01513423.
Lemma F_60f94 : fetch_word Asan.M.loaded_segments (0x60f94 : word) = Some W_60f94.
Proof. vm_refl. Qed.
Lemma D_60f94 : decode_any W_60f94 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_60f98 : bv 32 := 0x00060a63.
Lemma F_60f98 : fetch_word Asan.M.loaded_segments (0x60f98 : word) = Some W_60f98.
Proof. vm_refl. Qed.
Lemma D_60f98 : decode_any W_60f98 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_60f9c : bv 32 := 0x0007c697.
Lemma F_60f9c : fetch_word Asan.M.loaded_segments (0x60f9c : word) = Some W_60f9c.
Proof. vm_refl. Qed.
Lemma D_60f9c : decode_any W_60f9c = Some (Auipc 13 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_60fa0 : bv 32 := 0x40068683.
Lemma F_60fa0 : fetch_word Asan.M.loaded_segments (0x60fa0 : word) = Some W_60fa0.
Proof. vm_refl. Qed.
Lemma D_60fa0 : decode_any W_60fa0 = Some (Load SZ1 true 13 13 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_60fa4 : bv 32 := 0x0230000f.
Lemma F_60fa4 : fetch_word Asan.M.loaded_segments (0x60fa4 : word) = Some W_60fa4.
Proof. vm_refl. Qed.
Lemma D_60fa4 : decode_any W_60fa4 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60fa8 : bv 32 := 0x0a068a63.
Lemma F_60fa8 : fetch_word Asan.M.loaded_segments (0x60fa8 : word) = Some W_60fa8.
Proof. vm_refl. Qed.
Lemma D_60fa8 : decode_any W_60fa8 = Some (Branch BC_EQ 13 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_60fac : bv 32 := 0x00757693.
Lemma F_60fac : fetch_word Asan.M.loaded_segments (0x60fac : word) = Some W_60fac.
Proof. vm_refl. Qed.
Lemma D_60fac : decode_any W_60fac = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_60fb0 : bv 32 := 0x42069863.
Lemma F_60fb0 : fetch_word Asan.M.loaded_segments (0x60fb0 : word) = Some W_60fb0.
Proof. vm_refl. Qed.
Lemma D_60fb0 : decode_any W_60fb0 = Some (Branch BC_NE 13 0 1072, 4%Z).
Proof. vm_refl. Qed.

Definition W_60fb4 : bv 32 := 0x00075697.
Lemma F_60fb4 : fetch_word Asan.M.loaded_segments (0x60fb4 : word) = Some W_60fb4.
Proof. vm_refl. Qed.
Lemma D_60fb4 : decode_any W_60fb4 = Some (Auipc 13 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_60fb8 : bv 32 := 0x9046b683.
Lemma F_60fb8 : fetch_word Asan.M.loaded_segments (0x60fb8 : word) = Some W_60fb8.
Proof. vm_refl. Qed.
Lemma D_60fb8 : decode_any W_60fb8 = Some (Load SZ8 true 13 13 2308, 4%Z).
Proof. vm_refl. Qed.

Definition W_60fbc : bv 32 := 0x0006b483.
Lemma F_60fbc : fetch_word Asan.M.loaded_segments (0x60fbc : word) = Some W_60fbc.
Proof. vm_refl. Qed.
Lemma D_60fbc : decode_any W_60fbc = Some (Load SZ8 true 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60fc0 : bv 32 := 0xfff48693.
Lemma F_60fc0 : fetch_word Asan.M.loaded_segments (0x60fc0 : word) = Some W_60fc0.
Proof. vm_refl. Qed.
Lemma D_60fc0 : decode_any W_60fc0 = Some (OpImm ALU_ADD 13 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_60fc4 : bv 32 := 0x00d4b733.
Lemma F_60fc4 : fetch_word Asan.M.loaded_segments (0x60fc4 : word) = Some W_60fc4.
Proof. vm_refl. Qed.
Lemma D_60fc4 : decode_any W_60fc4 = Some (Op ALU_SLTU 14 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_60fc8 : bv 32 := 0xfff70713.
Lemma F_60fc8 : fetch_word Asan.M.loaded_segments (0x60fc8 : word) = Some W_60fc8.
Proof. vm_refl. Qed.
Lemma D_60fc8 : decode_any W_60fc8 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_60fcc : bv 32 := 0x00d77733.
Lemma F_60fcc : fetch_word Asan.M.loaded_segments (0x60fcc : word) = Some W_60fcc.
Proof. vm_refl. Qed.
Lemma D_60fcc : decode_any W_60fcc = Some (Op ALU_AND 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_60fd0 : bv 32 := 0x1ca77c63.
Lemma F_60fd0 : fetch_word Asan.M.loaded_segments (0x60fd0 : word) = Some W_60fd0.
Proof. vm_refl. Qed.
Lemma D_60fd0 : decode_any W_60fd0 = Some (Branch BC_GEU 14 10 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_60fd4 : bv 32 := 0x00075797.
Lemma F_60fd4 : fetch_word Asan.M.loaded_segments (0x60fd4 : word) = Some W_60fd4.
Proof. vm_refl. Qed.
Lemma D_60fd4 : decode_any W_60fd4 = Some (Auipc 15 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_60fd8 : bv 32 := 0x8ec7b783.
Lemma F_60fd8 : fetch_word Asan.M.loaded_segments (0x60fd8 : word) = Some W_60fd8.
Proof. vm_refl. Qed.
Lemma D_60fd8 : decode_any W_60fd8 = Some (Load SZ8 true 15 15 2284, 4%Z).
Proof. vm_refl. Qed.

Definition W_60fdc : bv 32 := 0x00075817.
Lemma F_60fdc : fetch_word Asan.M.loaded_segments (0x60fdc : word) = Some W_60fdc.
Proof. vm_refl. Qed.
Lemma D_60fdc : decode_any W_60fdc = Some (Auipc 16 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_60fe0 : bv 32 := 0x8ec83803.
Lemma F_60fe0 : fetch_word Asan.M.loaded_segments (0x60fe0 : word) = Some W_60fe0.
Proof. vm_refl. Qed.
Lemma D_60fe0 : decode_any W_60fe0 = Some (Load SZ8 true 16 16 2284, 4%Z).
Proof. vm_refl. Qed.

Definition W_60fe4 : bv 32 := 0x0007b883.
Lemma F_60fe4 : fetch_word Asan.M.loaded_segments (0x60fe4 : word) = Some W_60fe4.
Proof. vm_refl. Qed.
Lemma D_60fe4 : decode_any W_60fe4 = Some (Load SZ8 true 17 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60fe8 : bv 32 := 0x00083783.
Lemma F_60fe8 : fetch_word Asan.M.loaded_segments (0x60fe8 : word) = Some W_60fe8.
Proof. vm_refl. Qed.
Lemma D_60fe8 : decode_any W_60fe8 = Some (Load SZ8 true 15 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60fec : bv 32 := 0xfff88813.
Lemma F_60fec : fetch_word Asan.M.loaded_segments (0x60fec : word) = Some W_60fec.
Proof. vm_refl. Qed.
Lemma D_60fec : decode_any W_60fec = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_60ff0 : bv 32 := 0x00a87463.
Lemma F_60ff0 : fetch_word Asan.M.loaded_segments (0x60ff0 : word) = Some W_60ff0.
Proof. vm_refl. Qed.
Lemma D_60ff0 : decode_any W_60ff0 = Some (Branch BC_GEU 16 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_60ff4 : bv 32 := 0x1aa7fa63.
Lemma F_60ff4 : fetch_word Asan.M.loaded_segments (0x60ff4 : word) = Some W_60ff4.
Proof. vm_refl. Qed.
Lemma D_60ff4 : decode_any W_60ff4 = Some (Branch BC_GEU 15 10 436, 4%Z).
Proof. vm_refl. Qed.

Definition W_60ff8 : bv 32 := 0x00075297.
Lemma F_60ff8 : fetch_word Asan.M.loaded_segments (0x60ff8 : word) = Some W_60ff8.
Proof. vm_refl. Qed.
Lemma D_60ff8 : decode_any W_60ff8 = Some (Auipc 5 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_60ffc : bv 32 := 0x8d82b283.
Lemma F_60ffc : fetch_word Asan.M.loaded_segments (0x60ffc : word) = Some W_60ffc.
Proof. vm_refl. Qed.
Lemma D_60ffc : decode_any W_60ffc = Some (Load SZ8 true 5 5 2264, 4%Z).
Proof. vm_refl. Qed.

Definition W_61000 : bv 32 := 0x0002be03.
Lemma F_61000 : fetch_word Asan.M.loaded_segments (0x61000 : word) = Some W_61000.
Proof. vm_refl. Qed.
Lemma D_61000 : decode_any W_61000 = Some (Load SZ8 true 28 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61004 : bv 32 := 0x003e5313.
Lemma F_61004 : fetch_word Asan.M.loaded_segments (0x61004 : word) = Some W_61004.
Proof. vm_refl. Qed.
Lemma D_61004 : decode_any W_61004 = Some (ShiftImm ALU_SRL 6 28 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61008 : bv 32 := 0x009303b3.
Lemma F_61008 : fetch_word Asan.M.loaded_segments (0x61008 : word) = Some W_61008.
Proof. vm_refl. Qed.
Lemma D_61008 : decode_any W_61008 = Some (Op ALU_ADD 7 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_6100c : bv 32 := 0x00ae6463.
Lemma F_6100c : fetch_word Asan.M.loaded_segments (0x6100c : word) = Some W_6100c.
Proof. vm_refl. Qed.
Lemma D_6100c : decode_any W_6100c = Some (Branch BC_LTU 28 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_61010 : bv 32 := 0x0ca3e463.
Lemma F_61010 : fetch_word Asan.M.loaded_segments (0x61010 : word) = Some W_61010.
Proof. vm_refl. Qed.
Lemma D_61010 : decode_any W_61010 = Some (Branch BC_LTU 7 10 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_61014 : bv 32 := 0x00075e17.
Lemma F_61014 : fetch_word Asan.M.loaded_segments (0x61014 : word) = Some W_61014.
Proof. vm_refl. Qed.
Lemma D_61014 : decode_any W_61014 = Some (Auipc 28 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_61018 : bv 32 := 0x89ce3e03.
Lemma F_61018 : fetch_word Asan.M.loaded_segments (0x61018 : word) = Some W_61018.
Proof. vm_refl. Qed.
Lemma D_61018 : decode_any W_61018 = Some (Load SZ8 true 28 28 2204, 4%Z).
Proof. vm_refl. Qed.

Definition W_6101c : bv 32 := 0x04ee4e03.
Lemma F_6101c : fetch_word Asan.M.loaded_segments (0x6101c : word) = Some W_6101c.
Proof. vm_refl. Qed.
Lemma D_6101c : decode_any W_6101c = Some (Load SZ1 false 28 28 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_61020 : bv 32 := 0x3e0e1063.
Lemma F_61020 : fetch_word Asan.M.loaded_segments (0x61020 : word) = Some W_61020.
Proof. vm_refl. Qed.
Lemma D_61020 : decode_any W_61020 = Some (Branch BC_NE 28 0 992, 4%Z).
Proof. vm_refl. Qed.

Definition W_61024 : bv 32 := 0x04088e63.
Lemma F_61024 : fetch_word Asan.M.loaded_segments (0x61024 : word) = Some W_61024.
Proof. vm_refl. Qed.
Lemma D_61024 : decode_any W_61024 = Some (Branch BC_EQ 17 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_61028 : bv 32 := 0x0038d393.
Lemma F_61028 : fetch_word Asan.M.loaded_segments (0x61028 : word) = Some W_61028.
Proof. vm_refl. Qed.
Lemma D_61028 : decode_any W_61028 = Some (ShiftImm ALU_SRL 7 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6102c : bv 32 := 0x00d383b3.
Lemma F_6102c : fetch_word Asan.M.loaded_segments (0x6102c : word) = Some W_6102c.
Proof. vm_refl. Qed.
Lemma D_6102c : decode_any W_6102c = Some (Op ALU_ADD 7 7 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_61030 : bv 32 := 0x06a3fe63.
Lemma F_61030 : fetch_word Asan.M.loaded_segments (0x61030 : word) = Some W_61030.
Proof. vm_refl. Qed.
Lemma D_61030 : decode_any W_61030 = Some (Branch BC_GEU 7 10 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_61034 : bv 32 := 0x00148393.
Lemma F_61034 : fetch_word Asan.M.loaded_segments (0x61034 : word) = Some W_61034.
Proof. vm_refl. Qed.
Lemma D_61034 : decode_any W_61034 = Some (OpImm ALU_ADD 7 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61038 : bv 32 := 0x00a86863.
Lemma F_61038 : fetch_word Asan.M.loaded_segments (0x61038 : word) = Some W_61038.
Proof. vm_refl. Qed.
Lemma D_61038 : decode_any W_61038 = Some (Branch BC_LTU 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6103c : bv 32 := 0x0037de13.
Lemma F_6103c : fetch_word Asan.M.loaded_segments (0x6103c : word) = Some W_6103c.
Proof. vm_refl. Qed.
Lemma D_6103c : decode_any W_6103c = Some (ShiftImm ALU_SRL 28 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61040 : bv 32 := 0x007e0e33.
Lemma F_61040 : fetch_word Asan.M.loaded_segments (0x61040 : word) = Some W_61040.
Proof. vm_refl. Qed.
Lemma D_61040 : decode_any W_61040 = Some (Op ALU_ADD 28 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_61044 : bv 32 := 0x09c57a63.
Lemma F_61044 : fetch_word Asan.M.loaded_segments (0x61044 : word) = Some W_61044.
Proof. vm_refl. Qed.
Lemma D_61044 : decode_any W_61044 = Some (Branch BC_GEU 10 28 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_61048 : bv 32 := 0x00178e13.
Lemma F_61048 : fetch_word Asan.M.loaded_segments (0x61048 : word) = Some W_61048.
Proof. vm_refl. Qed.
Lemma D_61048 : decode_any W_61048 = Some (OpImm ALU_ADD 28 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6104c : bv 32 := 0x3bc56a63.
Lemma F_6104c : fetch_word Asan.M.loaded_segments (0x6104c : word) = Some W_6104c.
Proof. vm_refl. Qed.
Lemma D_6104c : decode_any W_6104c = Some (Branch BC_LTU 10 28 948, 4%Z).
Proof. vm_refl. Qed.

Definition W_61050 : bv 32 := 0x00730333.
Lemma F_61050 : fetch_word Asan.M.loaded_segments (0x61050 : word) = Some W_61050.
Proof. vm_refl. Qed.
Lemma D_61050 : decode_any W_61050 = Some (Op ALU_ADD 6 6 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_61054 : bv 32 := 0x00335313.
Lemma F_61054 : fetch_word Asan.M.loaded_segments (0x61054 : word) = Some W_61054.
Proof. vm_refl. Qed.
Lemma D_61054 : decode_any W_61054 = Some (ShiftImm ALU_SRL 6 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61058 : bv 32 := 0x0480006f.
Lemma F_61058 : fetch_word Asan.M.loaded_segments (0x61058 : word) = Some W_61058.
Proof. vm_refl. Qed.
Lemma D_61058 : decode_any W_61058 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_6105c : bv 32 := 0x03813083.
Lemma F_6105c : fetch_word Asan.M.loaded_segments (0x6105c : word) = Some W_6105c.
Proof. vm_refl. Qed.
Lemma D_6105c : decode_any W_6105c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_61060 : bv 32 := 0x03013403.
Lemma F_61060 : fetch_word Asan.M.loaded_segments (0x61060 : word) = Some W_61060.
Proof. vm_refl. Qed.
Lemma D_61060 : decode_any W_61060 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_61064 : bv 32 := 0x02813483.
Lemma F_61064 : fetch_word Asan.M.loaded_segments (0x61064 : word) = Some W_61064.
Proof. vm_refl. Qed.
Lemma D_61064 : decode_any W_61064 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_61068 : bv 32 := 0x02013903.
Lemma F_61068 : fetch_word Asan.M.loaded_segments (0x61068 : word) = Some W_61068.
Proof. vm_refl. Qed.
Lemma D_61068 : decode_any W_61068 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_6106c : bv 32 := 0x01813983.
Lemma F_6106c : fetch_word Asan.M.loaded_segments (0x6106c : word) = Some W_6106c.
Proof. vm_refl. Qed.
Lemma D_6106c : decode_any W_6106c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_61070 : bv 32 := 0x01013a03.
Lemma F_61070 : fetch_word Asan.M.loaded_segments (0x61070 : word) = Some W_61070.
Proof. vm_refl. Qed.
Lemma D_61070 : decode_any W_61070 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61074 : bv 32 := 0x00813a83.
Lemma F_61074 : fetch_word Asan.M.loaded_segments (0x61074 : word) = Some W_61074.
Proof. vm_refl. Qed.
Lemma D_61074 : decode_any W_61074 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_61078 : bv 32 := 0x04010113.
Lemma F_61078 : fetch_word Asan.M.loaded_segments (0x61078 : word) = Some W_61078.
Proof. vm_refl. Qed.
Lemma D_61078 : decode_any W_61078 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6107c : bv 32 := 0x00008067.
Lemma F_6107c : fetch_word Asan.M.loaded_segments (0x6107c : word) = Some W_6107c.
Proof. vm_refl. Qed.
Lemma D_6107c : decode_any W_6107c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61080 : bv 32 := 0x04048463.
Lemma F_61080 : fetch_word Asan.M.loaded_segments (0x61080 : word) = Some W_61080.
Proof. vm_refl. Qed.
Lemma D_61080 : decode_any W_61080 = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_61084 : bv 32 := 0x0036d313.
Lemma F_61084 : fetch_word Asan.M.loaded_segments (0x61084 : word) = Some W_61084.
Proof. vm_refl. Qed.
Lemma D_61084 : decode_any W_61084 = Some (ShiftImm ALU_SRL 6 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61088 : bv 32 := 0x00930333.
Lemma F_61088 : fetch_word Asan.M.loaded_segments (0x61088 : word) = Some W_61088.
Proof. vm_refl. Qed.
Lemma D_61088 : decode_any W_61088 = Some (Op ALU_ADD 6 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_6108c : bv 32 := 0x00030663.
Lemma F_6108c : fetch_word Asan.M.loaded_segments (0x6108c : word) = Some W_6108c.
Proof. vm_refl. Qed.
Lemma D_6108c : decode_any W_6108c = Some (Branch BC_EQ 6 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61090 : bv 32 := 0x00130313.
Lemma F_61090 : fetch_word Asan.M.loaded_segments (0x61090 : word) = Some W_61090.
Proof. vm_refl. Qed.
Lemma D_61090 : decode_any W_61090 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61094 : bv 32 := 0x36656663.
Lemma F_61094 : fetch_word Asan.M.loaded_segments (0x61094 : word) = Some W_61094.
Proof. vm_refl. Qed.
Lemma D_61094 : decode_any W_61094 = Some (Branch BC_LTU 10 6 876, 4%Z).
Proof. vm_refl. Qed.

Definition W_61098 : bv 32 := 0x00138393.
Lemma F_61098 : fetch_word Asan.M.loaded_segments (0x61098 : word) = Some W_61098.
Proof. vm_refl. Qed.
Lemma D_61098 : decode_any W_61098 = Some (OpImm ALU_ADD 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6109c : bv 32 := 0x0033d313.
Lemma F_6109c : fetch_word Asan.M.loaded_segments (0x6109c : word) = Some W_6109c.
Proof. vm_refl. Qed.
Lemma D_6109c : decode_any W_6109c = Some (ShiftImm ALU_SRL 6 7 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_610a0 : bv 32 := 0x00d30333.
Lemma F_610a0 : fetch_word Asan.M.loaded_segments (0x610a0 : word) = Some W_610a0.
Proof. vm_refl. Qed.
Lemma D_610a0 : decode_any W_610a0 = Some (Op ALU_ADD 6 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_610a4 : bv 32 := 0x02a37a63.
Lemma F_610a4 : fetch_word Asan.M.loaded_segments (0x610a4 : word) = Some W_610a4.
Proof. vm_refl. Qed.
Lemma D_610a4 : decode_any W_610a4 = Some (Branch BC_GEU 6 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_610a8 : bv 32 := 0x3580006f.
Lemma F_610a8 : fetch_word Asan.M.loaded_segments (0x610a8 : word) = Some W_610a8.
Proof. vm_refl. Qed.
Lemma D_610a8 : decode_any W_610a8 = Some (Jal 0 856, 4%Z).
Proof. vm_refl. Qed.

Definition W_610ac : bv 32 := 0x02048663.
Lemma F_610ac : fetch_word Asan.M.loaded_segments (0x610ac : word) = Some W_610ac.
Proof. vm_refl. Qed.
Lemma D_610ac : decode_any W_610ac = Some (Branch BC_EQ 9 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_610b0 : bv 32 := 0x0036d313.
Lemma F_610b0 : fetch_word Asan.M.loaded_segments (0x610b0 : word) = Some W_610b0.
Proof. vm_refl. Qed.
Lemma D_610b0 : decode_any W_610b0 = Some (ShiftImm ALU_SRL 6 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_610b4 : bv 32 := 0x00930333.
Lemma F_610b4 : fetch_word Asan.M.loaded_segments (0x610b4 : word) = Some W_610b4.
Proof. vm_refl. Qed.
Lemma D_610b4 : decode_any W_610b4 = Some (Op ALU_ADD 6 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_610b8 : bv 32 := 0x02030063.
Lemma F_610b8 : fetch_word Asan.M.loaded_segments (0x610b8 : word) = Some W_610b8.
Proof. vm_refl. Qed.
Lemma D_610b8 : decode_any W_610b8 = Some (Branch BC_EQ 6 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_610bc : bv 32 := 0x00130313.
Lemma F_610bc : fetch_word Asan.M.loaded_segments (0x610bc : word) = Some W_610bc.
Proof. vm_refl. Qed.
Lemma D_610bc : decode_any W_610bc = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_610c0 : bv 32 := 0x00657c63.
Lemma F_610c0 : fetch_word Asan.M.loaded_segments (0x610c0 : word) = Some W_610c0.
Proof. vm_refl. Qed.
Lemma D_610c0 : decode_any W_610c0 = Some (Branch BC_GEU 10 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_610c4 : bv 32 := 0x33c0006f.
Lemma F_610c4 : fetch_word Asan.M.loaded_segments (0x610c4 : word) = Some W_610c4.
Proof. vm_refl. Qed.
Lemma D_610c4 : decode_any W_610c4 = Some (Jal 0 828, 4%Z).
Proof. vm_refl. Qed.

Definition W_610c8 : bv 32 := 0x00130313.
Lemma F_610c8 : fetch_word Asan.M.loaded_segments (0x610c8 : word) = Some W_610c8.
Proof. vm_refl. Qed.
Lemma D_610c8 : decode_any W_610c8 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_610cc : bv 32 := 0x00335313.
Lemma F_610cc : fetch_word Asan.M.loaded_segments (0x610cc : word) = Some W_610cc.
Proof. vm_refl. Qed.
Lemma D_610cc : decode_any W_610cc = Some (ShiftImm ALU_SRL 6 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_610d0 : bv 32 := 0xfff30313.
Lemma F_610d0 : fetch_word Asan.M.loaded_segments (0x610d0 : word) = Some W_610d0.
Proof. vm_refl. Qed.
Lemma D_610d0 : decode_any W_610d0 = Some (OpImm ALU_ADD 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_610d4 : bv 32 := 0x32a36663.
Lemma F_610d4 : fetch_word Asan.M.loaded_segments (0x610d4 : word) = Some W_610d4.
Proof. vm_refl. Qed.
Lemma D_610d4 : decode_any W_610d4 = Some (Branch BC_LTU 6 10 812, 4%Z).
Proof. vm_refl. Qed.

Definition W_610d8 : bv 32 := 0x0002b383.
Lemma F_610d8 : fetch_word Asan.M.loaded_segments (0x610d8 : word) = Some W_610d8.
Proof. vm_refl. Qed.
Lemma D_610d8 : decode_any W_610d8 = Some (Load SZ8 true 7 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_610dc : bv 32 := 0x0033d293.
Lemma F_610dc : fetch_word Asan.M.loaded_segments (0x610dc : word) = Some W_610dc.
Proof. vm_refl. Qed.
Lemma D_610dc : decode_any W_610dc = Some (ShiftImm ALU_SRL 5 7 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_610e0 : bv 32 := 0x00928333.
Lemma F_610e0 : fetch_word Asan.M.loaded_segments (0x610e0 : word) = Some W_610e0.
Proof. vm_refl. Qed.
Lemma D_610e0 : decode_any W_610e0 = Some (Op ALU_ADD 6 5 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_610e4 : bv 32 := 0x00a3e463.
Lemma F_610e4 : fetch_word Asan.M.loaded_segments (0x610e4 : word) = Some W_610e4.
Proof. vm_refl. Qed.
Lemma D_610e4 : decode_any W_610e4 = Some (Branch BC_LTU 7 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_610e8 : bv 32 := 0x0ca36063.
Lemma F_610e8 : fetch_word Asan.M.loaded_segments (0x610e8 : word) = Some W_610e8.
Proof. vm_refl. Qed.
Lemma D_610e8 : decode_any W_610e8 = Some (Branch BC_LTU 6 10 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_610ec : bv 32 := 0x00074397.
Lemma F_610ec : fetch_word Asan.M.loaded_segments (0x610ec : word) = Some W_610ec.
Proof. vm_refl. Qed.
Lemma D_610ec : decode_any W_610ec = Some (Auipc 7 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_610f0 : bv 32 := 0x7c43b383.
Lemma F_610f0 : fetch_word Asan.M.loaded_segments (0x610f0 : word) = Some W_610f0.
Proof. vm_refl. Qed.
Lemma D_610f0 : decode_any W_610f0 = Some (Load SZ8 true 7 7 1988, 4%Z).
Proof. vm_refl. Qed.

Definition W_610f4 : bv 32 := 0x04e3c383.
Lemma F_610f4 : fetch_word Asan.M.loaded_segments (0x610f4 : word) = Some W_610f4.
Proof. vm_refl. Qed.
Lemma D_610f4 : decode_any W_610f4 = Some (Load SZ1 false 7 7 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_610f8 : bv 32 := 0x08039063.
Lemma F_610f8 : fetch_word Asan.M.loaded_segments (0x610f8 : word) = Some W_610f8.
Proof. vm_refl. Qed.
Lemma D_610f8 : decode_any W_610f8 = Some (Branch BC_NE 7 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_610fc : bv 32 := 0x02088c63.
Lemma F_610fc : fetch_word Asan.M.loaded_segments (0x610fc : word) = Some W_610fc.
Proof. vm_refl. Qed.
Lemma D_610fc : decode_any W_610fc = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_61100 : bv 32 := 0x0038d893.
Lemma F_61100 : fetch_word Asan.M.loaded_segments (0x61100 : word) = Some W_61100.
Proof. vm_refl. Qed.
Lemma D_61100 : decode_any W_61100 = Some (ShiftImm ALU_SRL 17 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61104 : bv 32 := 0x00d888b3.
Lemma F_61104 : fetch_word Asan.M.loaded_segments (0x61104 : word) = Some W_61104.
Proof. vm_refl. Qed.
Lemma D_61104 : decode_any W_61104 = Some (Op ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_61108 : bv 32 := 0x04a8fc63.
Lemma F_61108 : fetch_word Asan.M.loaded_segments (0x61108 : word) = Some W_61108.
Proof. vm_refl. Qed.
Lemma D_61108 : decode_any W_61108 = Some (Branch BC_GEU 17 10 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_6110c : bv 32 := 0x00148893.
Lemma F_6110c : fetch_word Asan.M.loaded_segments (0x6110c : word) = Some W_6110c.
Proof. vm_refl. Qed.
Lemma D_6110c : decode_any W_6110c = Some (OpImm ALU_ADD 17 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61110 : bv 32 := 0x00a86863.
Lemma F_61110 : fetch_word Asan.M.loaded_segments (0x61110 : word) = Some W_61110.
Proof. vm_refl. Qed.
Lemma D_61110 : decode_any W_61110 = Some (Branch BC_LTU 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61114 : bv 32 := 0x0037d813.
Lemma F_61114 : fetch_word Asan.M.loaded_segments (0x61114 : word) = Some W_61114.
Proof. vm_refl. Qed.
Lemma D_61114 : decode_any W_61114 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61118 : bv 32 := 0x01180833.
Lemma F_61118 : fetch_word Asan.M.loaded_segments (0x61118 : word) = Some W_61118.
Proof. vm_refl. Qed.
Lemma D_61118 : decode_any W_61118 = Some (Op ALU_ADD 16 16 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_6111c : bv 32 := 0x09057663.
Lemma F_6111c : fetch_word Asan.M.loaded_segments (0x6111c : word) = Some W_6111c.
Proof. vm_refl. Qed.
Lemma D_6111c : decode_any W_6111c = Some (Branch BC_GEU 10 16 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_61120 : bv 32 := 0x00178793.
Lemma F_61120 : fetch_word Asan.M.loaded_segments (0x61120 : word) = Some W_61120.
Proof. vm_refl. Qed.
Lemma D_61120 : decode_any W_61120 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61124 : bv 32 := 0x04f56a63.
Lemma F_61124 : fetch_word Asan.M.loaded_segments (0x61124 : word) = Some W_61124.
Proof. vm_refl. Qed.
Lemma D_61124 : decode_any W_61124 = Some (Branch BC_LTU 10 15 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_61128 : bv 32 := 0x011288b3.
Lemma F_61128 : fetch_word Asan.M.loaded_segments (0x61128 : word) = Some W_61128.
Proof. vm_refl. Qed.
Lemma D_61128 : decode_any W_61128 = Some (Op ALU_ADD 17 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_6112c : bv 32 := 0x0038d793.
Lemma F_6112c : fetch_word Asan.M.loaded_segments (0x6112c : word) = Some W_6112c.
Proof. vm_refl. Qed.
Lemma D_6112c : decode_any W_6112c = Some (ShiftImm ALU_SRL 15 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61130 : bv 32 := 0x0240006f.
Lemma F_61130 : fetch_word Asan.M.loaded_segments (0x61130 : word) = Some W_61130.
Proof. vm_refl. Qed.
Lemma D_61130 : decode_any W_61130 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_61134 : bv 32 := 0x06048263.
Lemma F_61134 : fetch_word Asan.M.loaded_segments (0x61134 : word) = Some W_61134.
Proof. vm_refl. Qed.
Lemma D_61134 : decode_any W_61134 = Some (Branch BC_EQ 9 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_61138 : bv 32 := 0x0036d793.
Lemma F_61138 : fetch_word Asan.M.loaded_segments (0x61138 : word) = Some W_61138.
Proof. vm_refl. Qed.
Lemma D_61138 : decode_any W_61138 = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6113c : bv 32 := 0x009787b3.
Lemma F_6113c : fetch_word Asan.M.loaded_segments (0x6113c : word) = Some W_6113c.
Proof. vm_refl. Qed.
Lemma D_6113c : decode_any W_6113c = Some (Op ALU_ADD 15 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_61140 : bv 32 := 0x00078663.
Lemma F_61140 : fetch_word Asan.M.loaded_segments (0x61140 : word) = Some W_61140.
Proof. vm_refl. Qed.
Lemma D_61140 : decode_any W_61140 = Some (Branch BC_EQ 15 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61144 : bv 32 := 0x00178793.
Lemma F_61144 : fetch_word Asan.M.loaded_segments (0x61144 : word) = Some W_61144.
Proof. vm_refl. Qed.
Lemma D_61144 : decode_any W_61144 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61148 : bv 32 := 0x02f56863.
Lemma F_61148 : fetch_word Asan.M.loaded_segments (0x61148 : word) = Some W_61148.
Proof. vm_refl. Qed.
Lemma D_61148 : decode_any W_61148 = Some (Branch BC_LTU 10 15 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6114c : bv 32 := 0x00130313.
Lemma F_6114c : fetch_word Asan.M.loaded_segments (0x6114c : word) = Some W_6114c.
Proof. vm_refl. Qed.
Lemma D_6114c : decode_any W_6114c = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61150 : bv 32 := 0x00335793.
Lemma F_61150 : fetch_word Asan.M.loaded_segments (0x61150 : word) = Some W_61150.
Proof. vm_refl. Qed.
Lemma D_61150 : decode_any W_61150 = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61154 : bv 32 := 0x00d787b3.
Lemma F_61154 : fetch_word Asan.M.loaded_segments (0x61154 : word) = Some W_61154.
Proof. vm_refl. Qed.
Lemma D_61154 : decode_any W_61154 = Some (Op ALU_ADD 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_61158 : bv 32 := 0x04a7f863.
Lemma F_61158 : fetch_word Asan.M.loaded_segments (0x61158 : word) = Some W_61158.
Proof. vm_refl. Qed.
Lemma D_61158 : decode_any W_61158 = Some (Branch BC_GEU 15 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_6115c : bv 32 := 0x01c0006f.
Lemma F_6115c : fetch_word Asan.M.loaded_segments (0x6115c : word) = Some W_6115c.
Proof. vm_refl. Qed.
Lemma D_6115c : decode_any W_6115c = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_61160 : bv 32 := 0x04048463.
Lemma F_61160 : fetch_word Asan.M.loaded_segments (0x61160 : word) = Some W_61160.
Proof. vm_refl. Qed.
Lemma D_61160 : decode_any W_61160 = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_61164 : bv 32 := 0x0036d793.
Lemma F_61164 : fetch_word Asan.M.loaded_segments (0x61164 : word) = Some W_61164.
Proof. vm_refl. Qed.
Lemma D_61164 : decode_any W_61164 = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61168 : bv 32 := 0x009787b3.
Lemma F_61168 : fetch_word Asan.M.loaded_segments (0x61168 : word) = Some W_61168.
Proof. vm_refl. Qed.
Lemma D_61168 : decode_any W_61168 = Some (Op ALU_ADD 15 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_6116c : bv 32 := 0x02078e63.
Lemma F_6116c : fetch_word Asan.M.loaded_segments (0x6116c : word) = Some W_6116c.
Proof. vm_refl. Qed.
Lemma D_6116c : decode_any W_6116c = Some (Branch BC_EQ 15 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_61170 : bv 32 := 0x00178793.
Lemma F_61170 : fetch_word Asan.M.loaded_segments (0x61170 : word) = Some W_61170.
Proof. vm_refl. Qed.
Lemma D_61170 : decode_any W_61170 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61174 : bv 32 := 0x02f57a63.
Lemma F_61174 : fetch_word Asan.M.loaded_segments (0x61174 : word) = Some W_61174.
Proof. vm_refl. Qed.
Lemma D_61174 : decode_any W_61174 = Some (Branch BC_GEU 10 15 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_61178 : bv 32 := 0xfffc0517.
Lemma F_61178 : fetch_word Asan.M.loaded_segments (0x61178 : word) = Some W_61178.
Proof. vm_refl. Qed.
Lemma D_61178 : decode_any W_61178 = Some (Auipc 10 1048512, 4%Z).
Proof. vm_refl. Qed.

Definition W_6117c : bv 32 := 0xfffb7597.
Lemma F_6117c : fetch_word Asan.M.loaded_segments (0x6117c : word) = Some W_6117c.
Proof. vm_refl. Qed.
Lemma D_6117c : decode_any W_6117c = Some (Auipc 11 1048503, 4%Z).
Proof. vm_refl. Qed.

Definition W_61180 : bv 32 := 0xaf450513.
Lemma F_61180 : fetch_word Asan.M.loaded_segments (0x61180 : word) = Some W_61180.
Proof. vm_refl. Qed.
Lemma D_61180 : decode_any W_61180 = Some (OpImm ALU_ADD 10 10 2804, 4%Z).
Proof. vm_refl. Qed.

Definition W_61184 : bv 32 := 0x38c58613.
Lemma F_61184 : fetch_word Asan.M.loaded_segments (0x61184 : word) = Some W_61184.
Proof. vm_refl. Qed.
Lemma D_61184 : decode_any W_61184 = Some (OpImm ALU_ADD 12 11 908, 4%Z).
Proof. vm_refl. Qed.

Definition W_61188 : bv 32 := 0x02f00593.
Lemma F_61188 : fetch_word Asan.M.loaded_segments (0x61188 : word) = Some W_61188.
Proof. vm_refl. Qed.
Lemma D_61188 : decode_any W_61188 = Some (OpImm ALU_ADD 11 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_6118c : bv 32 := 0x00000693.
Lemma F_6118c : fetch_word Asan.M.loaded_segments (0x6118c : word) = Some W_6118c.
Proof. vm_refl. Qed.
Lemma D_6118c : decode_any W_6118c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61190 : bv 32 := 0x00000713.
Lemma F_61190 : fetch_word Asan.M.loaded_segments (0x61190 : word) = Some W_61190.
Proof. vm_refl. Qed.
Lemma D_61190 : decode_any W_61190 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61194 : bv 32 := 0x6d5170ef.
Lemma F_61194 : fetch_word Asan.M.loaded_segments (0x61194 : word) = Some W_61194.
Proof. vm_refl. Qed.
Lemma D_61194 : decode_any W_61194 = Some (Jal 1 98004, 4%Z).
Proof. vm_refl. Qed.

Definition W_61198 : bv 32 := 0x00128293.
Lemma F_61198 : fetch_word Asan.M.loaded_segments (0x61198 : word) = Some W_61198.
Proof. vm_refl. Qed.
Lemma D_61198 : decode_any W_61198 = Some (OpImm ALU_ADD 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6119c : bv 32 := 0x0032d793.
Lemma F_6119c : fetch_word Asan.M.loaded_segments (0x6119c : word) = Some W_6119c.
Proof. vm_refl. Qed.
Lemma D_6119c : decode_any W_6119c = Some (ShiftImm ALU_SRL 15 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_611a0 : bv 32 := 0xfff78793.
Lemma F_611a0 : fetch_word Asan.M.loaded_segments (0x611a0 : word) = Some W_611a0.
Proof. vm_refl. Qed.
Lemma D_611a0 : decode_any W_611a0 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_611a4 : bv 32 := 0xfca7eae3.
Lemma F_611a4 : fetch_word Asan.M.loaded_segments (0x611a4 : word) = Some W_611a4.
Proof. vm_refl. Qed.
Lemma D_611a4 : decode_any W_611a4 = Some (Branch BC_LTU 15 10 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_611a8 : bv 32 := 0x0075f793.
Lemma F_611a8 : fetch_word Asan.M.loaded_segments (0x611a8 : word) = Some W_611a8.
Proof. vm_refl. Qed.
Lemma D_611a8 : decode_any W_611a8 = Some (OpImm ALU_AND 15 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_611ac : bv 32 := 0x26079a63.
Lemma F_611ac : fetch_word Asan.M.loaded_segments (0x611ac : word) = Some W_611ac.
Proof. vm_refl. Qed.
Lemma D_611ac : decode_any W_611ac = Some (Branch BC_NE 15 0 628, 4%Z).
Proof. vm_refl. Qed.

Definition W_611b0 : bv 32 := 0x00b505b3.
Lemma F_611b0 : fetch_word Asan.M.loaded_segments (0x611b0 : word) = Some W_611b0.
Proof. vm_refl. Qed.
Lemma D_611b0 : decode_any W_611b0 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_611b4 : bv 32 := 0xff858593.
Lemma F_611b4 : fetch_word Asan.M.loaded_segments (0x611b4 : word) = Some W_611b4.
Proof. vm_refl. Qed.
Lemma D_611b4 : decode_any W_611b4 = Some (OpImm ALU_ADD 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_611b8 : bv 32 := 0x04b77263.
Lemma F_611b8 : fetch_word Asan.M.loaded_segments (0x611b8 : word) = Some W_611b8.
Proof. vm_refl. Qed.
Lemma D_611b8 : decode_any W_611b8 = Some (Branch BC_GEU 14 11 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_611bc : bv 32 := 0x00074717.
Lemma F_611bc : fetch_word Asan.M.loaded_segments (0x611bc : word) = Some W_611bc.
Proof. vm_refl. Qed.
Lemma D_611bc : decode_any W_611bc = Some (Auipc 14 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_611c0 : bv 32 := 0x70473703.
Lemma F_611c0 : fetch_word Asan.M.loaded_segments (0x611c0 : word) = Some W_611c0.
Proof. vm_refl. Qed.
Lemma D_611c0 : decode_any W_611c0 = Some (Load SZ8 true 14 14 1796, 4%Z).
Proof. vm_refl. Qed.

Definition W_611c4 : bv 32 := 0x00074797.
Lemma F_611c4 : fetch_word Asan.M.loaded_segments (0x611c4 : word) = Some W_611c4.
Proof. vm_refl. Qed.
Lemma D_611c4 : decode_any W_611c4 = Some (Auipc 15 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_611c8 : bv 32 := 0x7047b783.
Lemma F_611c8 : fetch_word Asan.M.loaded_segments (0x611c8 : word) = Some W_611c8.
Proof. vm_refl. Qed.
Lemma D_611c8 : decode_any W_611c8 = Some (Load SZ8 true 15 15 1796, 4%Z).
Proof. vm_refl. Qed.

Definition W_611cc : bv 32 := 0x00073883.
Lemma F_611cc : fetch_word Asan.M.loaded_segments (0x611cc : word) = Some W_611cc.
Proof. vm_refl. Qed.
Lemma D_611cc : decode_any W_611cc = Some (Load SZ8 true 17 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_611d0 : bv 32 := 0x0007b703.
Lemma F_611d0 : fetch_word Asan.M.loaded_segments (0x611d0 : word) = Some W_611d0.
Proof. vm_refl. Qed.
Lemma D_611d0 : decode_any W_611d0 = Some (Load SZ8 true 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_611d4 : bv 32 := 0xfff88813.
Lemma F_611d4 : fetch_word Asan.M.loaded_segments (0x611d4 : word) = Some W_611d4.
Proof. vm_refl. Qed.
Lemma D_611d4 : decode_any W_611d4 = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_611d8 : bv 32 := 0x00b87463.
Lemma F_611d8 : fetch_word Asan.M.loaded_segments (0x611d8 : word) = Some W_611d8.
Proof. vm_refl. Qed.
Lemma D_611d8 : decode_any W_611d8 = Some (Branch BC_GEU 16 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_611dc : bv 32 := 0x02b77063.
Lemma F_611dc : fetch_word Asan.M.loaded_segments (0x611dc : word) = Some W_611dc.
Proof. vm_refl. Qed.
Lemma D_611dc : decode_any W_611dc = Some (Branch BC_GEU 14 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_611e0 : bv 32 := 0x00074797.
Lemma F_611e0 : fetch_word Asan.M.loaded_segments (0x611e0 : word) = Some W_611e0.
Proof. vm_refl. Qed.
Lemma D_611e0 : decode_any W_611e0 = Some (Auipc 15 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_611e4 : bv 32 := 0x6f07b783.
Lemma F_611e4 : fetch_word Asan.M.loaded_segments (0x611e4 : word) = Some W_611e4.
Proof. vm_refl. Qed.
Lemma D_611e4 : decode_any W_611e4 = Some (Load SZ8 true 15 15 1776, 4%Z).
Proof. vm_refl. Qed.

Definition W_611e8 : bv 32 := 0x0007b303.
Lemma F_611e8 : fetch_word Asan.M.loaded_segments (0x611e8 : word) = Some W_611e8.
Proof. vm_refl. Qed.
Lemma D_611e8 : decode_any W_611e8 = Some (Load SZ8 true 6 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_611ec : bv 32 := 0x00335793.
Lemma F_611ec : fetch_word Asan.M.loaded_segments (0x611ec : word) = Some W_611ec.
Proof. vm_refl. Qed.
Lemma D_611ec : decode_any W_611ec = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_611f0 : bv 32 := 0x009782b3.
Lemma F_611f0 : fetch_word Asan.M.loaded_segments (0x611f0 : word) = Some W_611f0.
Proof. vm_refl. Qed.
Lemma D_611f0 : decode_any W_611f0 = Some (Op ALU_ADD 5 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_611f4 : bv 32 := 0x12b36263.
Lemma F_611f4 : fetch_word Asan.M.loaded_segments (0x611f4 : word) = Some W_611f4.
Proof. vm_refl. Qed.
Lemma D_611f4 : decode_any W_611f4 = Some (Branch BC_LTU 6 11 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_611f8 : bv 32 := 0x12b2f063.
Lemma F_611f8 : fetch_word Asan.M.loaded_segments (0x611f8 : word) = Some W_611f8.
Proof. vm_refl. Qed.
Lemma D_611f8 : decode_any W_611f8 = Some (Branch BC_GEU 5 11 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_611fc : bv 32 := 0x00074697.
Lemma F_611fc : fetch_word Asan.M.loaded_segments (0x611fc : word) = Some W_611fc.
Proof. vm_refl. Qed.
Lemma D_611fc : decode_any W_611fc = Some (Auipc 13 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_61200 : bv 32 := 0x6dc6b983.
Lemma F_61200 : fetch_word Asan.M.loaded_segments (0x61200 : word) = Some W_61200.
Proof. vm_refl. Qed.
Lemma D_61200 : decode_any W_61200 = Some (Load SZ8 true 19 13 1756, 4%Z).
Proof. vm_refl. Qed.

Definition W_61204 : bv 32 := 0x0009b303.
Lemma F_61204 : fetch_word Asan.M.loaded_segments (0x61204 : word) = Some W_61204.
Proof. vm_refl. Qed.
Lemma D_61204 : decode_any W_61204 = Some (Load SZ8 true 6 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61208 : bv 32 := 0x22030c63.
Lemma F_61208 : fetch_word Asan.M.loaded_segments (0x61208 : word) = Some W_61208.
Proof. vm_refl. Qed.
Lemma D_61208 : decode_any W_61208 = Some (Branch BC_EQ 6 0 568, 4%Z).
Proof. vm_refl. Qed.

Definition W_6120c : bv 32 := 0x00355693.
Lemma F_6120c : fetch_word Asan.M.loaded_segments (0x6120c : word) = Some W_6120c.
Proof. vm_refl. Qed.
Lemma D_6120c : decode_any W_6120c = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61210 : bv 32 := 0x0035d593.
Lemma F_61210 : fetch_word Asan.M.loaded_segments (0x61210 : word) = Some W_61210.
Proof. vm_refl. Qed.
Lemma D_61210 : decode_any W_61210 = Some (ShiftImm ALU_SRL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61214 : bv 32 := 0x00d48533.
Lemma F_61214 : fetch_word Asan.M.loaded_segments (0x61214 : word) = Some W_61214.
Proof. vm_refl. Qed.
Lemma D_61214 : decode_any W_61214 = Some (Op ALU_ADD 10 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_61218 : bv 32 := 0x00158913.
Lemma F_61218 : fetch_word Asan.M.loaded_segments (0x61218 : word) = Some W_61218.
Proof. vm_refl. Qed.
Lemma D_61218 : decode_any W_61218 = Some (OpImm ALU_ADD 18 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6121c : bv 32 := 0x40d90433.
Lemma F_6121c : fetch_word Asan.M.loaded_segments (0x6121c : word) = Some W_6121c.
Proof. vm_refl. Qed.
Lemma D_6121c : decode_any W_6121c = Some (Op ALU_SUB 8 18 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_61220 : bv 32 := 0x0c061063.
Lemma F_61220 : fetch_word Asan.M.loaded_segments (0x61220 : word) = Some W_61220.
Proof. vm_refl. Qed.
Lemma D_61220 : decode_any W_61220 = Some (Branch BC_NE 12 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_61224 : bv 32 := 0x00074597.
Lemma F_61224 : fetch_word Asan.M.loaded_segments (0x61224 : word) = Some W_61224.
Proof. vm_refl. Qed.
Lemma D_61224 : decode_any W_61224 = Some (Auipc 11 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_61228 : bv 32 := 0x6845b583.
Lemma F_61228 : fetch_word Asan.M.loaded_segments (0x61228 : word) = Some W_61228.
Proof. vm_refl. Qed.
Lemma D_61228 : decode_any W_61228 = Some (Load SZ8 true 11 11 1668, 4%Z).
Proof. vm_refl. Qed.

Definition W_6122c : bv 32 := 0x0785b583.
Lemma F_6122c : fetch_word Asan.M.loaded_segments (0x6122c : word) = Some W_6122c.
Proof. vm_refl. Qed.
Lemma D_6122c : decode_any W_6122c = Some (Load SZ8 true 11 11 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_61230 : bv 32 := 0x0ab46863.
Lemma F_61230 : fetch_word Asan.M.loaded_segments (0x61230 : word) = Some W_61230.
Proof. vm_refl. Qed.
Lemma D_61230 : decode_any W_61230 = Some (Branch BC_LTU 8 11 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_61234 : bv 32 := 0x00074597.
Lemma F_61234 : fetch_word Asan.M.loaded_segments (0x61234 : word) = Some W_61234.
Proof. vm_refl. Qed.
Lemma D_61234 : decode_any W_61234 = Some (Auipc 11 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_61238 : bv 32 := 0x6645ba03.
Lemma F_61238 : fetch_word Asan.M.loaded_segments (0x61238 : word) = Some W_61238.
Proof. vm_refl. Qed.
Lemma D_61238 : decode_any W_61238 = Some (Load SZ8 true 20 11 1636, 4%Z).
Proof. vm_refl. Qed.

Definition W_6123c : bv 32 := 0x000a3583.
Lemma F_6123c : fetch_word Asan.M.loaded_segments (0x6123c : word) = Some W_6123c.
Proof. vm_refl. Qed.
Lemma D_6123c : decode_any W_6123c = Some (Load SZ8 true 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61240 : bv 32 := 0x00059c63.
Lemma F_61240 : fetch_word Asan.M.loaded_segments (0x61240 : word) = Some W_61240.
Proof. vm_refl. Qed.
Lemma D_61240 : decode_any W_61240 = Some (Branch BC_NE 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_61244 : bv 32 := 0x00050a93.
Lemma F_61244 : fetch_word Asan.M.loaded_segments (0x61244 : word) = Some W_61244.
Proof. vm_refl. Qed.
Lemma D_61244 : decode_any W_61244 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61248 : bv 32 := 0x045110ef.
Lemma F_61248 : fetch_word Asan.M.loaded_segments (0x61248 : word) = Some W_61248.
Proof. vm_refl. Qed.
Lemma D_61248 : decode_any W_61248 = Some (Jal 1 71748, 4%Z).
Proof. vm_refl. Qed.

Definition W_6124c : bv 32 := 0x00050593.
Lemma F_6124c : fetch_word Asan.M.loaded_segments (0x6124c : word) = Some W_6124c.
Proof. vm_refl. Qed.
Lemma D_6124c : decode_any W_6124c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61250 : bv 32 := 0x000a8513.
Lemma F_61250 : fetch_word Asan.M.loaded_segments (0x61250 : word) = Some W_61250.
Proof. vm_refl. Qed.
Lemma D_61250 : decode_any W_61250 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61254 : bv 32 := 0x00ba3023.
Lemma F_61254 : fetch_word Asan.M.loaded_segments (0x61254 : word) = Some W_61254.
Proof. vm_refl. Qed.
Lemma D_61254 : decode_any W_61254 = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61258 : bv 32 := 0xfff58613.
Lemma F_61258 : fetch_word Asan.M.loaded_segments (0x61258 : word) = Some W_61258.
Proof. vm_refl. Qed.
Lemma D_61258 : decode_any W_61258 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6125c : bv 32 := 0x00c5f633.
Lemma F_6125c : fetch_word Asan.M.loaded_segments (0x6125c : word) = Some W_6125c.
Proof. vm_refl. Qed.
Lemma D_6125c : decode_any W_6125c = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61260 : bv 32 := 0x20061063.
Lemma F_61260 : fetch_word Asan.M.loaded_segments (0x61260 : word) = Some W_61260.
Proof. vm_refl. Qed.
Lemma D_61260 : decode_any W_61260 = Some (Branch BC_NE 12 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_61264 : bv 32 := 0x00990a33.
Lemma F_61264 : fetch_word Asan.M.loaded_segments (0x61264 : word) = Some W_61264.
Proof. vm_refl. Qed.
Lemma D_61264 : decode_any W_61264 = Some (Op ALU_ADD 20 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_61268 : bv 32 := 0x00b50633.
Lemma F_61268 : fetch_word Asan.M.loaded_segments (0x61268 : word) = Some W_61268.
Proof. vm_refl. Qed.
Lemma D_61268 : decode_any W_61268 = Some (Op ALU_ADD 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6126c : bv 32 := 0x40b005b3.
Lemma F_6126c : fetch_word Asan.M.loaded_segments (0x6126c : word) = Some W_6126c.
Proof. vm_refl. Qed.
Lemma D_6126c : decode_any W_6126c = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_61270 : bv 32 := 0xfff60613.
Lemma F_61270 : fetch_word Asan.M.loaded_segments (0x61270 : word) = Some W_61270.
Proof. vm_refl. Qed.
Lemma D_61270 : decode_any W_61270 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61274 : bv 32 := 0x00b674b3.
Lemma F_61274 : fetch_word Asan.M.loaded_segments (0x61274 : word) = Some W_61274.
Proof. vm_refl. Qed.
Lemma D_61274 : decode_any W_61274 = Some (Op ALU_AND 9 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_61278 : bv 32 := 0x00ba7933.
Lemma F_61278 : fetch_word Asan.M.loaded_segments (0x61278 : word) = Some W_61278.
Proof. vm_refl. Qed.
Lemma D_61278 : decode_any W_61278 = Some (Op ALU_AND 18 20 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6127c : bv 32 := 0x0724f663.
Lemma F_6127c : fetch_word Asan.M.loaded_segments (0x6127c : word) = Some W_6127c.
Proof. vm_refl. Qed.
Lemma D_6127c : decode_any W_6127c = Some (Branch BC_GEU 9 18 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_61280 : bv 32 := 0x00a48a63.
Lemma F_61280 : fetch_word Asan.M.loaded_segments (0x61280 : word) = Some W_61280.
Proof. vm_refl. Qed.
Lemma D_61280 : decode_any W_61280 = Some (Branch BC_EQ 9 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_61284 : bv 32 := 0x0009b683.
Lemma F_61284 : fetch_word Asan.M.loaded_segments (0x61284 : word) = Some W_61284.
Proof. vm_refl. Qed.
Lemma D_61284 : decode_any W_61284 = Some (Load SZ8 true 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61288 : bv 32 := 0x40a48633.
Lemma F_61288 : fetch_word Asan.M.loaded_segments (0x61288 : word) = Some W_61288.
Proof. vm_refl. Qed.
Lemma D_61288 : decode_any W_61288 = Some (Op ALU_SUB 12 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6128c : bv 32 := 0x00000593.
Lemma F_6128c : fetch_word Asan.M.loaded_segments (0x6128c : word) = Some W_6128c.
Proof. vm_refl. Qed.
Lemma D_6128c : decode_any W_6128c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61290 : bv 32 := 0x000680e7.
Lemma F_61290 : fetch_word Asan.M.loaded_segments (0x61290 : word) = Some W_61290.
Proof. vm_refl. Qed.
Lemma D_61290 : decode_any W_61290 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61294 : bv 32 := 0x012a0c63.
Lemma F_61294 : fetch_word Asan.M.loaded_segments (0x61294 : word) = Some W_61294.
Proof. vm_refl. Qed.
Lemma D_61294 : decode_any W_61294 = Some (Branch BC_EQ 20 18 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_61298 : bv 32 := 0x0009b683.
Lemma F_61298 : fetch_word Asan.M.loaded_segments (0x61298 : word) = Some W_61298.
Proof. vm_refl. Qed.
Lemma D_61298 : decode_any W_61298 = Some (Load SZ8 true 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6129c : bv 32 := 0x412a0633.
Lemma F_6129c : fetch_word Asan.M.loaded_segments (0x6129c : word) = Some W_6129c.
Proof. vm_refl. Qed.
Lemma D_6129c : decode_any W_6129c = Some (Op ALU_SUB 12 20 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_612a0 : bv 32 := 0x00090513.
Lemma F_612a0 : fetch_word Asan.M.loaded_segments (0x612a0 : word) = Some W_612a0.
Proof. vm_refl. Qed.
Lemma D_612a0 : decode_any W_612a0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_612a4 : bv 32 := 0x00000593.
Lemma F_612a4 : fetch_word Asan.M.loaded_segments (0x612a4 : word) = Some W_612a4.
Proof. vm_refl. Qed.
Lemma D_612a4 : decode_any W_612a4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_612a8 : bv 32 := 0x000680e7.
Lemma F_612a8 : fetch_word Asan.M.loaded_segments (0x612a8 : word) = Some W_612a8.
Proof. vm_refl. Qed.
Lemma D_612a8 : decode_any W_612a8 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_612ac : bv 32 := 0xfff90593.
Lemma F_612ac : fetch_word Asan.M.loaded_segments (0x612ac : word) = Some W_612ac.
Proof. vm_refl. Qed.
Lemma D_612ac : decode_any W_612ac = Some (OpImm ALU_ADD 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_612b0 : bv 32 := 0x00100693.
Lemma F_612b0 : fetch_word Asan.M.loaded_segments (0x612b0 : word) = Some W_612b0.
Proof. vm_refl. Qed.
Lemma D_612b0 : decode_any W_612b0 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_612b4 : bv 32 := 0x00048513.
Lemma F_612b4 : fetch_word Asan.M.loaded_segments (0x612b4 : word) = Some W_612b4.
Proof. vm_refl. Qed.
Lemma D_612b4 : decode_any W_612b4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_612b8 : bv 32 := 0x00000613.
Lemma F_612b8 : fetch_word Asan.M.loaded_segments (0x612b8 : word) = Some W_612b8.
Proof. vm_refl. Qed.
Lemma D_612b8 : decode_any W_612b8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_612bc : bv 32 := 0x03813083.
Lemma F_612bc : fetch_word Asan.M.loaded_segments (0x612bc : word) = Some W_612bc.
Proof. vm_refl. Qed.
Lemma D_612bc : decode_any W_612bc = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_612c0 : bv 32 := 0x03013403.
Lemma F_612c0 : fetch_word Asan.M.loaded_segments (0x612c0 : word) = Some W_612c0.
Proof. vm_refl. Qed.
Lemma D_612c0 : decode_any W_612c0 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_612c4 : bv 32 := 0x02813483.
Lemma F_612c4 : fetch_word Asan.M.loaded_segments (0x612c4 : word) = Some W_612c4.
Proof. vm_refl. Qed.
Lemma D_612c4 : decode_any W_612c4 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_612c8 : bv 32 := 0x02013903.
Lemma F_612c8 : fetch_word Asan.M.loaded_segments (0x612c8 : word) = Some W_612c8.
Proof. vm_refl. Qed.
Lemma D_612c8 : decode_any W_612c8 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_612cc : bv 32 := 0x01813983.
Lemma F_612cc : fetch_word Asan.M.loaded_segments (0x612cc : word) = Some W_612cc.
Proof. vm_refl. Qed.
Lemma D_612cc : decode_any W_612cc = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_612d0 : bv 32 := 0x01013a03.
Lemma F_612d0 : fetch_word Asan.M.loaded_segments (0x612d0 : word) = Some W_612d0.
Proof. vm_refl. Qed.
Lemma D_612d0 : decode_any W_612d0 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_612d4 : bv 32 := 0x00813a83.
Lemma F_612d4 : fetch_word Asan.M.loaded_segments (0x612d4 : word) = Some W_612d4.
Proof. vm_refl. Qed.
Lemma D_612d4 : decode_any W_612d4 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_612d8 : bv 32 := 0x04010113.
Lemma F_612d8 : fetch_word Asan.M.loaded_segments (0x612d8 : word) = Some W_612d8.
Proof. vm_refl. Qed.
Lemma D_612d8 : decode_any W_612d8 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_612dc : bv 32 := 0x5941806f.
Lemma F_612dc : fetch_word Asan.M.loaded_segments (0x612dc : word) = Some W_612dc.
Proof. vm_refl. Qed.
Lemma D_612dc : decode_any W_612dc = Some (Jal 0 99732, 4%Z).
Proof. vm_refl. Qed.

Definition W_612e0 : bv 32 := 0x00060593.
Lemma F_612e0 : fetch_word Asan.M.loaded_segments (0x612e0 : word) = Some W_612e0.
Proof. vm_refl. Qed.
Lemma D_612e0 : decode_any W_612e0 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_612e4 : bv 32 := 0x00c0006f.
Lemma F_612e4 : fetch_word Asan.M.loaded_segments (0x612e4 : word) = Some W_612e4.
Proof. vm_refl. Qed.
Lemma D_612e4 : decode_any W_612e4 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_612e8 : bv 32 := 0x0009b303.
Lemma F_612e8 : fetch_word Asan.M.loaded_segments (0x612e8 : word) = Some W_612e8.
Proof. vm_refl. Qed.
Lemma D_612e8 : decode_any W_612e8 = Some (Load SZ8 true 6 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_612ec : bv 32 := 0x00000593.
Lemma F_612ec : fetch_word Asan.M.loaded_segments (0x612ec : word) = Some W_612ec.
Proof. vm_refl. Qed.
Lemma D_612ec : decode_any W_612ec = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_612f0 : bv 32 := 0x00040613.
Lemma F_612f0 : fetch_word Asan.M.loaded_segments (0x612f0 : word) = Some W_612f0.
Proof. vm_refl. Qed.
Lemma D_612f0 : decode_any W_612f0 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_612f4 : bv 32 := 0x03813083.
Lemma F_612f4 : fetch_word Asan.M.loaded_segments (0x612f4 : word) = Some W_612f4.
Proof. vm_refl. Qed.
Lemma D_612f4 : decode_any W_612f4 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_612f8 : bv 32 := 0x03013403.
Lemma F_612f8 : fetch_word Asan.M.loaded_segments (0x612f8 : word) = Some W_612f8.
Proof. vm_refl. Qed.
Lemma D_612f8 : decode_any W_612f8 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_612fc : bv 32 := 0x02813483.
Lemma F_612fc : fetch_word Asan.M.loaded_segments (0x612fc : word) = Some W_612fc.
Proof. vm_refl. Qed.
Lemma D_612fc : decode_any W_612fc = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_61300 : bv 32 := 0x02013903.
Lemma F_61300 : fetch_word Asan.M.loaded_segments (0x61300 : word) = Some W_61300.
Proof. vm_refl. Qed.
Lemma D_61300 : decode_any W_61300 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_61304 : bv 32 := 0x01813983.
Lemma F_61304 : fetch_word Asan.M.loaded_segments (0x61304 : word) = Some W_61304.
Proof. vm_refl. Qed.
Lemma D_61304 : decode_any W_61304 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_61308 : bv 32 := 0x01013a03.
Lemma F_61308 : fetch_word Asan.M.loaded_segments (0x61308 : word) = Some W_61308.
Proof. vm_refl. Qed.
Lemma D_61308 : decode_any W_61308 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6130c : bv 32 := 0x00813a83.
Lemma F_6130c : fetch_word Asan.M.loaded_segments (0x6130c : word) = Some W_6130c.
Proof. vm_refl. Qed.
Lemma D_6130c : decode_any W_6130c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_61310 : bv 32 := 0x04010113.
Lemma F_61310 : fetch_word Asan.M.loaded_segments (0x61310 : word) = Some W_61310.
Proof. vm_refl. Qed.
Lemma D_61310 : decode_any W_61310 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_61314 : bv 32 := 0x00030067.
Lemma F_61314 : fetch_word Asan.M.loaded_segments (0x61314 : word) = Some W_61314.
Proof. vm_refl. Qed.
Lemma D_61314 : decode_any W_61314 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61318 : bv 32 := 0x00074317.
Lemma F_61318 : fetch_word Asan.M.loaded_segments (0x61318 : word) = Some W_61318.
Proof. vm_refl. Qed.
Lemma D_61318 : decode_any W_61318 = Some (Auipc 6 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_6131c : bv 32 := 0x59833303.
Lemma F_6131c : fetch_word Asan.M.loaded_segments (0x6131c : word) = Some W_6131c.
Proof. vm_refl. Qed.
Lemma D_6131c : decode_any W_6131c = Some (Load SZ8 true 6 6 1432, 4%Z).
Proof. vm_refl. Qed.

Definition W_61320 : bv 32 := 0x04e34303.
Lemma F_61320 : fetch_word Asan.M.loaded_segments (0x61320 : word) = Some W_61320.
Proof. vm_refl. Qed.
Lemma D_61320 : decode_any W_61320 = Some (Load SZ1 false 6 6 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_61324 : bv 32 := 0x08031e63.
Lemma F_61324 : fetch_word Asan.M.loaded_segments (0x61324 : word) = Some W_61324.
Proof. vm_refl. Qed.
Lemma D_61324 : decode_any W_61324 = Some (Branch BC_NE 6 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_61328 : bv 32 := 0x04088063.
Lemma F_61328 : fetch_word Asan.M.loaded_segments (0x61328 : word) = Some W_61328.
Proof. vm_refl. Qed.
Lemma D_61328 : decode_any W_61328 = Some (Branch BC_EQ 17 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6132c : bv 32 := 0x0038d893.
Lemma F_6132c : fetch_word Asan.M.loaded_segments (0x6132c : word) = Some W_6132c.
Proof. vm_refl. Qed.
Lemma D_6132c : decode_any W_6132c = Some (ShiftImm ALU_SRL 17 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61330 : bv 32 := 0x00d888b3.
Lemma F_61330 : fetch_word Asan.M.loaded_segments (0x61330 : word) = Some W_61330.
Proof. vm_refl. Qed.
Lemma D_61330 : decode_any W_61330 = Some (Op ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_61334 : bv 32 := 0x06b8f063.
Lemma F_61334 : fetch_word Asan.M.loaded_segments (0x61334 : word) = Some W_61334.
Proof. vm_refl. Qed.
Lemma D_61334 : decode_any W_61334 = Some (Branch BC_GEU 17 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_61338 : bv 32 := 0x00148893.
Lemma F_61338 : fetch_word Asan.M.loaded_segments (0x61338 : word) = Some W_61338.
Proof. vm_refl. Qed.
Lemma D_61338 : decode_any W_61338 = Some (OpImm ALU_ADD 17 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6133c : bv 32 := 0x00b86863.
Lemma F_6133c : fetch_word Asan.M.loaded_segments (0x6133c : word) = Some W_6133c.
Proof. vm_refl. Qed.
Lemma D_6133c : decode_any W_6133c = Some (Branch BC_LTU 16 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61340 : bv 32 := 0x00375813.
Lemma F_61340 : fetch_word Asan.M.loaded_segments (0x61340 : word) = Some W_61340.
Proof. vm_refl. Qed.
Lemma D_61340 : decode_any W_61340 = Some (ShiftImm ALU_SRL 16 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61344 : bv 32 := 0x01180833.
Lemma F_61344 : fetch_word Asan.M.loaded_segments (0x61344 : word) = Some W_61344.
Proof. vm_refl. Qed.
Lemma D_61344 : decode_any W_61344 = Some (Op ALU_ADD 16 16 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_61348 : bv 32 := 0xeb05fae3.
Lemma F_61348 : fetch_word Asan.M.loaded_segments (0x61348 : word) = Some W_61348.
Proof. vm_refl. Qed.
Lemma D_61348 : decode_any W_61348 = Some (Branch BC_GEU 11 16 7860, 4%Z).
Proof. vm_refl. Qed.

Definition W_6134c : bv 32 := 0x00170713.
Lemma F_6134c : fetch_word Asan.M.loaded_segments (0x6134c : word) = Some W_6134c.
Proof. vm_refl. Qed.
Lemma D_6134c : decode_any W_6134c = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61350 : bv 32 := 0x06e5e863.
Lemma F_61350 : fetch_word Asan.M.loaded_segments (0x61350 : word) = Some W_61350.
Proof. vm_refl. Qed.
Lemma D_61350 : decode_any W_61350 = Some (Branch BC_LTU 11 14 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_61354 : bv 32 := 0x011787b3.
Lemma F_61354 : fetch_word Asan.M.loaded_segments (0x61354 : word) = Some W_61354.
Proof. vm_refl. Qed.
Lemma D_61354 : decode_any W_61354 = Some (Op ALU_ADD 15 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_61358 : bv 32 := 0x0037d793.
Lemma F_61358 : fetch_word Asan.M.loaded_segments (0x61358 : word) = Some W_61358.
Proof. vm_refl. Qed.
Lemma D_61358 : decode_any W_61358 = Some (ShiftImm ALU_SRL 15 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6135c : bv 32 := 0x00d786b3.
Lemma F_6135c : fetch_word Asan.M.loaded_segments (0x6135c : word) = Some W_6135c.
Proof. vm_refl. Qed.
Lemma D_6135c : decode_any W_6135c = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_61360 : bv 32 := 0xe8b6fee3.
Lemma F_61360 : fetch_word Asan.M.loaded_segments (0x61360 : word) = Some W_61360.
Proof. vm_refl. Qed.
Lemma D_61360 : decode_any W_61360 = Some (Branch BC_GEU 13 11 7836, 4%Z).
Proof. vm_refl. Qed.

Definition W_61364 : bv 32 := 0x05c0006f.
Lemma F_61364 : fetch_word Asan.M.loaded_segments (0x61364 : word) = Some W_61364.
Proof. vm_refl. Qed.
Lemma D_61364 : decode_any W_61364 = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_61368 : bv 32 := 0x04048463.
Lemma F_61368 : fetch_word Asan.M.loaded_segments (0x61368 : word) = Some W_61368.
Proof. vm_refl. Qed.
Lemma D_61368 : decode_any W_61368 = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_6136c : bv 32 := 0x0036d713.
Lemma F_6136c : fetch_word Asan.M.loaded_segments (0x6136c : word) = Some W_6136c.
Proof. vm_refl. Qed.
Lemma D_6136c : decode_any W_6136c = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61370 : bv 32 := 0x00970733.
Lemma F_61370 : fetch_word Asan.M.loaded_segments (0x61370 : word) = Some W_61370.
Proof. vm_refl. Qed.
Lemma D_61370 : decode_any W_61370 = Some (Op ALU_ADD 14 14 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_61374 : bv 32 := 0x00070663.
Lemma F_61374 : fetch_word Asan.M.loaded_segments (0x61374 : word) = Some W_61374.
Proof. vm_refl. Qed.
Lemma D_61374 : decode_any W_61374 = Some (Branch BC_EQ 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61378 : bv 32 := 0x00170713.
Lemma F_61378 : fetch_word Asan.M.loaded_segments (0x61378 : word) = Some W_61378.
Proof. vm_refl. Qed.
Lemma D_61378 : decode_any W_61378 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6137c : bv 32 := 0x04e5e263.
Lemma F_6137c : fetch_word Asan.M.loaded_segments (0x6137c : word) = Some W_6137c.
Proof. vm_refl. Qed.
Lemma D_6137c : decode_any W_6137c = Some (Branch BC_LTU 11 14 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_61380 : bv 32 := 0x00128293.
Lemma F_61380 : fetch_word Asan.M.loaded_segments (0x61380 : word) = Some W_61380.
Proof. vm_refl. Qed.
Lemma D_61380 : decode_any W_61380 = Some (OpImm ALU_ADD 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61384 : bv 32 := 0x0032d713.
Lemma F_61384 : fetch_word Asan.M.loaded_segments (0x61384 : word) = Some W_61384.
Proof. vm_refl. Qed.
Lemma D_61384 : decode_any W_61384 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61388 : bv 32 := 0x00d706b3.
Lemma F_61388 : fetch_word Asan.M.loaded_segments (0x61388 : word) = Some W_61388.
Proof. vm_refl. Qed.
Lemma D_61388 : decode_any W_61388 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_6138c : bv 32 := 0xe6b6f8e3.
Lemma F_6138c : fetch_word Asan.M.loaded_segments (0x6138c : word) = Some W_6138c.
Proof. vm_refl. Qed.
Lemma D_6138c : decode_any W_6138c = Some (Branch BC_GEU 13 11 7792, 4%Z).
Proof. vm_refl. Qed.

Definition W_61390 : bv 32 := 0x0300006f.
Lemma F_61390 : fetch_word Asan.M.loaded_segments (0x61390 : word) = Some W_61390.
Proof. vm_refl. Qed.
Lemma D_61390 : decode_any W_61390 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_61394 : bv 32 := 0xe60484e3.
Lemma F_61394 : fetch_word Asan.M.loaded_segments (0x61394 : word) = Some W_61394.
Proof. vm_refl. Qed.
Lemma D_61394 : decode_any W_61394 = Some (Branch BC_EQ 9 0 7784, 4%Z).
Proof. vm_refl. Qed.

Definition W_61398 : bv 32 := 0x0036d693.
Lemma F_61398 : fetch_word Asan.M.loaded_segments (0x61398 : word) = Some W_61398.
Proof. vm_refl. Qed.
Lemma D_61398 : decode_any W_61398 = Some (ShiftImm ALU_SRL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6139c : bv 32 := 0x009686b3.
Lemma F_6139c : fetch_word Asan.M.loaded_segments (0x6139c : word) = Some W_6139c.
Proof. vm_refl. Qed.
Lemma D_6139c : decode_any W_6139c = Some (Op ALU_ADD 13 13 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_613a0 : bv 32 := 0xe4068ee3.
Lemma F_613a0 : fetch_word Asan.M.loaded_segments (0x613a0 : word) = Some W_613a0.
Proof. vm_refl. Qed.
Lemma D_613a0 : decode_any W_613a0 = Some (Branch BC_EQ 13 0 7772, 4%Z).
Proof. vm_refl. Qed.

Definition W_613a4 : bv 32 := 0x00168693.
Lemma F_613a4 : fetch_word Asan.M.loaded_segments (0x613a4 : word) = Some W_613a4.
Proof. vm_refl. Qed.
Lemma D_613a4 : decode_any W_613a4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_613a8 : bv 32 := 0xe4d5fae3.
Lemma F_613a8 : fetch_word Asan.M.loaded_segments (0x613a8 : word) = Some W_613a8.
Proof. vm_refl. Qed.
Lemma D_613a8 : decode_any W_613a8 = Some (Branch BC_GEU 11 13 7764, 4%Z).
Proof. vm_refl. Qed.

Definition W_613ac : bv 32 := 0x0140006f.
Lemma F_613ac : fetch_word Asan.M.loaded_segments (0x613ac : word) = Some W_613ac.
Proof. vm_refl. Qed.
Lemma D_613ac : decode_any W_613ac = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_613b0 : bv 32 := 0x00178793.
Lemma F_613b0 : fetch_word Asan.M.loaded_segments (0x613b0 : word) = Some W_613b0.
Proof. vm_refl. Qed.
Lemma D_613b0 : decode_any W_613b0 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_613b4 : bv 32 := 0x0037d793.
Lemma F_613b4 : fetch_word Asan.M.loaded_segments (0x613b4 : word) = Some W_613b4.
Proof. vm_refl. Qed.
Lemma D_613b4 : decode_any W_613b4 = Some (ShiftImm ALU_SRL 15 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_613b8 : bv 32 := 0xfff78793.
Lemma F_613b8 : fetch_word Asan.M.loaded_segments (0x613b8 : word) = Some W_613b8.
Proof. vm_refl. Qed.
Lemma D_613b8 : decode_any W_613b8 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_613bc : bv 32 := 0xe4b7f0e3.
Lemma F_613bc : fetch_word Asan.M.loaded_segments (0x613bc : word) = Some W_613bc.
Proof. vm_refl. Qed.
Lemma D_613bc : decode_any W_613bc = Some (Branch BC_GEU 15 11 7744, 4%Z).
Proof. vm_refl. Qed.

Definition W_613c0 : bv 32 := 0xfffc0517.
Lemma F_613c0 : fetch_word Asan.M.loaded_segments (0x613c0 : word) = Some W_613c0.
Proof. vm_refl. Qed.
Lemma D_613c0 : decode_any W_613c0 = Some (Auipc 10 1048512, 4%Z).
Proof. vm_refl. Qed.

Definition W_613c4 : bv 32 := 0xfffb3597.
Lemma F_613c4 : fetch_word Asan.M.loaded_segments (0x613c4 : word) = Some W_613c4.
Proof. vm_refl. Qed.
Lemma D_613c4 : decode_any W_613c4 = Some (Auipc 11 1048499, 4%Z).
Proof. vm_refl. Qed.

Definition W_613c8 : bv 32 := 0x8ac50513.
Lemma F_613c8 : fetch_word Asan.M.loaded_segments (0x613c8 : word) = Some W_613c8.
Proof. vm_refl. Qed.
Lemma D_613c8 : decode_any W_613c8 = Some (OpImm ALU_ADD 10 10 2220, 4%Z).
Proof. vm_refl. Qed.

Definition W_613cc : bv 32 := 0xaea58613.
Lemma F_613cc : fetch_word Asan.M.loaded_segments (0x613cc : word) = Some W_613cc.
Proof. vm_refl. Qed.
Lemma D_613cc : decode_any W_613cc = Some (OpImm ALU_ADD 12 11 2794, 4%Z).
Proof. vm_refl. Qed.

Definition W_613d0 : bv 32 := 0x03100593.
Lemma F_613d0 : fetch_word Asan.M.loaded_segments (0x613d0 : word) = Some W_613d0.
Proof. vm_refl. Qed.
Lemma D_613d0 : decode_any W_613d0 = Some (OpImm ALU_ADD 11 0 49, 4%Z).
Proof. vm_refl. Qed.

Definition W_613d4 : bv 32 := 0x00000693.
Lemma F_613d4 : fetch_word Asan.M.loaded_segments (0x613d4 : word) = Some W_613d4.
Proof. vm_refl. Qed.
Lemma D_613d4 : decode_any W_613d4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_613d8 : bv 32 := 0x00000713.
Lemma F_613d8 : fetch_word Asan.M.loaded_segments (0x613d8 : word) = Some W_613d8.
Proof. vm_refl. Qed.
Lemma D_613d8 : decode_any W_613d8 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_613dc : bv 32 := 0x48d170ef.
Lemma F_613dc : fetch_word Asan.M.loaded_segments (0x613dc : word) = Some W_613dc.
Proof. vm_refl. Qed.
Lemma D_613dc : decode_any W_613dc = Some (Jal 1 97420, 4%Z).
Proof. vm_refl. Qed.

Definition W_613e0 : bv 32 := 0xfffc0517.
Lemma F_613e0 : fetch_word Asan.M.loaded_segments (0x613e0 : word) = Some W_613e0.
Proof. vm_refl. Qed.
Lemma D_613e0 : decode_any W_613e0 = Some (Auipc 10 1048512, 4%Z).
Proof. vm_refl. Qed.

Definition W_613e4 : bv 32 := 0xfffbd597.
Lemma F_613e4 : fetch_word Asan.M.loaded_segments (0x613e4 : word) = Some W_613e4.
Proof. vm_refl. Qed.
Lemma D_613e4 : decode_any W_613e4 = Some (Auipc 11 1048509, 4%Z).
Proof. vm_refl. Qed.

Definition W_613e8 : bv 32 := 0x88c50513.
Lemma F_613e8 : fetch_word Asan.M.loaded_segments (0x613e8 : word) = Some W_613e8.
Proof. vm_refl. Qed.
Lemma D_613e8 : decode_any W_613e8 = Some (OpImm ALU_ADD 10 10 2188, 4%Z).
Proof. vm_refl. Qed.

Definition W_613ec : bv 32 := 0x44058613.
Lemma F_613ec : fetch_word Asan.M.loaded_segments (0x613ec : word) = Some W_613ec.
Proof. vm_refl. Qed.
Lemma D_613ec : decode_any W_613ec = Some (OpImm ALU_ADD 12 11 1088, 4%Z).
Proof. vm_refl. Qed.

Definition W_613f0 : bv 32 := 0x02700593.
Lemma F_613f0 : fetch_word Asan.M.loaded_segments (0x613f0 : word) = Some W_613f0.
Proof. vm_refl. Qed.
Lemma D_613f0 : decode_any W_613f0 = Some (OpImm ALU_ADD 11 0 39, 4%Z).
Proof. vm_refl. Qed.

Definition W_613f4 : bv 32 := 0x00000693.
Lemma F_613f4 : fetch_word Asan.M.loaded_segments (0x613f4 : word) = Some W_613f4.
Proof. vm_refl. Qed.
Lemma D_613f4 : decode_any W_613f4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_613f8 : bv 32 := 0x00000713.
Lemma F_613f8 : fetch_word Asan.M.loaded_segments (0x613f8 : word) = Some W_613f8.
Proof. vm_refl. Qed.
Lemma D_613f8 : decode_any W_613f8 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_613fc : bv 32 := 0x46d170ef.
Lemma F_613fc : fetch_word Asan.M.loaded_segments (0x613fc : word) = Some W_613fc.
Proof. vm_refl. Qed.
Lemma D_613fc : decode_any W_613fc = Some (Jal 1 97388, 4%Z).
Proof. vm_refl. Qed.

Definition W_61400 : bv 32 := 0x00074317.
Lemma F_61400 : fetch_word Asan.M.loaded_segments (0x61400 : word) = Some W_61400.
Proof. vm_refl. Qed.
Lemma D_61400 : decode_any W_61400 = Some (Auipc 6 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_61404 : bv 32 := 0x4f833303.
Lemma F_61404 : fetch_word Asan.M.loaded_segments (0x61404 : word) = Some W_61404.
Proof. vm_refl. Qed.
Lemma D_61404 : decode_any W_61404 = Some (Load SZ8 true 6 6 1272, 4%Z).
Proof. vm_refl. Qed.

Definition W_61408 : bv 32 := 0xcc0308e3.
Lemma F_61408 : fetch_word Asan.M.loaded_segments (0x61408 : word) = Some W_61408.
Proof. vm_refl. Qed.
Lemma D_61408 : decode_any W_61408 = Some (Branch BC_EQ 6 0 7376, 4%Z).
Proof. vm_refl. Qed.

Definition W_6140c : bv 32 := 0x00074517.
Lemma F_6140c : fetch_word Asan.M.loaded_segments (0x6140c : word) = Some W_6140c.
Proof. vm_refl. Qed.
Lemma D_6140c : decode_any W_6140c = Some (Auipc 10 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_61410 : bv 32 := 0x4f453503.
Lemma F_61410 : fetch_word Asan.M.loaded_segments (0x61410 : word) = Some W_61410.
Proof. vm_refl. Qed.
Lemma D_61410 : decode_any W_61410 = Some (Load SZ8 true 10 10 1268, 4%Z).
Proof. vm_refl. Qed.

Definition W_61414 : bv 32 := 0x00052503.
Lemma F_61414 : fetch_word Asan.M.loaded_segments (0x61414 : word) = Some W_61414.
Proof. vm_refl. Qed.
Lemma D_61414 : decode_any W_61414 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61418 : bv 32 := 0x04051c63.
Lemma F_61418 : fetch_word Asan.M.loaded_segments (0x61418 : word) = Some W_61418.
Proof. vm_refl. Qed.
Lemma D_61418 : decode_any W_61418 = Some (Branch BC_NE 10 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_6141c : bv 32 := 0x0000006f.
Lemma F_6141c : fetch_word Asan.M.loaded_segments (0x6141c : word) = Some W_6141c.
Proof. vm_refl. Qed.
Lemma D_6141c : decode_any W_6141c = Some (Jal 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61420 : bv 32 := 0xfffc0517.
Lemma F_61420 : fetch_word Asan.M.loaded_segments (0x61420 : word) = Some W_61420.
Proof. vm_refl. Qed.
Lemma D_61420 : decode_any W_61420 = Some (Auipc 10 1048512, 4%Z).
Proof. vm_refl. Qed.

Definition W_61424 : bv 32 := 0xfffb2597.
Lemma F_61424 : fetch_word Asan.M.loaded_segments (0x61424 : word) = Some W_61424.
Proof. vm_refl. Qed.
Lemma D_61424 : decode_any W_61424 = Some (Auipc 11 1048498, 4%Z).
Proof. vm_refl. Qed.

Definition W_61428 : bv 32 := 0x84c50513.
Lemma F_61428 : fetch_word Asan.M.loaded_segments (0x61428 : word) = Some W_61428.
Proof. vm_refl. Qed.
Lemma D_61428 : decode_any W_61428 = Some (OpImm ALU_ADD 10 10 2124, 4%Z).
Proof. vm_refl. Qed.

Definition W_6142c : bv 32 := 0x0f558613.
Lemma F_6142c : fetch_word Asan.M.loaded_segments (0x6142c : word) = Some W_6142c.
Proof. vm_refl. Qed.
Lemma D_6142c : decode_any W_6142c = Some (OpImm ALU_ADD 12 11 245, 4%Z).
Proof. vm_refl. Qed.

Definition W_61430 : bv 32 := 0x03000593.
Lemma F_61430 : fetch_word Asan.M.loaded_segments (0x61430 : word) = Some W_61430.
Proof. vm_refl. Qed.
Lemma D_61430 : decode_any W_61430 = Some (OpImm ALU_ADD 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_61434 : bv 32 := 0x00000693.
Lemma F_61434 : fetch_word Asan.M.loaded_segments (0x61434 : word) = Some W_61434.
Proof. vm_refl. Qed.
Lemma D_61434 : decode_any W_61434 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61438 : bv 32 := 0x00000713.
Lemma F_61438 : fetch_word Asan.M.loaded_segments (0x61438 : word) = Some W_61438.
Proof. vm_refl. Qed.
Lemma D_61438 : decode_any W_61438 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6143c : bv 32 := 0x42d170ef.
Lemma F_6143c : fetch_word Asan.M.loaded_segments (0x6143c : word) = Some W_6143c.
Proof. vm_refl. Qed.
Lemma D_6143c : decode_any W_6143c = Some (Jal 1 97324, 4%Z).
Proof. vm_refl. Qed.

Definition W_61440 : bv 32 := 0xfffc0517.
Lemma F_61440 : fetch_word Asan.M.loaded_segments (0x61440 : word) = Some W_61440.
Proof. vm_refl. Qed.
Lemma D_61440 : decode_any W_61440 = Some (Auipc 10 1048512, 4%Z).
Proof. vm_refl. Qed.

Definition W_61444 : bv 32 := 0xfffb8597.
Lemma F_61444 : fetch_word Asan.M.loaded_segments (0x61444 : word) = Some W_61444.
Proof. vm_refl. Qed.
Lemma D_61444 : decode_any W_61444 = Some (Auipc 11 1048504, 4%Z).
Proof. vm_refl. Qed.

Definition W_61448 : bv 32 := 0x82c50513.
Lemma F_61448 : fetch_word Asan.M.loaded_segments (0x61448 : word) = Some W_61448.
Proof. vm_refl. Qed.
Lemma D_61448 : decode_any W_61448 = Some (OpImm ALU_ADD 10 10 2092, 4%Z).
Proof. vm_refl. Qed.

Definition W_6144c : bv 32 := 0xabb58613.
Lemma F_6144c : fetch_word Asan.M.loaded_segments (0x6144c : word) = Some W_6144c.
Proof. vm_refl. Qed.
Lemma D_6144c : decode_any W_6144c = Some (OpImm ALU_ADD 12 11 2747, 4%Z).
Proof. vm_refl. Qed.

Definition W_61450 : bv 32 := 0x03200593.
Lemma F_61450 : fetch_word Asan.M.loaded_segments (0x61450 : word) = Some W_61450.
Proof. vm_refl. Qed.
Lemma D_61450 : decode_any W_61450 = Some (OpImm ALU_ADD 11 0 50, 4%Z).
Proof. vm_refl. Qed.

Definition W_61454 : bv 32 := 0x00000693.
Lemma F_61454 : fetch_word Asan.M.loaded_segments (0x61454 : word) = Some W_61454.
Proof. vm_refl. Qed.
Lemma D_61454 : decode_any W_61454 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61458 : bv 32 := 0x00000713.
Lemma F_61458 : fetch_word Asan.M.loaded_segments (0x61458 : word) = Some W_61458.
Proof. vm_refl. Qed.
Lemma D_61458 : decode_any W_61458 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6145c : bv 32 := 0x40d170ef.
Lemma F_6145c : fetch_word Asan.M.loaded_segments (0x6145c : word) = Some W_6145c.
Proof. vm_refl. Qed.
Lemma D_6145c : decode_any W_6145c = Some (Jal 1 97292, 4%Z).
Proof. vm_refl. Qed.

Definition W_61460 : bv 32 := 0xfffb1517.
Lemma F_61460 : fetch_word Asan.M.loaded_segments (0x61460 : word) = Some W_61460.
Proof. vm_refl. Qed.
Lemma D_61460 : decode_any W_61460 = Some (Auipc 10 1048497, 4%Z).
Proof. vm_refl. Qed.

Definition W_61464 : bv 32 := 0x30a50513.
Lemma F_61464 : fetch_word Asan.M.loaded_segments (0x61464 : word) = Some W_61464.
Proof. vm_refl. Qed.
Lemma D_61464 : decode_any W_61464 = Some (OpImm ALU_ADD 10 10 778, 4%Z).
Proof. vm_refl. Qed.

Definition W_61468 : bv 32 := 0x5ad0c0ef.
Lemma F_61468 : fetch_word Asan.M.loaded_segments (0x61468 : word) = Some W_61468.
Proof. vm_refl. Qed.
Lemma D_61468 : decode_any W_61468 = Some (Jal 1 52652, 4%Z).
Proof. vm_refl. Qed.

Definition W_6146c : bv 32 := 0x331170ef.
Lemma F_6146c : fetch_word Asan.M.loaded_segments (0x6146c : word) = Some W_6146c.
Proof. vm_refl. Qed.
Lemma D_6146c : decode_any W_6146c = Some (Jal 1 97072, 4%Z).
Proof. vm_refl. Qed.

Definition W_61470 : bv 32 := 0x455190ef.
Lemma F_61470 : fetch_word Asan.M.loaded_segments (0x61470 : word) = Some W_61470.
Proof. vm_refl. Qed.
Lemma D_61470 : decode_any W_61470 = Some (Jal 1 105556, 4%Z).
Proof. vm_refl. Qed.

Definition W_61474 : bv 32 := 0x00074597.
Lemma F_61474 : fetch_word Asan.M.loaded_segments (0x61474 : word) = Some W_61474.
Proof. vm_refl. Qed.
Lemma D_61474 : decode_any W_61474 = Some (Auipc 11 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_61478 : bv 32 := 0x4445b583.
Lemma F_61478 : fetch_word Asan.M.loaded_segments (0x61478 : word) = Some W_61478.
Proof. vm_refl. Qed.
Lemma D_61478 : decode_any W_61478 = Some (Load SZ8 true 11 11 1092, 4%Z).
Proof. vm_refl. Qed.

Definition W_6147c : bv 32 := 0x0005b583.
Lemma F_6147c : fetch_word Asan.M.loaded_segments (0x6147c : word) = Some W_6147c.
Proof. vm_refl. Qed.
Lemma D_6147c : decode_any W_6147c = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_61480 : bv 32 := 0xfff58613.
Lemma F_61480 : fetch_word Asan.M.loaded_segments (0x61480 : word) = Some W_61480.
Proof. vm_refl. Qed.
Lemma D_61480 : decode_any W_61480 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61484 : bv 32 := 0x00c5b6b3.
Lemma F_61484 : fetch_word Asan.M.loaded_segments (0x61484 : word) = Some W_61484.
Proof. vm_refl. Qed.
Lemma D_61484 : decode_any W_61484 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61488 : bv 32 := 0xfff68693.
Lemma F_61488 : fetch_word Asan.M.loaded_segments (0x61488 : word) = Some W_61488.
Proof. vm_refl. Qed.
Lemma D_61488 : decode_any W_61488 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6148c : bv 32 := 0x00c6f6b3.
Lemma F_6148c : fetch_word Asan.M.loaded_segments (0x6148c : word) = Some W_6148c.
Proof. vm_refl. Qed.
Lemma D_6148c : decode_any W_6148c = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61490 : bv 32 := 0x04a6f263.
Lemma F_61490 : fetch_word Asan.M.loaded_segments (0x61490 : word) = Some W_61490.
Proof. vm_refl. Qed.
Lemma D_61490 : decode_any W_61490 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_61494 : bv 32 := 0x00074697.
Lemma F_61494 : fetch_word Asan.M.loaded_segments (0x61494 : word) = Some W_61494.
Proof. vm_refl. Qed.
Lemma D_61494 : decode_any W_61494 = Some (Auipc 13 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_61498 : bv 32 := 0x42c6b683.
Lemma F_61498 : fetch_word Asan.M.loaded_segments (0x61498 : word) = Some W_61498.
Proof. vm_refl. Qed.
Lemma D_61498 : decode_any W_61498 = Some (Load SZ8 true 13 13 1068, 4%Z).
Proof. vm_refl. Qed.

Definition W_6149c : bv 32 := 0x00074717.
Lemma F_6149c : fetch_word Asan.M.loaded_segments (0x6149c : word) = Some W_6149c.
Proof. vm_refl. Qed.
Lemma D_6149c : decode_any W_6149c = Some (Auipc 14 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_614a0 : bv 32 := 0x42c73703.
Lemma F_614a0 : fetch_word Asan.M.loaded_segments (0x614a0 : word) = Some W_614a0.
Proof. vm_refl. Qed.
Lemma D_614a0 : decode_any W_614a0 = Some (Load SZ8 true 14 14 1068, 4%Z).
Proof. vm_refl. Qed.

Definition W_614a4 : bv 32 := 0x0006b803.
Lemma F_614a4 : fetch_word Asan.M.loaded_segments (0x614a4 : word) = Some W_614a4.
Proof. vm_refl. Qed.
Lemma D_614a4 : decode_any W_614a4 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_614a8 : bv 32 := 0x00073683.
Lemma F_614a8 : fetch_word Asan.M.loaded_segments (0x614a8 : word) = Some W_614a8.
Proof. vm_refl. Qed.
Lemma D_614a8 : decode_any W_614a8 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_614ac : bv 32 := 0xfff80793.
Lemma F_614ac : fetch_word Asan.M.loaded_segments (0x614ac : word) = Some W_614ac.
Proof. vm_refl. Qed.
Lemma D_614ac : decode_any W_614ac = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_614b0 : bv 32 := 0x00a7f463.
Lemma F_614b0 : fetch_word Asan.M.loaded_segments (0x614b0 : word) = Some W_614b0.
Proof. vm_refl. Qed.
Lemma D_614b0 : decode_any W_614b0 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_614b4 : bv 32 := 0x02a6f063.
Lemma F_614b4 : fetch_word Asan.M.loaded_segments (0x614b4 : word) = Some W_614b4.
Proof. vm_refl. Qed.
Lemma D_614b4 : decode_any W_614b4 = Some (Branch BC_GEU 13 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_614b8 : bv 32 := 0x00074717.
Lemma F_614b8 : fetch_word Asan.M.loaded_segments (0x614b8 : word) = Some W_614b8.
Proof. vm_refl. Qed.
Lemma D_614b8 : decode_any W_614b8 = Some (Auipc 14 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_614bc : bv 32 := 0x41873703.
Lemma F_614bc : fetch_word Asan.M.loaded_segments (0x614bc : word) = Some W_614bc.
Proof. vm_refl. Qed.
Lemma D_614bc : decode_any W_614bc = Some (Load SZ8 true 14 14 1048, 4%Z).
Proof. vm_refl. Qed.

Definition W_614c0 : bv 32 := 0x00073283.
Lemma F_614c0 : fetch_word Asan.M.loaded_segments (0x614c0 : word) = Some W_614c0.
Proof. vm_refl. Qed.
Lemma D_614c0 : decode_any W_614c0 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_614c4 : bv 32 := 0x0032d713.
Lemma F_614c4 : fetch_word Asan.M.loaded_segments (0x614c4 : word) = Some W_614c4.
Proof. vm_refl. Qed.
Lemma D_614c4 : decode_any W_614c4 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_614c8 : bv 32 := 0x00b708b3.
Lemma F_614c8 : fetch_word Asan.M.loaded_segments (0x614c8 : word) = Some W_614c8.
Proof. vm_refl. Qed.
Lemma D_614c8 : decode_any W_614c8 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_614cc : bv 32 := 0x00a2ea63.
Lemma F_614cc : fetch_word Asan.M.loaded_segments (0x614cc : word) = Some W_614cc.
Proof. vm_refl. Qed.
Lemma D_614cc : decode_any W_614cc = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_614d0 : bv 32 := 0x00a8f863.
Lemma F_614d0 : fetch_word Asan.M.loaded_segments (0x614d0 : word) = Some W_614d0.
Proof. vm_refl. Qed.
Lemma D_614d0 : decode_any W_614d0 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_614d4 : bv 32 := 0x00355513.
Lemma F_614d4 : fetch_word Asan.M.loaded_segments (0x614d4 : word) = Some W_614d4.
Proof. vm_refl. Qed.
Lemma D_614d4 : decode_any W_614d4 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_614d8 : bv 32 := 0x00a58533.
Lemma F_614d8 : fetch_word Asan.M.loaded_segments (0x614d8 : word) = Some W_614d8.
Proof. vm_refl. Qed.
Lemma D_614d8 : decode_any W_614d8 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_614dc : bv 32 := 0x00008067.
Lemma F_614dc : fetch_word Asan.M.loaded_segments (0x614dc : word) = Some W_614dc.
Proof. vm_refl. Qed.
Lemma D_614dc : decode_any W_614dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_614e0 : bv 32 := 0x00074297.
Lemma F_614e0 : fetch_word Asan.M.loaded_segments (0x614e0 : word) = Some W_614e0.
Proof. vm_refl. Qed.
Lemma D_614e0 : decode_any W_614e0 = Some (Auipc 5 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_614e4 : bv 32 := 0x3d02b283.
Lemma F_614e4 : fetch_word Asan.M.loaded_segments (0x614e4 : word) = Some W_614e4.
Proof. vm_refl. Qed.
Lemma D_614e4 : decode_any W_614e4 = Some (Load SZ8 true 5 5 976, 4%Z).
Proof. vm_refl. Qed.

Definition W_614e8 : bv 32 := 0x04e2c283.
Lemma F_614e8 : fetch_word Asan.M.loaded_segments (0x614e8 : word) = Some W_614e8.
Proof. vm_refl. Qed.
Lemma D_614e8 : decode_any W_614e8 = Some (Load SZ1 false 5 5 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_614ec : bv 32 := 0x08029e63.
Lemma F_614ec : fetch_word Asan.M.loaded_segments (0x614ec : word) = Some W_614ec.
Proof. vm_refl. Qed.
Lemma D_614ec : decode_any W_614ec = Some (Branch BC_NE 5 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_614f0 : bv 32 := 0x04080063.
Lemma F_614f0 : fetch_word Asan.M.loaded_segments (0x614f0 : word) = Some W_614f0.
Proof. vm_refl. Qed.
Lemma D_614f0 : decode_any W_614f0 = Some (Branch BC_EQ 16 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_614f4 : bv 32 := 0x00385813.
Lemma F_614f4 : fetch_word Asan.M.loaded_segments (0x614f4 : word) = Some W_614f4.
Proof. vm_refl. Qed.
Lemma D_614f4 : decode_any W_614f4 = Some (ShiftImm ALU_SRL 16 16 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_614f8 : bv 32 := 0x00c80833.
Lemma F_614f8 : fetch_word Asan.M.loaded_segments (0x614f8 : word) = Some W_614f8.
Proof. vm_refl. Qed.
Lemma D_614f8 : decode_any W_614f8 = Some (Op ALU_ADD 16 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_614fc : bv 32 := 0x06a87063.
Lemma F_614fc : fetch_word Asan.M.loaded_segments (0x614fc : word) = Some W_614fc.
Proof. vm_refl. Qed.
Lemma D_614fc : decode_any W_614fc = Some (Branch BC_GEU 16 10 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_61500 : bv 32 := 0x00158813.
Lemma F_61500 : fetch_word Asan.M.loaded_segments (0x61500 : word) = Some W_61500.
Proof. vm_refl. Qed.
Lemma D_61500 : decode_any W_61500 = Some (OpImm ALU_ADD 16 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61504 : bv 32 := 0x00a7e863.
Lemma F_61504 : fetch_word Asan.M.loaded_segments (0x61504 : word) = Some W_61504.
Proof. vm_refl. Qed.
Lemma D_61504 : decode_any W_61504 = Some (Branch BC_LTU 15 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61508 : bv 32 := 0x0036d793.
Lemma F_61508 : fetch_word Asan.M.loaded_segments (0x61508 : word) = Some W_61508.
Proof. vm_refl. Qed.
Lemma D_61508 : decode_any W_61508 = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6150c : bv 32 := 0x010787b3.
Lemma F_6150c : fetch_word Asan.M.loaded_segments (0x6150c : word) = Some W_6150c.
Proof. vm_refl. Qed.
Lemma D_6150c : decode_any W_6150c = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61510 : bv 32 := 0xfcf572e3.
Lemma F_61510 : fetch_word Asan.M.loaded_segments (0x61510 : word) = Some W_61510.
Proof. vm_refl. Qed.
Lemma D_61510 : decode_any W_61510 = Some (Branch BC_GEU 10 15 8132, 4%Z).
Proof. vm_refl. Qed.

Definition W_61514 : bv 32 := 0x00168693.
Lemma F_61514 : fetch_word Asan.M.loaded_segments (0x61514 : word) = Some W_61514.
Proof. vm_refl. Qed.
Lemma D_61514 : decode_any W_61514 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61518 : bv 32 := 0x06d56863.
Lemma F_61518 : fetch_word Asan.M.loaded_segments (0x61518 : word) = Some W_61518.
Proof. vm_refl. Qed.
Lemma D_61518 : decode_any W_61518 = Some (Branch BC_LTU 10 13 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_6151c : bv 32 := 0x01070733.
Lemma F_6151c : fetch_word Asan.M.loaded_segments (0x6151c : word) = Some W_6151c.
Proof. vm_refl. Qed.
Lemma D_6151c : decode_any W_6151c = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_61520 : bv 32 := 0x00375713.
Lemma F_61520 : fetch_word Asan.M.loaded_segments (0x61520 : word) = Some W_61520.
Proof. vm_refl. Qed.
Lemma D_61520 : decode_any W_61520 = Some (ShiftImm ALU_SRL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61524 : bv 32 := 0x00c70633.
Lemma F_61524 : fetch_word Asan.M.loaded_segments (0x61524 : word) = Some W_61524.
Proof. vm_refl. Qed.
Lemma D_61524 : decode_any W_61524 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61528 : bv 32 := 0xfaa676e3.
Lemma F_61528 : fetch_word Asan.M.loaded_segments (0x61528 : word) = Some W_61528.
Proof. vm_refl. Qed.
Lemma D_61528 : decode_any W_61528 = Some (Branch BC_GEU 12 10 8108, 4%Z).
Proof. vm_refl. Qed.

Definition W_6152c : bv 32 := 0x05c0006f.
Lemma F_6152c : fetch_word Asan.M.loaded_segments (0x6152c : word) = Some W_6152c.
Proof. vm_refl. Qed.
Lemma D_6152c : decode_any W_6152c = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_61530 : bv 32 := 0x04058463.
Lemma F_61530 : fetch_word Asan.M.loaded_segments (0x61530 : word) = Some W_61530.
Proof. vm_refl. Qed.
Lemma D_61530 : decode_any W_61530 = Some (Branch BC_EQ 11 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_61534 : bv 32 := 0x00365693.
Lemma F_61534 : fetch_word Asan.M.loaded_segments (0x61534 : word) = Some W_61534.
Proof. vm_refl. Qed.
Lemma D_61534 : decode_any W_61534 = Some (ShiftImm ALU_SRL 13 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61538 : bv 32 := 0x00b686b3.
Lemma F_61538 : fetch_word Asan.M.loaded_segments (0x61538 : word) = Some W_61538.
Proof. vm_refl. Qed.
Lemma D_61538 : decode_any W_61538 = Some (Op ALU_ADD 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6153c : bv 32 := 0x00068663.
Lemma F_6153c : fetch_word Asan.M.loaded_segments (0x6153c : word) = Some W_6153c.
Proof. vm_refl. Qed.
Lemma D_6153c : decode_any W_6153c = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61540 : bv 32 := 0x00168693.
Lemma F_61540 : fetch_word Asan.M.loaded_segments (0x61540 : word) = Some W_61540.
Proof. vm_refl. Qed.
Lemma D_61540 : decode_any W_61540 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61544 : bv 32 := 0x04d56263.
Lemma F_61544 : fetch_word Asan.M.loaded_segments (0x61544 : word) = Some W_61544.
Proof. vm_refl. Qed.
Lemma D_61544 : decode_any W_61544 = Some (Branch BC_LTU 10 13 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_61548 : bv 32 := 0x00188893.
Lemma F_61548 : fetch_word Asan.M.loaded_segments (0x61548 : word) = Some W_61548.
Proof. vm_refl. Qed.
Lemma D_61548 : decode_any W_61548 = Some (OpImm ALU_ADD 17 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6154c : bv 32 := 0x0038d693.
Lemma F_6154c : fetch_word Asan.M.loaded_segments (0x6154c : word) = Some W_6154c.
Proof. vm_refl. Qed.
Lemma D_6154c : decode_any W_6154c = Some (ShiftImm ALU_SRL 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61550 : bv 32 := 0x00c68633.
Lemma F_61550 : fetch_word Asan.M.loaded_segments (0x61550 : word) = Some W_61550.
Proof. vm_refl. Qed.
Lemma D_61550 : decode_any W_61550 = Some (Op ALU_ADD 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_61554 : bv 32 := 0xf8a670e3.
Lemma F_61554 : fetch_word Asan.M.loaded_segments (0x61554 : word) = Some W_61554.
Proof. vm_refl. Qed.
Lemma D_61554 : decode_any W_61554 = Some (Branch BC_GEU 12 10 8064, 4%Z).
Proof. vm_refl. Qed.

Definition W_61558 : bv 32 := 0x0300006f.
Lemma F_61558 : fetch_word Asan.M.loaded_segments (0x61558 : word) = Some W_61558.
Proof. vm_refl. Qed.
Lemma D_61558 : decode_any W_61558 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6155c : bv 32 := 0xf6058ce3.
Lemma F_6155c : fetch_word Asan.M.loaded_segments (0x6155c : word) = Some W_6155c.
Proof. vm_refl. Qed.
Lemma D_6155c : decode_any W_6155c = Some (Branch BC_EQ 11 0 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_61560 : bv 32 := 0x00365613.
Lemma F_61560 : fetch_word Asan.M.loaded_segments (0x61560 : word) = Some W_61560.
Proof. vm_refl. Qed.
Lemma D_61560 : decode_any W_61560 = Some (ShiftImm ALU_SRL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61564 : bv 32 := 0x00b60633.
Lemma F_61564 : fetch_word Asan.M.loaded_segments (0x61564 : word) = Some W_61564.
Proof. vm_refl. Qed.
Lemma D_61564 : decode_any W_61564 = Some (Op ALU_ADD 12 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_61568 : bv 32 := 0xf60606e3.
Lemma F_61568 : fetch_word Asan.M.loaded_segments (0x61568 : word) = Some W_61568.
Proof. vm_refl. Qed.
Lemma D_61568 : decode_any W_61568 = Some (Branch BC_EQ 12 0 8044, 4%Z).
Proof. vm_refl. Qed.

Definition W_6156c : bv 32 := 0x00160613.
Lemma F_6156c : fetch_word Asan.M.loaded_segments (0x6156c : word) = Some W_6156c.
Proof. vm_refl. Qed.
Lemma D_6156c : decode_any W_6156c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_61570 : bv 32 := 0xf6c572e3.
Lemma F_61570 : fetch_word Asan.M.loaded_segments (0x61570 : word) = Some W_61570.
Proof. vm_refl. Qed.
Lemma D_61570 : decode_any W_61570 = Some (Branch BC_GEU 10 12 8036, 4%Z).
Proof. vm_refl. Qed.

Definition W_61574 : bv 32 := 0x0140006f.
Lemma F_61574 : fetch_word Asan.M.loaded_segments (0x61574 : word) = Some W_61574.
Proof. vm_refl. Qed.
Lemma D_61574 : decode_any W_61574 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_61578 : bv 32 := 0x00170713.
Lemma F_61578 : fetch_word Asan.M.loaded_segments (0x61578 : word) = Some W_61578.
Proof. vm_refl. Qed.
Lemma D_61578 : decode_any W_61578 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6157c : bv 32 := 0x00375713.
Lemma F_6157c : fetch_word Asan.M.loaded_segments (0x6157c : word) = Some W_6157c.
Proof. vm_refl. Qed.
Lemma D_6157c : decode_any W_6157c = Some (ShiftImm ALU_SRL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_61580 : bv 32 := 0xfff70713.
Lemma F_61580 : fetch_word Asan.M.loaded_segments (0x61580 : word) = Some W_61580.
Proof. vm_refl. Qed.
Lemma D_61580 : decode_any W_61580 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_61584 : bv 32 := 0xf4a778e3.
Lemma F_61584 : fetch_word Asan.M.loaded_segments (0x61584 : word) = Some W_61584.
Proof. vm_refl. Qed.
Lemma D_61584 : decode_any W_61584 = Some (Branch BC_GEU 14 10 8016, 4%Z).
Proof. vm_refl. Qed.

Definition W_61588 : bv 32 := 0xff010113.
Lemma F_61588 : fetch_word Asan.M.loaded_segments (0x61588 : word) = Some W_61588.
Proof. vm_refl. Qed.
Lemma D_61588 : decode_any W_61588 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_6158c : bv 32 := 0x00113423.
Lemma F_6158c : fetch_word Asan.M.loaded_segments (0x6158c : word) = Some W_6158c.
Proof. vm_refl. Qed.
Lemma D_6158c : decode_any W_6158c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_61590 : bv 32 := 0xfffc0517.
Lemma F_61590 : fetch_word Asan.M.loaded_segments (0x61590 : word) = Some W_61590.
Proof. vm_refl. Qed.
Lemma D_61590 : decode_any W_61590 = Some (Auipc 10 1048512, 4%Z).
Proof. vm_refl. Qed.

Definition W_61594 : bv 32 := 0xfffb6597.
Lemma F_61594 : fetch_word Asan.M.loaded_segments (0x61594 : word) = Some W_61594.
Proof. vm_refl. Qed.
Lemma D_61594 : decode_any W_61594 = Some (Auipc 11 1048502, 4%Z).
Proof. vm_refl. Qed.

Definition W_61598 : bv 32 := 0xdfd50513.
Lemma F_61598 : fetch_word Asan.M.loaded_segments (0x61598 : word) = Some W_61598.
Proof. vm_refl. Qed.
Lemma D_61598 : decode_any W_61598 = Some (OpImm ALU_ADD 10 10 3581, 4%Z).
Proof. vm_refl. Qed.

Definition W_6159c : bv 32 := 0x35758613.
Lemma F_6159c : fetch_word Asan.M.loaded_segments (0x6159c : word) = Some W_6159c.
Proof. vm_refl. Qed.
Lemma D_6159c : decode_any W_6159c = Some (OpImm ALU_ADD 12 11 855, 4%Z).
Proof. vm_refl. Qed.

Definition W_615a0 : bv 32 := 0x17700593.
Lemma F_615a0 : fetch_word Asan.M.loaded_segments (0x615a0 : word) = Some W_615a0.
Proof. vm_refl. Qed.
Lemma D_615a0 : decode_any W_615a0 = Some (OpImm ALU_ADD 11 0 375, 4%Z).
Proof. vm_refl. Qed.

Definition W_615a4 : bv 32 := 0x00000693.
Lemma F_615a4 : fetch_word Asan.M.loaded_segments (0x615a4 : word) = Some W_615a4.
Proof. vm_refl. Qed.
Lemma D_615a4 : decode_any W_615a4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_615a8 : bv 32 := 0x00000713.
Lemma F_615a8 : fetch_word Asan.M.loaded_segments (0x615a8 : word) = Some W_615a8.
Proof. vm_refl. Qed.
Lemma D_615a8 : decode_any W_615a8 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_615ac : bv 32 := 0x2bd170ef.
Lemma F_615ac : fetch_word Asan.M.loaded_segments (0x615ac : word) = Some W_615ac.
Proof. vm_refl. Qed.
Lemma D_615ac : decode_any W_615ac = Some (Jal 1 96956, 4%Z).
Proof. vm_refl. Qed.
