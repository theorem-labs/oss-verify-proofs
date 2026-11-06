(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_60fc0 : bv 32 := 0xfff48693.
Lemma F_60fc0 : fetch_word Asan.M.loaded_segments (0x60fc0 : word) = Some W_60fc0.
Proof. vm_refl. Qed.
Lemma D_60fc0 : decode_any W_60fc0 = Some (OpImm ALU_ADD 13 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60fc4 : bv 32 := 0x00d4b733.
Lemma F_60fc4 : fetch_word Asan.M.loaded_segments (0x60fc4 : word) = Some W_60fc4.
Proof. vm_refl. Qed.
Lemma D_60fc4 : decode_any W_60fc4 = Some (Op ALU_SLTU 14 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60fc8 : bv 32 := 0xfff70713.
Lemma F_60fc8 : fetch_word Asan.M.loaded_segments (0x60fc8 : word) = Some W_60fc8.
Proof. vm_refl. Qed.
Lemma D_60fc8 : decode_any W_60fc8 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60fcc : bv 32 := 0x00d77733.
Lemma F_60fcc : fetch_word Asan.M.loaded_segments (0x60fcc : word) = Some W_60fcc.
Proof. vm_refl. Qed.
Lemma D_60fcc : decode_any W_60fcc = Some (Op ALU_AND 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60fd0 : bv 32 := 0x1ca77c63.
Lemma F_60fd0 : fetch_word Asan.M.loaded_segments (0x60fd0 : word) = Some W_60fd0.
Proof. vm_refl. Qed.
Lemma D_60fd0 : decode_any W_60fd0 = Some (Branch BC_GEU 14 10 472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60fd4 : bv 32 := 0x00075797.
Lemma F_60fd4 : fetch_word Asan.M.loaded_segments (0x60fd4 : word) = Some W_60fd4.
Proof. vm_refl. Qed.
Lemma D_60fd4 : decode_any W_60fd4 = Some (Auipc 15 117, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60fd8 : bv 32 := 0x8ec7b783.
Lemma F_60fd8 : fetch_word Asan.M.loaded_segments (0x60fd8 : word) = Some W_60fd8.
Proof. vm_refl. Qed.
Lemma D_60fd8 : decode_any W_60fd8 = Some (Load SZ8 true 15 15 2284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60fdc : bv 32 := 0x00075817.
Lemma F_60fdc : fetch_word Asan.M.loaded_segments (0x60fdc : word) = Some W_60fdc.
Proof. vm_refl. Qed.
Lemma D_60fdc : decode_any W_60fdc = Some (Auipc 16 117, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60fe0 : bv 32 := 0x8ec83803.
Lemma F_60fe0 : fetch_word Asan.M.loaded_segments (0x60fe0 : word) = Some W_60fe0.
Proof. vm_refl. Qed.
Lemma D_60fe0 : decode_any W_60fe0 = Some (Load SZ8 true 16 16 2284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60fe4 : bv 32 := 0x0007b883.
Lemma F_60fe4 : fetch_word Asan.M.loaded_segments (0x60fe4 : word) = Some W_60fe4.
Proof. vm_refl. Qed.
Lemma D_60fe4 : decode_any W_60fe4 = Some (Load SZ8 true 17 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60fe8 : bv 32 := 0x00083783.
Lemma F_60fe8 : fetch_word Asan.M.loaded_segments (0x60fe8 : word) = Some W_60fe8.
Proof. vm_refl. Qed.
Lemma D_60fe8 : decode_any W_60fe8 = Some (Load SZ8 true 15 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60fec : bv 32 := 0xfff88813.
Lemma F_60fec : fetch_word Asan.M.loaded_segments (0x60fec : word) = Some W_60fec.
Proof. vm_refl. Qed.
Lemma D_60fec : decode_any W_60fec = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ff0 : bv 32 := 0x00a87463.
Lemma F_60ff0 : fetch_word Asan.M.loaded_segments (0x60ff0 : word) = Some W_60ff0.
Proof. vm_refl. Qed.
Lemma D_60ff0 : decode_any W_60ff0 = Some (Branch BC_GEU 16 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ff4 : bv 32 := 0x1aa7fa63.
Lemma F_60ff4 : fetch_word Asan.M.loaded_segments (0x60ff4 : word) = Some W_60ff4.
Proof. vm_refl. Qed.
Lemma D_60ff4 : decode_any W_60ff4 = Some (Branch BC_GEU 15 10 436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ff8 : bv 32 := 0x00075297.
Lemma F_60ff8 : fetch_word Asan.M.loaded_segments (0x60ff8 : word) = Some W_60ff8.
Proof. vm_refl. Qed.
Lemma D_60ff8 : decode_any W_60ff8 = Some (Auipc 5 117, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60ffc : bv 32 := 0x8d82b283.
Lemma F_60ffc : fetch_word Asan.M.loaded_segments (0x60ffc : word) = Some W_60ffc.
Proof. vm_refl. Qed.
Lemma D_60ffc : decode_any W_60ffc = Some (Load SZ8 true 5 5 2264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61000 : bv 32 := 0x0002be03.
Lemma F_61000 : fetch_word Asan.M.loaded_segments (0x61000 : word) = Some W_61000.
Proof. vm_refl. Qed.
Lemma D_61000 : decode_any W_61000 = Some (Load SZ8 true 28 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61004 : bv 32 := 0x003e5313.
Lemma F_61004 : fetch_word Asan.M.loaded_segments (0x61004 : word) = Some W_61004.
Proof. vm_refl. Qed.
Lemma D_61004 : decode_any W_61004 = Some (ShiftImm ALU_SRL 6 28 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61008 : bv 32 := 0x009303b3.
Lemma F_61008 : fetch_word Asan.M.loaded_segments (0x61008 : word) = Some W_61008.
Proof. vm_refl. Qed.
Lemma D_61008 : decode_any W_61008 = Some (Op ALU_ADD 7 6 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6100c : bv 32 := 0x00ae6463.
Lemma F_6100c : fetch_word Asan.M.loaded_segments (0x6100c : word) = Some W_6100c.
Proof. vm_refl. Qed.
Lemma D_6100c : decode_any W_6100c = Some (Branch BC_LTU 28 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61010 : bv 32 := 0x0ca3e463.
Lemma F_61010 : fetch_word Asan.M.loaded_segments (0x61010 : word) = Some W_61010.
Proof. vm_refl. Qed.
Lemma D_61010 : decode_any W_61010 = Some (Branch BC_LTU 7 10 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61014 : bv 32 := 0x00075e17.
Lemma F_61014 : fetch_word Asan.M.loaded_segments (0x61014 : word) = Some W_61014.
Proof. vm_refl. Qed.
Lemma D_61014 : decode_any W_61014 = Some (Auipc 28 117, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61018 : bv 32 := 0x89ce3e03.
Lemma F_61018 : fetch_word Asan.M.loaded_segments (0x61018 : word) = Some W_61018.
Proof. vm_refl. Qed.
Lemma D_61018 : decode_any W_61018 = Some (Load SZ8 true 28 28 2204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6101c : bv 32 := 0x04ee4e03.
Lemma F_6101c : fetch_word Asan.M.loaded_segments (0x6101c : word) = Some W_6101c.
Proof. vm_refl. Qed.
Lemma D_6101c : decode_any W_6101c = Some (Load SZ1 false 28 28 78, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61020 : bv 32 := 0x3e0e1063.
Lemma F_61020 : fetch_word Asan.M.loaded_segments (0x61020 : word) = Some W_61020.
Proof. vm_refl. Qed.
Lemma D_61020 : decode_any W_61020 = Some (Branch BC_NE 28 0 992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61024 : bv 32 := 0x04088e63.
Lemma F_61024 : fetch_word Asan.M.loaded_segments (0x61024 : word) = Some W_61024.
Proof. vm_refl. Qed.
Lemma D_61024 : decode_any W_61024 = Some (Branch BC_EQ 17 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61028 : bv 32 := 0x0038d393.
Lemma F_61028 : fetch_word Asan.M.loaded_segments (0x61028 : word) = Some W_61028.
Proof. vm_refl. Qed.
Lemma D_61028 : decode_any W_61028 = Some (ShiftImm ALU_SRL 7 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6102c : bv 32 := 0x00d383b3.
Lemma F_6102c : fetch_word Asan.M.loaded_segments (0x6102c : word) = Some W_6102c.
Proof. vm_refl. Qed.
Lemma D_6102c : decode_any W_6102c = Some (Op ALU_ADD 7 7 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61030 : bv 32 := 0x06a3fe63.
Lemma F_61030 : fetch_word Asan.M.loaded_segments (0x61030 : word) = Some W_61030.
Proof. vm_refl. Qed.
Lemma D_61030 : decode_any W_61030 = Some (Branch BC_GEU 7 10 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61034 : bv 32 := 0x00148393.
Lemma F_61034 : fetch_word Asan.M.loaded_segments (0x61034 : word) = Some W_61034.
Proof. vm_refl. Qed.
Lemma D_61034 : decode_any W_61034 = Some (OpImm ALU_ADD 7 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61038 : bv 32 := 0x00a86863.
Lemma F_61038 : fetch_word Asan.M.loaded_segments (0x61038 : word) = Some W_61038.
Proof. vm_refl. Qed.
Lemma D_61038 : decode_any W_61038 = Some (Branch BC_LTU 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6103c : bv 32 := 0x0037de13.
Lemma F_6103c : fetch_word Asan.M.loaded_segments (0x6103c : word) = Some W_6103c.
Proof. vm_refl. Qed.
Lemma D_6103c : decode_any W_6103c = Some (ShiftImm ALU_SRL 28 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61040 : bv 32 := 0x007e0e33.
Lemma F_61040 : fetch_word Asan.M.loaded_segments (0x61040 : word) = Some W_61040.
Proof. vm_refl. Qed.
Lemma D_61040 : decode_any W_61040 = Some (Op ALU_ADD 28 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61044 : bv 32 := 0x09c57a63.
Lemma F_61044 : fetch_word Asan.M.loaded_segments (0x61044 : word) = Some W_61044.
Proof. vm_refl. Qed.
Lemma D_61044 : decode_any W_61044 = Some (Branch BC_GEU 10 28 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61048 : bv 32 := 0x00178e13.
Lemma F_61048 : fetch_word Asan.M.loaded_segments (0x61048 : word) = Some W_61048.
Proof. vm_refl. Qed.
Lemma D_61048 : decode_any W_61048 = Some (OpImm ALU_ADD 28 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6104c : bv 32 := 0x3bc56a63.
Lemma F_6104c : fetch_word Asan.M.loaded_segments (0x6104c : word) = Some W_6104c.
Proof. vm_refl. Qed.
Lemma D_6104c : decode_any W_6104c = Some (Branch BC_LTU 10 28 948, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61050 : bv 32 := 0x00730333.
Lemma F_61050 : fetch_word Asan.M.loaded_segments (0x61050 : word) = Some W_61050.
Proof. vm_refl. Qed.
Lemma D_61050 : decode_any W_61050 = Some (Op ALU_ADD 6 6 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61054 : bv 32 := 0x00335313.
Lemma F_61054 : fetch_word Asan.M.loaded_segments (0x61054 : word) = Some W_61054.
Proof. vm_refl. Qed.
Lemma D_61054 : decode_any W_61054 = Some (ShiftImm ALU_SRL 6 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61058 : bv 32 := 0x0480006f.
Lemma F_61058 : fetch_word Asan.M.loaded_segments (0x61058 : word) = Some W_61058.
Proof. vm_refl. Qed.
Lemma D_61058 : decode_any W_61058 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6105c : bv 32 := 0x03813083.
Lemma F_6105c : fetch_word Asan.M.loaded_segments (0x6105c : word) = Some W_6105c.
Proof. vm_refl. Qed.
Lemma D_6105c : decode_any W_6105c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61060 : bv 32 := 0x03013403.
Lemma F_61060 : fetch_word Asan.M.loaded_segments (0x61060 : word) = Some W_61060.
Proof. vm_refl. Qed.
Lemma D_61060 : decode_any W_61060 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61064 : bv 32 := 0x02813483.
Lemma F_61064 : fetch_word Asan.M.loaded_segments (0x61064 : word) = Some W_61064.
Proof. vm_refl. Qed.
Lemma D_61064 : decode_any W_61064 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61068 : bv 32 := 0x02013903.
Lemma F_61068 : fetch_word Asan.M.loaded_segments (0x61068 : word) = Some W_61068.
Proof. vm_refl. Qed.
Lemma D_61068 : decode_any W_61068 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6106c : bv 32 := 0x01813983.
Lemma F_6106c : fetch_word Asan.M.loaded_segments (0x6106c : word) = Some W_6106c.
Proof. vm_refl. Qed.
Lemma D_6106c : decode_any W_6106c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61070 : bv 32 := 0x01013a03.
Lemma F_61070 : fetch_word Asan.M.loaded_segments (0x61070 : word) = Some W_61070.
Proof. vm_refl. Qed.
Lemma D_61070 : decode_any W_61070 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61074 : bv 32 := 0x00813a83.
Lemma F_61074 : fetch_word Asan.M.loaded_segments (0x61074 : word) = Some W_61074.
Proof. vm_refl. Qed.
Lemma D_61074 : decode_any W_61074 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61078 : bv 32 := 0x04010113.
Lemma F_61078 : fetch_word Asan.M.loaded_segments (0x61078 : word) = Some W_61078.
Proof. vm_refl. Qed.
Lemma D_61078 : decode_any W_61078 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6107c : bv 32 := 0x00008067.
Lemma F_6107c : fetch_word Asan.M.loaded_segments (0x6107c : word) = Some W_6107c.
Proof. vm_refl. Qed.
Lemma D_6107c : decode_any W_6107c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61080 : bv 32 := 0x04048463.
Lemma F_61080 : fetch_word Asan.M.loaded_segments (0x61080 : word) = Some W_61080.
Proof. vm_refl. Qed.
Lemma D_61080 : decode_any W_61080 = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61084 : bv 32 := 0x0036d313.
Lemma F_61084 : fetch_word Asan.M.loaded_segments (0x61084 : word) = Some W_61084.
Proof. vm_refl. Qed.
Lemma D_61084 : decode_any W_61084 = Some (ShiftImm ALU_SRL 6 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61088 : bv 32 := 0x00930333.
Lemma F_61088 : fetch_word Asan.M.loaded_segments (0x61088 : word) = Some W_61088.
Proof. vm_refl. Qed.
Lemma D_61088 : decode_any W_61088 = Some (Op ALU_ADD 6 6 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6108c : bv 32 := 0x00030663.
Lemma F_6108c : fetch_word Asan.M.loaded_segments (0x6108c : word) = Some W_6108c.
Proof. vm_refl. Qed.
Lemma D_6108c : decode_any W_6108c = Some (Branch BC_EQ 6 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61090 : bv 32 := 0x00130313.
Lemma F_61090 : fetch_word Asan.M.loaded_segments (0x61090 : word) = Some W_61090.
Proof. vm_refl. Qed.
Lemma D_61090 : decode_any W_61090 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61094 : bv 32 := 0x36656663.
Lemma F_61094 : fetch_word Asan.M.loaded_segments (0x61094 : word) = Some W_61094.
Proof. vm_refl. Qed.
Lemma D_61094 : decode_any W_61094 = Some (Branch BC_LTU 10 6 876, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61098 : bv 32 := 0x00138393.
Lemma F_61098 : fetch_word Asan.M.loaded_segments (0x61098 : word) = Some W_61098.
Proof. vm_refl. Qed.
Lemma D_61098 : decode_any W_61098 = Some (OpImm ALU_ADD 7 7 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6109c : bv 32 := 0x0033d313.
Lemma F_6109c : fetch_word Asan.M.loaded_segments (0x6109c : word) = Some W_6109c.
Proof. vm_refl. Qed.
Lemma D_6109c : decode_any W_6109c = Some (ShiftImm ALU_SRL 6 7 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610a0 : bv 32 := 0x00d30333.
Lemma F_610a0 : fetch_word Asan.M.loaded_segments (0x610a0 : word) = Some W_610a0.
Proof. vm_refl. Qed.
Lemma D_610a0 : decode_any W_610a0 = Some (Op ALU_ADD 6 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610a4 : bv 32 := 0x02a37a63.
Lemma F_610a4 : fetch_word Asan.M.loaded_segments (0x610a4 : word) = Some W_610a4.
Proof. vm_refl. Qed.
Lemma D_610a4 : decode_any W_610a4 = Some (Branch BC_GEU 6 10 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610a8 : bv 32 := 0x3580006f.
Lemma F_610a8 : fetch_word Asan.M.loaded_segments (0x610a8 : word) = Some W_610a8.
Proof. vm_refl. Qed.
Lemma D_610a8 : decode_any W_610a8 = Some (Jal 0 856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610ac : bv 32 := 0x02048663.
Lemma F_610ac : fetch_word Asan.M.loaded_segments (0x610ac : word) = Some W_610ac.
Proof. vm_refl. Qed.
Lemma D_610ac : decode_any W_610ac = Some (Branch BC_EQ 9 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610b0 : bv 32 := 0x0036d313.
Lemma F_610b0 : fetch_word Asan.M.loaded_segments (0x610b0 : word) = Some W_610b0.
Proof. vm_refl. Qed.
Lemma D_610b0 : decode_any W_610b0 = Some (ShiftImm ALU_SRL 6 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610b4 : bv 32 := 0x00930333.
Lemma F_610b4 : fetch_word Asan.M.loaded_segments (0x610b4 : word) = Some W_610b4.
Proof. vm_refl. Qed.
Lemma D_610b4 : decode_any W_610b4 = Some (Op ALU_ADD 6 6 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610b8 : bv 32 := 0x02030063.
Lemma F_610b8 : fetch_word Asan.M.loaded_segments (0x610b8 : word) = Some W_610b8.
Proof. vm_refl. Qed.
Lemma D_610b8 : decode_any W_610b8 = Some (Branch BC_EQ 6 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610bc : bv 32 := 0x00130313.
Lemma F_610bc : fetch_word Asan.M.loaded_segments (0x610bc : word) = Some W_610bc.
Proof. vm_refl. Qed.
Lemma D_610bc : decode_any W_610bc = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610c0 : bv 32 := 0x00657c63.
Lemma F_610c0 : fetch_word Asan.M.loaded_segments (0x610c0 : word) = Some W_610c0.
Proof. vm_refl. Qed.
Lemma D_610c0 : decode_any W_610c0 = Some (Branch BC_GEU 10 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610c4 : bv 32 := 0x33c0006f.
Lemma F_610c4 : fetch_word Asan.M.loaded_segments (0x610c4 : word) = Some W_610c4.
Proof. vm_refl. Qed.
Lemma D_610c4 : decode_any W_610c4 = Some (Jal 0 828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610c8 : bv 32 := 0x00130313.
Lemma F_610c8 : fetch_word Asan.M.loaded_segments (0x610c8 : word) = Some W_610c8.
Proof. vm_refl. Qed.
Lemma D_610c8 : decode_any W_610c8 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610cc : bv 32 := 0x00335313.
Lemma F_610cc : fetch_word Asan.M.loaded_segments (0x610cc : word) = Some W_610cc.
Proof. vm_refl. Qed.
Lemma D_610cc : decode_any W_610cc = Some (ShiftImm ALU_SRL 6 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610d0 : bv 32 := 0xfff30313.
Lemma F_610d0 : fetch_word Asan.M.loaded_segments (0x610d0 : word) = Some W_610d0.
Proof. vm_refl. Qed.
Lemma D_610d0 : decode_any W_610d0 = Some (OpImm ALU_ADD 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610d4 : bv 32 := 0x32a36663.
Lemma F_610d4 : fetch_word Asan.M.loaded_segments (0x610d4 : word) = Some W_610d4.
Proof. vm_refl. Qed.
Lemma D_610d4 : decode_any W_610d4 = Some (Branch BC_LTU 6 10 812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610d8 : bv 32 := 0x0002b383.
Lemma F_610d8 : fetch_word Asan.M.loaded_segments (0x610d8 : word) = Some W_610d8.
Proof. vm_refl. Qed.
Lemma D_610d8 : decode_any W_610d8 = Some (Load SZ8 true 7 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610dc : bv 32 := 0x0033d293.
Lemma F_610dc : fetch_word Asan.M.loaded_segments (0x610dc : word) = Some W_610dc.
Proof. vm_refl. Qed.
Lemma D_610dc : decode_any W_610dc = Some (ShiftImm ALU_SRL 5 7 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610e0 : bv 32 := 0x00928333.
Lemma F_610e0 : fetch_word Asan.M.loaded_segments (0x610e0 : word) = Some W_610e0.
Proof. vm_refl. Qed.
Lemma D_610e0 : decode_any W_610e0 = Some (Op ALU_ADD 6 5 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610e4 : bv 32 := 0x00a3e463.
Lemma F_610e4 : fetch_word Asan.M.loaded_segments (0x610e4 : word) = Some W_610e4.
Proof. vm_refl. Qed.
Lemma D_610e4 : decode_any W_610e4 = Some (Branch BC_LTU 7 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610e8 : bv 32 := 0x0ca36063.
Lemma F_610e8 : fetch_word Asan.M.loaded_segments (0x610e8 : word) = Some W_610e8.
Proof. vm_refl. Qed.
Lemma D_610e8 : decode_any W_610e8 = Some (Branch BC_LTU 6 10 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610ec : bv 32 := 0x00074397.
Lemma F_610ec : fetch_word Asan.M.loaded_segments (0x610ec : word) = Some W_610ec.
Proof. vm_refl. Qed.
Lemma D_610ec : decode_any W_610ec = Some (Auipc 7 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610f0 : bv 32 := 0x7c43b383.
Lemma F_610f0 : fetch_word Asan.M.loaded_segments (0x610f0 : word) = Some W_610f0.
Proof. vm_refl. Qed.
Lemma D_610f0 : decode_any W_610f0 = Some (Load SZ8 true 7 7 1988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610f4 : bv 32 := 0x04e3c383.
Lemma F_610f4 : fetch_word Asan.M.loaded_segments (0x610f4 : word) = Some W_610f4.
Proof. vm_refl. Qed.
Lemma D_610f4 : decode_any W_610f4 = Some (Load SZ1 false 7 7 78, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610f8 : bv 32 := 0x08039063.
Lemma F_610f8 : fetch_word Asan.M.loaded_segments (0x610f8 : word) = Some W_610f8.
Proof. vm_refl. Qed.
Lemma D_610f8 : decode_any W_610f8 = Some (Branch BC_NE 7 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_610fc : bv 32 := 0x02088c63.
Lemma F_610fc : fetch_word Asan.M.loaded_segments (0x610fc : word) = Some W_610fc.
Proof. vm_refl. Qed.
Lemma D_610fc : decode_any W_610fc = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61100 : bv 32 := 0x0038d893.
Lemma F_61100 : fetch_word Asan.M.loaded_segments (0x61100 : word) = Some W_61100.
Proof. vm_refl. Qed.
Lemma D_61100 : decode_any W_61100 = Some (ShiftImm ALU_SRL 17 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61104 : bv 32 := 0x00d888b3.
Lemma F_61104 : fetch_word Asan.M.loaded_segments (0x61104 : word) = Some W_61104.
Proof. vm_refl. Qed.
Lemma D_61104 : decode_any W_61104 = Some (Op ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61108 : bv 32 := 0x04a8fc63.
Lemma F_61108 : fetch_word Asan.M.loaded_segments (0x61108 : word) = Some W_61108.
Proof. vm_refl. Qed.
Lemma D_61108 : decode_any W_61108 = Some (Branch BC_GEU 17 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6110c : bv 32 := 0x00148893.
Lemma F_6110c : fetch_word Asan.M.loaded_segments (0x6110c : word) = Some W_6110c.
Proof. vm_refl. Qed.
Lemma D_6110c : decode_any W_6110c = Some (OpImm ALU_ADD 17 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61110 : bv 32 := 0x00a86863.
Lemma F_61110 : fetch_word Asan.M.loaded_segments (0x61110 : word) = Some W_61110.
Proof. vm_refl. Qed.
Lemma D_61110 : decode_any W_61110 = Some (Branch BC_LTU 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61114 : bv 32 := 0x0037d813.
Lemma F_61114 : fetch_word Asan.M.loaded_segments (0x61114 : word) = Some W_61114.
Proof. vm_refl. Qed.
Lemma D_61114 : decode_any W_61114 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61118 : bv 32 := 0x01180833.
Lemma F_61118 : fetch_word Asan.M.loaded_segments (0x61118 : word) = Some W_61118.
Proof. vm_refl. Qed.
Lemma D_61118 : decode_any W_61118 = Some (Op ALU_ADD 16 16 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6111c : bv 32 := 0x09057663.
Lemma F_6111c : fetch_word Asan.M.loaded_segments (0x6111c : word) = Some W_6111c.
Proof. vm_refl. Qed.
Lemma D_6111c : decode_any W_6111c = Some (Branch BC_GEU 10 16 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61120 : bv 32 := 0x00178793.
Lemma F_61120 : fetch_word Asan.M.loaded_segments (0x61120 : word) = Some W_61120.
Proof. vm_refl. Qed.
Lemma D_61120 : decode_any W_61120 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61124 : bv 32 := 0x04f56a63.
Lemma F_61124 : fetch_word Asan.M.loaded_segments (0x61124 : word) = Some W_61124.
Proof. vm_refl. Qed.
Lemma D_61124 : decode_any W_61124 = Some (Branch BC_LTU 10 15 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61128 : bv 32 := 0x011288b3.
Lemma F_61128 : fetch_word Asan.M.loaded_segments (0x61128 : word) = Some W_61128.
Proof. vm_refl. Qed.
Lemma D_61128 : decode_any W_61128 = Some (Op ALU_ADD 17 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6112c : bv 32 := 0x0038d793.
Lemma F_6112c : fetch_word Asan.M.loaded_segments (0x6112c : word) = Some W_6112c.
Proof. vm_refl. Qed.
Lemma D_6112c : decode_any W_6112c = Some (ShiftImm ALU_SRL 15 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61130 : bv 32 := 0x0240006f.
Lemma F_61130 : fetch_word Asan.M.loaded_segments (0x61130 : word) = Some W_61130.
Proof. vm_refl. Qed.
Lemma D_61130 : decode_any W_61130 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61134 : bv 32 := 0x06048263.
Lemma F_61134 : fetch_word Asan.M.loaded_segments (0x61134 : word) = Some W_61134.
Proof. vm_refl. Qed.
Lemma D_61134 : decode_any W_61134 = Some (Branch BC_EQ 9 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61138 : bv 32 := 0x0036d793.
Lemma F_61138 : fetch_word Asan.M.loaded_segments (0x61138 : word) = Some W_61138.
Proof. vm_refl. Qed.
Lemma D_61138 : decode_any W_61138 = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6113c : bv 32 := 0x009787b3.
Lemma F_6113c : fetch_word Asan.M.loaded_segments (0x6113c : word) = Some W_6113c.
Proof. vm_refl. Qed.
Lemma D_6113c : decode_any W_6113c = Some (Op ALU_ADD 15 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61140 : bv 32 := 0x00078663.
Lemma F_61140 : fetch_word Asan.M.loaded_segments (0x61140 : word) = Some W_61140.
Proof. vm_refl. Qed.
Lemma D_61140 : decode_any W_61140 = Some (Branch BC_EQ 15 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61144 : bv 32 := 0x00178793.
Lemma F_61144 : fetch_word Asan.M.loaded_segments (0x61144 : word) = Some W_61144.
Proof. vm_refl. Qed.
Lemma D_61144 : decode_any W_61144 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61148 : bv 32 := 0x02f56863.
Lemma F_61148 : fetch_word Asan.M.loaded_segments (0x61148 : word) = Some W_61148.
Proof. vm_refl. Qed.
Lemma D_61148 : decode_any W_61148 = Some (Branch BC_LTU 10 15 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6114c : bv 32 := 0x00130313.
Lemma F_6114c : fetch_word Asan.M.loaded_segments (0x6114c : word) = Some W_6114c.
Proof. vm_refl. Qed.
Lemma D_6114c : decode_any W_6114c = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61150 : bv 32 := 0x00335793.
Lemma F_61150 : fetch_word Asan.M.loaded_segments (0x61150 : word) = Some W_61150.
Proof. vm_refl. Qed.
Lemma D_61150 : decode_any W_61150 = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61154 : bv 32 := 0x00d787b3.
Lemma F_61154 : fetch_word Asan.M.loaded_segments (0x61154 : word) = Some W_61154.
Proof. vm_refl. Qed.
Lemma D_61154 : decode_any W_61154 = Some (Op ALU_ADD 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61158 : bv 32 := 0x04a7f863.
Lemma F_61158 : fetch_word Asan.M.loaded_segments (0x61158 : word) = Some W_61158.
Proof. vm_refl. Qed.
Lemma D_61158 : decode_any W_61158 = Some (Branch BC_GEU 15 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6115c : bv 32 := 0x01c0006f.
Lemma F_6115c : fetch_word Asan.M.loaded_segments (0x6115c : word) = Some W_6115c.
Proof. vm_refl. Qed.
Lemma D_6115c : decode_any W_6115c = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61160 : bv 32 := 0x04048463.
Lemma F_61160 : fetch_word Asan.M.loaded_segments (0x61160 : word) = Some W_61160.
Proof. vm_refl. Qed.
Lemma D_61160 : decode_any W_61160 = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61164 : bv 32 := 0x0036d793.
Lemma F_61164 : fetch_word Asan.M.loaded_segments (0x61164 : word) = Some W_61164.
Proof. vm_refl. Qed.
Lemma D_61164 : decode_any W_61164 = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61168 : bv 32 := 0x009787b3.
Lemma F_61168 : fetch_word Asan.M.loaded_segments (0x61168 : word) = Some W_61168.
Proof. vm_refl. Qed.
Lemma D_61168 : decode_any W_61168 = Some (Op ALU_ADD 15 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6116c : bv 32 := 0x02078e63.
Lemma F_6116c : fetch_word Asan.M.loaded_segments (0x6116c : word) = Some W_6116c.
Proof. vm_refl. Qed.
Lemma D_6116c : decode_any W_6116c = Some (Branch BC_EQ 15 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61170 : bv 32 := 0x00178793.
Lemma F_61170 : fetch_word Asan.M.loaded_segments (0x61170 : word) = Some W_61170.
Proof. vm_refl. Qed.
Lemma D_61170 : decode_any W_61170 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61174 : bv 32 := 0x02f57a63.
Lemma F_61174 : fetch_word Asan.M.loaded_segments (0x61174 : word) = Some W_61174.
Proof. vm_refl. Qed.
Lemma D_61174 : decode_any W_61174 = Some (Branch BC_GEU 10 15 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61178 : bv 32 := 0xfffc0517.
Lemma F_61178 : fetch_word Asan.M.loaded_segments (0x61178 : word) = Some W_61178.
Proof. vm_refl. Qed.
Lemma D_61178 : decode_any W_61178 = Some (Auipc 10 1048512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6117c : bv 32 := 0xfffb7597.
Lemma F_6117c : fetch_word Asan.M.loaded_segments (0x6117c : word) = Some W_6117c.
Proof. vm_refl. Qed.
Lemma D_6117c : decode_any W_6117c = Some (Auipc 11 1048503, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61180 : bv 32 := 0xaf450513.
Lemma F_61180 : fetch_word Asan.M.loaded_segments (0x61180 : word) = Some W_61180.
Proof. vm_refl. Qed.
Lemma D_61180 : decode_any W_61180 = Some (OpImm ALU_ADD 10 10 2804, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61184 : bv 32 := 0x38c58613.
Lemma F_61184 : fetch_word Asan.M.loaded_segments (0x61184 : word) = Some W_61184.
Proof. vm_refl. Qed.
Lemma D_61184 : decode_any W_61184 = Some (OpImm ALU_ADD 12 11 908, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61188 : bv 32 := 0x02f00593.
Lemma F_61188 : fetch_word Asan.M.loaded_segments (0x61188 : word) = Some W_61188.
Proof. vm_refl. Qed.
Lemma D_61188 : decode_any W_61188 = Some (OpImm ALU_ADD 11 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6118c : bv 32 := 0x00000693.
Lemma F_6118c : fetch_word Asan.M.loaded_segments (0x6118c : word) = Some W_6118c.
Proof. vm_refl. Qed.
Lemma D_6118c : decode_any W_6118c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61190 : bv 32 := 0x00000713.
Lemma F_61190 : fetch_word Asan.M.loaded_segments (0x61190 : word) = Some W_61190.
Proof. vm_refl. Qed.
Lemma D_61190 : decode_any W_61190 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61194 : bv 32 := 0x6d5170ef.
Lemma F_61194 : fetch_word Asan.M.loaded_segments (0x61194 : word) = Some W_61194.
Proof. vm_refl. Qed.
Lemma D_61194 : decode_any W_61194 = Some (Jal 1 98004, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61198 : bv 32 := 0x00128293.
Lemma F_61198 : fetch_word Asan.M.loaded_segments (0x61198 : word) = Some W_61198.
Proof. vm_refl. Qed.
Lemma D_61198 : decode_any W_61198 = Some (OpImm ALU_ADD 5 5 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6119c : bv 32 := 0x0032d793.
Lemma F_6119c : fetch_word Asan.M.loaded_segments (0x6119c : word) = Some W_6119c.
Proof. vm_refl. Qed.
Lemma D_6119c : decode_any W_6119c = Some (ShiftImm ALU_SRL 15 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611a0 : bv 32 := 0xfff78793.
Lemma F_611a0 : fetch_word Asan.M.loaded_segments (0x611a0 : word) = Some W_611a0.
Proof. vm_refl. Qed.
Lemma D_611a0 : decode_any W_611a0 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611a4 : bv 32 := 0xfca7eae3.
Lemma F_611a4 : fetch_word Asan.M.loaded_segments (0x611a4 : word) = Some W_611a4.
Proof. vm_refl. Qed.
Lemma D_611a4 : decode_any W_611a4 = Some (Branch BC_LTU 15 10 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611a8 : bv 32 := 0x0075f793.
Lemma F_611a8 : fetch_word Asan.M.loaded_segments (0x611a8 : word) = Some W_611a8.
Proof. vm_refl. Qed.
Lemma D_611a8 : decode_any W_611a8 = Some (OpImm ALU_AND 15 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611ac : bv 32 := 0x26079a63.
Lemma F_611ac : fetch_word Asan.M.loaded_segments (0x611ac : word) = Some W_611ac.
Proof. vm_refl. Qed.
Lemma D_611ac : decode_any W_611ac = Some (Branch BC_NE 15 0 628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611b0 : bv 32 := 0x00b505b3.
Lemma F_611b0 : fetch_word Asan.M.loaded_segments (0x611b0 : word) = Some W_611b0.
Proof. vm_refl. Qed.
Lemma D_611b0 : decode_any W_611b0 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611b4 : bv 32 := 0xff858593.
Lemma F_611b4 : fetch_word Asan.M.loaded_segments (0x611b4 : word) = Some W_611b4.
Proof. vm_refl. Qed.
Lemma D_611b4 : decode_any W_611b4 = Some (OpImm ALU_ADD 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611b8 : bv 32 := 0x04b77263.
Lemma F_611b8 : fetch_word Asan.M.loaded_segments (0x611b8 : word) = Some W_611b8.
Proof. vm_refl. Qed.
Lemma D_611b8 : decode_any W_611b8 = Some (Branch BC_GEU 14 11 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611bc : bv 32 := 0x00074717.
Lemma F_611bc : fetch_word Asan.M.loaded_segments (0x611bc : word) = Some W_611bc.
Proof. vm_refl. Qed.
Lemma D_611bc : decode_any W_611bc = Some (Auipc 14 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611c0 : bv 32 := 0x70473703.
Lemma F_611c0 : fetch_word Asan.M.loaded_segments (0x611c0 : word) = Some W_611c0.
Proof. vm_refl. Qed.
Lemma D_611c0 : decode_any W_611c0 = Some (Load SZ8 true 14 14 1796, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611c4 : bv 32 := 0x00074797.
Lemma F_611c4 : fetch_word Asan.M.loaded_segments (0x611c4 : word) = Some W_611c4.
Proof. vm_refl. Qed.
Lemma D_611c4 : decode_any W_611c4 = Some (Auipc 15 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611c8 : bv 32 := 0x7047b783.
Lemma F_611c8 : fetch_word Asan.M.loaded_segments (0x611c8 : word) = Some W_611c8.
Proof. vm_refl. Qed.
Lemma D_611c8 : decode_any W_611c8 = Some (Load SZ8 true 15 15 1796, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611cc : bv 32 := 0x00073883.
Lemma F_611cc : fetch_word Asan.M.loaded_segments (0x611cc : word) = Some W_611cc.
Proof. vm_refl. Qed.
Lemma D_611cc : decode_any W_611cc = Some (Load SZ8 true 17 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611d0 : bv 32 := 0x0007b703.
Lemma F_611d0 : fetch_word Asan.M.loaded_segments (0x611d0 : word) = Some W_611d0.
Proof. vm_refl. Qed.
Lemma D_611d0 : decode_any W_611d0 = Some (Load SZ8 true 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611d4 : bv 32 := 0xfff88813.
Lemma F_611d4 : fetch_word Asan.M.loaded_segments (0x611d4 : word) = Some W_611d4.
Proof. vm_refl. Qed.
Lemma D_611d4 : decode_any W_611d4 = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611d8 : bv 32 := 0x00b87463.
Lemma F_611d8 : fetch_word Asan.M.loaded_segments (0x611d8 : word) = Some W_611d8.
Proof. vm_refl. Qed.
Lemma D_611d8 : decode_any W_611d8 = Some (Branch BC_GEU 16 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611dc : bv 32 := 0x02b77063.
Lemma F_611dc : fetch_word Asan.M.loaded_segments (0x611dc : word) = Some W_611dc.
Proof. vm_refl. Qed.
Lemma D_611dc : decode_any W_611dc = Some (Branch BC_GEU 14 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611e0 : bv 32 := 0x00074797.
Lemma F_611e0 : fetch_word Asan.M.loaded_segments (0x611e0 : word) = Some W_611e0.
Proof. vm_refl. Qed.
Lemma D_611e0 : decode_any W_611e0 = Some (Auipc 15 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611e4 : bv 32 := 0x6f07b783.
Lemma F_611e4 : fetch_word Asan.M.loaded_segments (0x611e4 : word) = Some W_611e4.
Proof. vm_refl. Qed.
Lemma D_611e4 : decode_any W_611e4 = Some (Load SZ8 true 15 15 1776, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611e8 : bv 32 := 0x0007b303.
Lemma F_611e8 : fetch_word Asan.M.loaded_segments (0x611e8 : word) = Some W_611e8.
Proof. vm_refl. Qed.
Lemma D_611e8 : decode_any W_611e8 = Some (Load SZ8 true 6 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611ec : bv 32 := 0x00335793.
Lemma F_611ec : fetch_word Asan.M.loaded_segments (0x611ec : word) = Some W_611ec.
Proof. vm_refl. Qed.
Lemma D_611ec : decode_any W_611ec = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611f0 : bv 32 := 0x009782b3.
Lemma F_611f0 : fetch_word Asan.M.loaded_segments (0x611f0 : word) = Some W_611f0.
Proof. vm_refl. Qed.
Lemma D_611f0 : decode_any W_611f0 = Some (Op ALU_ADD 5 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611f4 : bv 32 := 0x12b36263.
Lemma F_611f4 : fetch_word Asan.M.loaded_segments (0x611f4 : word) = Some W_611f4.
Proof. vm_refl. Qed.
Lemma D_611f4 : decode_any W_611f4 = Some (Branch BC_LTU 6 11 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611f8 : bv 32 := 0x12b2f063.
Lemma F_611f8 : fetch_word Asan.M.loaded_segments (0x611f8 : word) = Some W_611f8.
Proof. vm_refl. Qed.
Lemma D_611f8 : decode_any W_611f8 = Some (Branch BC_GEU 5 11 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_611fc : bv 32 := 0x00074697.
Lemma F_611fc : fetch_word Asan.M.loaded_segments (0x611fc : word) = Some W_611fc.
Proof. vm_refl. Qed.
Lemma D_611fc : decode_any W_611fc = Some (Auipc 13 116, 4%Z).
Proof. vm_refl. Qed.
