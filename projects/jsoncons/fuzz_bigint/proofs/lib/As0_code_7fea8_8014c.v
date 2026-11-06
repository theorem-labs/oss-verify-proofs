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

Definition W_7fea8 : bv 32 := 0x00058613.
Lemma F_7fea8 : fetch_word Asan.M.loaded_segments (0x7fea8 : word) = Some W_7fea8.
Proof. vm_refl. Qed.
Lemma D_7fea8 : decode_any W_7fea8 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7feac : bv 32 := 0x00140597.
Lemma F_7feac : fetch_word Asan.M.loaded_segments (0x7feac : word) = Some W_7feac.
Proof. vm_refl. Qed.
Lemma D_7feac : decode_any W_7feac = Some (Auipc 11 320, 4%Z).
Proof. vm_refl. Qed.

Definition W_7feb0 : bv 32 := 0xb6c58593.
Lemma F_7feb0 : fetch_word Asan.M.loaded_segments (0x7feb0 : word) = Some W_7feb0.
Proof. vm_refl. Qed.
Lemma D_7feb0 : decode_any W_7feb0 = Some (OpImm ALU_ADD 11 11 2924, 4%Z).
Proof. vm_refl. Qed.

Definition W_7feb4 : bv 32 := 0x00050693.
Lemma F_7feb4 : fetch_word Asan.M.loaded_segments (0x7feb4 : word) = Some W_7feb4.
Proof. vm_refl. Qed.
Lemma D_7feb4 : decode_any W_7feb4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7feb8 : bv 32 := 0x00058513.
Lemma F_7feb8 : fetch_word Asan.M.loaded_segments (0x7feb8 : word) = Some W_7feb8.
Proof. vm_refl. Qed.
Lemma D_7feb8 : decode_any W_7feb8 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7febc : bv 32 := 0x00068593.
Lemma F_7febc : fetch_word Asan.M.loaded_segments (0x7febc : word) = Some W_7febc.
Proof. vm_refl. Qed.
Lemma D_7febc : decode_any W_7febc = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fec0 : bv 32 := 0x00000693.
Lemma F_7fec0 : fetch_word Asan.M.loaded_segments (0x7fec0 : word) = Some W_7fec0.
Proof. vm_refl. Qed.
Lemma D_7fec0 : decode_any W_7fec0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fec4 : bv 32 := 0x0040006f.
Lemma F_7fec4 : fetch_word Asan.M.loaded_segments (0x7fec4 : word) = Some W_7fec4.
Proof. vm_refl. Qed.
Lemma D_7fec4 : decode_any W_7fec4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fec8 : bv 32 := 0xf9010113.
Lemma F_7fec8 : fetch_word Asan.M.loaded_segments (0x7fec8 : word) = Some W_7fec8.
Proof. vm_refl. Qed.
Lemma D_7fec8 : decode_any W_7fec8 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fecc : bv 32 := 0x06113423.
Lemma F_7fecc : fetch_word Asan.M.loaded_segments (0x7fecc : word) = Some W_7fecc.
Proof. vm_refl. Qed.
Lemma D_7fecc : decode_any W_7fecc = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fed0 : bv 32 := 0x06813023.
Lemma F_7fed0 : fetch_word Asan.M.loaded_segments (0x7fed0 : word) = Some W_7fed0.
Proof. vm_refl. Qed.
Lemma D_7fed0 : decode_any W_7fed0 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fed4 : bv 32 := 0x04913c23.
Lemma F_7fed4 : fetch_word Asan.M.loaded_segments (0x7fed4 : word) = Some W_7fed4.
Proof. vm_refl. Qed.
Lemma D_7fed4 : decode_any W_7fed4 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fed8 : bv 32 := 0x05213823.
Lemma F_7fed8 : fetch_word Asan.M.loaded_segments (0x7fed8 : word) = Some W_7fed8.
Proof. vm_refl. Qed.
Lemma D_7fed8 : decode_any W_7fed8 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fedc : bv 32 := 0x05313423.
Lemma F_7fedc : fetch_word Asan.M.loaded_segments (0x7fedc : word) = Some W_7fedc.
Proof. vm_refl. Qed.
Lemma D_7fedc : decode_any W_7fedc = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fee0 : bv 32 := 0x05413023.
Lemma F_7fee0 : fetch_word Asan.M.loaded_segments (0x7fee0 : word) = Some W_7fee0.
Proof. vm_refl. Qed.
Lemma D_7fee0 : decode_any W_7fee0 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fee4 : bv 32 := 0x03513c23.
Lemma F_7fee4 : fetch_word Asan.M.loaded_segments (0x7fee4 : word) = Some W_7fee4.
Proof. vm_refl. Qed.
Lemma D_7fee4 : decode_any W_7fee4 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fee8 : bv 32 := 0x03613823.
Lemma F_7fee8 : fetch_word Asan.M.loaded_segments (0x7fee8 : word) = Some W_7fee8.
Proof. vm_refl. Qed.
Lemma D_7fee8 : decode_any W_7fee8 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7feec : bv 32 := 0x03713423.
Lemma F_7feec : fetch_word Asan.M.loaded_segments (0x7feec : word) = Some W_7feec.
Proof. vm_refl. Qed.
Lemma D_7feec : decode_any W_7feec = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fef0 : bv 32 := 0x03813023.
Lemma F_7fef0 : fetch_word Asan.M.loaded_segments (0x7fef0 : word) = Some W_7fef0.
Proof. vm_refl. Qed.
Lemma D_7fef0 : decode_any W_7fef0 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fef4 : bv 32 := 0x01913c23.
Lemma F_7fef4 : fetch_word Asan.M.loaded_segments (0x7fef4 : word) = Some W_7fef4.
Proof. vm_refl. Qed.
Lemma D_7fef4 : decode_any W_7fef4 = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fef8 : bv 32 := 0x00068413.
Lemma F_7fef8 : fetch_word Asan.M.loaded_segments (0x7fef8 : word) = Some W_7fef8.
Proof. vm_refl. Qed.
Lemma D_7fef8 : decode_any W_7fef8 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fefc : bv 32 := 0x00050493.
Lemma F_7fefc : fetch_word Asan.M.loaded_segments (0x7fefc : word) = Some W_7fefc.
Proof. vm_refl. Qed.
Lemma D_7fefc : decode_any W_7fefc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff00 : bv 32 := 0x00b13423.
Lemma F_7ff00 : fetch_word Asan.M.loaded_segments (0x7ff00 : word) = Some W_7ff00.
Proof. vm_refl. Qed.
Lemma D_7ff00 : decode_any W_7ff00 = Some (Store SZ8 2 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff04 : bv 32 := 0x00c13823.
Lemma F_7ff04 : fetch_word Asan.M.loaded_segments (0x7ff04 : word) = Some W_7ff04.
Proof. vm_refl. Qed.
Lemma D_7ff04 : decode_any W_7ff04 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff08 : bv 32 := 0x00068463.
Lemma F_7ff08 : fetch_word Asan.M.loaded_segments (0x7ff08 : word) = Some W_7ff08.
Proof. vm_refl. Qed.
Lemma D_7ff08 : decode_any W_7ff08 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff0c : bv 32 := 0x00040023.
Lemma F_7ff0c : fetch_word Asan.M.loaded_segments (0x7ff0c : word) = Some W_7ff0c.
Proof. vm_refl. Qed.
Lemma D_7ff0c : decode_any W_7ff0c = Some (Store SZ1 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff10 : bv 32 := 0x0006069b.
Lemma F_7ff10 : fetch_word Asan.M.loaded_segments (0x7ff10 : word) = Some W_7ff10.
Proof. vm_refl. Qed.
Lemma D_7ff10 : decode_any W_7ff10 = Some (OpImm32 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff14 : bv 32 := 0x00000513.
Lemma F_7ff14 : fetch_word Asan.M.loaded_segments (0x7ff14 : word) = Some W_7ff14.
Proof. vm_refl. Qed.
Lemma D_7ff14 : decode_any W_7ff14 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff18 : bv 32 := 0x1c068a63.
Lemma F_7ff18 : fetch_word Asan.M.loaded_segments (0x7ff18 : word) = Some W_7ff18.
Proof. vm_refl. Qed.
Lemma D_7ff18 : decode_any W_7ff18 = Some (Branch BC_EQ 13 0 468, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff1c : bv 32 := 0x1c058863.
Lemma F_7ff1c : fetch_word Asan.M.loaded_segments (0x7ff1c : word) = Some W_7ff1c.
Proof. vm_refl. Qed.
Lemma D_7ff1c : decode_any W_7ff1c = Some (Branch BC_EQ 11 0 464, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff20 : bv 32 := 0x02065693.
Lemma F_7ff20 : fetch_word Asan.M.loaded_segments (0x7ff20 : word) = Some W_7ff20.
Proof. vm_refl. Qed.
Lemma D_7ff20 : decode_any W_7ff20 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff24 : bv 32 := 0xfff00513.
Lemma F_7ff24 : fetch_word Asan.M.loaded_segments (0x7ff24 : word) = Some W_7ff24.
Proof. vm_refl. Qed.
Lemma D_7ff24 : decode_any W_7ff24 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff28 : bv 32 := 0xfff90717.
Lemma F_7ff28 : fetch_word Asan.M.loaded_segments (0x7ff28 : word) = Some W_7ff28.
Proof. vm_refl. Qed.
Lemma D_7ff28 : decode_any W_7ff28 = Some (Auipc 14 1048464, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff2c : bv 32 := 0xfff90797.
Lemma F_7ff2c : fetch_word Asan.M.loaded_segments (0x7ff2c : word) = Some W_7ff2c.
Proof. vm_refl. Qed.
Lemma D_7ff2c : decode_any W_7ff2c = Some (Auipc 15 1048464, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff30 : bv 32 := 0x02055513.
Lemma F_7ff30 : fetch_word Asan.M.loaded_segments (0x7ff30 : word) = Some W_7ff30.
Proof. vm_refl. Qed.
Lemma D_7ff30 : decode_any W_7ff30 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff34 : bv 32 := 0x3e47b783.
Lemma F_7ff34 : fetch_word Asan.M.loaded_segments (0x7ff34 : word) = Some W_7ff34.
Proof. vm_refl. Qed.
Lemma D_7ff34 : decode_any W_7ff34 = Some (Load SZ8 true 15 15 996, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff38 : bv 32 := 0x00a67633.
Lemma F_7ff38 : fetch_word Asan.M.loaded_segments (0x7ff38 : word) = Some W_7ff38.
Proof. vm_refl. Qed.
Lemma D_7ff38 : decode_any W_7ff38 = Some (Op ALU_AND 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff3c : bv 32 := 0xfff90517.
Lemma F_7ff3c : fetch_word Asan.M.loaded_segments (0x7ff3c : word) = Some W_7ff3c.
Proof. vm_refl. Qed.
Lemma D_7ff3c : decode_any W_7ff3c = Some (Auipc 10 1048464, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff40 : bv 32 := 0x49453803.
Lemma F_7ff40 : fetch_word Asan.M.loaded_segments (0x7ff40 : word) = Some W_7ff40.
Proof. vm_refl. Qed.
Lemma D_7ff40 : decode_any W_7ff40 = Some (Load SZ8 true 16 10 1172, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff44 : bv 32 := 0x3c073503.
Lemma F_7ff44 : fetch_word Asan.M.loaded_segments (0x7ff44 : word) = Some W_7ff44.
Proof. vm_refl. Qed.
Lemma D_7ff44 : decode_any W_7ff44 = Some (Load SZ8 true 10 14 960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff48 : bv 32 := 0x02f60733.
Lemma F_7ff48 : fetch_word Asan.M.loaded_segments (0x7ff48 : word) = Some W_7ff48.
Proof. vm_refl. Qed.
Lemma D_7ff48 : decode_any W_7ff48 = Some (Mul M_MUL 14 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff4c : bv 32 := 0x00361793.
Lemma F_7ff4c : fetch_word Asan.M.loaded_segments (0x7ff4c : word) = Some W_7ff4c.
Proof. vm_refl. Qed.
Lemma D_7ff4c : decode_any W_7ff4c = Some (ShiftImm ALU_SLL 15 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff50 : bv 32 := 0x01074633.
Lemma F_7ff50 : fetch_word Asan.M.loaded_segments (0x7ff50 : word) = Some W_7ff50.
Proof. vm_refl. Qed.
Lemma D_7ff50 : decode_any W_7ff50 = Some (Op ALU_XOR 12 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff54 : bv 32 := 0x00f58733.
Lemma F_7ff54 : fetch_word Asan.M.loaded_segments (0x7ff54 : word) = Some W_7ff54.
Proof. vm_refl. Qed.
Lemma D_7ff54 : decode_any W_7ff54 = Some (Op ALU_ADD 14 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff58 : bv 32 := 0x0005b783.
Lemma F_7ff58 : fetch_word Asan.M.loaded_segments (0x7ff58 : word) = Some W_7ff58.
Proof. vm_refl. Qed.
Lemma D_7ff58 : decode_any W_7ff58 = Some (Load SZ8 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff5c : bv 32 := 0x00858593.
Lemma F_7ff5c : fetch_word Asan.M.loaded_segments (0x7ff5c : word) = Some W_7ff5c.
Proof. vm_refl. Qed.
Lemma D_7ff5c : decode_any W_7ff5c = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff60 : bv 32 := 0x02a787b3.
Lemma F_7ff60 : fetch_word Asan.M.loaded_segments (0x7ff60 : word) = Some W_7ff60.
Proof. vm_refl. Qed.
Lemma D_7ff60 : decode_any W_7ff60 = Some (Mul M_MUL 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff64 : bv 32 := 0x02f7d813.
Lemma F_7ff64 : fetch_word Asan.M.loaded_segments (0x7ff64 : word) = Some W_7ff64.
Proof. vm_refl. Qed.
Lemma D_7ff64 : decode_any W_7ff64 = Some (ShiftImm ALU_SRL 16 15 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff68 : bv 32 := 0x00f847b3.
Lemma F_7ff68 : fetch_word Asan.M.loaded_segments (0x7ff68 : word) = Some W_7ff68.
Proof. vm_refl. Qed.
Lemma D_7ff68 : decode_any W_7ff68 = Some (Op ALU_XOR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff6c : bv 32 := 0x02a787b3.
Lemma F_7ff6c : fetch_word Asan.M.loaded_segments (0x7ff6c : word) = Some W_7ff6c.
Proof. vm_refl. Qed.
Lemma D_7ff6c : decode_any W_7ff6c = Some (Mul M_MUL 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff70 : bv 32 := 0x00c7c633.
Lemma F_7ff70 : fetch_word Asan.M.loaded_segments (0x7ff70 : word) = Some W_7ff70.
Proof. vm_refl. Qed.
Lemma D_7ff70 : decode_any W_7ff70 = Some (Op ALU_XOR 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff74 : bv 32 := 0x02a60633.
Lemma F_7ff74 : fetch_word Asan.M.loaded_segments (0x7ff74 : word) = Some W_7ff74.
Proof. vm_refl. Qed.
Lemma D_7ff74 : decode_any W_7ff74 = Some (Mul M_MUL 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff78 : bv 32 := 0xfee590e3.
Lemma F_7ff78 : fetch_word Asan.M.loaded_segments (0x7ff78 : word) = Some W_7ff78.
Proof. vm_refl. Qed.
Lemma D_7ff78 : decode_any W_7ff78 = Some (Branch BC_NE 11 14 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff7c : bv 32 := 0x00010b37.
Lemma F_7ff7c : fetch_word Asan.M.loaded_segments (0x7ff7c : word) = Some W_7ff7c.
Proof. vm_refl. Qed.
Lemma D_7ff7c : decode_any W_7ff7c = Some (Lui 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff80 : bv 32 := 0x80000bb7.
Lemma F_7ff80 : fetch_word Asan.M.loaded_segments (0x7ff80 : word) = Some W_7ff80.
Proof. vm_refl. Qed.
Lemma D_7ff80 : decode_any W_7ff80 = Some (Lui 23 524288, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff84 : bv 32 := 0x02a685b3.
Lemma F_7ff84 : fetch_word Asan.M.loaded_segments (0x7ff84 : word) = Some W_7ff84.
Proof. vm_refl. Qed.
Lemma D_7ff84 : decode_any W_7ff84 = Some (Mul M_MUL 11 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff88 : bv 32 := 0x004006b7.
Lemma F_7ff88 : fetch_word Asan.M.loaded_segments (0x7ff88 : word) = Some W_7ff88.
Proof. vm_refl. Qed.
Lemma D_7ff88 : decode_any W_7ff88 = Some (Lui 13 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff8c : bv 32 := 0xfffb0b1b.
Lemma F_7ff8c : fetch_word Asan.M.loaded_segments (0x7ff8c : word) = Some W_7ff8c.
Proof. vm_refl. Qed.
Lemma D_7ff8c : decode_any W_7ff8c = Some (OpImm32 22 22 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff90 : bv 32 := 0xfffb8b9b.
Lemma F_7ff90 : fetch_word Asan.M.loaded_segments (0x7ff90 : word) = Some W_7ff90.
Proof. vm_refl. Qed.
Lemma D_7ff90 : decode_any W_7ff90 = Some (OpImm32 23 23 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff94 : bv 32 := 0x02f5d713.
Lemma F_7ff94 : fetch_word Asan.M.loaded_segments (0x7ff94 : word) = Some W_7ff94.
Proof. vm_refl. Qed.
Lemma D_7ff94 : decode_any W_7ff94 = Some (ShiftImm ALU_SRL 14 11 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff98 : bv 32 := 0x00b745b3.
Lemma F_7ff98 : fetch_word Asan.M.loaded_segments (0x7ff98 : word) = Some W_7ff98.
Proof. vm_refl. Qed.
Lemma D_7ff98 : decode_any W_7ff98 = Some (Op ALU_XOR 11 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ff9c : bv 32 := 0x02a585b3.
Lemma F_7ff9c : fetch_word Asan.M.loaded_segments (0x7ff9c : word) = Some W_7ff9c.
Proof. vm_refl. Qed.
Lemma D_7ff9c : decode_any W_7ff9c = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffa0 : bv 32 := 0x00c5c5b3.
Lemma F_7ffa0 : fetch_word Asan.M.loaded_segments (0x7ffa0 : word) = Some W_7ffa0.
Proof. vm_refl. Qed.
Lemma D_7ffa0 : decode_any W_7ffa0 = Some (Op ALU_XOR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffa4 : bv 32 := 0x02a585b3.
Lemma F_7ffa4 : fetch_word Asan.M.loaded_segments (0x7ffa4 : word) = Some W_7ffa4.
Proof. vm_refl. Qed.
Lemma D_7ffa4 : decode_any W_7ffa4 = Some (Mul M_MUL 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffa8 : bv 32 := 0x02f5d613.
Lemma F_7ffa8 : fetch_word Asan.M.loaded_segments (0x7ffa8 : word) = Some W_7ffa8.
Proof. vm_refl. Qed.
Lemma D_7ffa8 : decode_any W_7ffa8 = Some (ShiftImm ALU_SRL 12 11 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffac : bv 32 := 0x00b645b3.
Lemma F_7ffac : fetch_word Asan.M.loaded_segments (0x7ffac : word) = Some W_7ffac.
Proof. vm_refl. Qed.
Lemma D_7ffac : decode_any W_7ffac = Some (Op ALU_XOR 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffb0 : bv 32 := 0x02a58533.
Lemma F_7ffb0 : fetch_word Asan.M.loaded_segments (0x7ffb0 : word) = Some W_7ffb0.
Proof. vm_refl. Qed.
Lemma D_7ffb0 : decode_any W_7ffb0 = Some (Mul M_MUL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffb4 : bv 32 := 0x02f55593.
Lemma F_7ffb4 : fetch_word Asan.M.loaded_segments (0x7ffb4 : word) = Some W_7ffb4.
Proof. vm_refl. Qed.
Lemma D_7ffb4 : decode_any W_7ffb4 = Some (ShiftImm ALU_SRL 11 10 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffb8 : bv 32 := 0x00a5c9b3.
Lemma F_7ffb8 : fetch_word Asan.M.loaded_segments (0x7ffb8 : word) = Some W_7ffb8.
Proof. vm_refl. Qed.
Lemma D_7ffb8 : decode_any W_7ffb8 = Some (Op ALU_XOR 19 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffbc : bv 32 := 0x02c99513.
Lemma F_7ffbc : fetch_word Asan.M.loaded_segments (0x7ffbc : word) = Some W_7ffbc.
Proof. vm_refl. Qed.
Lemma D_7ffbc : decode_any W_7ffbc = Some (ShiftImm ALU_SLL 10 19 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffc0 : bv 32 := 0x02a55513.
Lemma F_7ffc0 : fetch_word Asan.M.loaded_segments (0x7ffc0 : word) = Some W_7ffc0.
Proof. vm_refl. Qed.
Lemma D_7ffc0 : decode_any W_7ffc0 = Some (ShiftImm ALU_SRL 10 10 42, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffc4 : bv 32 := 0x00a48933.
Lemma F_7ffc4 : fetch_word Asan.M.loaded_segments (0x7ffc4 : word) = Some W_7ffc4.
Proof. vm_refl. Qed.
Lemma D_7ffc4 : decode_any W_7ffc4 = Some (Op ALU_ADD 18 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffc8 : bv 32 := 0x00092503.
Lemma F_7ffc8 : fetch_word Asan.M.loaded_segments (0x7ffc8 : word) = Some W_7ffc8.
Proof. vm_refl. Qed.
Lemma D_7ffc8 : decode_any W_7ffc8 = Some (Load SZ4 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffcc : bv 32 := 0x01068c1b.
Lemma F_7ffcc : fetch_word Asan.M.loaded_segments (0x7ffcc : word) = Some W_7ffcc.
Proof. vm_refl. Qed.
Lemma D_7ffcc : decode_any W_7ffcc = Some (OpImm32 24 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffd0 : bv 32 := 0x01848c33.
Lemma F_7ffd0 : fetch_word Asan.M.loaded_segments (0x7ffd0 : word) = Some W_7ffd0.
Proof. vm_refl. Qed.
Lemma D_7ffd0 : decode_any W_7ffd0 = Some (Op ALU_ADD 24 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffd4 : bv 32 := 0x0230000f.
Lemma F_7ffd4 : fetch_word Asan.M.loaded_segments (0x7ffd4 : word) = Some W_7ffd4.
Proof. vm_refl. Qed.
Lemma D_7ffd4 : decode_any W_7ffd4 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffd8 : bv 32 := 0x01757cb3.
Lemma F_7ffd8 : fetch_word Asan.M.loaded_segments (0x7ffd8 : word) = Some W_7ffd8.
Proof. vm_refl. Qed.
Lemma D_7ffd8 : decode_any W_7ffd8 = Some (Op ALU_AND 25 10 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffdc : bv 32 := 0x0086869b.
Lemma F_7ffdc : fetch_word Asan.M.loaded_segments (0x7ffdc : word) = Some W_7ffdc.
Proof. vm_refl. Qed.
Lemma D_7ffdc : decode_any W_7ffdc = Some (OpImm32 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffe0 : bv 32 := 0x00d48a33.
Lemma F_7ffe0 : fetch_word Asan.M.loaded_segments (0x7ffe0 : word) = Some W_7ffe0.
Proof. vm_refl. Qed.
Lemma D_7ffe0 : decode_any W_7ffe0 = Some (Op ALU_ADD 20 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffe4 : bv 32 := 0x000c8593.
Lemma F_7ffe4 : fetch_word Asan.M.loaded_segments (0x7ffe4 : word) = Some W_7ffe4.
Proof. vm_refl. Qed.
Lemma D_7ffe4 : decode_any W_7ffe4 = Some (OpImm ALU_ADD 11 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffe8 : bv 32 := 0x04058c63.
Lemma F_7ffe8 : fetch_word Asan.M.loaded_segments (0x7ffe8 : word) = Some W_7ffe8.
Proof. vm_refl. Qed.
Lemma D_7ffe8 : decode_any W_7ffe8 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ffec : bv 32 := 0x00058513.
Lemma F_7ffec : fetch_word Asan.M.loaded_segments (0x7ffec : word) = Some W_7ffec.
Proof. vm_refl. Qed.
Lemma D_7ffec : decode_any W_7ffec = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fff0 : bv 32 := 0x0105d59b.
Lemma F_7fff0 : fetch_word Asan.M.loaded_segments (0x7fff0 : word) = Some W_7fff0.
Proof. vm_refl. Qed.
Lemma D_7fff0 : decode_any W_7fff0 = Some (ShiftImm32 ALU_SRL 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fff4 : bv 32 := 0x00359613.
Lemma F_7fff4 : fetch_word Asan.M.loaded_segments (0x7fff4 : word) = Some W_7fff4.
Proof. vm_refl. Qed.
Lemma D_7fff4 : decode_any W_7fff4 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fff8 : bv 32 := 0x00cc0633.
Lemma F_7fff8 : fetch_word Asan.M.loaded_segments (0x7fff8 : word) = Some W_7fff8.
Proof. vm_refl. Qed.
Lemma D_7fff8 : decode_any W_7fff8 = Some (Op ALU_ADD 12 24 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7fffc : bv 32 := 0x00063603.
Lemma F_7fffc : fetch_word Asan.M.loaded_segments (0x7fffc : word) = Some W_7fffc.
Proof. vm_refl. Qed.
Lemma D_7fffc : decode_any W_7fffc = Some (Load SZ8 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80000 : bv 32 := 0x02060463.
Lemma F_80000 : fetch_word Asan.M.loaded_segments (0x80000 : word) = Some W_80000.
Proof. vm_refl. Qed.
Lemma D_80000 : decode_any W_80000 = Some (Branch BC_EQ 12 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_80004 : bv 32 := 0x02051593.
Lemma F_80004 : fetch_word Asan.M.loaded_segments (0x80004 : word) = Some W_80004.
Proof. vm_refl. Qed.
Lemma D_80004 : decode_any W_80004 = Some (ShiftImm ALU_SLL 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80008 : bv 32 := 0x0205d593.
Lemma F_80008 : fetch_word Asan.M.loaded_segments (0x80008 : word) = Some W_80008.
Proof. vm_refl. Qed.
Lemma D_80008 : decode_any W_80008 = Some (ShiftImm ALU_SRL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8000c : bv 32 := 0x0165f5b3.
Lemma F_8000c : fetch_word Asan.M.loaded_segments (0x8000c : word) = Some W_8000c.
Proof. vm_refl. Qed.
Lemma D_8000c : decode_any W_8000c = Some (Op ALU_AND 11 11 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_80010 : bv 32 := 0x00459593.
Lemma F_80010 : fetch_word Asan.M.loaded_segments (0x80010 : word) = Some W_80010.
Proof. vm_refl. Qed.
Lemma D_80010 : decode_any W_80010 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_80014 : bv 32 := 0x00b605b3.
Lemma F_80014 : fetch_word Asan.M.loaded_segments (0x80014 : word) = Some W_80014.
Proof. vm_refl. Qed.
Lemma D_80014 : decode_any W_80014 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_80018 : bv 32 := 0x0005b603.
Lemma F_80018 : fetch_word Asan.M.loaded_segments (0x80018 : word) = Some W_80018.
Proof. vm_refl. Qed.
Lemma D_80018 : decode_any W_80018 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8001c : bv 32 := 0x0085a583.
Lemma F_8001c : fetch_word Asan.M.loaded_segments (0x8001c : word) = Some W_8001c.
Proof. vm_refl. Qed.
Lemma D_8001c : decode_any W_8001c = Some (Load SZ4 true 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80020 : bv 32 := 0xfcc994e3.
Lemma F_80020 : fetch_word Asan.M.loaded_segments (0x80020 : word) = Some W_80020.
Proof. vm_refl. Qed.
Lemma D_80020 : decode_any W_80020 = Some (Branch BC_NE 19 12 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_80024 : bv 32 := 0x0c80006f.
Lemma F_80024 : fetch_word Asan.M.loaded_segments (0x80024 : word) = Some W_80024.
Proof. vm_refl. Qed.
Lemma D_80024 : decode_any W_80024 = Some (Jal 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_80028 : bv 32 := 0x00050a93.
Lemma F_80028 : fetch_word Asan.M.loaded_segments (0x80028 : word) = Some W_80028.
Proof. vm_refl. Qed.
Lemma D_80028 : decode_any W_80028 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8002c : bv 32 := 0x000a0513.
Lemma F_8002c : fetch_word Asan.M.loaded_segments (0x8002c : word) = Some W_8002c.
Proof. vm_refl. Qed.
Lemma D_8002c : decode_any W_8002c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80030 : bv 32 := 0x69c000ef.
Lemma F_80030 : fetch_word Asan.M.loaded_segments (0x80030 : word) = Some W_80030.
Proof. vm_refl. Qed.
Lemma D_80030 : decode_any W_80030 = Some (Jal 1 1692, 4%Z).
Proof. vm_refl. Qed.

Definition W_80034 : bv 32 := 0x00050613.
Lemma F_80034 : fetch_word Asan.M.loaded_segments (0x80034 : word) = Some W_80034.
Proof. vm_refl. Qed.
Lemma D_80034 : decode_any W_80034 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80038 : bv 32 := 0x000a8513.
Lemma F_80038 : fetch_word Asan.M.loaded_segments (0x80038 : word) = Some W_80038.
Proof. vm_refl. Qed.
Lemma D_80038 : decode_any W_80038 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8003c : bv 32 := 0xfc9ff06f.
Lemma F_8003c : fetch_word Asan.M.loaded_segments (0x8003c : word) = Some W_8003c.
Proof. vm_refl. Qed.
Lemma D_8003c : decode_any W_8003c = Some (Jal 0 2097096, 4%Z).
Proof. vm_refl. Qed.

Definition W_80040 : bv 32 := 0x00090513.
Lemma F_80040 : fetch_word Asan.M.loaded_segments (0x80040 : word) = Some W_80040.
Proof. vm_refl. Qed.
Lemma D_80040 : decode_any W_80040 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80044 : bv 32 := 0x5f8000ef.
Lemma F_80044 : fetch_word Asan.M.loaded_segments (0x80044 : word) = Some W_80044.
Proof. vm_refl. Qed.
Lemma D_80044 : decode_any W_80044 = Some (Jal 1 1528, 4%Z).
Proof. vm_refl. Qed.

Definition W_80048 : bv 32 := 0x00050a93.
Lemma F_80048 : fetch_word Asan.M.loaded_segments (0x80048 : word) = Some W_80048.
Proof. vm_refl. Qed.
Lemma D_80048 : decode_any W_80048 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8004c : bv 32 := 0x03950663.
Lemma F_8004c : fetch_word Asan.M.loaded_segments (0x8004c : word) = Some W_8004c.
Proof. vm_refl. Qed.
Lemma D_8004c : decode_any W_8004c = Some (Branch BC_EQ 10 25 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_80050 : bv 32 := 0x00813603.
Lemma F_80050 : fetch_word Asan.M.loaded_segments (0x80050 : word) = Some W_80050.
Proof. vm_refl. Qed.
Lemma D_80050 : decode_any W_80050 = Some (Load SZ8 true 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80054 : bv 32 := 0x01013683.
Lemma F_80054 : fetch_word Asan.M.loaded_segments (0x80054 : word) = Some W_80054.
Proof. vm_refl. Qed.
Lemma D_80054 : decode_any W_80054 = Some (Load SZ8 true 13 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80058 : bv 32 := 0x00048513.
Lemma F_80058 : fetch_word Asan.M.loaded_segments (0x80058 : word) = Some W_80058.
Proof. vm_refl. Qed.
Lemma D_80058 : decode_any W_80058 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8005c : bv 32 := 0x000a8593.
Lemma F_8005c : fetch_word Asan.M.loaded_segments (0x8005c : word) = Some W_8005c.
Proof. vm_refl. Qed.
Lemma D_8005c : decode_any W_8005c = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80060 : bv 32 := 0x00098713.
Lemma F_80060 : fetch_word Asan.M.loaded_segments (0x80060 : word) = Some W_80060.
Proof. vm_refl. Qed.
Lemma D_80060 : decode_any W_80060 = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80064 : bv 32 := 0x524000ef.
Lemma F_80064 : fetch_word Asan.M.loaded_segments (0x80064 : word) = Some W_80064.
Proof. vm_refl. Qed.
Lemma D_80064 : decode_any W_80064 = Some (Jal 1 1316, 4%Z).
Proof. vm_refl. Qed.

Definition W_80068 : bv 32 := 0x00050863.
Lemma F_80068 : fetch_word Asan.M.loaded_segments (0x80068 : word) = Some W_80068.
Proof. vm_refl. Qed.
Lemma D_80068 : decode_any W_80068 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8006c : bv 32 := 0x0310000f.
Lemma F_8006c : fetch_word Asan.M.loaded_segments (0x8006c : word) = Some W_8006c.
Proof. vm_refl. Qed.
Lemma D_8006c : decode_any W_8006c = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80070 : bv 32 := 0x01592023.
Lemma F_80070 : fetch_word Asan.M.loaded_segments (0x80070 : word) = Some W_80070.
Proof. vm_refl. Qed.
Lemma D_80070 : decode_any W_80070 = Some (Store SZ4 18 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80074 : bv 32 := 0x0780006f.
Lemma F_80074 : fetch_word Asan.M.loaded_segments (0x80074 : word) = Some W_80074.
Proof. vm_refl. Qed.
Lemma D_80074 : decode_any W_80074 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_80078 : bv 32 := 0x00400537.
Lemma F_80078 : fetch_word Asan.M.loaded_segments (0x80078 : word) = Some W_80078.
Proof. vm_refl. Qed.
Lemma D_80078 : decode_any W_80078 = Some (Lui 10 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_8007c : bv 32 := 0x00a48533.
Lemma F_8007c : fetch_word Asan.M.loaded_segments (0x8007c : word) = Some W_8007c.
Proof. vm_refl. Qed.
Lemma D_8007c : decode_any W_8007c = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_80080 : bv 32 := 0x00100593.
Lemma F_80080 : fetch_word Asan.M.loaded_segments (0x80080 : word) = Some W_80080.
Proof. vm_refl. Qed.
Lemma D_80080 : decode_any W_80080 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80084 : bv 32 := 0x00b5252f.
Lemma F_80084 : fetch_word Asan.M.loaded_segments (0x80084 : word) = Some W_80084.
Proof. vm_refl. Qed.
Lemma D_80084 : decode_any W_80084 = Some (Amo AMO_ADD AW false false 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_80088 : bv 32 := 0x0015051b.
Lemma F_80088 : fetch_word Asan.M.loaded_segments (0x80088 : word) = Some W_80088.
Proof. vm_refl. Qed.
Lemma D_80088 : decode_any W_80088 = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8008c : bv 32 := 0x02051493.
Lemma F_8008c : fetch_word Asan.M.loaded_segments (0x8008c : word) = Some W_8008c.
Proof. vm_refl. Qed.
Lemma D_8008c : decode_any W_8008c = Some (ShiftImm ALU_SLL 9 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80090 : bv 32 := 0x0204d493.
Lemma F_80090 : fetch_word Asan.M.loaded_segments (0x80090 : word) = Some W_80090.
Proof. vm_refl. Qed.
Lemma D_80090 : decode_any W_80090 = Some (ShiftImm ALU_SRL 9 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80094 : bv 32 := 0x08054663.
Lemma F_80094 : fetch_word Asan.M.loaded_segments (0x80094 : word) = Some W_80094.
Proof. vm_refl. Qed.
Lemma D_80094 : decode_any W_80094 = Some (Branch BC_LT 10 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_80098 : bv 32 := 0x00050b93.
Lemma F_80098 : fetch_word Asan.M.loaded_segments (0x80098 : word) = Some W_80098.
Proof. vm_refl. Qed.
Lemma D_80098 : decode_any W_80098 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8009c : bv 32 := 0x0104d593.
Lemma F_8009c : fetch_word Asan.M.loaded_segments (0x8009c : word) = Some W_8009c.
Proof. vm_refl. Qed.
Lemma D_8009c : decode_any W_8009c = Some (ShiftImm ALU_SRL 11 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_800a0 : bv 32 := 0x00359513.
Lemma F_800a0 : fetch_word Asan.M.loaded_segments (0x800a0 : word) = Some W_800a0.
Proof. vm_refl. Qed.
Lemma D_800a0 : decode_any W_800a0 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_800a4 : bv 32 := 0x00ac0533.
Lemma F_800a4 : fetch_word Asan.M.loaded_segments (0x800a4 : word) = Some W_800a4.
Proof. vm_refl. Qed.
Lemma D_800a4 : decode_any W_800a4 = Some (Op ALU_ADD 10 24 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_800a8 : bv 32 := 0x00053503.
Lemma F_800a8 : fetch_word Asan.M.loaded_segments (0x800a8 : word) = Some W_800a8.
Proof. vm_refl. Qed.
Lemma D_800a8 : decode_any W_800a8 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_800ac : bv 32 := 0x08050a63.
Lemma F_800ac : fetch_word Asan.M.loaded_segments (0x800ac : word) = Some W_800ac.
Proof. vm_refl. Qed.
Lemma D_800ac : decode_any W_800ac = Some (Branch BC_EQ 10 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_800b0 : bv 32 := 0x0164f5b3.
Lemma F_800b0 : fetch_word Asan.M.loaded_segments (0x800b0 : word) = Some W_800b0.
Proof. vm_refl. Qed.
Lemma D_800b0 : decode_any W_800b0 = Some (Op ALU_AND 11 9 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_800b4 : bv 32 := 0x00459593.
Lemma F_800b4 : fetch_word Asan.M.loaded_segments (0x800b4 : word) = Some W_800b4.
Proof. vm_refl. Qed.
Lemma D_800b4 : decode_any W_800b4 = Some (ShiftImm ALU_SLL 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_800b8 : bv 32 := 0x00b504b3.
Lemma F_800b8 : fetch_word Asan.M.loaded_segments (0x800b8 : word) = Some W_800b8.
Proof. vm_refl. Qed.
Lemma D_800b8 : decode_any W_800b8 = Some (Op ALU_ADD 9 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_800bc : bv 32 := 0x00810613.
Lemma F_800bc : fetch_word Asan.M.loaded_segments (0x800bc : word) = Some W_800bc.
Proof. vm_refl. Qed.
Lemma D_800bc : decode_any W_800bc = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_800c0 : bv 32 := 0x00048513.
Lemma F_800c0 : fetch_word Asan.M.loaded_segments (0x800c0 : word) = Some W_800c0.
Proof. vm_refl. Qed.
Lemma D_800c0 : decode_any W_800c0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_800c4 : bv 32 := 0x00000593.
Lemma F_800c4 : fetch_word Asan.M.loaded_segments (0x800c4 : word) = Some W_800c4.
Proof. vm_refl. Qed.
Lemma D_800c4 : decode_any W_800c4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_800c8 : bv 32 := 0x00098693.
Lemma F_800c8 : fetch_word Asan.M.loaded_segments (0x800c8 : word) = Some W_800c8.
Proof. vm_refl. Qed.
Lemma D_800c8 : decode_any W_800c8 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_800cc : bv 32 := 0xaf5ff0ef.
Lemma F_800cc : fetch_word Asan.M.loaded_segments (0x800cc : word) = Some W_800cc.
Proof. vm_refl. Qed.
Lemma D_800cc : decode_any W_800cc = Some (Jal 1 2095860, 4%Z).
Proof. vm_refl. Qed.

Definition W_800d0 : bv 32 := 0x0154a423.
Lemma F_800d0 : fetch_word Asan.M.loaded_segments (0x800d0 : word) = Some W_800d0.
Proof. vm_refl. Qed.
Lemma D_800d0 : decode_any W_800d0 = Some (Store SZ4 9 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_800d4 : bv 32 := 0x0310000f.
Lemma F_800d4 : fetch_word Asan.M.loaded_segments (0x800d4 : word) = Some W_800d4.
Proof. vm_refl. Qed.
Lemma D_800d4 : decode_any W_800d4 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_800d8 : bv 32 := 0x000b8513.
Lemma F_800d8 : fetch_word Asan.M.loaded_segments (0x800d8 : word) = Some W_800d8.
Proof. vm_refl. Qed.
Lemma D_800d8 : decode_any W_800d8 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_800dc : bv 32 := 0x01792023.
Lemma F_800dc : fetch_word Asan.M.loaded_segments (0x800dc : word) = Some W_800dc.
Proof. vm_refl. Qed.
Lemma D_800dc : decode_any W_800dc = Some (Store SZ4 18 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_800e0 : bv 32 := 0x00040663.
Lemma F_800e0 : fetch_word Asan.M.loaded_segments (0x800e0 : word) = Some W_800e0.
Proof. vm_refl. Qed.
Lemma D_800e0 : decode_any W_800e0 = Some (Branch BC_EQ 8 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_800e4 : bv 32 := 0x00100593.
Lemma F_800e4 : fetch_word Asan.M.loaded_segments (0x800e4 : word) = Some W_800e4.
Proof. vm_refl. Qed.
Lemma D_800e4 : decode_any W_800e4 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_800e8 : bv 32 := 0x00b40023.
Lemma F_800e8 : fetch_word Asan.M.loaded_segments (0x800e8 : word) = Some W_800e8.
Proof. vm_refl. Qed.
Lemma D_800e8 : decode_any W_800e8 = Some (Store SZ1 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_800ec : bv 32 := 0x06813083.
Lemma F_800ec : fetch_word Asan.M.loaded_segments (0x800ec : word) = Some W_800ec.
Proof. vm_refl. Qed.
Lemma D_800ec : decode_any W_800ec = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_800f0 : bv 32 := 0x06013403.
Lemma F_800f0 : fetch_word Asan.M.loaded_segments (0x800f0 : word) = Some W_800f0.
Proof. vm_refl. Qed.
Lemma D_800f0 : decode_any W_800f0 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_800f4 : bv 32 := 0x05813483.
Lemma F_800f4 : fetch_word Asan.M.loaded_segments (0x800f4 : word) = Some W_800f4.
Proof. vm_refl. Qed.
Lemma D_800f4 : decode_any W_800f4 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_800f8 : bv 32 := 0x05013903.
Lemma F_800f8 : fetch_word Asan.M.loaded_segments (0x800f8 : word) = Some W_800f8.
Proof. vm_refl. Qed.
Lemma D_800f8 : decode_any W_800f8 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_800fc : bv 32 := 0x04813983.
Lemma F_800fc : fetch_word Asan.M.loaded_segments (0x800fc : word) = Some W_800fc.
Proof. vm_refl. Qed.
Lemma D_800fc : decode_any W_800fc = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_80100 : bv 32 := 0x04013a03.
Lemma F_80100 : fetch_word Asan.M.loaded_segments (0x80100 : word) = Some W_80100.
Proof. vm_refl. Qed.
Lemma D_80100 : decode_any W_80100 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_80104 : bv 32 := 0x03813a83.
Lemma F_80104 : fetch_word Asan.M.loaded_segments (0x80104 : word) = Some W_80104.
Proof. vm_refl. Qed.
Lemma D_80104 : decode_any W_80104 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_80108 : bv 32 := 0x03013b03.
Lemma F_80108 : fetch_word Asan.M.loaded_segments (0x80108 : word) = Some W_80108.
Proof. vm_refl. Qed.
Lemma D_80108 : decode_any W_80108 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8010c : bv 32 := 0x02813b83.
Lemma F_8010c : fetch_word Asan.M.loaded_segments (0x8010c : word) = Some W_8010c.
Proof. vm_refl. Qed.
Lemma D_8010c : decode_any W_8010c = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_80110 : bv 32 := 0x02013c03.
Lemma F_80110 : fetch_word Asan.M.loaded_segments (0x80110 : word) = Some W_80110.
Proof. vm_refl. Qed.
Lemma D_80110 : decode_any W_80110 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80114 : bv 32 := 0x01813c83.
Lemma F_80114 : fetch_word Asan.M.loaded_segments (0x80114 : word) = Some W_80114.
Proof. vm_refl. Qed.
Lemma D_80114 : decode_any W_80114 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_80118 : bv 32 := 0x07010113.
Lemma F_80118 : fetch_word Asan.M.loaded_segments (0x80118 : word) = Some W_80118.
Proof. vm_refl. Qed.
Lemma D_80118 : decode_any W_80118 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_8011c : bv 32 := 0x00008067.
Lemma F_8011c : fetch_word Asan.M.loaded_segments (0x8011c : word) = Some W_8011c.
Proof. vm_refl. Qed.
Lemma D_8011c : decode_any W_8011c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80120 : bv 32 := 0x017576b3.
Lemma F_80120 : fetch_word Asan.M.loaded_segments (0x80120 : word) = Some W_80120.
Proof. vm_refl. Qed.
Lemma D_80120 : decode_any W_80120 = Some (Op ALU_AND 13 10 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_80124 : bv 32 := 0xfff99517.
Lemma F_80124 : fetch_word Asan.M.loaded_segments (0x80124 : word) = Some W_80124.
Proof. vm_refl. Qed.
Lemma D_80124 : decode_any W_80124 = Some (Auipc 10 1048473, 4%Z).
Proof. vm_refl. Qed.

Definition W_80128 : bv 32 := 0xfff96597.
Lemma F_80128 : fetch_word Asan.M.loaded_segments (0x80128 : word) = Some W_80128.
Proof. vm_refl. Qed.
Lemma D_80128 : decode_any W_80128 = Some (Auipc 11 1048470, 4%Z).
Proof. vm_refl. Qed.

Definition W_8012c : bv 32 := 0x12450513.
Lemma F_8012c : fetch_word Asan.M.loaded_segments (0x8012c : word) = Some W_8012c.
Proof. vm_refl. Qed.
Lemma D_8012c : decode_any W_8012c = Some (OpImm ALU_ADD 10 10 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_80130 : bv 32 := 0x53d58613.
Lemma F_80130 : fetch_word Asan.M.loaded_segments (0x80130 : word) = Some W_80130.
Proof. vm_refl. Qed.
Lemma D_80130 : decode_any W_80130 = Some (OpImm ALU_ADD 12 11 1341, 4%Z).
Proof. vm_refl. Qed.

Definition W_80134 : bv 32 := 0x08c00593.
Lemma F_80134 : fetch_word Asan.M.loaded_segments (0x80134 : word) = Some W_80134.
Proof. vm_refl. Qed.
Lemma D_80134 : decode_any W_80134 = Some (OpImm ALU_ADD 11 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_80138 : bv 32 := 0x00048713.
Lemma F_80138 : fetch_word Asan.M.loaded_segments (0x80138 : word) = Some W_80138.
Proof. vm_refl. Qed.
Lemma D_80138 : decode_any W_80138 = Some (OpImm ALU_ADD 14 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8013c : bv 32 := 0xf2df80ef.
Lemma F_8013c : fetch_word Asan.M.loaded_segments (0x8013c : word) = Some W_8013c.
Proof. vm_refl. Qed.
Lemma D_8013c : decode_any W_8013c = Some (Jal 1 2068268, 4%Z).
Proof. vm_refl. Qed.

Definition W_80140 : bv 32 := 0x000a0513.
Lemma F_80140 : fetch_word Asan.M.loaded_segments (0x80140 : word) = Some W_80140.
Proof. vm_refl. Qed.
Lemma D_80140 : decode_any W_80140 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80144 : bv 32 := 0x588000ef.
Lemma F_80144 : fetch_word Asan.M.loaded_segments (0x80144 : word) = Some W_80144.
Proof. vm_refl. Qed.
Lemma D_80144 : decode_any W_80144 = Some (Jal 1 1416, 4%Z).
Proof. vm_refl. Qed.

Definition W_80148 : bv 32 := 0xf69ff06f.
Lemma F_80148 : fetch_word Asan.M.loaded_segments (0x80148 : word) = Some W_80148.
Proof. vm_refl. Qed.
Lemma D_80148 : decode_any W_80148 = Some (Jal 0 2097000, 4%Z).
Proof. vm_refl. Qed.
