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

Definition W_8e2bc : bv 32 := 0x00060693.
Lemma F_8e2bc : fetch_word Asan.M.loaded_segments (0x8e30c : word) = Some W_8e2bc.
Proof. vm_refl. Qed.
Lemma D_8e2bc : decode_any W_8e2bc = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2c0 : bv 32 := 0x00000613.
Lemma F_8e2c0 : fetch_word Asan.M.loaded_segments (0x8e310 : word) = Some W_8e2c0.
Proof. vm_refl. Qed.
Lemma D_8e2c0 : decode_any W_8e2c0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2c4 : bv 32 := 0x0040006f.
Lemma F_8e2c4 : fetch_word Asan.M.loaded_segments (0x8e314 : word) = Some W_8e2c4.
Proof. vm_refl. Qed.
Lemma D_8e2c4 : decode_any W_8e2c4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2c8 : bv 32 := 0xfa010113.
Lemma F_8e2c8 : fetch_word Asan.M.loaded_segments (0x8e318 : word) = Some W_8e2c8.
Proof. vm_refl. Qed.
Lemma D_8e2c8 : decode_any W_8e2c8 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2cc : bv 32 := 0x04113c23.
Lemma F_8e2cc : fetch_word Asan.M.loaded_segments (0x8e31c : word) = Some W_8e2cc.
Proof. vm_refl. Qed.
Lemma D_8e2cc : decode_any W_8e2cc = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2d0 : bv 32 := 0x04813823.
Lemma F_8e2d0 : fetch_word Asan.M.loaded_segments (0x8e320 : word) = Some W_8e2d0.
Proof. vm_refl. Qed.
Lemma D_8e2d0 : decode_any W_8e2d0 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2d4 : bv 32 := 0x04913423.
Lemma F_8e2d4 : fetch_word Asan.M.loaded_segments (0x8e324 : word) = Some W_8e2d4.
Proof. vm_refl. Qed.
Lemma D_8e2d4 : decode_any W_8e2d4 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2d8 : bv 32 := 0x05213023.
Lemma F_8e2d8 : fetch_word Asan.M.loaded_segments (0x8e328 : word) = Some W_8e2d8.
Proof. vm_refl. Qed.
Lemma D_8e2d8 : decode_any W_8e2d8 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2dc : bv 32 := 0x03313c23.
Lemma F_8e2dc : fetch_word Asan.M.loaded_segments (0x8e32c : word) = Some W_8e2dc.
Proof. vm_refl. Qed.
Lemma D_8e2dc : decode_any W_8e2dc = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2e0 : bv 32 := 0x03413823.
Lemma F_8e2e0 : fetch_word Asan.M.loaded_segments (0x8e330 : word) = Some W_8e2e0.
Proof. vm_refl. Qed.
Lemma D_8e2e0 : decode_any W_8e2e0 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2e4 : bv 32 := 0x00068993.
Lemma F_8e2e4 : fetch_word Asan.M.loaded_segments (0x8e334 : word) = Some W_8e2e4.
Proof. vm_refl. Qed.
Lemma D_8e2e4 : decode_any W_8e2e4 = Some (OpImm ALU_ADD 19 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2e8 : bv 32 := 0x00060493.
Lemma F_8e2e8 : fetch_word Asan.M.loaded_segments (0x8e338 : word) = Some W_8e2e8.
Proof. vm_refl. Qed.
Lemma D_8e2e8 : decode_any W_8e2e8 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2ec : bv 32 := 0x00058413.
Lemma F_8e2ec : fetch_word Asan.M.loaded_segments (0x8e33c : word) = Some W_8e2ec.
Proof. vm_refl. Qed.
Lemma D_8e2ec : decode_any W_8e2ec = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2f0 : bv 32 := 0x000ab597.
Lemma F_8e2f0 : fetch_word Asan.M.loaded_segments (0x8e340 : word) = Some W_8e2f0.
Proof. vm_refl. Qed.
Lemma D_8e2f0 : decode_any W_8e2f0 = Some (Auipc 11 171, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2f4 : bv 32 := 0xe585ba03.
Lemma F_8e2f4 : fetch_word Asan.M.loaded_segments (0x8e344 : word) = Some W_8e2f4.
Proof. vm_refl. Qed.
Lemma D_8e2f4 : decode_any W_8e2f4 = Some (Load SZ8 true 20 11 3672, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2f8 : bv 32 := 0x000a3583.
Lemma F_8e2f8 : fetch_word Asan.M.loaded_segments (0x8e348 : word) = Some W_8e2f8.
Proof. vm_refl. Qed.
Lemma D_8e2f8 : decode_any W_8e2f8 = Some (Load SZ8 true 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e2fc : bv 32 := 0x00050913.
Lemma F_8e2fc : fetch_word Asan.M.loaded_segments (0x8e34c : word) = Some W_8e2fc.
Proof. vm_refl. Qed.
Lemma D_8e2fc : decode_any W_8e2fc = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e300 : bv 32 := 0x00059863.
Lemma F_8e300 : fetch_word Asan.M.loaded_segments (0x8e350 : word) = Some W_8e300.
Proof. vm_refl. Qed.
Lemma D_8e300 : decode_any W_8e300 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e310 : bv 32 := 0xfff58513.
Lemma F_8e310 : fetch_word Asan.M.loaded_segments (0x8e360 : word) = Some W_8e310.
Proof. vm_refl. Qed.
Lemma D_8e310 : decode_any W_8e310 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e314 : bv 32 := 0x00a5f533.
Lemma F_8e314 : fetch_word Asan.M.loaded_segments (0x8e364 : word) = Some W_8e314.
Proof. vm_refl. Qed.
Lemma D_8e314 : decode_any W_8e314 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e318 : bv 32 := 0x0a051863.
Lemma F_8e318 : fetch_word Asan.M.loaded_segments (0x8e368 : word) = Some W_8e318.
Proof. vm_refl. Qed.
Lemma D_8e318 : decode_any W_8e318 = Some (Branch BC_NE 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e31c : bv 32 := 0x00b40433.
Lemma F_8e31c : fetch_word Asan.M.loaded_segments (0x8e36c : word) = Some W_8e31c.
Proof. vm_refl. Qed.
Lemma D_8e31c : decode_any W_8e31c = Some (Op ALU_ADD 8 8 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e320 : bv 32 := 0xfff40413.
Lemma F_8e320 : fetch_word Asan.M.loaded_segments (0x8e370 : word) = Some W_8e320.
Proof. vm_refl. Qed.
Lemma D_8e320 : decode_any W_8e320 = Some (OpImm ALU_ADD 8 8 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e324 : bv 32 := 0x40b00533.
Lemma F_8e324 : fetch_word Asan.M.loaded_segments (0x8e374 : word) = Some W_8e324.
Proof. vm_refl. Qed.
Lemma D_8e324 : decode_any W_8e324 = Some (Op ALU_SUB 10 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e328 : bv 32 := 0x00a47433.
Lemma F_8e328 : fetch_word Asan.M.loaded_segments (0x8e378 : word) = Some W_8e328.
Proof. vm_refl. Qed.
Lemma D_8e328 : decode_any W_8e328 = Some (Op ALU_AND 8 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e32c : bv 32 := 0x00059863.
Lemma F_8e32c : fetch_word Asan.M.loaded_segments (0x8e37c : word) = Some W_8e32c.
Proof. vm_refl. Qed.
Lemma D_8e32c : decode_any W_8e32c = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e33c : bv 32 := 0x00a97933.
Lemma F_8e33c : fetch_word Asan.M.loaded_segments (0x8e38c : word) = Some W_8e33c.
Proof. vm_refl. Qed.
Lemma D_8e33c : decode_any W_8e33c = Some (Op ALU_AND 18 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e340 : bv 32 := 0x03200513.
Lemma F_8e340 : fetch_word Asan.M.loaded_segments (0x8e390 : word) = Some W_8e340.
Proof. vm_refl. Qed.
Lemma D_8e340 : decode_any W_8e340 = Some (OpImm ALU_ADD 10 0 50, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e344 : bv 32 := 0x00a12023.
Lemma F_8e344 : fetch_word Asan.M.loaded_segments (0x8e394 : word) = Some W_8e344.
Proof. vm_refl. Qed.
Lemma D_8e344 : decode_any W_8e344 = Some (Store SZ4 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e348 : bv 32 := 0x00010613.
Lemma F_8e348 : fetch_word Asan.M.loaded_segments (0x8e398 : word) = Some W_8e348.
Proof. vm_refl. Qed.
Lemma D_8e348 : decode_any W_8e348 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e34c : bv 32 := 0x00098513.
Lemma F_8e34c : fetch_word Asan.M.loaded_segments (0x8e39c : word) = Some W_8e34c.
Proof. vm_refl. Qed.
Lemma D_8e34c : decode_any W_8e34c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e350 : bv 32 := 0x00040593.
Lemma F_8e350 : fetch_word Asan.M.loaded_segments (0x8e3a0 : word) = Some W_8e350.
Proof. vm_refl. Qed.
Lemma D_8e350 : decode_any W_8e350 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e354 : bv 32 := 0x608000ef.
Lemma F_8e354 : fetch_word Asan.M.loaded_segments (0x8e3a4 : word) = Some W_8e354.
Proof. vm_refl. Qed.
Lemma D_8e354 : decode_any W_8e354 = Some (Jal 1 1544, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e358 : bv 32 := 0x00012683.
Lemma F_8e358 : fetch_word Asan.M.loaded_segments (0x8e3a8 : word) = Some W_8e358.
Proof. vm_refl. Qed.
Lemma D_8e358 : decode_any W_8e358 = Some (Load SZ4 true 13 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e35c : bv 32 := 0x00050713.
Lemma F_8e35c : fetch_word Asan.M.loaded_segments (0x8e3ac : word) = Some W_8e35c.
Proof. vm_refl. Qed.
Lemma D_8e35c : decode_any W_8e35c = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e360 : bv 32 := 0x00300613.
Lemma F_8e360 : fetch_word Asan.M.loaded_segments (0x8e3b0 : word) = Some W_8e360.
Proof. vm_refl. Qed.
Lemma D_8e360 : decode_any W_8e360 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e364 : bv 32 := 0x00090513.
Lemma F_8e364 : fetch_word Asan.M.loaded_segments (0x8e3b4 : word) = Some W_8e364.
Proof. vm_refl. Qed.
Lemma D_8e364 : decode_any W_8e364 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e368 : bv 32 := 0x00040593.
Lemma F_8e368 : fetch_word Asan.M.loaded_segments (0x8e3b8 : word) = Some W_8e368.
Proof. vm_refl. Qed.
Lemma D_8e368 : decode_any W_8e368 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e36c : bv 32 := 0x00000793.
Lemma F_8e36c : fetch_word Asan.M.loaded_segments (0x8e3bc : word) = Some W_8e36c.
Proof. vm_refl. Qed.
Lemma D_8e36c : decode_any W_8e36c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e370 : bv 32 := 0xa40fe0ef.
Lemma F_8e370 : fetch_word Asan.M.loaded_segments (0x8e3c0 : word) = Some W_8e370.
Proof. vm_refl. Qed.
Lemma D_8e370 : decode_any W_8e370 = Some (Jal 1 2089536, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e374 : bv 32 := 0x00050993.
Lemma F_8e374 : fetch_word Asan.M.loaded_segments (0x8e3c4 : word) = Some W_8e374.
Proof. vm_refl. Qed.
Lemma D_8e374 : decode_any W_8e374 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e378 : bv 32 := 0x00000593.
Lemma F_8e378 : fetch_word Asan.M.loaded_segments (0x8e3c8 : word) = Some W_8e378.
Proof. vm_refl. Qed.
Lemma D_8e378 : decode_any W_8e378 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e37c : bv 32 := 0xa14fe0ef.
Lemma F_8e37c : fetch_word Asan.M.loaded_segments (0x8e3cc : word) = Some W_8e37c.
Proof. vm_refl. Qed.
Lemma D_8e37c : decode_any W_8e37c = Some (Jal 1 2089492, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e380 : bv 32 := 0xaaaab537.
Lemma F_8e380 : fetch_word Asan.M.loaded_segments (0x8e3d0 : word) = Some W_8e380.
Proof. vm_refl. Qed.
Lemma D_8e380 : decode_any W_8e380 = Some (Lui 10 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e384 : bv 32 := 0xaaa50513.
Lemma F_8e384 : fetch_word Asan.M.loaded_segments (0x8e3d4 : word) = Some W_8e384.
Proof. vm_refl. Qed.
Lemma D_8e384 : decode_any W_8e384 = Some (OpImm ALU_ADD 10 10 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e388 : bv 32 := 0x02a12623.
Lemma F_8e388 : fetch_word Asan.M.loaded_segments (0x8e3d8 : word) = Some W_8e388.
Proof. vm_refl. Qed.
Lemma D_8e388 : decode_any W_8e388 = Some (Store SZ4 2 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e38c : bv 32 := 0x02c10593.
Lemma F_8e38c : fetch_word Asan.M.loaded_segments (0x8e3dc : word) = Some W_8e38c.
Proof. vm_refl. Qed.
Lemma D_8e38c : decode_any W_8e38c = Some (OpImm ALU_ADD 11 2 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e390 : bv 32 := 0x00098513.
Lemma F_8e390 : fetch_word Asan.M.loaded_segments (0x8e3e0 : word) = Some W_8e390.
Proof. vm_refl. Qed.
Lemma D_8e390 : decode_any W_8e390 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e394 : bv 32 := 0x9fcfe0ef.
Lemma F_8e394 : fetch_word Asan.M.loaded_segments (0x8e3e4 : word) = Some W_8e394.
Proof. vm_refl. Qed.
Lemma D_8e394 : decode_any W_8e394 = Some (Jal 1 2089468, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e398 : bv 32 := 0x04051063.
Lemma F_8e398 : fetch_word Asan.M.loaded_segments (0x8e3e8 : word) = Some W_8e398.
Proof. vm_refl. Qed.
Lemma D_8e398 : decode_any W_8e398 = Some (Branch BC_NE 10 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e39c : bv 32 := 0x00040513.
Lemma F_8e39c : fetch_word Asan.M.loaded_segments (0x8e3ec : word) = Some W_8e39c.
Proof. vm_refl. Qed.
Lemma D_8e39c : decode_any W_8e39c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e3a0 : bv 32 := 0x8d8fa0ef.
Lemma F_8e3a0 : fetch_word Asan.M.loaded_segments (0x8e3f0 : word) = Some W_8e3a0.
Proof. vm_refl. Qed.
Lemma D_8e3a0 : decode_any W_8e3a0 = Some (Jal 1 2072792, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e3a4 : bv 32 := 0x00098513.
Lemma F_8e3a4 : fetch_word Asan.M.loaded_segments (0x8e3f4 : word) = Some W_8e3a4.
Proof. vm_refl. Qed.
Lemma D_8e3a4 : decode_any W_8e3a4 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e3a8 : bv 32 := 0x05813083.
Lemma F_8e3a8 : fetch_word Asan.M.loaded_segments (0x8e3f8 : word) = Some W_8e3a8.
Proof. vm_refl. Qed.
Lemma D_8e3a8 : decode_any W_8e3a8 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e3ac : bv 32 := 0x05013403.
Lemma F_8e3ac : fetch_word Asan.M.loaded_segments (0x8e3fc : word) = Some W_8e3ac.
Proof. vm_refl. Qed.
Lemma D_8e3ac : decode_any W_8e3ac = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e3b0 : bv 32 := 0x04813483.
Lemma F_8e3b0 : fetch_word Asan.M.loaded_segments (0x8e400 : word) = Some W_8e3b0.
Proof. vm_refl. Qed.
Lemma D_8e3b0 : decode_any W_8e3b0 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e3b4 : bv 32 := 0x04013903.
Lemma F_8e3b4 : fetch_word Asan.M.loaded_segments (0x8e404 : word) = Some W_8e3b4.
Proof. vm_refl. Qed.
Lemma D_8e3b4 : decode_any W_8e3b4 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e3b8 : bv 32 := 0x03813983.
Lemma F_8e3b8 : fetch_word Asan.M.loaded_segments (0x8e408 : word) = Some W_8e3b8.
Proof. vm_refl. Qed.
Lemma D_8e3b8 : decode_any W_8e3b8 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e3bc : bv 32 := 0x03013a03.
Lemma F_8e3bc : fetch_word Asan.M.loaded_segments (0x8e40c : word) = Some W_8e3bc.
Proof. vm_refl. Qed.
Lemma D_8e3bc : decode_any W_8e3bc = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e3c0 : bv 32 := 0x06010113.
Lemma F_8e3c0 : fetch_word Asan.M.loaded_segments (0x8e410 : word) = Some W_8e3c0.
Proof. vm_refl. Qed.
Lemma D_8e3c0 : decode_any W_8e3c0 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e3c4 : bv 32 := 0x00008067.
Lemma F_8e3c4 : fetch_word Asan.M.loaded_segments (0x8e414 : word) = Some W_8e3c4.
Proof. vm_refl. Qed.
Lemma D_8e3c4 : decode_any W_8e3c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e440 : bv 32 := 0x00060693.
Lemma F_8e440 : fetch_word Asan.M.loaded_segments (0x8e490 : word) = Some W_8e440.
Proof. vm_refl. Qed.
Lemma D_8e440 : decode_any W_8e440 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e444 : bv 32 := 0x00100613.
Lemma F_8e444 : fetch_word Asan.M.loaded_segments (0x8e494 : word) = Some W_8e444.
Proof. vm_refl. Qed.
Lemma D_8e444 : decode_any W_8e444 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8e448 : bv 32 := 0xe81ff06f.
Lemma F_8e448 : fetch_word Asan.M.loaded_segments (0x8e498 : word) = Some W_8e448.
Proof. vm_refl. Qed.
Lemma D_8e448 : decode_any W_8e448 = Some (Jal 0 2096768, 4%Z).
Proof. vm_refl. Qed.
