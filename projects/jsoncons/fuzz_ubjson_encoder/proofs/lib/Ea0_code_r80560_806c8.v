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

Definition W_9b27c : bv 32 := 0x00008513.
Lemma F_9b27c : fetch_word Asan.M.loaded_segments (0x9b2cc : word) = Some W_9b27c.
Proof. vm_refl. Qed.
Lemma D_9b27c : decode_any W_9b27c = Some (OpImm ALU_ADD 10 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b280 : bv 32 := 0x00008067.
Lemma F_9b280 : fetch_word Asan.M.loaded_segments (0x9b2d0 : word) = Some W_9b280.
Proof. vm_refl. Qed.
Lemma D_9b280 : decode_any W_9b280 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b284 : bv 32 := 0xfc010113.
Lemma F_9b284 : fetch_word Asan.M.loaded_segments (0x9b2d4 : word) = Some W_9b284.
Proof. vm_refl. Qed.
Lemma D_9b284 : decode_any W_9b284 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b288 : bv 32 := 0x02113c23.
Lemma F_9b288 : fetch_word Asan.M.loaded_segments (0x9b2d8 : word) = Some W_9b288.
Proof. vm_refl. Qed.
Lemma D_9b288 : decode_any W_9b288 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b28c : bv 32 := 0x02813823.
Lemma F_9b28c : fetch_word Asan.M.loaded_segments (0x9b2dc : word) = Some W_9b28c.
Proof. vm_refl. Qed.
Lemma D_9b28c : decode_any W_9b28c = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b290 : bv 32 := 0x02913423.
Lemma F_9b290 : fetch_word Asan.M.loaded_segments (0x9b2e0 : word) = Some W_9b290.
Proof. vm_refl. Qed.
Lemma D_9b290 : decode_any W_9b290 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b294 : bv 32 := 0x03213023.
Lemma F_9b294 : fetch_word Asan.M.loaded_segments (0x9b2e4 : word) = Some W_9b294.
Proof. vm_refl. Qed.
Lemma D_9b294 : decode_any W_9b294 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b298 : bv 32 := 0x01313c23.
Lemma F_9b298 : fetch_word Asan.M.loaded_segments (0x9b2e8 : word) = Some W_9b298.
Proof. vm_refl. Qed.
Lemma D_9b298 : decode_any W_9b298 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b29c : bv 32 := 0x01413823.
Lemma F_9b29c : fetch_word Asan.M.loaded_segments (0x9b2ec : word) = Some W_9b29c.
Proof. vm_refl. Qed.
Lemma D_9b29c : decode_any W_9b29c = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2a0 : bv 32 := 0x01513423.
Lemma F_9b2a0 : fetch_word Asan.M.loaded_segments (0x9b2f0 : word) = Some W_9b2a0.
Proof. vm_refl. Qed.
Lemma D_9b2a0 : decode_any W_9b2a0 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2a4 : bv 32 := 0x01613023.
Lemma F_9b2a4 : fetch_word Asan.M.loaded_segments (0x9b2f4 : word) = Some W_9b2a4.
Proof. vm_refl. Qed.
Lemma D_9b2a4 : decode_any W_9b2a4 = Some (Store SZ8 2 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2a8 : bv 32 := 0x00068493.
Lemma F_9b2a8 : fetch_word Asan.M.loaded_segments (0x9b2f8 : word) = Some W_9b2a8.
Proof. vm_refl. Qed.
Lemma D_9b2a8 : decode_any W_9b2a8 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2ac : bv 32 := 0x02079413.
Lemma F_9b2ac : fetch_word Asan.M.loaded_segments (0x9b2fc : word) = Some W_9b2ac.
Proof. vm_refl. Qed.
Lemma D_9b2ac : decode_any W_9b2ac = Some (ShiftImm ALU_SLL 8 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2b0 : bv 32 := 0x00100693.
Lemma F_9b2b0 : fetch_word Asan.M.loaded_segments (0x9b300 : word) = Some W_9b2b0.
Proof. vm_refl. Qed.
Lemma D_9b2b0 : decode_any W_9b2b0 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2b4 : bv 32 := 0x02045413.
Lemma F_9b2b4 : fetch_word Asan.M.loaded_segments (0x9b304 : word) = Some W_9b2b4.
Proof. vm_refl. Qed.
Lemma D_9b2b4 : decode_any W_9b2b4 = Some (ShiftImm ALU_SRL 8 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2b8 : bv 32 := 0x0ef6f863.
Lemma F_9b2b8 : fetch_word Asan.M.loaded_segments (0x9b308 : word) = Some W_9b2b8.
Proof. vm_refl. Qed.
Lemma D_9b2b8 : decode_any W_9b2b8 = Some (Branch BC_GEU 13 15 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2bc : bv 32 := 0x0009e697.
Lemma F_9b2bc : fetch_word Asan.M.loaded_segments (0x9b30c : word) = Some W_9b2bc.
Proof. vm_refl. Qed.
Lemma D_9b2bc : decode_any W_9b2bc = Some (Auipc 13 158, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2c0 : bv 32 := 0xe8c6b903.
Lemma F_9b2c0 : fetch_word Asan.M.loaded_segments (0x9b310 : word) = Some W_9b2c0.
Proof. vm_refl. Qed.
Lemma D_9b2c0 : decode_any W_9b2c0 = Some (Load SZ8 true 18 13 3724, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2c4 : bv 32 := 0x00093683.
Lemma F_9b2c4 : fetch_word Asan.M.loaded_segments (0x9b314 : word) = Some W_9b2c4.
Proof. vm_refl. Qed.
Lemma D_9b2c4 : decode_any W_9b2c4 = Some (Load SZ8 true 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2c8 : bv 32 := 0x00068e63.
Lemma F_9b2c8 : fetch_word Asan.M.loaded_segments (0x9b318 : word) = Some W_9b2c8.
Proof. vm_refl. Qed.
Lemma D_9b2c8 : decode_any W_9b2c8 = Some (Branch BC_EQ 13 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2cc : bv 32 := 0x00100793.
Lemma F_9b2cc : fetch_word Asan.M.loaded_segments (0x9b31c : word) = Some W_9b2cc.
Proof. vm_refl. Qed.
Lemma D_9b2cc : decode_any W_9b2cc = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2d0 : bv 32 := 0x00c4d813.
Lemma F_9b2d0 : fetch_word Asan.M.loaded_segments (0x9b320 : word) = Some W_9b2d0.
Proof. vm_refl. Qed.
Lemma D_9b2d0 : decode_any W_9b2d0 = Some (ShiftImm ALU_SRL 16 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2d4 : bv 32 := 0x00f52423.
Lemma F_9b2d4 : fetch_word Asan.M.loaded_segments (0x9b324 : word) = Some W_9b2d4.
Proof. vm_refl. Qed.
Lemma D_9b2d4 : decode_any W_9b2d4 = Some (Store SZ4 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2d8 : bv 32 := 0x00b53823.
Lemma F_9b2d8 : fetch_word Asan.M.loaded_segments (0x9b328 : word) = Some W_9b2d8.
Proof. vm_refl. Qed.
Lemma D_9b2d8 : decode_any W_9b2d8 = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b2dc : bv 32 := 0x04081463.
Lemma F_9b2dc : fetch_word Asan.M.loaded_segments (0x9b32c : word) = Some W_9b2dc.
Proof. vm_refl. Qed.
Lemma D_9b2dc : decode_any W_9b2dc = Some (Branch BC_NE 16 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b324 : bv 32 := 0x0a977263.
Lemma F_9b324 : fetch_word Asan.M.loaded_segments (0x9b374 : word) = Some W_9b324.
Proof. vm_refl. Qed.
Lemma D_9b324 : decode_any W_9b324 = Some (Branch BC_GEU 14 9 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b328 : bv 32 := 0x04c77c63.
Lemma F_9b328 : fetch_word Asan.M.loaded_segments (0x9b378 : word) = Some W_9b328.
Proof. vm_refl. Qed.
Lemma D_9b328 : decode_any W_9b328 = Some (Branch BC_GEU 14 12 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b32c : bv 32 := 0xff048493.
Lemma F_9b32c : fetch_word Asan.M.loaded_segments (0x9b37c : word) = Some W_9b32c.
Proof. vm_refl. Qed.
Lemma D_9b32c : decode_any W_9b32c = Some (OpImm ALU_ADD 9 9 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b330 : bv 32 := 0x04967863.
Lemma F_9b330 : fetch_word Asan.M.loaded_segments (0x9b380 : word) = Some W_9b330.
Proof. vm_refl. Qed.
Lemma D_9b330 : decode_any W_9b330 = Some (Branch BC_GEU 12 9 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b334 : bv 32 := 0x00767713.
Lemma F_9b334 : fetch_word Asan.M.loaded_segments (0x9b384 : word) = Some W_9b334.
Proof. vm_refl. Qed.
Lemma D_9b334 : decode_any W_9b334 = Some (OpImm ALU_AND 14 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b338 : bv 32 := 0x04071463.
Lemma F_9b338 : fetch_word Asan.M.loaded_segments (0x9b388 : word) = Some W_9b338.
Proof. vm_refl. Qed.
Lemma D_9b338 : decode_any W_9b338 = Some (Branch BC_NE 14 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b33c : bv 32 := 0x01050713.
Lemma F_9b33c : fetch_word Asan.M.loaded_segments (0x9b38c : word) = Some W_9b33c.
Proof. vm_refl. Qed.
Lemma D_9b33c : decode_any W_9b33c = Some (OpImm ALU_ADD 14 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b340 : bv 32 := 0x00100793.
Lemma F_9b340 : fetch_word Asan.M.loaded_segments (0x9b390 : word) = Some W_9b340.
Proof. vm_refl. Qed.
Lemma D_9b340 : decode_any W_9b340 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b344 : bv 32 := 0x0287fe63.
Lemma F_9b344 : fetch_word Asan.M.loaded_segments (0x9b394 : word) = Some W_9b344.
Proof. vm_refl. Qed.
Lemma D_9b344 : decode_any W_9b344 = Some (Branch BC_GEU 15 8 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b348 : bv 32 := 0xff863803.
Lemma F_9b348 : fetch_word Asan.M.loaded_segments (0x9b398 : word) = Some W_9b348.
Proof. vm_refl. Qed.
Lemma D_9b348 : decode_any W_9b348 = Some (Load SZ8 true 16 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b34c : bv 32 := 0x02d86a63.
Lemma F_9b34c : fetch_word Asan.M.loaded_segments (0x9b39c : word) = Some W_9b34c.
Proof. vm_refl. Qed.
Lemma D_9b34c : decode_any W_9b34c = Some (Branch BC_LTU 16 13 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b350 : bv 32 := 0x00b80c63.
Lemma F_9b350 : fetch_word Asan.M.loaded_segments (0x9b3a0 : word) = Some W_9b350.
Proof. vm_refl. Qed.
Lemma D_9b350 : decode_any W_9b350 = Some (Branch BC_EQ 16 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b354 : bv 32 := 0x00379893.
Lemma F_9b354 : fetch_word Asan.M.loaded_segments (0x9b3a4 : word) = Some W_9b354.
Proof. vm_refl. Qed.
Lemma D_9b354 : decode_any W_9b354 = Some (ShiftImm ALU_SLL 17 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b358 : bv 32 := 0x00178793.
Lemma F_9b358 : fetch_word Asan.M.loaded_segments (0x9b3a8 : word) = Some W_9b358.
Proof. vm_refl. Qed.
Lemma D_9b358 : decode_any W_9b358 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b35c : bv 32 := 0x011708b3.
Lemma F_9b35c : fetch_word Asan.M.loaded_segments (0x9b3ac : word) = Some W_9b35c.
Proof. vm_refl. Qed.
Lemma D_9b35c : decode_any W_9b35c = Some (Op ALU_ADD 17 14 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b360 : bv 32 := 0x00f52423.
Lemma F_9b360 : fetch_word Asan.M.loaded_segments (0x9b3b0 : word) = Some W_9b360.
Proof. vm_refl. Qed.
Lemma D_9b360 : decode_any W_9b360 = Some (Store SZ4 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b364 : bv 32 := 0x0108b023.
Lemma F_9b364 : fetch_word Asan.M.loaded_segments (0x9b3b4 : word) = Some W_9b364.
Proof. vm_refl. Qed.
Lemma D_9b364 : decode_any W_9b364 = Some (Store SZ8 17 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b368 : bv 32 := 0xff063803.
Lemma F_9b368 : fetch_word Asan.M.loaded_segments (0x9b3b8 : word) = Some W_9b368.
Proof. vm_refl. Qed.
Lemma D_9b368 : decode_any W_9b368 = Some (Load SZ8 true 16 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b36c : bv 32 := 0x01067a63.
Lemma F_9b36c : fetch_word Asan.M.loaded_segments (0x9b3bc : word) = Some W_9b36c.
Proof. vm_refl. Qed.
Lemma D_9b36c : decode_any W_9b36c = Some (Branch BC_GEU 12 16 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b370 : bv 32 := 0x00987863.
Lemma F_9b370 : fetch_word Asan.M.loaded_segments (0x9b3c0 : word) = Some W_9b370.
Proof. vm_refl. Qed.
Lemma D_9b370 : decode_any W_9b370 = Some (Branch BC_GEU 16 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b374 : bv 32 := 0x00787893.
Lemma F_9b374 : fetch_word Asan.M.loaded_segments (0x9b3c4 : word) = Some W_9b374.
Proof. vm_refl. Qed.
Lemma D_9b374 : decode_any W_9b374 = Some (OpImm ALU_AND 17 16 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b378 : bv 32 := 0x00080613.
Lemma F_9b378 : fetch_word Asan.M.loaded_segments (0x9b3c8 : word) = Some W_9b378.
Proof. vm_refl. Qed.
Lemma D_9b378 : decode_any W_9b378 = Some (OpImm ALU_ADD 12 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b37c : bv 32 := 0xfc0884e3.
Lemma F_9b37c : fetch_word Asan.M.loaded_segments (0x9b3cc : word) = Some W_9b37c.
Proof. vm_refl. Qed.
Lemma D_9b37c : decode_any W_9b37c = Some (Branch BC_EQ 17 0 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b380 : bv 32 := 0x03813083.
Lemma F_9b380 : fetch_word Asan.M.loaded_segments (0x9b3d0 : word) = Some W_9b380.
Proof. vm_refl. Qed.
Lemma D_9b380 : decode_any W_9b380 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b384 : bv 32 := 0x03013403.
Lemma F_9b384 : fetch_word Asan.M.loaded_segments (0x9b3d4 : word) = Some W_9b384.
Proof. vm_refl. Qed.
Lemma D_9b384 : decode_any W_9b384 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b388 : bv 32 := 0x02813483.
Lemma F_9b388 : fetch_word Asan.M.loaded_segments (0x9b3d8 : word) = Some W_9b388.
Proof. vm_refl. Qed.
Lemma D_9b388 : decode_any W_9b388 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b38c : bv 32 := 0x02013903.
Lemma F_9b38c : fetch_word Asan.M.loaded_segments (0x9b3dc : word) = Some W_9b38c.
Proof. vm_refl. Qed.
Lemma D_9b38c : decode_any W_9b38c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b390 : bv 32 := 0x01813983.
Lemma F_9b390 : fetch_word Asan.M.loaded_segments (0x9b3e0 : word) = Some W_9b390.
Proof. vm_refl. Qed.
Lemma D_9b390 : decode_any W_9b390 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b394 : bv 32 := 0x01013a03.
Lemma F_9b394 : fetch_word Asan.M.loaded_segments (0x9b3e4 : word) = Some W_9b394.
Proof. vm_refl. Qed.
Lemma D_9b394 : decode_any W_9b394 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b398 : bv 32 := 0x00813a83.
Lemma F_9b398 : fetch_word Asan.M.loaded_segments (0x9b3e8 : word) = Some W_9b398.
Proof. vm_refl. Qed.
Lemma D_9b398 : decode_any W_9b398 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b39c : bv 32 := 0x00013b03.
Lemma F_9b39c : fetch_word Asan.M.loaded_segments (0x9b3ec : word) = Some W_9b39c.
Proof. vm_refl. Qed.
Lemma D_9b39c : decode_any W_9b39c = Some (Load SZ8 true 22 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b3a0 : bv 32 := 0x04010113.
Lemma F_9b3a0 : fetch_word Asan.M.loaded_segments (0x9b3f0 : word) = Some W_9b3a0.
Proof. vm_refl. Qed.
Lemma D_9b3a0 : decode_any W_9b3a0 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_9b3a4 : bv 32 := 0x00008067.
Lemma F_9b3a4 : fetch_word Asan.M.loaded_segments (0x9b3f4 : word) = Some W_9b3a4.
Proof. vm_refl. Qed.
Lemma D_9b3a4 : decode_any W_9b3a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
