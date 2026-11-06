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

Definition W_8c2e0 : bv 32 := 0xff010113.
Lemma F_8c2e0 : fetch_word Asan.M.loaded_segments (0x8c330 : word) = Some W_8c2e0.
Proof. vm_refl. Qed.
Lemma D_8c2e0 : decode_any W_8c2e0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c2e4 : bv 32 := 0x00113423.
Lemma F_8c2e4 : fetch_word Asan.M.loaded_segments (0x8c334 : word) = Some W_8c2e4.
Proof. vm_refl. Qed.
Lemma D_8c2e4 : decode_any W_8c2e4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c2e8 : bv 32 := 0x00058693.
Lemma F_8c2e8 : fetch_word Asan.M.loaded_segments (0x8c338 : word) = Some W_8c2e8.
Proof. vm_refl. Qed.
Lemma D_8c2e8 : decode_any W_8c2e8 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c2ec : bv 32 := 0x00100713.
Lemma F_8c2ec : fetch_word Asan.M.loaded_segments (0x8c33c : word) = Some W_8c2ec.
Proof. vm_refl. Qed.
Lemma D_8c2ec : decode_any W_8c2ec = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c2f0 : bv 32 := 0x02871713.
Lemma F_8c2f0 : fetch_word Asan.M.loaded_segments (0x8c340 : word) = Some W_8c2f0.
Proof. vm_refl. Qed.
Lemma D_8c2f0 : decode_any W_8c2f0 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c2f4 : bv 32 := 0x00170593.
Lemma F_8c2f4 : fetch_word Asan.M.loaded_segments (0x8c344 : word) = Some W_8c2f4.
Proof. vm_refl. Qed.
Lemma D_8c2f4 : decode_any W_8c2f4 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c2f8 : bv 32 := 0x08b6f263.
Lemma F_8c2f8 : fetch_word Asan.M.loaded_segments (0x8c348 : word) = Some W_8c2f8.
Proof. vm_refl. Qed.
Lemma D_8c2f8 : decode_any W_8c2f8 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c2fc : bv 32 := 0x00000593.
Lemma F_8c2fc : fetch_word Asan.M.loaded_segments (0x8c34c : word) = Some W_8c2fc.
Proof. vm_refl. Qed.
Lemma D_8c2fc : decode_any W_8c2fc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c300 : bv 32 := 0x00d50733.
Lemma F_8c300 : fetch_word Asan.M.loaded_segments (0x8c350 : word) = Some W_8c300.
Proof. vm_refl. Qed.
Lemma D_8c300 : decode_any W_8c300 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c304 : bv 32 := 0x00750793.
Lemma F_8c304 : fetch_word Asan.M.loaded_segments (0x8c354 : word) = Some W_8c304.
Proof. vm_refl. Qed.
Lemma D_8c304 : decode_any W_8c304 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c308 : bv 32 := 0xff87f793.
Lemma F_8c308 : fetch_word Asan.M.loaded_segments (0x8c358 : word) = Some W_8c308.
Proof. vm_refl. Qed.
Lemma D_8c308 : decode_any W_8c308 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c30c : bv 32 := 0xff877613.
Lemma F_8c30c : fetch_word Asan.M.loaded_segments (0x8c35c : word) = Some W_8c30c.
Proof. vm_refl. Qed.
Lemma D_8c30c : decode_any W_8c30c = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c310 : bv 32 := 0x02f57463.
Lemma F_8c310 : fetch_word Asan.M.loaded_segments (0x8c360 : word) = Some W_8c310.
Proof. vm_refl. Qed.
Lemma D_8c310 : decode_any W_8c310 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c314 : bv 32 := 0x02068263.
Lemma F_8c314 : fetch_word Asan.M.loaded_segments (0x8c364 : word) = Some W_8c314.
Proof. vm_refl. Qed.
Lemma D_8c314 : decode_any W_8c314 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c318 : bv 32 := 0x00000593.
Lemma F_8c318 : fetch_word Asan.M.loaded_segments (0x8c368 : word) = Some W_8c318.
Proof. vm_refl. Qed.
Lemma D_8c318 : decode_any W_8c318 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c31c : bv 32 := 0x00150693.
Lemma F_8c31c : fetch_word Asan.M.loaded_segments (0x8c36c : word) = Some W_8c31c.
Proof. vm_refl. Qed.
Lemma D_8c31c : decode_any W_8c31c = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c320 : bv 32 := 0x00068813.
Lemma F_8c320 : fetch_word Asan.M.loaded_segments (0x8c370 : word) = Some W_8c320.
Proof. vm_refl. Qed.
Lemma D_8c320 : decode_any W_8c320 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c324 : bv 32 := 0xfff6c683.
Lemma F_8c324 : fetch_word Asan.M.loaded_segments (0x8c374 : word) = Some W_8c324.
Proof. vm_refl. Qed.
Lemma D_8c324 : decode_any W_8c324 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c328 : bv 32 := 0x00d5e5b3.
Lemma F_8c328 : fetch_word Asan.M.loaded_segments (0x8c378 : word) = Some W_8c328.
Proof. vm_refl. Qed.
Lemma D_8c328 : decode_any W_8c328 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c32c : bv 32 := 0x00f87663.
Lemma F_8c32c : fetch_word Asan.M.loaded_segments (0x8c37c : word) = Some W_8c32c.
Proof. vm_refl. Qed.
Lemma D_8c32c : decode_any W_8c32c = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c330 : bv 32 := 0x00180693.
Lemma F_8c330 : fetch_word Asan.M.loaded_segments (0x8c380 : word) = Some W_8c330.
Proof. vm_refl. Qed.
Lemma D_8c330 : decode_any W_8c330 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c334 : bv 32 := 0xfee866e3.
Lemma F_8c334 : fetch_word Asan.M.loaded_segments (0x8c384 : word) = Some W_8c334.
Proof. vm_refl. Qed.
Lemma D_8c334 : decode_any W_8c334 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c338 : bv 32 := 0x00c7fa63.
Lemma F_8c338 : fetch_word Asan.M.loaded_segments (0x8c388 : word) = Some W_8c338.
Proof. vm_refl. Qed.
Lemma D_8c338 : decode_any W_8c338 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c33c : bv 32 := 0x0007b683.
Lemma F_8c33c : fetch_word Asan.M.loaded_segments (0x8c38c : word) = Some W_8c33c.
Proof. vm_refl. Qed.
Lemma D_8c33c : decode_any W_8c33c = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c340 : bv 32 := 0x00878793.
Lemma F_8c340 : fetch_word Asan.M.loaded_segments (0x8c390 : word) = Some W_8c340.
Proof. vm_refl. Qed.
Lemma D_8c340 : decode_any W_8c340 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c344 : bv 32 := 0x00b6e5b3.
Lemma F_8c344 : fetch_word Asan.M.loaded_segments (0x8c394 : word) = Some W_8c344.
Proof. vm_refl. Qed.
Lemma D_8c344 : decode_any W_8c344 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c348 : bv 32 := 0xfec7eae3.
Lemma F_8c348 : fetch_word Asan.M.loaded_segments (0x8c398 : word) = Some W_8c348.
Proof. vm_refl. Qed.
Lemma D_8c348 : decode_any W_8c348 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c34c : bv 32 := 0x02a66063.
Lemma F_8c34c : fetch_word Asan.M.loaded_segments (0x8c39c : word) = Some W_8c34c.
Proof. vm_refl. Qed.
Lemma D_8c34c : decode_any W_8c34c = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c350 : bv 32 := 0x00e67e63.
Lemma F_8c350 : fetch_word Asan.M.loaded_segments (0x8c3a0 : word) = Some W_8c350.
Proof. vm_refl. Qed.
Lemma D_8c350 : decode_any W_8c350 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c354 : bv 32 := 0x40c70733.
Lemma F_8c354 : fetch_word Asan.M.loaded_segments (0x8c3a4 : word) = Some W_8c354.
Proof. vm_refl. Qed.
Lemma D_8c354 : decode_any W_8c354 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c358 : bv 32 := 0x00064503.
Lemma F_8c358 : fetch_word Asan.M.loaded_segments (0x8c3a8 : word) = Some W_8c358.
Proof. vm_refl. Qed.
Lemma D_8c358 : decode_any W_8c358 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c35c : bv 32 := 0xfff70713.
Lemma F_8c35c : fetch_word Asan.M.loaded_segments (0x8c3ac : word) = Some W_8c35c.
Proof. vm_refl. Qed.
Lemma D_8c35c : decode_any W_8c35c = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c360 : bv 32 := 0x00a5e5b3.
Lemma F_8c360 : fetch_word Asan.M.loaded_segments (0x8c3b0 : word) = Some W_8c360.
Proof. vm_refl. Qed.
Lemma D_8c360 : decode_any W_8c360 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c364 : bv 32 := 0x00160613.
Lemma F_8c364 : fetch_word Asan.M.loaded_segments (0x8c3b4 : word) = Some W_8c364.
Proof. vm_refl. Qed.
Lemma D_8c364 : decode_any W_8c364 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c368 : bv 32 := 0xfe0718e3.
Lemma F_8c368 : fetch_word Asan.M.loaded_segments (0x8c3b8 : word) = Some W_8c368.
Proof. vm_refl. Qed.
Lemma D_8c368 : decode_any W_8c368 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c36c : bv 32 := 0x0015b513.
Lemma F_8c36c : fetch_word Asan.M.loaded_segments (0x8c3bc : word) = Some W_8c36c.
Proof. vm_refl. Qed.
Lemma D_8c36c : decode_any W_8c36c = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c370 : bv 32 := 0x00813083.
Lemma F_8c370 : fetch_word Asan.M.loaded_segments (0x8c3c0 : word) = Some W_8c370.
Proof. vm_refl. Qed.
Lemma D_8c370 : decode_any W_8c370 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c374 : bv 32 := 0x01010113.
Lemma F_8c374 : fetch_word Asan.M.loaded_segments (0x8c3c4 : word) = Some W_8c374.
Proof. vm_refl. Qed.
Lemma D_8c374 : decode_any W_8c374 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c378 : bv 32 := 0x00008067.
Lemma F_8c378 : fetch_word Asan.M.loaded_segments (0x8c3c8 : word) = Some W_8c378.
Proof. vm_refl. Qed.
Lemma D_8c378 : decode_any W_8c378 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
