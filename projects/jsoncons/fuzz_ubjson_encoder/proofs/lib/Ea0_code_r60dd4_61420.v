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

Definition W_7b458 : bv 32 := 0x000c6517.
Lemma F_7b458 : fetch_word Asan.M.loaded_segments (0x7b4a8 : word) = Some W_7b458.
Proof. vm_refl. Qed.
Lemma D_7b458 : decode_any W_7b458 = Some (Auipc 10 198, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b45c : bv 32 := 0xdb450503.
Lemma F_7b45c : fetch_word Asan.M.loaded_segments (0x7b4ac : word) = Some W_7b45c.
Proof. vm_refl. Qed.
Lemma D_7b45c : decode_any W_7b45c = Some (Load SZ1 true 10 10 3508, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b460 : bv 32 := 0x0230000f.
Lemma F_7b460 : fetch_word Asan.M.loaded_segments (0x7b4b0 : word) = Some W_7b460.
Proof. vm_refl. Qed.
Lemma D_7b460 : decode_any W_7b460 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b464 : bv 32 := 0x00a03533.
Lemma F_7b464 : fetch_word Asan.M.loaded_segments (0x7b4b4 : word) = Some W_7b464.
Proof. vm_refl. Qed.
Lemma D_7b464 : decode_any W_7b464 = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b468 : bv 32 := 0x00008067.
Lemma F_7b468 : fetch_word Asan.M.loaded_segments (0x7b4b8 : word) = Some W_7b468.
Proof. vm_refl. Qed.
Lemma D_7b468 : decode_any W_7b468 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b46c : bv 32 := 0xfc010113.
Lemma F_7b46c : fetch_word Asan.M.loaded_segments (0x7b4bc : word) = Some W_7b46c.
Proof. vm_refl. Qed.
Lemma D_7b46c : decode_any W_7b46c = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b470 : bv 32 := 0x02113c23.
Lemma F_7b470 : fetch_word Asan.M.loaded_segments (0x7b4c0 : word) = Some W_7b470.
Proof. vm_refl. Qed.
Lemma D_7b470 : decode_any W_7b470 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b474 : bv 32 := 0x02813823.
Lemma F_7b474 : fetch_word Asan.M.loaded_segments (0x7b4c4 : word) = Some W_7b474.
Proof. vm_refl. Qed.
Lemma D_7b474 : decode_any W_7b474 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b478 : bv 32 := 0x02913423.
Lemma F_7b478 : fetch_word Asan.M.loaded_segments (0x7b4c8 : word) = Some W_7b478.
Proof. vm_refl. Qed.
Lemma D_7b478 : decode_any W_7b478 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b47c : bv 32 := 0x03213023.
Lemma F_7b47c : fetch_word Asan.M.loaded_segments (0x7b4cc : word) = Some W_7b47c.
Proof. vm_refl. Qed.
Lemma D_7b47c : decode_any W_7b47c = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b480 : bv 32 := 0x01313c23.
Lemma F_7b480 : fetch_word Asan.M.loaded_segments (0x7b4d0 : word) = Some W_7b480.
Proof. vm_refl. Qed.
Lemma D_7b480 : decode_any W_7b480 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b484 : bv 32 := 0x01413823.
Lemma F_7b484 : fetch_word Asan.M.loaded_segments (0x7b4d4 : word) = Some W_7b484.
Proof. vm_refl. Qed.
Lemma D_7b484 : decode_any W_7b484 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b488 : bv 32 := 0x01513423.
Lemma F_7b488 : fetch_word Asan.M.loaded_segments (0x7b4d8 : word) = Some W_7b488.
Proof. vm_refl. Qed.
Lemma D_7b488 : decode_any W_7b488 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b48c : bv 32 := 0x00060a63.
Lemma F_7b48c : fetch_word Asan.M.loaded_segments (0x7b4dc : word) = Some W_7b48c.
Proof. vm_refl. Qed.
Lemma D_7b48c : decode_any W_7b48c = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b490 : bv 32 := 0x000c6697.
Lemma F_7b490 : fetch_word Asan.M.loaded_segments (0x7b4e0 : word) = Some W_7b490.
Proof. vm_refl. Qed.
Lemma D_7b490 : decode_any W_7b490 = Some (Auipc 13 198, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b494 : bv 32 := 0xd7c68683.
Lemma F_7b494 : fetch_word Asan.M.loaded_segments (0x7b4e4 : word) = Some W_7b494.
Proof. vm_refl. Qed.
Lemma D_7b494 : decode_any W_7b494 = Some (Load SZ1 true 13 13 3452, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b498 : bv 32 := 0x0230000f.
Lemma F_7b498 : fetch_word Asan.M.loaded_segments (0x7b4e8 : word) = Some W_7b498.
Proof. vm_refl. Qed.
Lemma D_7b498 : decode_any W_7b498 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b49c : bv 32 := 0x0a068a63.
Lemma F_7b49c : fetch_word Asan.M.loaded_segments (0x7b4ec : word) = Some W_7b49c.
Proof. vm_refl. Qed.
Lemma D_7b49c : decode_any W_7b49c = Some (Branch BC_EQ 13 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4a0 : bv 32 := 0x00757693.
Lemma F_7b4a0 : fetch_word Asan.M.loaded_segments (0x7b4f0 : word) = Some W_7b4a0.
Proof. vm_refl. Qed.
Lemma D_7b4a0 : decode_any W_7b4a0 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4a4 : bv 32 := 0x42069863.
Lemma F_7b4a4 : fetch_word Asan.M.loaded_segments (0x7b4f4 : word) = Some W_7b4a4.
Proof. vm_refl. Qed.
Lemma D_7b4a4 : decode_any W_7b4a4 = Some (Branch BC_NE 13 0 1072, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4a8 : bv 32 := 0x000be697.
Lemma F_7b4a8 : fetch_word Asan.M.loaded_segments (0x7b4f8 : word) = Some W_7b4a8.
Proof. vm_refl. Qed.
Lemma D_7b4a8 : decode_any W_7b4a8 = Some (Auipc 13 190, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4ac : bv 32 := 0xcc06b683.
Lemma F_7b4ac : fetch_word Asan.M.loaded_segments (0x7b4fc : word) = Some W_7b4ac.
Proof. vm_refl. Qed.
Lemma D_7b4ac : decode_any W_7b4ac = Some (Load SZ8 true 13 13 3264, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4b0 : bv 32 := 0x0006b483.
Lemma F_7b4b0 : fetch_word Asan.M.loaded_segments (0x7b500 : word) = Some W_7b4b0.
Proof. vm_refl. Qed.
Lemma D_7b4b0 : decode_any W_7b4b0 = Some (Load SZ8 true 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4b4 : bv 32 := 0xfff48693.
Lemma F_7b4b4 : fetch_word Asan.M.loaded_segments (0x7b504 : word) = Some W_7b4b4.
Proof. vm_refl. Qed.
Lemma D_7b4b4 : decode_any W_7b4b4 = Some (OpImm ALU_ADD 13 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4b8 : bv 32 := 0x00d4b733.
Lemma F_7b4b8 : fetch_word Asan.M.loaded_segments (0x7b508 : word) = Some W_7b4b8.
Proof. vm_refl. Qed.
Lemma D_7b4b8 : decode_any W_7b4b8 = Some (Op ALU_SLTU 14 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4bc : bv 32 := 0xfff70713.
Lemma F_7b4bc : fetch_word Asan.M.loaded_segments (0x7b50c : word) = Some W_7b4bc.
Proof. vm_refl. Qed.
Lemma D_7b4bc : decode_any W_7b4bc = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4c0 : bv 32 := 0x00d77733.
Lemma F_7b4c0 : fetch_word Asan.M.loaded_segments (0x7b510 : word) = Some W_7b4c0.
Proof. vm_refl. Qed.
Lemma D_7b4c0 : decode_any W_7b4c0 = Some (Op ALU_AND 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4c4 : bv 32 := 0x1ca77c63.
Lemma F_7b4c4 : fetch_word Asan.M.loaded_segments (0x7b514 : word) = Some W_7b4c4.
Proof. vm_refl. Qed.
Lemma D_7b4c4 : decode_any W_7b4c4 = Some (Branch BC_GEU 14 10 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4c8 : bv 32 := 0x000be797.
Lemma F_7b4c8 : fetch_word Asan.M.loaded_segments (0x7b518 : word) = Some W_7b4c8.
Proof. vm_refl. Qed.
Lemma D_7b4c8 : decode_any W_7b4c8 = Some (Auipc 15 190, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4cc : bv 32 := 0xca87b783.
Lemma F_7b4cc : fetch_word Asan.M.loaded_segments (0x7b51c : word) = Some W_7b4cc.
Proof. vm_refl. Qed.
Lemma D_7b4cc : decode_any W_7b4cc = Some (Load SZ8 true 15 15 3240, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4d0 : bv 32 := 0x000be817.
Lemma F_7b4d0 : fetch_word Asan.M.loaded_segments (0x7b520 : word) = Some W_7b4d0.
Proof. vm_refl. Qed.
Lemma D_7b4d0 : decode_any W_7b4d0 = Some (Auipc 16 190, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4d4 : bv 32 := 0xca883803.
Lemma F_7b4d4 : fetch_word Asan.M.loaded_segments (0x7b524 : word) = Some W_7b4d4.
Proof. vm_refl. Qed.
Lemma D_7b4d4 : decode_any W_7b4d4 = Some (Load SZ8 true 16 16 3240, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4d8 : bv 32 := 0x0007b883.
Lemma F_7b4d8 : fetch_word Asan.M.loaded_segments (0x7b528 : word) = Some W_7b4d8.
Proof. vm_refl. Qed.
Lemma D_7b4d8 : decode_any W_7b4d8 = Some (Load SZ8 true 17 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4dc : bv 32 := 0x00083783.
Lemma F_7b4dc : fetch_word Asan.M.loaded_segments (0x7b52c : word) = Some W_7b4dc.
Proof. vm_refl. Qed.
Lemma D_7b4dc : decode_any W_7b4dc = Some (Load SZ8 true 15 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4e0 : bv 32 := 0xfff88813.
Lemma F_7b4e0 : fetch_word Asan.M.loaded_segments (0x7b530 : word) = Some W_7b4e0.
Proof. vm_refl. Qed.
Lemma D_7b4e0 : decode_any W_7b4e0 = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4e4 : bv 32 := 0x00a87463.
Lemma F_7b4e4 : fetch_word Asan.M.loaded_segments (0x7b534 : word) = Some W_7b4e4.
Proof. vm_refl. Qed.
Lemma D_7b4e4 : decode_any W_7b4e4 = Some (Branch BC_GEU 16 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4e8 : bv 32 := 0x1aa7fa63.
Lemma F_7b4e8 : fetch_word Asan.M.loaded_segments (0x7b538 : word) = Some W_7b4e8.
Proof. vm_refl. Qed.
Lemma D_7b4e8 : decode_any W_7b4e8 = Some (Branch BC_GEU 15 10 436, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4ec : bv 32 := 0x000be297.
Lemma F_7b4ec : fetch_word Asan.M.loaded_segments (0x7b53c : word) = Some W_7b4ec.
Proof. vm_refl. Qed.
Lemma D_7b4ec : decode_any W_7b4ec = Some (Auipc 5 190, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4f0 : bv 32 := 0xc942b283.
Lemma F_7b4f0 : fetch_word Asan.M.loaded_segments (0x7b540 : word) = Some W_7b4f0.
Proof. vm_refl. Qed.
Lemma D_7b4f0 : decode_any W_7b4f0 = Some (Load SZ8 true 5 5 3220, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4f4 : bv 32 := 0x0002be03.
Lemma F_7b4f4 : fetch_word Asan.M.loaded_segments (0x7b544 : word) = Some W_7b4f4.
Proof. vm_refl. Qed.
Lemma D_7b4f4 : decode_any W_7b4f4 = Some (Load SZ8 true 28 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4f8 : bv 32 := 0x003e5313.
Lemma F_7b4f8 : fetch_word Asan.M.loaded_segments (0x7b548 : word) = Some W_7b4f8.
Proof. vm_refl. Qed.
Lemma D_7b4f8 : decode_any W_7b4f8 = Some (ShiftImm ALU_SRL 6 28 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b4fc : bv 32 := 0x009303b3.
Lemma F_7b4fc : fetch_word Asan.M.loaded_segments (0x7b54c : word) = Some W_7b4fc.
Proof. vm_refl. Qed.
Lemma D_7b4fc : decode_any W_7b4fc = Some (Op ALU_ADD 7 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b500 : bv 32 := 0x00ae6463.
Lemma F_7b500 : fetch_word Asan.M.loaded_segments (0x7b550 : word) = Some W_7b500.
Proof. vm_refl. Qed.
Lemma D_7b500 : decode_any W_7b500 = Some (Branch BC_LTU 28 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b504 : bv 32 := 0x0ca3e463.
Lemma F_7b504 : fetch_word Asan.M.loaded_segments (0x7b554 : word) = Some W_7b504.
Proof. vm_refl. Qed.
Lemma D_7b504 : decode_any W_7b504 = Some (Branch BC_LTU 7 10 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b508 : bv 32 := 0x000bee17.
Lemma F_7b508 : fetch_word Asan.M.loaded_segments (0x7b558 : word) = Some W_7b508.
Proof. vm_refl. Qed.
Lemma D_7b508 : decode_any W_7b508 = Some (Auipc 28 190, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b50c : bv 32 := 0xc58e3e03.
Lemma F_7b50c : fetch_word Asan.M.loaded_segments (0x7b55c : word) = Some W_7b50c.
Proof. vm_refl. Qed.
Lemma D_7b50c : decode_any W_7b50c = Some (Load SZ8 true 28 28 3160, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b510 : bv 32 := 0x04ee4e03.
Lemma F_7b510 : fetch_word Asan.M.loaded_segments (0x7b560 : word) = Some W_7b510.
Proof. vm_refl. Qed.
Lemma D_7b510 : decode_any W_7b510 = Some (Load SZ1 false 28 28 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b514 : bv 32 := 0x3e0e1063.
Lemma F_7b514 : fetch_word Asan.M.loaded_segments (0x7b564 : word) = Some W_7b514.
Proof. vm_refl. Qed.
Lemma D_7b514 : decode_any W_7b514 = Some (Branch BC_NE 28 0 992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b518 : bv 32 := 0x04088e63.
Lemma F_7b518 : fetch_word Asan.M.loaded_segments (0x7b568 : word) = Some W_7b518.
Proof. vm_refl. Qed.
Lemma D_7b518 : decode_any W_7b518 = Some (Branch BC_EQ 17 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b51c : bv 32 := 0x0038d393.
Lemma F_7b51c : fetch_word Asan.M.loaded_segments (0x7b56c : word) = Some W_7b51c.
Proof. vm_refl. Qed.
Lemma D_7b51c : decode_any W_7b51c = Some (ShiftImm ALU_SRL 7 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b520 : bv 32 := 0x00d383b3.
Lemma F_7b520 : fetch_word Asan.M.loaded_segments (0x7b570 : word) = Some W_7b520.
Proof. vm_refl. Qed.
Lemma D_7b520 : decode_any W_7b520 = Some (Op ALU_ADD 7 7 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b524 : bv 32 := 0x06a3fe63.
Lemma F_7b524 : fetch_word Asan.M.loaded_segments (0x7b574 : word) = Some W_7b524.
Proof. vm_refl. Qed.
Lemma D_7b524 : decode_any W_7b524 = Some (Branch BC_GEU 7 10 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b528 : bv 32 := 0x00148393.
Lemma F_7b528 : fetch_word Asan.M.loaded_segments (0x7b578 : word) = Some W_7b528.
Proof. vm_refl. Qed.
Lemma D_7b528 : decode_any W_7b528 = Some (OpImm ALU_ADD 7 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b52c : bv 32 := 0x00a86863.
Lemma F_7b52c : fetch_word Asan.M.loaded_segments (0x7b57c : word) = Some W_7b52c.
Proof. vm_refl. Qed.
Lemma D_7b52c : decode_any W_7b52c = Some (Branch BC_LTU 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b530 : bv 32 := 0x0037de13.
Lemma F_7b530 : fetch_word Asan.M.loaded_segments (0x7b580 : word) = Some W_7b530.
Proof. vm_refl. Qed.
Lemma D_7b530 : decode_any W_7b530 = Some (ShiftImm ALU_SRL 28 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b534 : bv 32 := 0x007e0e33.
Lemma F_7b534 : fetch_word Asan.M.loaded_segments (0x7b584 : word) = Some W_7b534.
Proof. vm_refl. Qed.
Lemma D_7b534 : decode_any W_7b534 = Some (Op ALU_ADD 28 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b538 : bv 32 := 0x09c57a63.
Lemma F_7b538 : fetch_word Asan.M.loaded_segments (0x7b588 : word) = Some W_7b538.
Proof. vm_refl. Qed.
Lemma D_7b538 : decode_any W_7b538 = Some (Branch BC_GEU 10 28 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b53c : bv 32 := 0x00178e13.
Lemma F_7b53c : fetch_word Asan.M.loaded_segments (0x7b58c : word) = Some W_7b53c.
Proof. vm_refl. Qed.
Lemma D_7b53c : decode_any W_7b53c = Some (OpImm ALU_ADD 28 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b540 : bv 32 := 0x3bc56a63.
Lemma F_7b540 : fetch_word Asan.M.loaded_segments (0x7b590 : word) = Some W_7b540.
Proof. vm_refl. Qed.
Lemma D_7b540 : decode_any W_7b540 = Some (Branch BC_LTU 10 28 948, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b544 : bv 32 := 0x00730333.
Lemma F_7b544 : fetch_word Asan.M.loaded_segments (0x7b594 : word) = Some W_7b544.
Proof. vm_refl. Qed.
Lemma D_7b544 : decode_any W_7b544 = Some (Op ALU_ADD 6 6 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b548 : bv 32 := 0x00335313.
Lemma F_7b548 : fetch_word Asan.M.loaded_segments (0x7b598 : word) = Some W_7b548.
Proof. vm_refl. Qed.
Lemma D_7b548 : decode_any W_7b548 = Some (ShiftImm ALU_SRL 6 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b54c : bv 32 := 0x0480006f.
Lemma F_7b54c : fetch_word Asan.M.loaded_segments (0x7b59c : word) = Some W_7b54c.
Proof. vm_refl. Qed.
Lemma D_7b54c : decode_any W_7b54c = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b550 : bv 32 := 0x03813083.
Lemma F_7b550 : fetch_word Asan.M.loaded_segments (0x7b5a0 : word) = Some W_7b550.
Proof. vm_refl. Qed.
Lemma D_7b550 : decode_any W_7b550 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b554 : bv 32 := 0x03013403.
Lemma F_7b554 : fetch_word Asan.M.loaded_segments (0x7b5a4 : word) = Some W_7b554.
Proof. vm_refl. Qed.
Lemma D_7b554 : decode_any W_7b554 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b558 : bv 32 := 0x02813483.
Lemma F_7b558 : fetch_word Asan.M.loaded_segments (0x7b5a8 : word) = Some W_7b558.
Proof. vm_refl. Qed.
Lemma D_7b558 : decode_any W_7b558 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b55c : bv 32 := 0x02013903.
Lemma F_7b55c : fetch_word Asan.M.loaded_segments (0x7b5ac : word) = Some W_7b55c.
Proof. vm_refl. Qed.
Lemma D_7b55c : decode_any W_7b55c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b560 : bv 32 := 0x01813983.
Lemma F_7b560 : fetch_word Asan.M.loaded_segments (0x7b5b0 : word) = Some W_7b560.
Proof. vm_refl. Qed.
Lemma D_7b560 : decode_any W_7b560 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b564 : bv 32 := 0x01013a03.
Lemma F_7b564 : fetch_word Asan.M.loaded_segments (0x7b5b4 : word) = Some W_7b564.
Proof. vm_refl. Qed.
Lemma D_7b564 : decode_any W_7b564 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b568 : bv 32 := 0x00813a83.
Lemma F_7b568 : fetch_word Asan.M.loaded_segments (0x7b5b8 : word) = Some W_7b568.
Proof. vm_refl. Qed.
Lemma D_7b568 : decode_any W_7b568 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b56c : bv 32 := 0x04010113.
Lemma F_7b56c : fetch_word Asan.M.loaded_segments (0x7b5bc : word) = Some W_7b56c.
Proof. vm_refl. Qed.
Lemma D_7b56c : decode_any W_7b56c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b570 : bv 32 := 0x00008067.
Lemma F_7b570 : fetch_word Asan.M.loaded_segments (0x7b5c0 : word) = Some W_7b570.
Proof. vm_refl. Qed.
Lemma D_7b570 : decode_any W_7b570 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b574 : bv 32 := 0x04048463.
Lemma F_7b574 : fetch_word Asan.M.loaded_segments (0x7b5c4 : word) = Some W_7b574.
Proof. vm_refl. Qed.
Lemma D_7b574 : decode_any W_7b574 = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b578 : bv 32 := 0x0036d313.
Lemma F_7b578 : fetch_word Asan.M.loaded_segments (0x7b5c8 : word) = Some W_7b578.
Proof. vm_refl. Qed.
Lemma D_7b578 : decode_any W_7b578 = Some (ShiftImm ALU_SRL 6 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b57c : bv 32 := 0x00930333.
Lemma F_7b57c : fetch_word Asan.M.loaded_segments (0x7b5cc : word) = Some W_7b57c.
Proof. vm_refl. Qed.
Lemma D_7b57c : decode_any W_7b57c = Some (Op ALU_ADD 6 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b580 : bv 32 := 0x00030663.
Lemma F_7b580 : fetch_word Asan.M.loaded_segments (0x7b5d0 : word) = Some W_7b580.
Proof. vm_refl. Qed.
Lemma D_7b580 : decode_any W_7b580 = Some (Branch BC_EQ 6 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b584 : bv 32 := 0x00130313.
Lemma F_7b584 : fetch_word Asan.M.loaded_segments (0x7b5d4 : word) = Some W_7b584.
Proof. vm_refl. Qed.
Lemma D_7b584 : decode_any W_7b584 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b588 : bv 32 := 0x36656663.
Lemma F_7b588 : fetch_word Asan.M.loaded_segments (0x7b5d8 : word) = Some W_7b588.
Proof. vm_refl. Qed.
Lemma D_7b588 : decode_any W_7b588 = Some (Branch BC_LTU 10 6 876, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b58c : bv 32 := 0x00138393.
Lemma F_7b58c : fetch_word Asan.M.loaded_segments (0x7b5dc : word) = Some W_7b58c.
Proof. vm_refl. Qed.
Lemma D_7b58c : decode_any W_7b58c = Some (OpImm ALU_ADD 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b590 : bv 32 := 0x0033d313.
Lemma F_7b590 : fetch_word Asan.M.loaded_segments (0x7b5e0 : word) = Some W_7b590.
Proof. vm_refl. Qed.
Lemma D_7b590 : decode_any W_7b590 = Some (ShiftImm ALU_SRL 6 7 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b594 : bv 32 := 0x00d30333.
Lemma F_7b594 : fetch_word Asan.M.loaded_segments (0x7b5e4 : word) = Some W_7b594.
Proof. vm_refl. Qed.
Lemma D_7b594 : decode_any W_7b594 = Some (Op ALU_ADD 6 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b598 : bv 32 := 0x02a37a63.
Lemma F_7b598 : fetch_word Asan.M.loaded_segments (0x7b5e8 : word) = Some W_7b598.
Proof. vm_refl. Qed.
Lemma D_7b598 : decode_any W_7b598 = Some (Branch BC_GEU 6 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b59c : bv 32 := 0x3580006f.
Lemma F_7b59c : fetch_word Asan.M.loaded_segments (0x7b5ec : word) = Some W_7b59c.
Proof. vm_refl. Qed.
Lemma D_7b59c : decode_any W_7b59c = Some (Jal 0 856, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5a0 : bv 32 := 0x02048663.
Lemma F_7b5a0 : fetch_word Asan.M.loaded_segments (0x7b5f0 : word) = Some W_7b5a0.
Proof. vm_refl. Qed.
Lemma D_7b5a0 : decode_any W_7b5a0 = Some (Branch BC_EQ 9 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5a4 : bv 32 := 0x0036d313.
Lemma F_7b5a4 : fetch_word Asan.M.loaded_segments (0x7b5f4 : word) = Some W_7b5a4.
Proof. vm_refl. Qed.
Lemma D_7b5a4 : decode_any W_7b5a4 = Some (ShiftImm ALU_SRL 6 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5a8 : bv 32 := 0x00930333.
Lemma F_7b5a8 : fetch_word Asan.M.loaded_segments (0x7b5f8 : word) = Some W_7b5a8.
Proof. vm_refl. Qed.
Lemma D_7b5a8 : decode_any W_7b5a8 = Some (Op ALU_ADD 6 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5ac : bv 32 := 0x02030063.
Lemma F_7b5ac : fetch_word Asan.M.loaded_segments (0x7b5fc : word) = Some W_7b5ac.
Proof. vm_refl. Qed.
Lemma D_7b5ac : decode_any W_7b5ac = Some (Branch BC_EQ 6 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5b0 : bv 32 := 0x00130313.
Lemma F_7b5b0 : fetch_word Asan.M.loaded_segments (0x7b600 : word) = Some W_7b5b0.
Proof. vm_refl. Qed.
Lemma D_7b5b0 : decode_any W_7b5b0 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5b4 : bv 32 := 0x00657c63.
Lemma F_7b5b4 : fetch_word Asan.M.loaded_segments (0x7b604 : word) = Some W_7b5b4.
Proof. vm_refl. Qed.
Lemma D_7b5b4 : decode_any W_7b5b4 = Some (Branch BC_GEU 10 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5b8 : bv 32 := 0x33c0006f.
Lemma F_7b5b8 : fetch_word Asan.M.loaded_segments (0x7b608 : word) = Some W_7b5b8.
Proof. vm_refl. Qed.
Lemma D_7b5b8 : decode_any W_7b5b8 = Some (Jal 0 828, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5bc : bv 32 := 0x00130313.
Lemma F_7b5bc : fetch_word Asan.M.loaded_segments (0x7b60c : word) = Some W_7b5bc.
Proof. vm_refl. Qed.
Lemma D_7b5bc : decode_any W_7b5bc = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5c0 : bv 32 := 0x00335313.
Lemma F_7b5c0 : fetch_word Asan.M.loaded_segments (0x7b610 : word) = Some W_7b5c0.
Proof. vm_refl. Qed.
Lemma D_7b5c0 : decode_any W_7b5c0 = Some (ShiftImm ALU_SRL 6 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5c4 : bv 32 := 0xfff30313.
Lemma F_7b5c4 : fetch_word Asan.M.loaded_segments (0x7b614 : word) = Some W_7b5c4.
Proof. vm_refl. Qed.
Lemma D_7b5c4 : decode_any W_7b5c4 = Some (OpImm ALU_ADD 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5c8 : bv 32 := 0x32a36663.
Lemma F_7b5c8 : fetch_word Asan.M.loaded_segments (0x7b618 : word) = Some W_7b5c8.
Proof. vm_refl. Qed.
Lemma D_7b5c8 : decode_any W_7b5c8 = Some (Branch BC_LTU 6 10 812, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5cc : bv 32 := 0x0002b383.
Lemma F_7b5cc : fetch_word Asan.M.loaded_segments (0x7b61c : word) = Some W_7b5cc.
Proof. vm_refl. Qed.
Lemma D_7b5cc : decode_any W_7b5cc = Some (Load SZ8 true 7 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5d0 : bv 32 := 0x0033d293.
Lemma F_7b5d0 : fetch_word Asan.M.loaded_segments (0x7b620 : word) = Some W_7b5d0.
Proof. vm_refl. Qed.
Lemma D_7b5d0 : decode_any W_7b5d0 = Some (ShiftImm ALU_SRL 5 7 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5d4 : bv 32 := 0x00928333.
Lemma F_7b5d4 : fetch_word Asan.M.loaded_segments (0x7b624 : word) = Some W_7b5d4.
Proof. vm_refl. Qed.
Lemma D_7b5d4 : decode_any W_7b5d4 = Some (Op ALU_ADD 6 5 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5d8 : bv 32 := 0x00a3e463.
Lemma F_7b5d8 : fetch_word Asan.M.loaded_segments (0x7b628 : word) = Some W_7b5d8.
Proof. vm_refl. Qed.
Lemma D_7b5d8 : decode_any W_7b5d8 = Some (Branch BC_LTU 7 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5dc : bv 32 := 0x0ca36063.
Lemma F_7b5dc : fetch_word Asan.M.loaded_segments (0x7b62c : word) = Some W_7b5dc.
Proof. vm_refl. Qed.
Lemma D_7b5dc : decode_any W_7b5dc = Some (Branch BC_LTU 6 10 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5e0 : bv 32 := 0x000be397.
Lemma F_7b5e0 : fetch_word Asan.M.loaded_segments (0x7b630 : word) = Some W_7b5e0.
Proof. vm_refl. Qed.
Lemma D_7b5e0 : decode_any W_7b5e0 = Some (Auipc 7 190, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5e4 : bv 32 := 0xb803b383.
Lemma F_7b5e4 : fetch_word Asan.M.loaded_segments (0x7b634 : word) = Some W_7b5e4.
Proof. vm_refl. Qed.
Lemma D_7b5e4 : decode_any W_7b5e4 = Some (Load SZ8 true 7 7 2944, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5e8 : bv 32 := 0x04e3c383.
Lemma F_7b5e8 : fetch_word Asan.M.loaded_segments (0x7b638 : word) = Some W_7b5e8.
Proof. vm_refl. Qed.
Lemma D_7b5e8 : decode_any W_7b5e8 = Some (Load SZ1 false 7 7 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5ec : bv 32 := 0x08039063.
Lemma F_7b5ec : fetch_word Asan.M.loaded_segments (0x7b63c : word) = Some W_7b5ec.
Proof. vm_refl. Qed.
Lemma D_7b5ec : decode_any W_7b5ec = Some (Branch BC_NE 7 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5f0 : bv 32 := 0x02088c63.
Lemma F_7b5f0 : fetch_word Asan.M.loaded_segments (0x7b640 : word) = Some W_7b5f0.
Proof. vm_refl. Qed.
Lemma D_7b5f0 : decode_any W_7b5f0 = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5f4 : bv 32 := 0x0038d893.
Lemma F_7b5f4 : fetch_word Asan.M.loaded_segments (0x7b644 : word) = Some W_7b5f4.
Proof. vm_refl. Qed.
Lemma D_7b5f4 : decode_any W_7b5f4 = Some (ShiftImm ALU_SRL 17 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5f8 : bv 32 := 0x00d888b3.
Lemma F_7b5f8 : fetch_word Asan.M.loaded_segments (0x7b648 : word) = Some W_7b5f8.
Proof. vm_refl. Qed.
Lemma D_7b5f8 : decode_any W_7b5f8 = Some (Op ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b5fc : bv 32 := 0x04a8fc63.
Lemma F_7b5fc : fetch_word Asan.M.loaded_segments (0x7b64c : word) = Some W_7b5fc.
Proof. vm_refl. Qed.
Lemma D_7b5fc : decode_any W_7b5fc = Some (Branch BC_GEU 17 10 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b600 : bv 32 := 0x00148893.
Lemma F_7b600 : fetch_word Asan.M.loaded_segments (0x7b650 : word) = Some W_7b600.
Proof. vm_refl. Qed.
Lemma D_7b600 : decode_any W_7b600 = Some (OpImm ALU_ADD 17 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b604 : bv 32 := 0x00a86863.
Lemma F_7b604 : fetch_word Asan.M.loaded_segments (0x7b654 : word) = Some W_7b604.
Proof. vm_refl. Qed.
Lemma D_7b604 : decode_any W_7b604 = Some (Branch BC_LTU 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b608 : bv 32 := 0x0037d813.
Lemma F_7b608 : fetch_word Asan.M.loaded_segments (0x7b658 : word) = Some W_7b608.
Proof. vm_refl. Qed.
Lemma D_7b608 : decode_any W_7b608 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b60c : bv 32 := 0x01180833.
Lemma F_7b60c : fetch_word Asan.M.loaded_segments (0x7b65c : word) = Some W_7b60c.
Proof. vm_refl. Qed.
Lemma D_7b60c : decode_any W_7b60c = Some (Op ALU_ADD 16 16 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b610 : bv 32 := 0x09057663.
Lemma F_7b610 : fetch_word Asan.M.loaded_segments (0x7b660 : word) = Some W_7b610.
Proof. vm_refl. Qed.
Lemma D_7b610 : decode_any W_7b610 = Some (Branch BC_GEU 10 16 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b614 : bv 32 := 0x00178793.
Lemma F_7b614 : fetch_word Asan.M.loaded_segments (0x7b664 : word) = Some W_7b614.
Proof. vm_refl. Qed.
Lemma D_7b614 : decode_any W_7b614 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b618 : bv 32 := 0x04f56a63.
Lemma F_7b618 : fetch_word Asan.M.loaded_segments (0x7b668 : word) = Some W_7b618.
Proof. vm_refl. Qed.
Lemma D_7b618 : decode_any W_7b618 = Some (Branch BC_LTU 10 15 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b61c : bv 32 := 0x011288b3.
Lemma F_7b61c : fetch_word Asan.M.loaded_segments (0x7b66c : word) = Some W_7b61c.
Proof. vm_refl. Qed.
Lemma D_7b61c : decode_any W_7b61c = Some (Op ALU_ADD 17 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b620 : bv 32 := 0x0038d793.
Lemma F_7b620 : fetch_word Asan.M.loaded_segments (0x7b670 : word) = Some W_7b620.
Proof. vm_refl. Qed.
Lemma D_7b620 : decode_any W_7b620 = Some (ShiftImm ALU_SRL 15 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b624 : bv 32 := 0x0240006f.
Lemma F_7b624 : fetch_word Asan.M.loaded_segments (0x7b674 : word) = Some W_7b624.
Proof. vm_refl. Qed.
Lemma D_7b624 : decode_any W_7b624 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b628 : bv 32 := 0x06048263.
Lemma F_7b628 : fetch_word Asan.M.loaded_segments (0x7b678 : word) = Some W_7b628.
Proof. vm_refl. Qed.
Lemma D_7b628 : decode_any W_7b628 = Some (Branch BC_EQ 9 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b62c : bv 32 := 0x0036d793.
Lemma F_7b62c : fetch_word Asan.M.loaded_segments (0x7b67c : word) = Some W_7b62c.
Proof. vm_refl. Qed.
Lemma D_7b62c : decode_any W_7b62c = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b630 : bv 32 := 0x009787b3.
Lemma F_7b630 : fetch_word Asan.M.loaded_segments (0x7b680 : word) = Some W_7b630.
Proof. vm_refl. Qed.
Lemma D_7b630 : decode_any W_7b630 = Some (Op ALU_ADD 15 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b634 : bv 32 := 0x00078663.
Lemma F_7b634 : fetch_word Asan.M.loaded_segments (0x7b684 : word) = Some W_7b634.
Proof. vm_refl. Qed.
Lemma D_7b634 : decode_any W_7b634 = Some (Branch BC_EQ 15 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b638 : bv 32 := 0x00178793.
Lemma F_7b638 : fetch_word Asan.M.loaded_segments (0x7b688 : word) = Some W_7b638.
Proof. vm_refl. Qed.
Lemma D_7b638 : decode_any W_7b638 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b63c : bv 32 := 0x02f56863.
Lemma F_7b63c : fetch_word Asan.M.loaded_segments (0x7b68c : word) = Some W_7b63c.
Proof. vm_refl. Qed.
Lemma D_7b63c : decode_any W_7b63c = Some (Branch BC_LTU 10 15 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b640 : bv 32 := 0x00130313.
Lemma F_7b640 : fetch_word Asan.M.loaded_segments (0x7b690 : word) = Some W_7b640.
Proof. vm_refl. Qed.
Lemma D_7b640 : decode_any W_7b640 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b644 : bv 32 := 0x00335793.
Lemma F_7b644 : fetch_word Asan.M.loaded_segments (0x7b694 : word) = Some W_7b644.
Proof. vm_refl. Qed.
Lemma D_7b644 : decode_any W_7b644 = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b648 : bv 32 := 0x00d787b3.
Lemma F_7b648 : fetch_word Asan.M.loaded_segments (0x7b698 : word) = Some W_7b648.
Proof. vm_refl. Qed.
Lemma D_7b648 : decode_any W_7b648 = Some (Op ALU_ADD 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b64c : bv 32 := 0x04a7f863.
Lemma F_7b64c : fetch_word Asan.M.loaded_segments (0x7b69c : word) = Some W_7b64c.
Proof. vm_refl. Qed.
Lemma D_7b64c : decode_any W_7b64c = Some (Branch BC_GEU 15 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b650 : bv 32 := 0x01c0006f.
Lemma F_7b650 : fetch_word Asan.M.loaded_segments (0x7b6a0 : word) = Some W_7b650.
Proof. vm_refl. Qed.
Lemma D_7b650 : decode_any W_7b650 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b654 : bv 32 := 0x04048463.
Lemma F_7b654 : fetch_word Asan.M.loaded_segments (0x7b6a4 : word) = Some W_7b654.
Proof. vm_refl. Qed.
Lemma D_7b654 : decode_any W_7b654 = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b658 : bv 32 := 0x0036d793.
Lemma F_7b658 : fetch_word Asan.M.loaded_segments (0x7b6a8 : word) = Some W_7b658.
Proof. vm_refl. Qed.
Lemma D_7b658 : decode_any W_7b658 = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b65c : bv 32 := 0x009787b3.
Lemma F_7b65c : fetch_word Asan.M.loaded_segments (0x7b6ac : word) = Some W_7b65c.
Proof. vm_refl. Qed.
Lemma D_7b65c : decode_any W_7b65c = Some (Op ALU_ADD 15 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b660 : bv 32 := 0x02078e63.
Lemma F_7b660 : fetch_word Asan.M.loaded_segments (0x7b6b0 : word) = Some W_7b660.
Proof. vm_refl. Qed.
Lemma D_7b660 : decode_any W_7b660 = Some (Branch BC_EQ 15 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b664 : bv 32 := 0x00178793.
Lemma F_7b664 : fetch_word Asan.M.loaded_segments (0x7b6b4 : word) = Some W_7b664.
Proof. vm_refl. Qed.
Lemma D_7b664 : decode_any W_7b664 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b668 : bv 32 := 0x02f57a63.
Lemma F_7b668 : fetch_word Asan.M.loaded_segments (0x7b6b8 : word) = Some W_7b668.
Proof. vm_refl. Qed.
Lemma D_7b668 : decode_any W_7b668 = Some (Branch BC_GEU 10 15 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b66c : bv 32 := 0xfffa6517.
Lemma F_7b66c : fetch_word Asan.M.loaded_segments (0x7b6bc : word) = Some W_7b66c.
Proof. vm_refl. Qed.
Lemma D_7b66c : decode_any W_7b66c = Some (Auipc 10 1048486, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b670 : bv 32 := 0xfff9d597.
Lemma F_7b670 : fetch_word Asan.M.loaded_segments (0x7b6c0 : word) = Some W_7b670.
Proof. vm_refl. Qed.
Lemma D_7b670 : decode_any W_7b670 = Some (Auipc 11 1048477, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b674 : bv 32 := 0xc1d50513.
Lemma F_7b674 : fetch_word Asan.M.loaded_segments (0x7b6c4 : word) = Some W_7b674.
Proof. vm_refl. Qed.
Lemma D_7b674 : decode_any W_7b674 = Some (OpImm ALU_ADD 10 10 3101, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b678 : bv 32 := 0x23e58613.
Lemma F_7b678 : fetch_word Asan.M.loaded_segments (0x7b6c8 : word) = Some W_7b678.
Proof. vm_refl. Qed.
Lemma D_7b678 : decode_any W_7b678 = Some (OpImm ALU_ADD 12 11 574, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b67c : bv 32 := 0x02f00593.
Lemma F_7b67c : fetch_word Asan.M.loaded_segments (0x7b6cc : word) = Some W_7b67c.
Proof. vm_refl. Qed.
Lemma D_7b67c : decode_any W_7b67c = Some (OpImm ALU_ADD 11 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b680 : bv 32 := 0x00000693.
Lemma F_7b680 : fetch_word Asan.M.loaded_segments (0x7b6d0 : word) = Some W_7b680.
Proof. vm_refl. Qed.
Lemma D_7b680 : decode_any W_7b680 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b684 : bv 32 := 0x00000713.
Lemma F_7b684 : fetch_word Asan.M.loaded_segments (0x7b6d4 : word) = Some W_7b684.
Proof. vm_refl. Qed.
Lemma D_7b684 : decode_any W_7b684 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b688 : bv 32 := 0x430180ef.
Lemma F_7b688 : fetch_word Asan.M.loaded_segments (0x7b6d8 : word) = Some W_7b688.
Proof. vm_refl. Qed.
Lemma D_7b688 : decode_any W_7b688 = Some (Jal 1 99376, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b68c : bv 32 := 0x00128293.
Lemma F_7b68c : fetch_word Asan.M.loaded_segments (0x7b6dc : word) = Some W_7b68c.
Proof. vm_refl. Qed.
Lemma D_7b68c : decode_any W_7b68c = Some (OpImm ALU_ADD 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b690 : bv 32 := 0x0032d793.
Lemma F_7b690 : fetch_word Asan.M.loaded_segments (0x7b6e0 : word) = Some W_7b690.
Proof. vm_refl. Qed.
Lemma D_7b690 : decode_any W_7b690 = Some (ShiftImm ALU_SRL 15 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b694 : bv 32 := 0xfff78793.
Lemma F_7b694 : fetch_word Asan.M.loaded_segments (0x7b6e4 : word) = Some W_7b694.
Proof. vm_refl. Qed.
Lemma D_7b694 : decode_any W_7b694 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b698 : bv 32 := 0xfca7eae3.
Lemma F_7b698 : fetch_word Asan.M.loaded_segments (0x7b6e8 : word) = Some W_7b698.
Proof. vm_refl. Qed.
Lemma D_7b698 : decode_any W_7b698 = Some (Branch BC_LTU 15 10 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b69c : bv 32 := 0x0075f793.
Lemma F_7b69c : fetch_word Asan.M.loaded_segments (0x7b6ec : word) = Some W_7b69c.
Proof. vm_refl. Qed.
Lemma D_7b69c : decode_any W_7b69c = Some (OpImm ALU_AND 15 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6a0 : bv 32 := 0x26079a63.
Lemma F_7b6a0 : fetch_word Asan.M.loaded_segments (0x7b6f0 : word) = Some W_7b6a0.
Proof. vm_refl. Qed.
Lemma D_7b6a0 : decode_any W_7b6a0 = Some (Branch BC_NE 15 0 628, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6a4 : bv 32 := 0x00b505b3.
Lemma F_7b6a4 : fetch_word Asan.M.loaded_segments (0x7b6f4 : word) = Some W_7b6a4.
Proof. vm_refl. Qed.
Lemma D_7b6a4 : decode_any W_7b6a4 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6a8 : bv 32 := 0xff858593.
Lemma F_7b6a8 : fetch_word Asan.M.loaded_segments (0x7b6f8 : word) = Some W_7b6a8.
Proof. vm_refl. Qed.
Lemma D_7b6a8 : decode_any W_7b6a8 = Some (OpImm ALU_ADD 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6ac : bv 32 := 0x04b77263.
Lemma F_7b6ac : fetch_word Asan.M.loaded_segments (0x7b6fc : word) = Some W_7b6ac.
Proof. vm_refl. Qed.
Lemma D_7b6ac : decode_any W_7b6ac = Some (Branch BC_GEU 14 11 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6b0 : bv 32 := 0x000be717.
Lemma F_7b6b0 : fetch_word Asan.M.loaded_segments (0x7b700 : word) = Some W_7b6b0.
Proof. vm_refl. Qed.
Lemma D_7b6b0 : decode_any W_7b6b0 = Some (Auipc 14 190, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6b4 : bv 32 := 0xac073703.
Lemma F_7b6b4 : fetch_word Asan.M.loaded_segments (0x7b704 : word) = Some W_7b6b4.
Proof. vm_refl. Qed.
Lemma D_7b6b4 : decode_any W_7b6b4 = Some (Load SZ8 true 14 14 2752, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6b8 : bv 32 := 0x000be797.
Lemma F_7b6b8 : fetch_word Asan.M.loaded_segments (0x7b708 : word) = Some W_7b6b8.
Proof. vm_refl. Qed.
Lemma D_7b6b8 : decode_any W_7b6b8 = Some (Auipc 15 190, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6bc : bv 32 := 0xac07b783.
Lemma F_7b6bc : fetch_word Asan.M.loaded_segments (0x7b70c : word) = Some W_7b6bc.
Proof. vm_refl. Qed.
Lemma D_7b6bc : decode_any W_7b6bc = Some (Load SZ8 true 15 15 2752, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6c0 : bv 32 := 0x00073883.
Lemma F_7b6c0 : fetch_word Asan.M.loaded_segments (0x7b710 : word) = Some W_7b6c0.
Proof. vm_refl. Qed.
Lemma D_7b6c0 : decode_any W_7b6c0 = Some (Load SZ8 true 17 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6c4 : bv 32 := 0x0007b703.
Lemma F_7b6c4 : fetch_word Asan.M.loaded_segments (0x7b714 : word) = Some W_7b6c4.
Proof. vm_refl. Qed.
Lemma D_7b6c4 : decode_any W_7b6c4 = Some (Load SZ8 true 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6c8 : bv 32 := 0xfff88813.
Lemma F_7b6c8 : fetch_word Asan.M.loaded_segments (0x7b718 : word) = Some W_7b6c8.
Proof. vm_refl. Qed.
Lemma D_7b6c8 : decode_any W_7b6c8 = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6cc : bv 32 := 0x00b87463.
Lemma F_7b6cc : fetch_word Asan.M.loaded_segments (0x7b71c : word) = Some W_7b6cc.
Proof. vm_refl. Qed.
Lemma D_7b6cc : decode_any W_7b6cc = Some (Branch BC_GEU 16 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6d0 : bv 32 := 0x02b77063.
Lemma F_7b6d0 : fetch_word Asan.M.loaded_segments (0x7b720 : word) = Some W_7b6d0.
Proof. vm_refl. Qed.
Lemma D_7b6d0 : decode_any W_7b6d0 = Some (Branch BC_GEU 14 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6d4 : bv 32 := 0x000be797.
Lemma F_7b6d4 : fetch_word Asan.M.loaded_segments (0x7b724 : word) = Some W_7b6d4.
Proof. vm_refl. Qed.
Lemma D_7b6d4 : decode_any W_7b6d4 = Some (Auipc 15 190, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6d8 : bv 32 := 0xaac7b783.
Lemma F_7b6d8 : fetch_word Asan.M.loaded_segments (0x7b728 : word) = Some W_7b6d8.
Proof. vm_refl. Qed.
Lemma D_7b6d8 : decode_any W_7b6d8 = Some (Load SZ8 true 15 15 2732, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6dc : bv 32 := 0x0007b303.
Lemma F_7b6dc : fetch_word Asan.M.loaded_segments (0x7b72c : word) = Some W_7b6dc.
Proof. vm_refl. Qed.
Lemma D_7b6dc : decode_any W_7b6dc = Some (Load SZ8 true 6 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6e0 : bv 32 := 0x00335793.
Lemma F_7b6e0 : fetch_word Asan.M.loaded_segments (0x7b730 : word) = Some W_7b6e0.
Proof. vm_refl. Qed.
Lemma D_7b6e0 : decode_any W_7b6e0 = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6e4 : bv 32 := 0x009782b3.
Lemma F_7b6e4 : fetch_word Asan.M.loaded_segments (0x7b734 : word) = Some W_7b6e4.
Proof. vm_refl. Qed.
Lemma D_7b6e4 : decode_any W_7b6e4 = Some (Op ALU_ADD 5 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6e8 : bv 32 := 0x12b36263.
Lemma F_7b6e8 : fetch_word Asan.M.loaded_segments (0x7b738 : word) = Some W_7b6e8.
Proof. vm_refl. Qed.
Lemma D_7b6e8 : decode_any W_7b6e8 = Some (Branch BC_LTU 6 11 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6ec : bv 32 := 0x12b2f063.
Lemma F_7b6ec : fetch_word Asan.M.loaded_segments (0x7b73c : word) = Some W_7b6ec.
Proof. vm_refl. Qed.
Lemma D_7b6ec : decode_any W_7b6ec = Some (Branch BC_GEU 5 11 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6f0 : bv 32 := 0x000be697.
Lemma F_7b6f0 : fetch_word Asan.M.loaded_segments (0x7b740 : word) = Some W_7b6f0.
Proof. vm_refl. Qed.
Lemma D_7b6f0 : decode_any W_7b6f0 = Some (Auipc 13 190, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6f4 : bv 32 := 0xa986b983.
Lemma F_7b6f4 : fetch_word Asan.M.loaded_segments (0x7b744 : word) = Some W_7b6f4.
Proof. vm_refl. Qed.
Lemma D_7b6f4 : decode_any W_7b6f4 = Some (Load SZ8 true 19 13 2712, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6f8 : bv 32 := 0x0009b303.
Lemma F_7b6f8 : fetch_word Asan.M.loaded_segments (0x7b748 : word) = Some W_7b6f8.
Proof. vm_refl. Qed.
Lemma D_7b6f8 : decode_any W_7b6f8 = Some (Load SZ8 true 6 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b6fc : bv 32 := 0x22030c63.
Lemma F_7b6fc : fetch_word Asan.M.loaded_segments (0x7b74c : word) = Some W_7b6fc.
Proof. vm_refl. Qed.
Lemma D_7b6fc : decode_any W_7b6fc = Some (Branch BC_EQ 6 0 568, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b700 : bv 32 := 0x00355693.
Lemma F_7b700 : fetch_word Asan.M.loaded_segments (0x7b750 : word) = Some W_7b700.
Proof. vm_refl. Qed.
Lemma D_7b700 : decode_any W_7b700 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b704 : bv 32 := 0x0035d593.
Lemma F_7b704 : fetch_word Asan.M.loaded_segments (0x7b754 : word) = Some W_7b704.
Proof. vm_refl. Qed.
Lemma D_7b704 : decode_any W_7b704 = Some (ShiftImm ALU_SRL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b708 : bv 32 := 0x00d48533.
Lemma F_7b708 : fetch_word Asan.M.loaded_segments (0x7b758 : word) = Some W_7b708.
Proof. vm_refl. Qed.
Lemma D_7b708 : decode_any W_7b708 = Some (Op ALU_ADD 10 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b70c : bv 32 := 0x00158913.
Lemma F_7b70c : fetch_word Asan.M.loaded_segments (0x7b75c : word) = Some W_7b70c.
Proof. vm_refl. Qed.
Lemma D_7b70c : decode_any W_7b70c = Some (OpImm ALU_ADD 18 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b710 : bv 32 := 0x40d90433.
Lemma F_7b710 : fetch_word Asan.M.loaded_segments (0x7b760 : word) = Some W_7b710.
Proof. vm_refl. Qed.
Lemma D_7b710 : decode_any W_7b710 = Some (Op ALU_SUB 8 18 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b714 : bv 32 := 0x0c061063.
Lemma F_7b714 : fetch_word Asan.M.loaded_segments (0x7b764 : word) = Some W_7b714.
Proof. vm_refl. Qed.
Lemma D_7b714 : decode_any W_7b714 = Some (Branch BC_NE 12 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b718 : bv 32 := 0x000be597.
Lemma F_7b718 : fetch_word Asan.M.loaded_segments (0x7b768 : word) = Some W_7b718.
Proof. vm_refl. Qed.
Lemma D_7b718 : decode_any W_7b718 = Some (Auipc 11 190, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b71c : bv 32 := 0xa405b583.
Lemma F_7b71c : fetch_word Asan.M.loaded_segments (0x7b76c : word) = Some W_7b71c.
Proof. vm_refl. Qed.
Lemma D_7b71c : decode_any W_7b71c = Some (Load SZ8 true 11 11 2624, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b720 : bv 32 := 0x0785b583.
Lemma F_7b720 : fetch_word Asan.M.loaded_segments (0x7b770 : word) = Some W_7b720.
Proof. vm_refl. Qed.
Lemma D_7b720 : decode_any W_7b720 = Some (Load SZ8 true 11 11 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b724 : bv 32 := 0x0ab46863.
Lemma F_7b724 : fetch_word Asan.M.loaded_segments (0x7b774 : word) = Some W_7b724.
Proof. vm_refl. Qed.
Lemma D_7b724 : decode_any W_7b724 = Some (Branch BC_LTU 8 11 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b734 : bv 32 := 0x00059c63.
Lemma F_7b734 : fetch_word Asan.M.loaded_segments (0x7b784 : word) = Some W_7b734.
Proof. vm_refl. Qed.
Lemma D_7b734 : decode_any W_7b734 = Some (Branch BC_NE 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b738 : bv 32 := 0x00050a93.
Lemma F_7b738 : fetch_word Asan.M.loaded_segments (0x7b788 : word) = Some W_7b738.
Proof. vm_refl. Qed.
Lemma D_7b738 : decode_any W_7b738 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b73c : bv 32 := 0x5a1110ef.
Lemma F_7b73c : fetch_word Asan.M.loaded_segments (0x7b78c : word) = Some W_7b73c.
Proof. vm_refl. Qed.
Lemma D_7b73c : decode_any W_7b73c = Some (Jal 1 73120, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b740 : bv 32 := 0x00050593.
Lemma F_7b740 : fetch_word Asan.M.loaded_segments (0x7b790 : word) = Some W_7b740.
Proof. vm_refl. Qed.
Lemma D_7b740 : decode_any W_7b740 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b744 : bv 32 := 0x000a8513.
Lemma F_7b744 : fetch_word Asan.M.loaded_segments (0x7b794 : word) = Some W_7b744.
Proof. vm_refl. Qed.
Lemma D_7b744 : decode_any W_7b744 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b748 : bv 32 := 0x00ba3023.
Lemma F_7b748 : fetch_word Asan.M.loaded_segments (0x7b798 : word) = Some W_7b748.
Proof. vm_refl. Qed.
Lemma D_7b748 : decode_any W_7b748 = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b74c : bv 32 := 0xfff58613.
Lemma F_7b74c : fetch_word Asan.M.loaded_segments (0x7b79c : word) = Some W_7b74c.
Proof. vm_refl. Qed.
Lemma D_7b74c : decode_any W_7b74c = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b750 : bv 32 := 0x00c5f633.
Lemma F_7b750 : fetch_word Asan.M.loaded_segments (0x7b7a0 : word) = Some W_7b750.
Proof. vm_refl. Qed.
Lemma D_7b750 : decode_any W_7b750 = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b754 : bv 32 := 0x20061063.
Lemma F_7b754 : fetch_word Asan.M.loaded_segments (0x7b7a4 : word) = Some W_7b754.
Proof. vm_refl. Qed.
Lemma D_7b754 : decode_any W_7b754 = Some (Branch BC_NE 12 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b758 : bv 32 := 0x00990a33.
Lemma F_7b758 : fetch_word Asan.M.loaded_segments (0x7b7a8 : word) = Some W_7b758.
Proof. vm_refl. Qed.
Lemma D_7b758 : decode_any W_7b758 = Some (Op ALU_ADD 20 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b75c : bv 32 := 0x00b50633.
Lemma F_7b75c : fetch_word Asan.M.loaded_segments (0x7b7ac : word) = Some W_7b75c.
Proof. vm_refl. Qed.
Lemma D_7b75c : decode_any W_7b75c = Some (Op ALU_ADD 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b760 : bv 32 := 0x40b005b3.
Lemma F_7b760 : fetch_word Asan.M.loaded_segments (0x7b7b0 : word) = Some W_7b760.
Proof. vm_refl. Qed.
Lemma D_7b760 : decode_any W_7b760 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b764 : bv 32 := 0xfff60613.
Lemma F_7b764 : fetch_word Asan.M.loaded_segments (0x7b7b4 : word) = Some W_7b764.
Proof. vm_refl. Qed.
Lemma D_7b764 : decode_any W_7b764 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b768 : bv 32 := 0x00b674b3.
Lemma F_7b768 : fetch_word Asan.M.loaded_segments (0x7b7b8 : word) = Some W_7b768.
Proof. vm_refl. Qed.
Lemma D_7b768 : decode_any W_7b768 = Some (Op ALU_AND 9 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b76c : bv 32 := 0x00ba7933.
Lemma F_7b76c : fetch_word Asan.M.loaded_segments (0x7b7bc : word) = Some W_7b76c.
Proof. vm_refl. Qed.
Lemma D_7b76c : decode_any W_7b76c = Some (Op ALU_AND 18 20 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b770 : bv 32 := 0x0724f663.
Lemma F_7b770 : fetch_word Asan.M.loaded_segments (0x7b7c0 : word) = Some W_7b770.
Proof. vm_refl. Qed.
Lemma D_7b770 : decode_any W_7b770 = Some (Branch BC_GEU 9 18 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b774 : bv 32 := 0x00a48a63.
Lemma F_7b774 : fetch_word Asan.M.loaded_segments (0x7b7c4 : word) = Some W_7b774.
Proof. vm_refl. Qed.
Lemma D_7b774 : decode_any W_7b774 = Some (Branch BC_EQ 9 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b778 : bv 32 := 0x0009b683.
Lemma F_7b778 : fetch_word Asan.M.loaded_segments (0x7b7c8 : word) = Some W_7b778.
Proof. vm_refl. Qed.
Lemma D_7b778 : decode_any W_7b778 = Some (Load SZ8 true 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b77c : bv 32 := 0x40a48633.
Lemma F_7b77c : fetch_word Asan.M.loaded_segments (0x7b7cc : word) = Some W_7b77c.
Proof. vm_refl. Qed.
Lemma D_7b77c : decode_any W_7b77c = Some (Op ALU_SUB 12 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b780 : bv 32 := 0x00000593.
Lemma F_7b780 : fetch_word Asan.M.loaded_segments (0x7b7d0 : word) = Some W_7b780.
Proof. vm_refl. Qed.
Lemma D_7b780 : decode_any W_7b780 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b784 : bv 32 := 0x000680e7.
Lemma F_7b784 : fetch_word Asan.M.loaded_segments (0x7b7d4 : word) = Some W_7b784.
Proof. vm_refl. Qed.
Lemma D_7b784 : decode_any W_7b784 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b788 : bv 32 := 0x012a0c63.
Lemma F_7b788 : fetch_word Asan.M.loaded_segments (0x7b7d8 : word) = Some W_7b788.
Proof. vm_refl. Qed.
Lemma D_7b788 : decode_any W_7b788 = Some (Branch BC_EQ 20 18 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b78c : bv 32 := 0x0009b683.
Lemma F_7b78c : fetch_word Asan.M.loaded_segments (0x7b7dc : word) = Some W_7b78c.
Proof. vm_refl. Qed.
Lemma D_7b78c : decode_any W_7b78c = Some (Load SZ8 true 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b790 : bv 32 := 0x412a0633.
Lemma F_7b790 : fetch_word Asan.M.loaded_segments (0x7b7e0 : word) = Some W_7b790.
Proof. vm_refl. Qed.
Lemma D_7b790 : decode_any W_7b790 = Some (Op ALU_SUB 12 20 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b794 : bv 32 := 0x00090513.
Lemma F_7b794 : fetch_word Asan.M.loaded_segments (0x7b7e4 : word) = Some W_7b794.
Proof. vm_refl. Qed.
Lemma D_7b794 : decode_any W_7b794 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b798 : bv 32 := 0x00000593.
Lemma F_7b798 : fetch_word Asan.M.loaded_segments (0x7b7e8 : word) = Some W_7b798.
Proof. vm_refl. Qed.
Lemma D_7b798 : decode_any W_7b798 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b79c : bv 32 := 0x000680e7.
Lemma F_7b79c : fetch_word Asan.M.loaded_segments (0x7b7ec : word) = Some W_7b79c.
Proof. vm_refl. Qed.
Lemma D_7b79c : decode_any W_7b79c = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7a0 : bv 32 := 0xfff90593.
Lemma F_7b7a0 : fetch_word Asan.M.loaded_segments (0x7b7f0 : word) = Some W_7b7a0.
Proof. vm_refl. Qed.
Lemma D_7b7a0 : decode_any W_7b7a0 = Some (OpImm ALU_ADD 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7a4 : bv 32 := 0x00100693.
Lemma F_7b7a4 : fetch_word Asan.M.loaded_segments (0x7b7f4 : word) = Some W_7b7a4.
Proof. vm_refl. Qed.
Lemma D_7b7a4 : decode_any W_7b7a4 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7a8 : bv 32 := 0x00048513.
Lemma F_7b7a8 : fetch_word Asan.M.loaded_segments (0x7b7f8 : word) = Some W_7b7a8.
Proof. vm_refl. Qed.
Lemma D_7b7a8 : decode_any W_7b7a8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7ac : bv 32 := 0x00000613.
Lemma F_7b7ac : fetch_word Asan.M.loaded_segments (0x7b7fc : word) = Some W_7b7ac.
Proof. vm_refl. Qed.
Lemma D_7b7ac : decode_any W_7b7ac = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7b0 : bv 32 := 0x03813083.
Lemma F_7b7b0 : fetch_word Asan.M.loaded_segments (0x7b800 : word) = Some W_7b7b0.
Proof. vm_refl. Qed.
Lemma D_7b7b0 : decode_any W_7b7b0 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7b4 : bv 32 := 0x03013403.
Lemma F_7b7b4 : fetch_word Asan.M.loaded_segments (0x7b804 : word) = Some W_7b7b4.
Proof. vm_refl. Qed.
Lemma D_7b7b4 : decode_any W_7b7b4 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7b8 : bv 32 := 0x02813483.
Lemma F_7b7b8 : fetch_word Asan.M.loaded_segments (0x7b808 : word) = Some W_7b7b8.
Proof. vm_refl. Qed.
Lemma D_7b7b8 : decode_any W_7b7b8 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7bc : bv 32 := 0x02013903.
Lemma F_7b7bc : fetch_word Asan.M.loaded_segments (0x7b80c : word) = Some W_7b7bc.
Proof. vm_refl. Qed.
Lemma D_7b7bc : decode_any W_7b7bc = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7c0 : bv 32 := 0x01813983.
Lemma F_7b7c0 : fetch_word Asan.M.loaded_segments (0x7b810 : word) = Some W_7b7c0.
Proof. vm_refl. Qed.
Lemma D_7b7c0 : decode_any W_7b7c0 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7c4 : bv 32 := 0x01013a03.
Lemma F_7b7c4 : fetch_word Asan.M.loaded_segments (0x7b814 : word) = Some W_7b7c4.
Proof. vm_refl. Qed.
Lemma D_7b7c4 : decode_any W_7b7c4 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7c8 : bv 32 := 0x00813a83.
Lemma F_7b7c8 : fetch_word Asan.M.loaded_segments (0x7b818 : word) = Some W_7b7c8.
Proof. vm_refl. Qed.
Lemma D_7b7c8 : decode_any W_7b7c8 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7cc : bv 32 := 0x04010113.
Lemma F_7b7cc : fetch_word Asan.M.loaded_segments (0x7b81c : word) = Some W_7b7cc.
Proof. vm_refl. Qed.
Lemma D_7b7cc : decode_any W_7b7cc = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7d0 : bv 32 := 0x2f11806f.
Lemma F_7b7d0 : fetch_word Asan.M.loaded_segments (0x7b820 : word) = Some W_7b7d0.
Proof. vm_refl. Qed.
Lemma D_7b7d0 : decode_any W_7b7d0 = Some (Jal 0 101104, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7d4 : bv 32 := 0x00060593.
Lemma F_7b7d4 : fetch_word Asan.M.loaded_segments (0x7b824 : word) = Some W_7b7d4.
Proof. vm_refl. Qed.
Lemma D_7b7d4 : decode_any W_7b7d4 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7d8 : bv 32 := 0x00c0006f.
Lemma F_7b7d8 : fetch_word Asan.M.loaded_segments (0x7b828 : word) = Some W_7b7d8.
Proof. vm_refl. Qed.
Lemma D_7b7d8 : decode_any W_7b7d8 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7dc : bv 32 := 0x0009b303.
Lemma F_7b7dc : fetch_word Asan.M.loaded_segments (0x7b82c : word) = Some W_7b7dc.
Proof. vm_refl. Qed.
Lemma D_7b7dc : decode_any W_7b7dc = Some (Load SZ8 true 6 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7e0 : bv 32 := 0x00000593.
Lemma F_7b7e0 : fetch_word Asan.M.loaded_segments (0x7b830 : word) = Some W_7b7e0.
Proof. vm_refl. Qed.
Lemma D_7b7e0 : decode_any W_7b7e0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7e4 : bv 32 := 0x00040613.
Lemma F_7b7e4 : fetch_word Asan.M.loaded_segments (0x7b834 : word) = Some W_7b7e4.
Proof. vm_refl. Qed.
Lemma D_7b7e4 : decode_any W_7b7e4 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7e8 : bv 32 := 0x03813083.
Lemma F_7b7e8 : fetch_word Asan.M.loaded_segments (0x7b838 : word) = Some W_7b7e8.
Proof. vm_refl. Qed.
Lemma D_7b7e8 : decode_any W_7b7e8 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7ec : bv 32 := 0x03013403.
Lemma F_7b7ec : fetch_word Asan.M.loaded_segments (0x7b83c : word) = Some W_7b7ec.
Proof. vm_refl. Qed.
Lemma D_7b7ec : decode_any W_7b7ec = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7f0 : bv 32 := 0x02813483.
Lemma F_7b7f0 : fetch_word Asan.M.loaded_segments (0x7b840 : word) = Some W_7b7f0.
Proof. vm_refl. Qed.
Lemma D_7b7f0 : decode_any W_7b7f0 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7f4 : bv 32 := 0x02013903.
Lemma F_7b7f4 : fetch_word Asan.M.loaded_segments (0x7b844 : word) = Some W_7b7f4.
Proof. vm_refl. Qed.
Lemma D_7b7f4 : decode_any W_7b7f4 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7f8 : bv 32 := 0x01813983.
Lemma F_7b7f8 : fetch_word Asan.M.loaded_segments (0x7b848 : word) = Some W_7b7f8.
Proof. vm_refl. Qed.
Lemma D_7b7f8 : decode_any W_7b7f8 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b7fc : bv 32 := 0x01013a03.
Lemma F_7b7fc : fetch_word Asan.M.loaded_segments (0x7b84c : word) = Some W_7b7fc.
Proof. vm_refl. Qed.
Lemma D_7b7fc : decode_any W_7b7fc = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b800 : bv 32 := 0x00813a83.
Lemma F_7b800 : fetch_word Asan.M.loaded_segments (0x7b850 : word) = Some W_7b800.
Proof. vm_refl. Qed.
Lemma D_7b800 : decode_any W_7b800 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b804 : bv 32 := 0x04010113.
Lemma F_7b804 : fetch_word Asan.M.loaded_segments (0x7b854 : word) = Some W_7b804.
Proof. vm_refl. Qed.
Lemma D_7b804 : decode_any W_7b804 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b808 : bv 32 := 0x00030067.
Lemma F_7b808 : fetch_word Asan.M.loaded_segments (0x7b858 : word) = Some W_7b808.
Proof. vm_refl. Qed.
Lemma D_7b808 : decode_any W_7b808 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b80c : bv 32 := 0x000be317.
Lemma F_7b80c : fetch_word Asan.M.loaded_segments (0x7b85c : word) = Some W_7b80c.
Proof. vm_refl. Qed.
Lemma D_7b80c : decode_any W_7b80c = Some (Auipc 6 190, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b810 : bv 32 := 0x95433303.
Lemma F_7b810 : fetch_word Asan.M.loaded_segments (0x7b860 : word) = Some W_7b810.
Proof. vm_refl. Qed.
Lemma D_7b810 : decode_any W_7b810 = Some (Load SZ8 true 6 6 2388, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b814 : bv 32 := 0x04e34303.
Lemma F_7b814 : fetch_word Asan.M.loaded_segments (0x7b864 : word) = Some W_7b814.
Proof. vm_refl. Qed.
Lemma D_7b814 : decode_any W_7b814 = Some (Load SZ1 false 6 6 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b818 : bv 32 := 0x08031e63.
Lemma F_7b818 : fetch_word Asan.M.loaded_segments (0x7b868 : word) = Some W_7b818.
Proof. vm_refl. Qed.
Lemma D_7b818 : decode_any W_7b818 = Some (Branch BC_NE 6 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b81c : bv 32 := 0x04088063.
Lemma F_7b81c : fetch_word Asan.M.loaded_segments (0x7b86c : word) = Some W_7b81c.
Proof. vm_refl. Qed.
Lemma D_7b81c : decode_any W_7b81c = Some (Branch BC_EQ 17 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b820 : bv 32 := 0x0038d893.
Lemma F_7b820 : fetch_word Asan.M.loaded_segments (0x7b870 : word) = Some W_7b820.
Proof. vm_refl. Qed.
Lemma D_7b820 : decode_any W_7b820 = Some (ShiftImm ALU_SRL 17 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b824 : bv 32 := 0x00d888b3.
Lemma F_7b824 : fetch_word Asan.M.loaded_segments (0x7b874 : word) = Some W_7b824.
Proof. vm_refl. Qed.
Lemma D_7b824 : decode_any W_7b824 = Some (Op ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b828 : bv 32 := 0x06b8f063.
Lemma F_7b828 : fetch_word Asan.M.loaded_segments (0x7b878 : word) = Some W_7b828.
Proof. vm_refl. Qed.
Lemma D_7b828 : decode_any W_7b828 = Some (Branch BC_GEU 17 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b82c : bv 32 := 0x00148893.
Lemma F_7b82c : fetch_word Asan.M.loaded_segments (0x7b87c : word) = Some W_7b82c.
Proof. vm_refl. Qed.
Lemma D_7b82c : decode_any W_7b82c = Some (OpImm ALU_ADD 17 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b830 : bv 32 := 0x00b86863.
Lemma F_7b830 : fetch_word Asan.M.loaded_segments (0x7b880 : word) = Some W_7b830.
Proof. vm_refl. Qed.
Lemma D_7b830 : decode_any W_7b830 = Some (Branch BC_LTU 16 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b834 : bv 32 := 0x00375813.
Lemma F_7b834 : fetch_word Asan.M.loaded_segments (0x7b884 : word) = Some W_7b834.
Proof. vm_refl. Qed.
Lemma D_7b834 : decode_any W_7b834 = Some (ShiftImm ALU_SRL 16 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b838 : bv 32 := 0x01180833.
Lemma F_7b838 : fetch_word Asan.M.loaded_segments (0x7b888 : word) = Some W_7b838.
Proof. vm_refl. Qed.
Lemma D_7b838 : decode_any W_7b838 = Some (Op ALU_ADD 16 16 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b83c : bv 32 := 0xeb05fae3.
Lemma F_7b83c : fetch_word Asan.M.loaded_segments (0x7b88c : word) = Some W_7b83c.
Proof. vm_refl. Qed.
Lemma D_7b83c : decode_any W_7b83c = Some (Branch BC_GEU 11 16 7860, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b840 : bv 32 := 0x00170713.
Lemma F_7b840 : fetch_word Asan.M.loaded_segments (0x7b890 : word) = Some W_7b840.
Proof. vm_refl. Qed.
Lemma D_7b840 : decode_any W_7b840 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b844 : bv 32 := 0x06e5e863.
Lemma F_7b844 : fetch_word Asan.M.loaded_segments (0x7b894 : word) = Some W_7b844.
Proof. vm_refl. Qed.
Lemma D_7b844 : decode_any W_7b844 = Some (Branch BC_LTU 11 14 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b848 : bv 32 := 0x011787b3.
Lemma F_7b848 : fetch_word Asan.M.loaded_segments (0x7b898 : word) = Some W_7b848.
Proof. vm_refl. Qed.
Lemma D_7b848 : decode_any W_7b848 = Some (Op ALU_ADD 15 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b84c : bv 32 := 0x0037d793.
Lemma F_7b84c : fetch_word Asan.M.loaded_segments (0x7b89c : word) = Some W_7b84c.
Proof. vm_refl. Qed.
Lemma D_7b84c : decode_any W_7b84c = Some (ShiftImm ALU_SRL 15 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b850 : bv 32 := 0x00d786b3.
Lemma F_7b850 : fetch_word Asan.M.loaded_segments (0x7b8a0 : word) = Some W_7b850.
Proof. vm_refl. Qed.
Lemma D_7b850 : decode_any W_7b850 = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b854 : bv 32 := 0xe8b6fee3.
Lemma F_7b854 : fetch_word Asan.M.loaded_segments (0x7b8a4 : word) = Some W_7b854.
Proof. vm_refl. Qed.
Lemma D_7b854 : decode_any W_7b854 = Some (Branch BC_GEU 13 11 7836, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b858 : bv 32 := 0x05c0006f.
Lemma F_7b858 : fetch_word Asan.M.loaded_segments (0x7b8a8 : word) = Some W_7b858.
Proof. vm_refl. Qed.
Lemma D_7b858 : decode_any W_7b858 = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b85c : bv 32 := 0x04048463.
Lemma F_7b85c : fetch_word Asan.M.loaded_segments (0x7b8ac : word) = Some W_7b85c.
Proof. vm_refl. Qed.
Lemma D_7b85c : decode_any W_7b85c = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b860 : bv 32 := 0x0036d713.
Lemma F_7b860 : fetch_word Asan.M.loaded_segments (0x7b8b0 : word) = Some W_7b860.
Proof. vm_refl. Qed.
Lemma D_7b860 : decode_any W_7b860 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b864 : bv 32 := 0x00970733.
Lemma F_7b864 : fetch_word Asan.M.loaded_segments (0x7b8b4 : word) = Some W_7b864.
Proof. vm_refl. Qed.
Lemma D_7b864 : decode_any W_7b864 = Some (Op ALU_ADD 14 14 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b868 : bv 32 := 0x00070663.
Lemma F_7b868 : fetch_word Asan.M.loaded_segments (0x7b8b8 : word) = Some W_7b868.
Proof. vm_refl. Qed.
Lemma D_7b868 : decode_any W_7b868 = Some (Branch BC_EQ 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b86c : bv 32 := 0x00170713.
Lemma F_7b86c : fetch_word Asan.M.loaded_segments (0x7b8bc : word) = Some W_7b86c.
Proof. vm_refl. Qed.
Lemma D_7b86c : decode_any W_7b86c = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b870 : bv 32 := 0x04e5e263.
Lemma F_7b870 : fetch_word Asan.M.loaded_segments (0x7b8c0 : word) = Some W_7b870.
Proof. vm_refl. Qed.
Lemma D_7b870 : decode_any W_7b870 = Some (Branch BC_LTU 11 14 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b874 : bv 32 := 0x00128293.
Lemma F_7b874 : fetch_word Asan.M.loaded_segments (0x7b8c4 : word) = Some W_7b874.
Proof. vm_refl. Qed.
Lemma D_7b874 : decode_any W_7b874 = Some (OpImm ALU_ADD 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b878 : bv 32 := 0x0032d713.
Lemma F_7b878 : fetch_word Asan.M.loaded_segments (0x7b8c8 : word) = Some W_7b878.
Proof. vm_refl. Qed.
Lemma D_7b878 : decode_any W_7b878 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b87c : bv 32 := 0x00d706b3.
Lemma F_7b87c : fetch_word Asan.M.loaded_segments (0x7b8cc : word) = Some W_7b87c.
Proof. vm_refl. Qed.
Lemma D_7b87c : decode_any W_7b87c = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b880 : bv 32 := 0xe6b6f8e3.
Lemma F_7b880 : fetch_word Asan.M.loaded_segments (0x7b8d0 : word) = Some W_7b880.
Proof. vm_refl. Qed.
Lemma D_7b880 : decode_any W_7b880 = Some (Branch BC_GEU 13 11 7792, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b884 : bv 32 := 0x0300006f.
Lemma F_7b884 : fetch_word Asan.M.loaded_segments (0x7b8d4 : word) = Some W_7b884.
Proof. vm_refl. Qed.
Lemma D_7b884 : decode_any W_7b884 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b888 : bv 32 := 0xe60484e3.
Lemma F_7b888 : fetch_word Asan.M.loaded_segments (0x7b8d8 : word) = Some W_7b888.
Proof. vm_refl. Qed.
Lemma D_7b888 : decode_any W_7b888 = Some (Branch BC_EQ 9 0 7784, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b88c : bv 32 := 0x0036d693.
Lemma F_7b88c : fetch_word Asan.M.loaded_segments (0x7b8dc : word) = Some W_7b88c.
Proof. vm_refl. Qed.
Lemma D_7b88c : decode_any W_7b88c = Some (ShiftImm ALU_SRL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b890 : bv 32 := 0x009686b3.
Lemma F_7b890 : fetch_word Asan.M.loaded_segments (0x7b8e0 : word) = Some W_7b890.
Proof. vm_refl. Qed.
Lemma D_7b890 : decode_any W_7b890 = Some (Op ALU_ADD 13 13 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b894 : bv 32 := 0xe4068ee3.
Lemma F_7b894 : fetch_word Asan.M.loaded_segments (0x7b8e4 : word) = Some W_7b894.
Proof. vm_refl. Qed.
Lemma D_7b894 : decode_any W_7b894 = Some (Branch BC_EQ 13 0 7772, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b898 : bv 32 := 0x00168693.
Lemma F_7b898 : fetch_word Asan.M.loaded_segments (0x7b8e8 : word) = Some W_7b898.
Proof. vm_refl. Qed.
Lemma D_7b898 : decode_any W_7b898 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b89c : bv 32 := 0xe4d5fae3.
Lemma F_7b89c : fetch_word Asan.M.loaded_segments (0x7b8ec : word) = Some W_7b89c.
Proof. vm_refl. Qed.
Lemma D_7b89c : decode_any W_7b89c = Some (Branch BC_GEU 11 13 7764, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8a0 : bv 32 := 0x0140006f.
Lemma F_7b8a0 : fetch_word Asan.M.loaded_segments (0x7b8f0 : word) = Some W_7b8a0.
Proof. vm_refl. Qed.
Lemma D_7b8a0 : decode_any W_7b8a0 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8a4 : bv 32 := 0x00178793.
Lemma F_7b8a4 : fetch_word Asan.M.loaded_segments (0x7b8f4 : word) = Some W_7b8a4.
Proof. vm_refl. Qed.
Lemma D_7b8a4 : decode_any W_7b8a4 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8a8 : bv 32 := 0x0037d793.
Lemma F_7b8a8 : fetch_word Asan.M.loaded_segments (0x7b8f8 : word) = Some W_7b8a8.
Proof. vm_refl. Qed.
Lemma D_7b8a8 : decode_any W_7b8a8 = Some (ShiftImm ALU_SRL 15 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8ac : bv 32 := 0xfff78793.
Lemma F_7b8ac : fetch_word Asan.M.loaded_segments (0x7b8fc : word) = Some W_7b8ac.
Proof. vm_refl. Qed.
Lemma D_7b8ac : decode_any W_7b8ac = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8b0 : bv 32 := 0xe4b7f0e3.
Lemma F_7b8b0 : fetch_word Asan.M.loaded_segments (0x7b900 : word) = Some W_7b8b0.
Proof. vm_refl. Qed.
Lemma D_7b8b0 : decode_any W_7b8b0 = Some (Branch BC_GEU 15 11 7744, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8b4 : bv 32 := 0xfffa6517.
Lemma F_7b8b4 : fetch_word Asan.M.loaded_segments (0x7b904 : word) = Some W_7b8b4.
Proof. vm_refl. Qed.
Lemma D_7b8b4 : decode_any W_7b8b4 = Some (Auipc 10 1048486, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8b8 : bv 32 := 0xfff99597.
Lemma F_7b8b8 : fetch_word Asan.M.loaded_segments (0x7b908 : word) = Some W_7b8b8.
Proof. vm_refl. Qed.
Lemma D_7b8b8 : decode_any W_7b8b8 = Some (Auipc 11 1048473, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8bc : bv 32 := 0x9d550513.
Lemma F_7b8bc : fetch_word Asan.M.loaded_segments (0x7b90c : word) = Some W_7b8bc.
Proof. vm_refl. Qed.
Lemma D_7b8bc : decode_any W_7b8bc = Some (OpImm ALU_ADD 10 10 2517, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8c0 : bv 32 := 0x88258613.
Lemma F_7b8c0 : fetch_word Asan.M.loaded_segments (0x7b910 : word) = Some W_7b8c0.
Proof. vm_refl. Qed.
Lemma D_7b8c0 : decode_any W_7b8c0 = Some (OpImm ALU_ADD 12 11 2178, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8c4 : bv 32 := 0x03100593.
Lemma F_7b8c4 : fetch_word Asan.M.loaded_segments (0x7b914 : word) = Some W_7b8c4.
Proof. vm_refl. Qed.
Lemma D_7b8c4 : decode_any W_7b8c4 = Some (OpImm ALU_ADD 11 0 49, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8c8 : bv 32 := 0x00000693.
Lemma F_7b8c8 : fetch_word Asan.M.loaded_segments (0x7b918 : word) = Some W_7b8c8.
Proof. vm_refl. Qed.
Lemma D_7b8c8 : decode_any W_7b8c8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8cc : bv 32 := 0x00000713.
Lemma F_7b8cc : fetch_word Asan.M.loaded_segments (0x7b91c : word) = Some W_7b8cc.
Proof. vm_refl. Qed.
Lemma D_7b8cc : decode_any W_7b8cc = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8d0 : bv 32 := 0x1e8180ef.
Lemma F_7b8d0 : fetch_word Asan.M.loaded_segments (0x7b920 : word) = Some W_7b8d0.
Proof. vm_refl. Qed.
Lemma D_7b8d0 : decode_any W_7b8d0 = Some (Jal 1 98792, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8d4 : bv 32 := 0xfffa6517.
Lemma F_7b8d4 : fetch_word Asan.M.loaded_segments (0x7b924 : word) = Some W_7b8d4.
Proof. vm_refl. Qed.
Lemma D_7b8d4 : decode_any W_7b8d4 = Some (Auipc 10 1048486, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8d8 : bv 32 := 0xfffa3597.
Lemma F_7b8d8 : fetch_word Asan.M.loaded_segments (0x7b928 : word) = Some W_7b8d8.
Proof. vm_refl. Qed.
Lemma D_7b8d8 : decode_any W_7b8d8 = Some (Auipc 11 1048483, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8dc : bv 32 := 0x9b550513.
Lemma F_7b8dc : fetch_word Asan.M.loaded_segments (0x7b92c : word) = Some W_7b8dc.
Proof. vm_refl. Qed.
Lemma D_7b8dc : decode_any W_7b8dc = Some (OpImm ALU_ADD 10 10 2485, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8e0 : bv 32 := 0x4b258613.
Lemma F_7b8e0 : fetch_word Asan.M.loaded_segments (0x7b930 : word) = Some W_7b8e0.
Proof. vm_refl. Qed.
Lemma D_7b8e0 : decode_any W_7b8e0 = Some (OpImm ALU_ADD 12 11 1202, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8e4 : bv 32 := 0x02700593.
Lemma F_7b8e4 : fetch_word Asan.M.loaded_segments (0x7b934 : word) = Some W_7b8e4.
Proof. vm_refl. Qed.
Lemma D_7b8e4 : decode_any W_7b8e4 = Some (OpImm ALU_ADD 11 0 39, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8e8 : bv 32 := 0x00000693.
Lemma F_7b8e8 : fetch_word Asan.M.loaded_segments (0x7b938 : word) = Some W_7b8e8.
Proof. vm_refl. Qed.
Lemma D_7b8e8 : decode_any W_7b8e8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8ec : bv 32 := 0x00000713.
Lemma F_7b8ec : fetch_word Asan.M.loaded_segments (0x7b93c : word) = Some W_7b8ec.
Proof. vm_refl. Qed.
Lemma D_7b8ec : decode_any W_7b8ec = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8f0 : bv 32 := 0x1c8180ef.
Lemma F_7b8f0 : fetch_word Asan.M.loaded_segments (0x7b940 : word) = Some W_7b8f0.
Proof. vm_refl. Qed.
Lemma D_7b8f0 : decode_any W_7b8f0 = Some (Jal 1 98760, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8f4 : bv 32 := 0x000be317.
Lemma F_7b8f4 : fetch_word Asan.M.loaded_segments (0x7b944 : word) = Some W_7b8f4.
Proof. vm_refl. Qed.
Lemma D_7b8f4 : decode_any W_7b8f4 = Some (Auipc 6 190, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8f8 : bv 32 := 0x8b433303.
Lemma F_7b8f8 : fetch_word Asan.M.loaded_segments (0x7b948 : word) = Some W_7b8f8.
Proof. vm_refl. Qed.
Lemma D_7b8f8 : decode_any W_7b8f8 = Some (Load SZ8 true 6 6 2228, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b8fc : bv 32 := 0xcc0308e3.
Lemma F_7b8fc : fetch_word Asan.M.loaded_segments (0x7b94c : word) = Some W_7b8fc.
Proof. vm_refl. Qed.
Lemma D_7b8fc : decode_any W_7b8fc = Some (Branch BC_EQ 6 0 7376, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b900 : bv 32 := 0x000be517.
Lemma F_7b900 : fetch_word Asan.M.loaded_segments (0x7b950 : word) = Some W_7b900.
Proof. vm_refl. Qed.
Lemma D_7b900 : decode_any W_7b900 = Some (Auipc 10 190, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b904 : bv 32 := 0x8b053503.
Lemma F_7b904 : fetch_word Asan.M.loaded_segments (0x7b954 : word) = Some W_7b904.
Proof. vm_refl. Qed.
Lemma D_7b904 : decode_any W_7b904 = Some (Load SZ8 true 10 10 2224, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b908 : bv 32 := 0x00052503.
Lemma F_7b908 : fetch_word Asan.M.loaded_segments (0x7b958 : word) = Some W_7b908.
Proof. vm_refl. Qed.
Lemma D_7b908 : decode_any W_7b908 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b90c : bv 32 := 0x04051c63.
Lemma F_7b90c : fetch_word Asan.M.loaded_segments (0x7b95c : word) = Some W_7b90c.
Proof. vm_refl. Qed.
Lemma D_7b90c : decode_any W_7b90c = Some (Branch BC_NE 10 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b910 : bv 32 := 0x0000006f.
Lemma F_7b910 : fetch_word Asan.M.loaded_segments (0x7b960 : word) = Some W_7b910.
Proof. vm_refl. Qed.
Lemma D_7b910 : decode_any W_7b910 = Some (Jal 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b914 : bv 32 := 0xfffa6517.
Lemma F_7b914 : fetch_word Asan.M.loaded_segments (0x7b964 : word) = Some W_7b914.
Proof. vm_refl. Qed.
Lemma D_7b914 : decode_any W_7b914 = Some (Auipc 10 1048486, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b918 : bv 32 := 0xfff98597.
Lemma F_7b918 : fetch_word Asan.M.loaded_segments (0x7b968 : word) = Some W_7b918.
Proof. vm_refl. Qed.
Lemma D_7b918 : decode_any W_7b918 = Some (Auipc 11 1048472, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b91c : bv 32 := 0x97550513.
Lemma F_7b91c : fetch_word Asan.M.loaded_segments (0x7b96c : word) = Some W_7b91c.
Proof. vm_refl. Qed.
Lemma D_7b91c : decode_any W_7b91c = Some (OpImm ALU_ADD 10 10 2421, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b920 : bv 32 := 0xdfe58613.
Lemma F_7b920 : fetch_word Asan.M.loaded_segments (0x7b970 : word) = Some W_7b920.
Proof. vm_refl. Qed.
Lemma D_7b920 : decode_any W_7b920 = Some (OpImm ALU_ADD 12 11 3582, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b924 : bv 32 := 0x03000593.
Lemma F_7b924 : fetch_word Asan.M.loaded_segments (0x7b974 : word) = Some W_7b924.
Proof. vm_refl. Qed.
Lemma D_7b924 : decode_any W_7b924 = Some (OpImm ALU_ADD 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b928 : bv 32 := 0x00000693.
Lemma F_7b928 : fetch_word Asan.M.loaded_segments (0x7b978 : word) = Some W_7b928.
Proof. vm_refl. Qed.
Lemma D_7b928 : decode_any W_7b928 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b92c : bv 32 := 0x00000713.
Lemma F_7b92c : fetch_word Asan.M.loaded_segments (0x7b97c : word) = Some W_7b92c.
Proof. vm_refl. Qed.
Lemma D_7b92c : decode_any W_7b92c = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b930 : bv 32 := 0x188180ef.
Lemma F_7b930 : fetch_word Asan.M.loaded_segments (0x7b980 : word) = Some W_7b930.
Proof. vm_refl. Qed.
Lemma D_7b930 : decode_any W_7b930 = Some (Jal 1 98696, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b934 : bv 32 := 0xfffa6517.
Lemma F_7b934 : fetch_word Asan.M.loaded_segments (0x7b984 : word) = Some W_7b934.
Proof. vm_refl. Qed.
Lemma D_7b934 : decode_any W_7b934 = Some (Auipc 10 1048486, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b938 : bv 32 := 0xfff9e597.
Lemma F_7b938 : fetch_word Asan.M.loaded_segments (0x7b988 : word) = Some W_7b938.
Proof. vm_refl. Qed.
Lemma D_7b938 : decode_any W_7b938 = Some (Auipc 11 1048478, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b93c : bv 32 := 0x95550513.
Lemma F_7b93c : fetch_word Asan.M.loaded_segments (0x7b98c : word) = Some W_7b93c.
Proof. vm_refl. Qed.
Lemma D_7b93c : decode_any W_7b93c = Some (OpImm ALU_ADD 10 10 2389, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b940 : bv 32 := 0x99c58613.
Lemma F_7b940 : fetch_word Asan.M.loaded_segments (0x7b990 : word) = Some W_7b940.
Proof. vm_refl. Qed.
Lemma D_7b940 : decode_any W_7b940 = Some (OpImm ALU_ADD 12 11 2460, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b944 : bv 32 := 0x03200593.
Lemma F_7b944 : fetch_word Asan.M.loaded_segments (0x7b994 : word) = Some W_7b944.
Proof. vm_refl. Qed.
Lemma D_7b944 : decode_any W_7b944 = Some (OpImm ALU_ADD 11 0 50, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b948 : bv 32 := 0x00000693.
Lemma F_7b948 : fetch_word Asan.M.loaded_segments (0x7b998 : word) = Some W_7b948.
Proof. vm_refl. Qed.
Lemma D_7b948 : decode_any W_7b948 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b94c : bv 32 := 0x00000713.
Lemma F_7b94c : fetch_word Asan.M.loaded_segments (0x7b99c : word) = Some W_7b94c.
Proof. vm_refl. Qed.
Lemma D_7b94c : decode_any W_7b94c = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b950 : bv 32 := 0x168180ef.
Lemma F_7b950 : fetch_word Asan.M.loaded_segments (0x7b9a0 : word) = Some W_7b950.
Proof. vm_refl. Qed.
Lemma D_7b950 : decode_any W_7b950 = Some (Jal 1 98664, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b954 : bv 32 := 0xfff97517.
Lemma F_7b954 : fetch_word Asan.M.loaded_segments (0x7b9a4 : word) = Some W_7b954.
Proof. vm_refl. Qed.
Lemma D_7b954 : decode_any W_7b954 = Some (Auipc 10 1048471, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b958 : bv 32 := 0xfdc50513.
Lemma F_7b958 : fetch_word Asan.M.loaded_segments (0x7b9a8 : word) = Some W_7b958.
Proof. vm_refl. Qed.
Lemma D_7b958 : decode_any W_7b958 = Some (OpImm ALU_ADD 10 10 4060, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b95c : bv 32 := 0x2ec0d0ef.
Lemma F_7b95c : fetch_word Asan.M.loaded_segments (0x7b9ac : word) = Some W_7b95c.
Proof. vm_refl. Qed.
Lemma D_7b95c : decode_any W_7b95c = Some (Jal 1 53996, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b960 : bv 32 := 0x08c180ef.
Lemma F_7b960 : fetch_word Asan.M.loaded_segments (0x7b9b0 : word) = Some W_7b960.
Proof. vm_refl. Qed.
Lemma D_7b960 : decode_any W_7b960 = Some (Jal 1 98444, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b964 : bv 32 := 0x1b01a0ef.
Lemma F_7b964 : fetch_word Asan.M.loaded_segments (0x7b9b4 : word) = Some W_7b964.
Proof. vm_refl. Qed.
Lemma D_7b964 : decode_any W_7b964 = Some (Jal 1 106928, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b968 : bv 32 := 0x000be597.
Lemma F_7b968 : fetch_word Asan.M.loaded_segments (0x7b9b8 : word) = Some W_7b968.
Proof. vm_refl. Qed.
Lemma D_7b968 : decode_any W_7b968 = Some (Auipc 11 190, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b96c : bv 32 := 0x8005b583.
Lemma F_7b96c : fetch_word Asan.M.loaded_segments (0x7b9bc : word) = Some W_7b96c.
Proof. vm_refl. Qed.
Lemma D_7b96c : decode_any W_7b96c = Some (Load SZ8 true 11 11 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b970 : bv 32 := 0x0005b583.
Lemma F_7b970 : fetch_word Asan.M.loaded_segments (0x7b9c0 : word) = Some W_7b970.
Proof. vm_refl. Qed.
Lemma D_7b970 : decode_any W_7b970 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b974 : bv 32 := 0xfff58613.
Lemma F_7b974 : fetch_word Asan.M.loaded_segments (0x7b9c4 : word) = Some W_7b974.
Proof. vm_refl. Qed.
Lemma D_7b974 : decode_any W_7b974 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b978 : bv 32 := 0x00c5b6b3.
Lemma F_7b978 : fetch_word Asan.M.loaded_segments (0x7b9c8 : word) = Some W_7b978.
Proof. vm_refl. Qed.
Lemma D_7b978 : decode_any W_7b978 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b97c : bv 32 := 0xfff68693.
Lemma F_7b97c : fetch_word Asan.M.loaded_segments (0x7b9cc : word) = Some W_7b97c.
Proof. vm_refl. Qed.
Lemma D_7b97c : decode_any W_7b97c = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b980 : bv 32 := 0x00c6f6b3.
Lemma F_7b980 : fetch_word Asan.M.loaded_segments (0x7b9d0 : word) = Some W_7b980.
Proof. vm_refl. Qed.
Lemma D_7b980 : decode_any W_7b980 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b984 : bv 32 := 0x04a6f263.
Lemma F_7b984 : fetch_word Asan.M.loaded_segments (0x7b9d4 : word) = Some W_7b984.
Proof. vm_refl. Qed.
Lemma D_7b984 : decode_any W_7b984 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b988 : bv 32 := 0x000bd697.
Lemma F_7b988 : fetch_word Asan.M.loaded_segments (0x7b9d8 : word) = Some W_7b988.
Proof. vm_refl. Qed.
Lemma D_7b988 : decode_any W_7b988 = Some (Auipc 13 189, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b98c : bv 32 := 0x7e86b683.
Lemma F_7b98c : fetch_word Asan.M.loaded_segments (0x7b9dc : word) = Some W_7b98c.
Proof. vm_refl. Qed.
Lemma D_7b98c : decode_any W_7b98c = Some (Load SZ8 true 13 13 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b990 : bv 32 := 0x000bd717.
Lemma F_7b990 : fetch_word Asan.M.loaded_segments (0x7b9e0 : word) = Some W_7b990.
Proof. vm_refl. Qed.
Lemma D_7b990 : decode_any W_7b990 = Some (Auipc 14 189, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b994 : bv 32 := 0x7e873703.
Lemma F_7b994 : fetch_word Asan.M.loaded_segments (0x7b9e4 : word) = Some W_7b994.
Proof. vm_refl. Qed.
Lemma D_7b994 : decode_any W_7b994 = Some (Load SZ8 true 14 14 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b998 : bv 32 := 0x0006b803.
Lemma F_7b998 : fetch_word Asan.M.loaded_segments (0x7b9e8 : word) = Some W_7b998.
Proof. vm_refl. Qed.
Lemma D_7b998 : decode_any W_7b998 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b99c : bv 32 := 0x00073683.
Lemma F_7b99c : fetch_word Asan.M.loaded_segments (0x7b9ec : word) = Some W_7b99c.
Proof. vm_refl. Qed.
Lemma D_7b99c : decode_any W_7b99c = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b9a0 : bv 32 := 0xfff80793.
Lemma F_7b9a0 : fetch_word Asan.M.loaded_segments (0x7b9f0 : word) = Some W_7b9a0.
Proof. vm_refl. Qed.
Lemma D_7b9a0 : decode_any W_7b9a0 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b9a4 : bv 32 := 0x00a7f463.
Lemma F_7b9a4 : fetch_word Asan.M.loaded_segments (0x7b9f4 : word) = Some W_7b9a4.
Proof. vm_refl. Qed.
Lemma D_7b9a4 : decode_any W_7b9a4 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b9ac : bv 32 := 0x000bd717.
Lemma F_7b9ac : fetch_word Asan.M.loaded_segments (0x7b9fc : word) = Some W_7b9ac.
Proof. vm_refl. Qed.
Lemma D_7b9ac : decode_any W_7b9ac = Some (Auipc 14 189, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b9b0 : bv 32 := 0x7d473703.
Lemma F_7b9b0 : fetch_word Asan.M.loaded_segments (0x7ba00 : word) = Some W_7b9b0.
Proof. vm_refl. Qed.
Lemma D_7b9b0 : decode_any W_7b9b0 = Some (Load SZ8 true 14 14 2004, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b9b4 : bv 32 := 0x00073283.
Lemma F_7b9b4 : fetch_word Asan.M.loaded_segments (0x7ba04 : word) = Some W_7b9b4.
Proof. vm_refl. Qed.
Lemma D_7b9b4 : decode_any W_7b9b4 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b9b8 : bv 32 := 0x0032d713.
Lemma F_7b9b8 : fetch_word Asan.M.loaded_segments (0x7ba08 : word) = Some W_7b9b8.
Proof. vm_refl. Qed.
Lemma D_7b9b8 : decode_any W_7b9b8 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b9bc : bv 32 := 0x00b708b3.
Lemma F_7b9bc : fetch_word Asan.M.loaded_segments (0x7ba0c : word) = Some W_7b9bc.
Proof. vm_refl. Qed.
Lemma D_7b9bc : decode_any W_7b9bc = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b9c0 : bv 32 := 0x00a2ea63.
Lemma F_7b9c0 : fetch_word Asan.M.loaded_segments (0x7ba10 : word) = Some W_7b9c0.
Proof. vm_refl. Qed.
Lemma D_7b9c0 : decode_any W_7b9c0 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b9c4 : bv 32 := 0x00a8f863.
Lemma F_7b9c4 : fetch_word Asan.M.loaded_segments (0x7ba14 : word) = Some W_7b9c4.
Proof. vm_refl. Qed.
Lemma D_7b9c4 : decode_any W_7b9c4 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b9c8 : bv 32 := 0x00355513.
Lemma F_7b9c8 : fetch_word Asan.M.loaded_segments (0x7ba18 : word) = Some W_7b9c8.
Proof. vm_refl. Qed.
Lemma D_7b9c8 : decode_any W_7b9c8 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b9cc : bv 32 := 0x00a58533.
Lemma F_7b9cc : fetch_word Asan.M.loaded_segments (0x7ba1c : word) = Some W_7b9cc.
Proof. vm_refl. Qed.
Lemma D_7b9cc : decode_any W_7b9cc = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b9d0 : bv 32 := 0x00008067.
Lemma F_7b9d0 : fetch_word Asan.M.loaded_segments (0x7ba20 : word) = Some W_7b9d0.
Proof. vm_refl. Qed.
Lemma D_7b9d0 : decode_any W_7b9d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
