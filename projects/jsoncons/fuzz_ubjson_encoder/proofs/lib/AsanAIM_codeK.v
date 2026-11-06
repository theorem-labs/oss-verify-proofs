(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_7b4b4 : bv 32 := 0xfff48693.
Lemma F_7b4b4 : fetch_word Asan.M.loaded_segments (0x7b504 : word) = Some W_7b4b4.
Proof. vm_refl. Qed.
Lemma D_7b4b4 : decode_any W_7b4b4 = Some (OpImm ALU_ADD 13 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4b8 : bv 32 := 0x00d4b733.
Lemma F_7b4b8 : fetch_word Asan.M.loaded_segments (0x7b508 : word) = Some W_7b4b8.
Proof. vm_refl. Qed.
Lemma D_7b4b8 : decode_any W_7b4b8 = Some (Op ALU_SLTU 14 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4bc : bv 32 := 0xfff70713.
Lemma F_7b4bc : fetch_word Asan.M.loaded_segments (0x7b50c : word) = Some W_7b4bc.
Proof. vm_refl. Qed.
Lemma D_7b4bc : decode_any W_7b4bc = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4c0 : bv 32 := 0x00d77733.
Lemma F_7b4c0 : fetch_word Asan.M.loaded_segments (0x7b510 : word) = Some W_7b4c0.
Proof. vm_refl. Qed.
Lemma D_7b4c0 : decode_any W_7b4c0 = Some (Op ALU_AND 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4c4 : bv 32 := 0x1ca77c63.
Lemma F_7b4c4 : fetch_word Asan.M.loaded_segments (0x7b514 : word) = Some W_7b4c4.
Proof. vm_refl. Qed.
Lemma D_7b4c4 : decode_any W_7b4c4 = Some (Branch BC_GEU 14 10 472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4c8 : bv 32 := 0x000be797.
Lemma F_7b4c8 : fetch_word Asan.M.loaded_segments (0x7b518 : word) = Some W_7b4c8.
Proof. vm_refl. Qed.
Lemma D_7b4c8 : decode_any W_7b4c8 = Some (Auipc 15 190, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4cc : bv 32 := 0xca87b783.
Lemma F_7b4cc : fetch_word Asan.M.loaded_segments (0x7b51c : word) = Some W_7b4cc.
Proof. vm_refl. Qed.
Lemma D_7b4cc : decode_any W_7b4cc = Some (Load SZ8 true 15 15 3240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4d0 : bv 32 := 0x000be817.
Lemma F_7b4d0 : fetch_word Asan.M.loaded_segments (0x7b520 : word) = Some W_7b4d0.
Proof. vm_refl. Qed.
Lemma D_7b4d0 : decode_any W_7b4d0 = Some (Auipc 16 190, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4d4 : bv 32 := 0xca883803.
Lemma F_7b4d4 : fetch_word Asan.M.loaded_segments (0x7b524 : word) = Some W_7b4d4.
Proof. vm_refl. Qed.
Lemma D_7b4d4 : decode_any W_7b4d4 = Some (Load SZ8 true 16 16 3240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4d8 : bv 32 := 0x0007b883.
Lemma F_7b4d8 : fetch_word Asan.M.loaded_segments (0x7b528 : word) = Some W_7b4d8.
Proof. vm_refl. Qed.
Lemma D_7b4d8 : decode_any W_7b4d8 = Some (Load SZ8 true 17 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4dc : bv 32 := 0x00083783.
Lemma F_7b4dc : fetch_word Asan.M.loaded_segments (0x7b52c : word) = Some W_7b4dc.
Proof. vm_refl. Qed.
Lemma D_7b4dc : decode_any W_7b4dc = Some (Load SZ8 true 15 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4e0 : bv 32 := 0xfff88813.
Lemma F_7b4e0 : fetch_word Asan.M.loaded_segments (0x7b530 : word) = Some W_7b4e0.
Proof. vm_refl. Qed.
Lemma D_7b4e0 : decode_any W_7b4e0 = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4e4 : bv 32 := 0x00a87463.
Lemma F_7b4e4 : fetch_word Asan.M.loaded_segments (0x7b534 : word) = Some W_7b4e4.
Proof. vm_refl. Qed.
Lemma D_7b4e4 : decode_any W_7b4e4 = Some (Branch BC_GEU 16 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4e8 : bv 32 := 0x1aa7fa63.
Lemma F_7b4e8 : fetch_word Asan.M.loaded_segments (0x7b538 : word) = Some W_7b4e8.
Proof. vm_refl. Qed.
Lemma D_7b4e8 : decode_any W_7b4e8 = Some (Branch BC_GEU 15 10 436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4ec : bv 32 := 0x000be297.
Lemma F_7b4ec : fetch_word Asan.M.loaded_segments (0x7b53c : word) = Some W_7b4ec.
Proof. vm_refl. Qed.
Lemma D_7b4ec : decode_any W_7b4ec = Some (Auipc 5 190, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4f0 : bv 32 := 0xc942b283.
Lemma F_7b4f0 : fetch_word Asan.M.loaded_segments (0x7b540 : word) = Some W_7b4f0.
Proof. vm_refl. Qed.
Lemma D_7b4f0 : decode_any W_7b4f0 = Some (Load SZ8 true 5 5 3220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4f4 : bv 32 := 0x0002be03.
Lemma F_7b4f4 : fetch_word Asan.M.loaded_segments (0x7b544 : word) = Some W_7b4f4.
Proof. vm_refl. Qed.
Lemma D_7b4f4 : decode_any W_7b4f4 = Some (Load SZ8 true 28 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4f8 : bv 32 := 0x003e5313.
Lemma F_7b4f8 : fetch_word Asan.M.loaded_segments (0x7b548 : word) = Some W_7b4f8.
Proof. vm_refl. Qed.
Lemma D_7b4f8 : decode_any W_7b4f8 = Some (ShiftImm ALU_SRL 6 28 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b4fc : bv 32 := 0x009303b3.
Lemma F_7b4fc : fetch_word Asan.M.loaded_segments (0x7b54c : word) = Some W_7b4fc.
Proof. vm_refl. Qed.
Lemma D_7b4fc : decode_any W_7b4fc = Some (Op ALU_ADD 7 6 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b500 : bv 32 := 0x00ae6463.
Lemma F_7b500 : fetch_word Asan.M.loaded_segments (0x7b550 : word) = Some W_7b500.
Proof. vm_refl. Qed.
Lemma D_7b500 : decode_any W_7b500 = Some (Branch BC_LTU 28 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b504 : bv 32 := 0x0ca3e463.
Lemma F_7b504 : fetch_word Asan.M.loaded_segments (0x7b554 : word) = Some W_7b504.
Proof. vm_refl. Qed.
Lemma D_7b504 : decode_any W_7b504 = Some (Branch BC_LTU 7 10 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b508 : bv 32 := 0x000bee17.
Lemma F_7b508 : fetch_word Asan.M.loaded_segments (0x7b558 : word) = Some W_7b508.
Proof. vm_refl. Qed.
Lemma D_7b508 : decode_any W_7b508 = Some (Auipc 28 190, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b50c : bv 32 := 0xc58e3e03.
Lemma F_7b50c : fetch_word Asan.M.loaded_segments (0x7b55c : word) = Some W_7b50c.
Proof. vm_refl. Qed.
Lemma D_7b50c : decode_any W_7b50c = Some (Load SZ8 true 28 28 3160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b510 : bv 32 := 0x04ee4e03.
Lemma F_7b510 : fetch_word Asan.M.loaded_segments (0x7b560 : word) = Some W_7b510.
Proof. vm_refl. Qed.
Lemma D_7b510 : decode_any W_7b510 = Some (Load SZ1 false 28 28 78, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b514 : bv 32 := 0x3e0e1063.
Lemma F_7b514 : fetch_word Asan.M.loaded_segments (0x7b564 : word) = Some W_7b514.
Proof. vm_refl. Qed.
Lemma D_7b514 : decode_any W_7b514 = Some (Branch BC_NE 28 0 992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b518 : bv 32 := 0x04088e63.
Lemma F_7b518 : fetch_word Asan.M.loaded_segments (0x7b568 : word) = Some W_7b518.
Proof. vm_refl. Qed.
Lemma D_7b518 : decode_any W_7b518 = Some (Branch BC_EQ 17 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b51c : bv 32 := 0x0038d393.
Lemma F_7b51c : fetch_word Asan.M.loaded_segments (0x7b56c : word) = Some W_7b51c.
Proof. vm_refl. Qed.
Lemma D_7b51c : decode_any W_7b51c = Some (ShiftImm ALU_SRL 7 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b520 : bv 32 := 0x00d383b3.
Lemma F_7b520 : fetch_word Asan.M.loaded_segments (0x7b570 : word) = Some W_7b520.
Proof. vm_refl. Qed.
Lemma D_7b520 : decode_any W_7b520 = Some (Op ALU_ADD 7 7 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b524 : bv 32 := 0x06a3fe63.
Lemma F_7b524 : fetch_word Asan.M.loaded_segments (0x7b574 : word) = Some W_7b524.
Proof. vm_refl. Qed.
Lemma D_7b524 : decode_any W_7b524 = Some (Branch BC_GEU 7 10 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b528 : bv 32 := 0x00148393.
Lemma F_7b528 : fetch_word Asan.M.loaded_segments (0x7b578 : word) = Some W_7b528.
Proof. vm_refl. Qed.
Lemma D_7b528 : decode_any W_7b528 = Some (OpImm ALU_ADD 7 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b52c : bv 32 := 0x00a86863.
Lemma F_7b52c : fetch_word Asan.M.loaded_segments (0x7b57c : word) = Some W_7b52c.
Proof. vm_refl. Qed.
Lemma D_7b52c : decode_any W_7b52c = Some (Branch BC_LTU 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b530 : bv 32 := 0x0037de13.
Lemma F_7b530 : fetch_word Asan.M.loaded_segments (0x7b580 : word) = Some W_7b530.
Proof. vm_refl. Qed.
Lemma D_7b530 : decode_any W_7b530 = Some (ShiftImm ALU_SRL 28 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b534 : bv 32 := 0x007e0e33.
Lemma F_7b534 : fetch_word Asan.M.loaded_segments (0x7b584 : word) = Some W_7b534.
Proof. vm_refl. Qed.
Lemma D_7b534 : decode_any W_7b534 = Some (Op ALU_ADD 28 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b538 : bv 32 := 0x09c57a63.
Lemma F_7b538 : fetch_word Asan.M.loaded_segments (0x7b588 : word) = Some W_7b538.
Proof. vm_refl. Qed.
Lemma D_7b538 : decode_any W_7b538 = Some (Branch BC_GEU 10 28 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b53c : bv 32 := 0x00178e13.
Lemma F_7b53c : fetch_word Asan.M.loaded_segments (0x7b58c : word) = Some W_7b53c.
Proof. vm_refl. Qed.
Lemma D_7b53c : decode_any W_7b53c = Some (OpImm ALU_ADD 28 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b540 : bv 32 := 0x3bc56a63.
Lemma F_7b540 : fetch_word Asan.M.loaded_segments (0x7b590 : word) = Some W_7b540.
Proof. vm_refl. Qed.
Lemma D_7b540 : decode_any W_7b540 = Some (Branch BC_LTU 10 28 948, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b544 : bv 32 := 0x00730333.
Lemma F_7b544 : fetch_word Asan.M.loaded_segments (0x7b594 : word) = Some W_7b544.
Proof. vm_refl. Qed.
Lemma D_7b544 : decode_any W_7b544 = Some (Op ALU_ADD 6 6 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b548 : bv 32 := 0x00335313.
Lemma F_7b548 : fetch_word Asan.M.loaded_segments (0x7b598 : word) = Some W_7b548.
Proof. vm_refl. Qed.
Lemma D_7b548 : decode_any W_7b548 = Some (ShiftImm ALU_SRL 6 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b54c : bv 32 := 0x0480006f.
Lemma F_7b54c : fetch_word Asan.M.loaded_segments (0x7b59c : word) = Some W_7b54c.
Proof. vm_refl. Qed.
Lemma D_7b54c : decode_any W_7b54c = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b550 : bv 32 := 0x03813083.
Lemma F_7b550 : fetch_word Asan.M.loaded_segments (0x7b5a0 : word) = Some W_7b550.
Proof. vm_refl. Qed.
Lemma D_7b550 : decode_any W_7b550 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b554 : bv 32 := 0x03013403.
Lemma F_7b554 : fetch_word Asan.M.loaded_segments (0x7b5a4 : word) = Some W_7b554.
Proof. vm_refl. Qed.
Lemma D_7b554 : decode_any W_7b554 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b558 : bv 32 := 0x02813483.
Lemma F_7b558 : fetch_word Asan.M.loaded_segments (0x7b5a8 : word) = Some W_7b558.
Proof. vm_refl. Qed.
Lemma D_7b558 : decode_any W_7b558 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b55c : bv 32 := 0x02013903.
Lemma F_7b55c : fetch_word Asan.M.loaded_segments (0x7b5ac : word) = Some W_7b55c.
Proof. vm_refl. Qed.
Lemma D_7b55c : decode_any W_7b55c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b560 : bv 32 := 0x01813983.
Lemma F_7b560 : fetch_word Asan.M.loaded_segments (0x7b5b0 : word) = Some W_7b560.
Proof. vm_refl. Qed.
Lemma D_7b560 : decode_any W_7b560 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b564 : bv 32 := 0x01013a03.
Lemma F_7b564 : fetch_word Asan.M.loaded_segments (0x7b5b4 : word) = Some W_7b564.
Proof. vm_refl. Qed.
Lemma D_7b564 : decode_any W_7b564 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b568 : bv 32 := 0x00813a83.
Lemma F_7b568 : fetch_word Asan.M.loaded_segments (0x7b5b8 : word) = Some W_7b568.
Proof. vm_refl. Qed.
Lemma D_7b568 : decode_any W_7b568 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b56c : bv 32 := 0x04010113.
Lemma F_7b56c : fetch_word Asan.M.loaded_segments (0x7b5bc : word) = Some W_7b56c.
Proof. vm_refl. Qed.
Lemma D_7b56c : decode_any W_7b56c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b570 : bv 32 := 0x00008067.
Lemma F_7b570 : fetch_word Asan.M.loaded_segments (0x7b5c0 : word) = Some W_7b570.
Proof. vm_refl. Qed.
Lemma D_7b570 : decode_any W_7b570 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b574 : bv 32 := 0x04048463.
Lemma F_7b574 : fetch_word Asan.M.loaded_segments (0x7b5c4 : word) = Some W_7b574.
Proof. vm_refl. Qed.
Lemma D_7b574 : decode_any W_7b574 = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b578 : bv 32 := 0x0036d313.
Lemma F_7b578 : fetch_word Asan.M.loaded_segments (0x7b5c8 : word) = Some W_7b578.
Proof. vm_refl. Qed.
Lemma D_7b578 : decode_any W_7b578 = Some (ShiftImm ALU_SRL 6 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b57c : bv 32 := 0x00930333.
Lemma F_7b57c : fetch_word Asan.M.loaded_segments (0x7b5cc : word) = Some W_7b57c.
Proof. vm_refl. Qed.
Lemma D_7b57c : decode_any W_7b57c = Some (Op ALU_ADD 6 6 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b580 : bv 32 := 0x00030663.
Lemma F_7b580 : fetch_word Asan.M.loaded_segments (0x7b5d0 : word) = Some W_7b580.
Proof. vm_refl. Qed.
Lemma D_7b580 : decode_any W_7b580 = Some (Branch BC_EQ 6 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b584 : bv 32 := 0x00130313.
Lemma F_7b584 : fetch_word Asan.M.loaded_segments (0x7b5d4 : word) = Some W_7b584.
Proof. vm_refl. Qed.
Lemma D_7b584 : decode_any W_7b584 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b588 : bv 32 := 0x36656663.
Lemma F_7b588 : fetch_word Asan.M.loaded_segments (0x7b5d8 : word) = Some W_7b588.
Proof. vm_refl. Qed.
Lemma D_7b588 : decode_any W_7b588 = Some (Branch BC_LTU 10 6 876, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b58c : bv 32 := 0x00138393.
Lemma F_7b58c : fetch_word Asan.M.loaded_segments (0x7b5dc : word) = Some W_7b58c.
Proof. vm_refl. Qed.
Lemma D_7b58c : decode_any W_7b58c = Some (OpImm ALU_ADD 7 7 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b590 : bv 32 := 0x0033d313.
Lemma F_7b590 : fetch_word Asan.M.loaded_segments (0x7b5e0 : word) = Some W_7b590.
Proof. vm_refl. Qed.
Lemma D_7b590 : decode_any W_7b590 = Some (ShiftImm ALU_SRL 6 7 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b594 : bv 32 := 0x00d30333.
Lemma F_7b594 : fetch_word Asan.M.loaded_segments (0x7b5e4 : word) = Some W_7b594.
Proof. vm_refl. Qed.
Lemma D_7b594 : decode_any W_7b594 = Some (Op ALU_ADD 6 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b598 : bv 32 := 0x02a37a63.
Lemma F_7b598 : fetch_word Asan.M.loaded_segments (0x7b5e8 : word) = Some W_7b598.
Proof. vm_refl. Qed.
Lemma D_7b598 : decode_any W_7b598 = Some (Branch BC_GEU 6 10 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b59c : bv 32 := 0x3580006f.
Lemma F_7b59c : fetch_word Asan.M.loaded_segments (0x7b5ec : word) = Some W_7b59c.
Proof. vm_refl. Qed.
Lemma D_7b59c : decode_any W_7b59c = Some (Jal 0 856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5a0 : bv 32 := 0x02048663.
Lemma F_7b5a0 : fetch_word Asan.M.loaded_segments (0x7b5f0 : word) = Some W_7b5a0.
Proof. vm_refl. Qed.
Lemma D_7b5a0 : decode_any W_7b5a0 = Some (Branch BC_EQ 9 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5a4 : bv 32 := 0x0036d313.
Lemma F_7b5a4 : fetch_word Asan.M.loaded_segments (0x7b5f4 : word) = Some W_7b5a4.
Proof. vm_refl. Qed.
Lemma D_7b5a4 : decode_any W_7b5a4 = Some (ShiftImm ALU_SRL 6 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5a8 : bv 32 := 0x00930333.
Lemma F_7b5a8 : fetch_word Asan.M.loaded_segments (0x7b5f8 : word) = Some W_7b5a8.
Proof. vm_refl. Qed.
Lemma D_7b5a8 : decode_any W_7b5a8 = Some (Op ALU_ADD 6 6 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5ac : bv 32 := 0x02030063.
Lemma F_7b5ac : fetch_word Asan.M.loaded_segments (0x7b5fc : word) = Some W_7b5ac.
Proof. vm_refl. Qed.
Lemma D_7b5ac : decode_any W_7b5ac = Some (Branch BC_EQ 6 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5b0 : bv 32 := 0x00130313.
Lemma F_7b5b0 : fetch_word Asan.M.loaded_segments (0x7b600 : word) = Some W_7b5b0.
Proof. vm_refl. Qed.
Lemma D_7b5b0 : decode_any W_7b5b0 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5b4 : bv 32 := 0x00657c63.
Lemma F_7b5b4 : fetch_word Asan.M.loaded_segments (0x7b604 : word) = Some W_7b5b4.
Proof. vm_refl. Qed.
Lemma D_7b5b4 : decode_any W_7b5b4 = Some (Branch BC_GEU 10 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5b8 : bv 32 := 0x33c0006f.
Lemma F_7b5b8 : fetch_word Asan.M.loaded_segments (0x7b608 : word) = Some W_7b5b8.
Proof. vm_refl. Qed.
Lemma D_7b5b8 : decode_any W_7b5b8 = Some (Jal 0 828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5bc : bv 32 := 0x00130313.
Lemma F_7b5bc : fetch_word Asan.M.loaded_segments (0x7b60c : word) = Some W_7b5bc.
Proof. vm_refl. Qed.
Lemma D_7b5bc : decode_any W_7b5bc = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5c0 : bv 32 := 0x00335313.
Lemma F_7b5c0 : fetch_word Asan.M.loaded_segments (0x7b610 : word) = Some W_7b5c0.
Proof. vm_refl. Qed.
Lemma D_7b5c0 : decode_any W_7b5c0 = Some (ShiftImm ALU_SRL 6 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5c4 : bv 32 := 0xfff30313.
Lemma F_7b5c4 : fetch_word Asan.M.loaded_segments (0x7b614 : word) = Some W_7b5c4.
Proof. vm_refl. Qed.
Lemma D_7b5c4 : decode_any W_7b5c4 = Some (OpImm ALU_ADD 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5c8 : bv 32 := 0x32a36663.
Lemma F_7b5c8 : fetch_word Asan.M.loaded_segments (0x7b618 : word) = Some W_7b5c8.
Proof. vm_refl. Qed.
Lemma D_7b5c8 : decode_any W_7b5c8 = Some (Branch BC_LTU 6 10 812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5cc : bv 32 := 0x0002b383.
Lemma F_7b5cc : fetch_word Asan.M.loaded_segments (0x7b61c : word) = Some W_7b5cc.
Proof. vm_refl. Qed.
Lemma D_7b5cc : decode_any W_7b5cc = Some (Load SZ8 true 7 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5d0 : bv 32 := 0x0033d293.
Lemma F_7b5d0 : fetch_word Asan.M.loaded_segments (0x7b620 : word) = Some W_7b5d0.
Proof. vm_refl. Qed.
Lemma D_7b5d0 : decode_any W_7b5d0 = Some (ShiftImm ALU_SRL 5 7 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5d4 : bv 32 := 0x00928333.
Lemma F_7b5d4 : fetch_word Asan.M.loaded_segments (0x7b624 : word) = Some W_7b5d4.
Proof. vm_refl. Qed.
Lemma D_7b5d4 : decode_any W_7b5d4 = Some (Op ALU_ADD 6 5 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5d8 : bv 32 := 0x00a3e463.
Lemma F_7b5d8 : fetch_word Asan.M.loaded_segments (0x7b628 : word) = Some W_7b5d8.
Proof. vm_refl. Qed.
Lemma D_7b5d8 : decode_any W_7b5d8 = Some (Branch BC_LTU 7 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5dc : bv 32 := 0x0ca36063.
Lemma F_7b5dc : fetch_word Asan.M.loaded_segments (0x7b62c : word) = Some W_7b5dc.
Proof. vm_refl. Qed.
Lemma D_7b5dc : decode_any W_7b5dc = Some (Branch BC_LTU 6 10 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5e0 : bv 32 := 0x000be397.
Lemma F_7b5e0 : fetch_word Asan.M.loaded_segments (0x7b630 : word) = Some W_7b5e0.
Proof. vm_refl. Qed.
Lemma D_7b5e0 : decode_any W_7b5e0 = Some (Auipc 7 190, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5e4 : bv 32 := 0xb803b383.
Lemma F_7b5e4 : fetch_word Asan.M.loaded_segments (0x7b634 : word) = Some W_7b5e4.
Proof. vm_refl. Qed.
Lemma D_7b5e4 : decode_any W_7b5e4 = Some (Load SZ8 true 7 7 2944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5e8 : bv 32 := 0x04e3c383.
Lemma F_7b5e8 : fetch_word Asan.M.loaded_segments (0x7b638 : word) = Some W_7b5e8.
Proof. vm_refl. Qed.
Lemma D_7b5e8 : decode_any W_7b5e8 = Some (Load SZ1 false 7 7 78, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5ec : bv 32 := 0x08039063.
Lemma F_7b5ec : fetch_word Asan.M.loaded_segments (0x7b63c : word) = Some W_7b5ec.
Proof. vm_refl. Qed.
Lemma D_7b5ec : decode_any W_7b5ec = Some (Branch BC_NE 7 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5f0 : bv 32 := 0x02088c63.
Lemma F_7b5f0 : fetch_word Asan.M.loaded_segments (0x7b640 : word) = Some W_7b5f0.
Proof. vm_refl. Qed.
Lemma D_7b5f0 : decode_any W_7b5f0 = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5f4 : bv 32 := 0x0038d893.
Lemma F_7b5f4 : fetch_word Asan.M.loaded_segments (0x7b644 : word) = Some W_7b5f4.
Proof. vm_refl. Qed.
Lemma D_7b5f4 : decode_any W_7b5f4 = Some (ShiftImm ALU_SRL 17 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5f8 : bv 32 := 0x00d888b3.
Lemma F_7b5f8 : fetch_word Asan.M.loaded_segments (0x7b648 : word) = Some W_7b5f8.
Proof. vm_refl. Qed.
Lemma D_7b5f8 : decode_any W_7b5f8 = Some (Op ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b5fc : bv 32 := 0x04a8fc63.
Lemma F_7b5fc : fetch_word Asan.M.loaded_segments (0x7b64c : word) = Some W_7b5fc.
Proof. vm_refl. Qed.
Lemma D_7b5fc : decode_any W_7b5fc = Some (Branch BC_GEU 17 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b600 : bv 32 := 0x00148893.
Lemma F_7b600 : fetch_word Asan.M.loaded_segments (0x7b650 : word) = Some W_7b600.
Proof. vm_refl. Qed.
Lemma D_7b600 : decode_any W_7b600 = Some (OpImm ALU_ADD 17 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b604 : bv 32 := 0x00a86863.
Lemma F_7b604 : fetch_word Asan.M.loaded_segments (0x7b654 : word) = Some W_7b604.
Proof. vm_refl. Qed.
Lemma D_7b604 : decode_any W_7b604 = Some (Branch BC_LTU 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b608 : bv 32 := 0x0037d813.
Lemma F_7b608 : fetch_word Asan.M.loaded_segments (0x7b658 : word) = Some W_7b608.
Proof. vm_refl. Qed.
Lemma D_7b608 : decode_any W_7b608 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b60c : bv 32 := 0x01180833.
Lemma F_7b60c : fetch_word Asan.M.loaded_segments (0x7b65c : word) = Some W_7b60c.
Proof. vm_refl. Qed.
Lemma D_7b60c : decode_any W_7b60c = Some (Op ALU_ADD 16 16 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b610 : bv 32 := 0x09057663.
Lemma F_7b610 : fetch_word Asan.M.loaded_segments (0x7b660 : word) = Some W_7b610.
Proof. vm_refl. Qed.
Lemma D_7b610 : decode_any W_7b610 = Some (Branch BC_GEU 10 16 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b614 : bv 32 := 0x00178793.
Lemma F_7b614 : fetch_word Asan.M.loaded_segments (0x7b664 : word) = Some W_7b614.
Proof. vm_refl. Qed.
Lemma D_7b614 : decode_any W_7b614 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b618 : bv 32 := 0x04f56a63.
Lemma F_7b618 : fetch_word Asan.M.loaded_segments (0x7b668 : word) = Some W_7b618.
Proof. vm_refl. Qed.
Lemma D_7b618 : decode_any W_7b618 = Some (Branch BC_LTU 10 15 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b61c : bv 32 := 0x011288b3.
Lemma F_7b61c : fetch_word Asan.M.loaded_segments (0x7b66c : word) = Some W_7b61c.
Proof. vm_refl. Qed.
Lemma D_7b61c : decode_any W_7b61c = Some (Op ALU_ADD 17 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b620 : bv 32 := 0x0038d793.
Lemma F_7b620 : fetch_word Asan.M.loaded_segments (0x7b670 : word) = Some W_7b620.
Proof. vm_refl. Qed.
Lemma D_7b620 : decode_any W_7b620 = Some (ShiftImm ALU_SRL 15 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b624 : bv 32 := 0x0240006f.
Lemma F_7b624 : fetch_word Asan.M.loaded_segments (0x7b674 : word) = Some W_7b624.
Proof. vm_refl. Qed.
Lemma D_7b624 : decode_any W_7b624 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b628 : bv 32 := 0x06048263.
Lemma F_7b628 : fetch_word Asan.M.loaded_segments (0x7b678 : word) = Some W_7b628.
Proof. vm_refl. Qed.
Lemma D_7b628 : decode_any W_7b628 = Some (Branch BC_EQ 9 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b62c : bv 32 := 0x0036d793.
Lemma F_7b62c : fetch_word Asan.M.loaded_segments (0x7b67c : word) = Some W_7b62c.
Proof. vm_refl. Qed.
Lemma D_7b62c : decode_any W_7b62c = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b630 : bv 32 := 0x009787b3.
Lemma F_7b630 : fetch_word Asan.M.loaded_segments (0x7b680 : word) = Some W_7b630.
Proof. vm_refl. Qed.
Lemma D_7b630 : decode_any W_7b630 = Some (Op ALU_ADD 15 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b634 : bv 32 := 0x00078663.
Lemma F_7b634 : fetch_word Asan.M.loaded_segments (0x7b684 : word) = Some W_7b634.
Proof. vm_refl. Qed.
Lemma D_7b634 : decode_any W_7b634 = Some (Branch BC_EQ 15 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b638 : bv 32 := 0x00178793.
Lemma F_7b638 : fetch_word Asan.M.loaded_segments (0x7b688 : word) = Some W_7b638.
Proof. vm_refl. Qed.
Lemma D_7b638 : decode_any W_7b638 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b63c : bv 32 := 0x02f56863.
Lemma F_7b63c : fetch_word Asan.M.loaded_segments (0x7b68c : word) = Some W_7b63c.
Proof. vm_refl. Qed.
Lemma D_7b63c : decode_any W_7b63c = Some (Branch BC_LTU 10 15 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b640 : bv 32 := 0x00130313.
Lemma F_7b640 : fetch_word Asan.M.loaded_segments (0x7b690 : word) = Some W_7b640.
Proof. vm_refl. Qed.
Lemma D_7b640 : decode_any W_7b640 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b644 : bv 32 := 0x00335793.
Lemma F_7b644 : fetch_word Asan.M.loaded_segments (0x7b694 : word) = Some W_7b644.
Proof. vm_refl. Qed.
Lemma D_7b644 : decode_any W_7b644 = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b648 : bv 32 := 0x00d787b3.
Lemma F_7b648 : fetch_word Asan.M.loaded_segments (0x7b698 : word) = Some W_7b648.
Proof. vm_refl. Qed.
Lemma D_7b648 : decode_any W_7b648 = Some (Op ALU_ADD 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b64c : bv 32 := 0x04a7f863.
Lemma F_7b64c : fetch_word Asan.M.loaded_segments (0x7b69c : word) = Some W_7b64c.
Proof. vm_refl. Qed.
Lemma D_7b64c : decode_any W_7b64c = Some (Branch BC_GEU 15 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b650 : bv 32 := 0x01c0006f.
Lemma F_7b650 : fetch_word Asan.M.loaded_segments (0x7b6a0 : word) = Some W_7b650.
Proof. vm_refl. Qed.
Lemma D_7b650 : decode_any W_7b650 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b654 : bv 32 := 0x04048463.
Lemma F_7b654 : fetch_word Asan.M.loaded_segments (0x7b6a4 : word) = Some W_7b654.
Proof. vm_refl. Qed.
Lemma D_7b654 : decode_any W_7b654 = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b658 : bv 32 := 0x0036d793.
Lemma F_7b658 : fetch_word Asan.M.loaded_segments (0x7b6a8 : word) = Some W_7b658.
Proof. vm_refl. Qed.
Lemma D_7b658 : decode_any W_7b658 = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b65c : bv 32 := 0x009787b3.
Lemma F_7b65c : fetch_word Asan.M.loaded_segments (0x7b6ac : word) = Some W_7b65c.
Proof. vm_refl. Qed.
Lemma D_7b65c : decode_any W_7b65c = Some (Op ALU_ADD 15 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b660 : bv 32 := 0x02078e63.
Lemma F_7b660 : fetch_word Asan.M.loaded_segments (0x7b6b0 : word) = Some W_7b660.
Proof. vm_refl. Qed.
Lemma D_7b660 : decode_any W_7b660 = Some (Branch BC_EQ 15 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b664 : bv 32 := 0x00178793.
Lemma F_7b664 : fetch_word Asan.M.loaded_segments (0x7b6b4 : word) = Some W_7b664.
Proof. vm_refl. Qed.
Lemma D_7b664 : decode_any W_7b664 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b668 : bv 32 := 0x02f57a63.
Lemma F_7b668 : fetch_word Asan.M.loaded_segments (0x7b6b8 : word) = Some W_7b668.
Proof. vm_refl. Qed.
Lemma D_7b668 : decode_any W_7b668 = Some (Branch BC_GEU 10 15 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b66c : bv 32 := 0xfffa6517.
Lemma F_7b66c : fetch_word Asan.M.loaded_segments (0x7b6bc : word) = Some W_7b66c.
Proof. vm_refl. Qed.
Lemma D_7b66c : decode_any W_7b66c = Some (Auipc 10 1048486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b670 : bv 32 := 0xfff9d597.
Lemma F_7b670 : fetch_word Asan.M.loaded_segments (0x7b6c0 : word) = Some W_7b670.
Proof. vm_refl. Qed.
Lemma D_7b670 : decode_any W_7b670 = Some (Auipc 11 1048477, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b674 : bv 32 := 0xc1d50513.
Lemma F_7b674 : fetch_word Asan.M.loaded_segments (0x7b6c4 : word) = Some W_7b674.
Proof. vm_refl. Qed.
Lemma D_7b674 : decode_any W_7b674 = Some (OpImm ALU_ADD 10 10 3101, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b678 : bv 32 := 0x23e58613.
Lemma F_7b678 : fetch_word Asan.M.loaded_segments (0x7b6c8 : word) = Some W_7b678.
Proof. vm_refl. Qed.
Lemma D_7b678 : decode_any W_7b678 = Some (OpImm ALU_ADD 12 11 574, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b67c : bv 32 := 0x02f00593.
Lemma F_7b67c : fetch_word Asan.M.loaded_segments (0x7b6cc : word) = Some W_7b67c.
Proof. vm_refl. Qed.
Lemma D_7b67c : decode_any W_7b67c = Some (OpImm ALU_ADD 11 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b680 : bv 32 := 0x00000693.
Lemma F_7b680 : fetch_word Asan.M.loaded_segments (0x7b6d0 : word) = Some W_7b680.
Proof. vm_refl. Qed.
Lemma D_7b680 : decode_any W_7b680 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b684 : bv 32 := 0x00000713.
Lemma F_7b684 : fetch_word Asan.M.loaded_segments (0x7b6d4 : word) = Some W_7b684.
Proof. vm_refl. Qed.
Lemma D_7b684 : decode_any W_7b684 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b688 : bv 32 := 0x430180ef.
Lemma F_7b688 : fetch_word Asan.M.loaded_segments (0x7b6d8 : word) = Some W_7b688.
Proof. vm_refl. Qed.
Lemma D_7b688 : decode_any W_7b688 = Some (Jal 1 99376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b68c : bv 32 := 0x00128293.
Lemma F_7b68c : fetch_word Asan.M.loaded_segments (0x7b6dc : word) = Some W_7b68c.
Proof. vm_refl. Qed.
Lemma D_7b68c : decode_any W_7b68c = Some (OpImm ALU_ADD 5 5 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b690 : bv 32 := 0x0032d793.
Lemma F_7b690 : fetch_word Asan.M.loaded_segments (0x7b6e0 : word) = Some W_7b690.
Proof. vm_refl. Qed.
Lemma D_7b690 : decode_any W_7b690 = Some (ShiftImm ALU_SRL 15 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b694 : bv 32 := 0xfff78793.
Lemma F_7b694 : fetch_word Asan.M.loaded_segments (0x7b6e4 : word) = Some W_7b694.
Proof. vm_refl. Qed.
Lemma D_7b694 : decode_any W_7b694 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b698 : bv 32 := 0xfca7eae3.
Lemma F_7b698 : fetch_word Asan.M.loaded_segments (0x7b6e8 : word) = Some W_7b698.
Proof. vm_refl. Qed.
Lemma D_7b698 : decode_any W_7b698 = Some (Branch BC_LTU 15 10 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b69c : bv 32 := 0x0075f793.
Lemma F_7b69c : fetch_word Asan.M.loaded_segments (0x7b6ec : word) = Some W_7b69c.
Proof. vm_refl. Qed.
Lemma D_7b69c : decode_any W_7b69c = Some (OpImm ALU_AND 15 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6a0 : bv 32 := 0x26079a63.
Lemma F_7b6a0 : fetch_word Asan.M.loaded_segments (0x7b6f0 : word) = Some W_7b6a0.
Proof. vm_refl. Qed.
Lemma D_7b6a0 : decode_any W_7b6a0 = Some (Branch BC_NE 15 0 628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6a4 : bv 32 := 0x00b505b3.
Lemma F_7b6a4 : fetch_word Asan.M.loaded_segments (0x7b6f4 : word) = Some W_7b6a4.
Proof. vm_refl. Qed.
Lemma D_7b6a4 : decode_any W_7b6a4 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6a8 : bv 32 := 0xff858593.
Lemma F_7b6a8 : fetch_word Asan.M.loaded_segments (0x7b6f8 : word) = Some W_7b6a8.
Proof. vm_refl. Qed.
Lemma D_7b6a8 : decode_any W_7b6a8 = Some (OpImm ALU_ADD 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6ac : bv 32 := 0x04b77263.
Lemma F_7b6ac : fetch_word Asan.M.loaded_segments (0x7b6fc : word) = Some W_7b6ac.
Proof. vm_refl. Qed.
Lemma D_7b6ac : decode_any W_7b6ac = Some (Branch BC_GEU 14 11 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6b0 : bv 32 := 0x000be717.
Lemma F_7b6b0 : fetch_word Asan.M.loaded_segments (0x7b700 : word) = Some W_7b6b0.
Proof. vm_refl. Qed.
Lemma D_7b6b0 : decode_any W_7b6b0 = Some (Auipc 14 190, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6b4 : bv 32 := 0xac073703.
Lemma F_7b6b4 : fetch_word Asan.M.loaded_segments (0x7b704 : word) = Some W_7b6b4.
Proof. vm_refl. Qed.
Lemma D_7b6b4 : decode_any W_7b6b4 = Some (Load SZ8 true 14 14 2752, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6b8 : bv 32 := 0x000be797.
Lemma F_7b6b8 : fetch_word Asan.M.loaded_segments (0x7b708 : word) = Some W_7b6b8.
Proof. vm_refl. Qed.
Lemma D_7b6b8 : decode_any W_7b6b8 = Some (Auipc 15 190, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6bc : bv 32 := 0xac07b783.
Lemma F_7b6bc : fetch_word Asan.M.loaded_segments (0x7b70c : word) = Some W_7b6bc.
Proof. vm_refl. Qed.
Lemma D_7b6bc : decode_any W_7b6bc = Some (Load SZ8 true 15 15 2752, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6c0 : bv 32 := 0x00073883.
Lemma F_7b6c0 : fetch_word Asan.M.loaded_segments (0x7b710 : word) = Some W_7b6c0.
Proof. vm_refl. Qed.
Lemma D_7b6c0 : decode_any W_7b6c0 = Some (Load SZ8 true 17 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6c4 : bv 32 := 0x0007b703.
Lemma F_7b6c4 : fetch_word Asan.M.loaded_segments (0x7b714 : word) = Some W_7b6c4.
Proof. vm_refl. Qed.
Lemma D_7b6c4 : decode_any W_7b6c4 = Some (Load SZ8 true 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6c8 : bv 32 := 0xfff88813.
Lemma F_7b6c8 : fetch_word Asan.M.loaded_segments (0x7b718 : word) = Some W_7b6c8.
Proof. vm_refl. Qed.
Lemma D_7b6c8 : decode_any W_7b6c8 = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6cc : bv 32 := 0x00b87463.
Lemma F_7b6cc : fetch_word Asan.M.loaded_segments (0x7b71c : word) = Some W_7b6cc.
Proof. vm_refl. Qed.
Lemma D_7b6cc : decode_any W_7b6cc = Some (Branch BC_GEU 16 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6d0 : bv 32 := 0x02b77063.
Lemma F_7b6d0 : fetch_word Asan.M.loaded_segments (0x7b720 : word) = Some W_7b6d0.
Proof. vm_refl. Qed.
Lemma D_7b6d0 : decode_any W_7b6d0 = Some (Branch BC_GEU 14 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6d4 : bv 32 := 0x000be797.
Lemma F_7b6d4 : fetch_word Asan.M.loaded_segments (0x7b724 : word) = Some W_7b6d4.
Proof. vm_refl. Qed.
Lemma D_7b6d4 : decode_any W_7b6d4 = Some (Auipc 15 190, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6d8 : bv 32 := 0xaac7b783.
Lemma F_7b6d8 : fetch_word Asan.M.loaded_segments (0x7b728 : word) = Some W_7b6d8.
Proof. vm_refl. Qed.
Lemma D_7b6d8 : decode_any W_7b6d8 = Some (Load SZ8 true 15 15 2732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6dc : bv 32 := 0x0007b303.
Lemma F_7b6dc : fetch_word Asan.M.loaded_segments (0x7b72c : word) = Some W_7b6dc.
Proof. vm_refl. Qed.
Lemma D_7b6dc : decode_any W_7b6dc = Some (Load SZ8 true 6 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6e0 : bv 32 := 0x00335793.
Lemma F_7b6e0 : fetch_word Asan.M.loaded_segments (0x7b730 : word) = Some W_7b6e0.
Proof. vm_refl. Qed.
Lemma D_7b6e0 : decode_any W_7b6e0 = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6e4 : bv 32 := 0x009782b3.
Lemma F_7b6e4 : fetch_word Asan.M.loaded_segments (0x7b734 : word) = Some W_7b6e4.
Proof. vm_refl. Qed.
Lemma D_7b6e4 : decode_any W_7b6e4 = Some (Op ALU_ADD 5 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6e8 : bv 32 := 0x12b36263.
Lemma F_7b6e8 : fetch_word Asan.M.loaded_segments (0x7b738 : word) = Some W_7b6e8.
Proof. vm_refl. Qed.
Lemma D_7b6e8 : decode_any W_7b6e8 = Some (Branch BC_LTU 6 11 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6ec : bv 32 := 0x12b2f063.
Lemma F_7b6ec : fetch_word Asan.M.loaded_segments (0x7b73c : word) = Some W_7b6ec.
Proof. vm_refl. Qed.
Lemma D_7b6ec : decode_any W_7b6ec = Some (Branch BC_GEU 5 11 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6f0 : bv 32 := 0x000be697.
Lemma F_7b6f0 : fetch_word Asan.M.loaded_segments (0x7b740 : word) = Some W_7b6f0.
Proof. vm_refl. Qed.
Lemma D_7b6f0 : decode_any W_7b6f0 = Some (Auipc 13 190, 4%Z).
Proof. vm_refl. Qed.
