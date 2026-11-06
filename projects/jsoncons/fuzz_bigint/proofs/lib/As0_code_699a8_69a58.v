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

Definition W_699a8 : bv 32 := 0x02850583.
Lemma F_699a8 : fetch_word Asan.M.loaded_segments (0x699a8 : word) = Some W_699a8.
Proof. vm_refl. Qed.
Lemma D_699a8 : decode_any W_699a8 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_699ac : bv 32 := 0x0230000f.
Lemma F_699ac : fetch_word Asan.M.loaded_segments (0x699ac : word) = Some W_699ac.
Proof. vm_refl. Qed.
Lemma D_699ac : decode_any W_699ac = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_699b0 : bv 32 := 0x02058c63.
Lemma F_699b0 : fetch_word Asan.M.loaded_segments (0x699b0 : word) = Some W_699b0.
Proof. vm_refl. Qed.
Lemma D_699b0 : decode_any W_699b0 = Some (Branch BC_EQ 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_699b4 : bv 32 := 0xff010113.
Lemma F_699b4 : fetch_word Asan.M.loaded_segments (0x699b4 : word) = Some W_699b4.
Proof. vm_refl. Qed.
Lemma D_699b4 : decode_any W_699b4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_699b8 : bv 32 := 0x02053603.
Lemma F_699b8 : fetch_word Asan.M.loaded_segments (0x699b8 : word) = Some W_699b8.
Proof. vm_refl. Qed.
Lemma D_699b8 : decode_any W_699b8 = Some (Load SZ8 true 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_699bc : bv 32 := 0x01853583.
Lemma F_699bc : fetch_word Asan.M.loaded_segments (0x699bc : word) = Some W_699bc.
Proof. vm_refl. Qed.
Lemma D_699bc : decode_any W_699bc = Some (Load SZ8 true 11 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_699c0 : bv 32 := 0x00f10693.
Lemma F_699c0 : fetch_word Asan.M.loaded_segments (0x699c0 : word) = Some W_699c0.
Proof. vm_refl. Qed.
Lemma D_699c0 : decode_any W_699c0 = Some (OpImm ALU_ADD 13 2 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_699c4 : bv 32 := 0x00c6b633.
Lemma F_699c4 : fetch_word Asan.M.loaded_segments (0x699c4 : word) = Some W_699c4.
Proof. vm_refl. Qed.
Lemma D_699c4 : decode_any W_699c4 = Some (Op ALU_SLTU 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_699c8 : bv 32 := 0xfff64613.
Lemma F_699c8 : fetch_word Asan.M.loaded_segments (0x699c8 : word) = Some W_699c8.
Proof. vm_refl. Qed.
Lemma D_699c8 : decode_any W_699c8 = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_699cc : bv 32 := 0x00b6b6b3.
Lemma F_699cc : fetch_word Asan.M.loaded_segments (0x699cc : word) = Some W_699cc.
Proof. vm_refl. Qed.
Lemma D_699cc : decode_any W_699cc = Some (Op ALU_SLTU 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_699d0 : bv 32 := 0x00d67633.
Lemma F_699d0 : fetch_word Asan.M.loaded_segments (0x699d0 : word) = Some W_699d0.
Proof. vm_refl. Qed.
Lemma D_699d0 : decode_any W_699d0 = Some (Op ALU_AND 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_699d4 : bv 32 := 0x01010113.
Lemma F_699d4 : fetch_word Asan.M.loaded_segments (0x699d4 : word) = Some W_699d4.
Proof. vm_refl. Qed.
Lemma D_699d4 : decode_any W_699d4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_699d8 : bv 32 := 0x00061463.
Lemma F_699d8 : fetch_word Asan.M.loaded_segments (0x699d8 : word) = Some W_699d8.
Proof. vm_refl. Qed.
Lemma D_699d8 : decode_any W_699d8 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_699dc : bv 32 := 0x00853583.
Lemma F_699dc : fetch_word Asan.M.loaded_segments (0x699dc : word) = Some W_699dc.
Proof. vm_refl. Qed.
Lemma D_699dc : decode_any W_699dc = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_699e0 : bv 32 := 0x00058513.
Lemma F_699e0 : fetch_word Asan.M.loaded_segments (0x699e0 : word) = Some W_699e0.
Proof. vm_refl. Qed.
Lemma D_699e0 : decode_any W_699e0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_699e4 : bv 32 := 0x00008067.
Lemma F_699e4 : fetch_word Asan.M.loaded_segments (0x699e4 : word) = Some W_699e4.
Proof. vm_refl. Qed.
Lemma D_699e4 : decode_any W_699e4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_699e8 : bv 32 := 0x00853583.
Lemma F_699e8 : fetch_word Asan.M.loaded_segments (0x699e8 : word) = Some W_699e8.
Proof. vm_refl. Qed.
Lemma D_699e8 : decode_any W_699e8 = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_699ec : bv 32 := 0x01053503.
Lemma F_699ec : fetch_word Asan.M.loaded_segments (0x699ec : word) = Some W_699ec.
Proof. vm_refl. Qed.
Lemma D_699ec : decode_any W_699ec = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_699f0 : bv 32 := 0x00b53533.
Lemma F_699f0 : fetch_word Asan.M.loaded_segments (0x699f0 : word) = Some W_699f0.
Proof. vm_refl. Qed.
Lemma D_699f0 : decode_any W_699f0 = Some (Op ALU_SLTU 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_699f4 : bv 32 := 0x40a00533.
Lemma F_699f4 : fetch_word Asan.M.loaded_segments (0x699f4 : word) = Some W_699f4.
Proof. vm_refl. Qed.
Lemma D_699f4 : decode_any W_699f4 = Some (Op ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_699f8 : bv 32 := 0x00b57533.
Lemma F_699f8 : fetch_word Asan.M.loaded_segments (0x699f8 : word) = Some W_699f8.
Proof. vm_refl. Qed.
Lemma D_699f8 : decode_any W_699f8 = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_699fc : bv 32 := 0x00008067.
Lemma F_699fc : fetch_word Asan.M.loaded_segments (0x699fc : word) = Some W_699fc.
Proof. vm_refl. Qed.
Lemma D_699fc : decode_any W_699fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a00 : bv 32 := 0x02850583.
Lemma F_69a00 : fetch_word Asan.M.loaded_segments (0x69a00 : word) = Some W_69a00.
Proof. vm_refl. Qed.
Lemma D_69a00 : decode_any W_69a00 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a04 : bv 32 := 0x0230000f.
Lemma F_69a04 : fetch_word Asan.M.loaded_segments (0x69a04 : word) = Some W_69a04.
Proof. vm_refl. Qed.
Lemma D_69a04 : decode_any W_69a04 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a08 : bv 32 := 0x02058c63.
Lemma F_69a08 : fetch_word Asan.M.loaded_segments (0x69a08 : word) = Some W_69a08.
Proof. vm_refl. Qed.
Lemma D_69a08 : decode_any W_69a08 = Some (Branch BC_EQ 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a0c : bv 32 := 0xff010113.
Lemma F_69a0c : fetch_word Asan.M.loaded_segments (0x69a0c : word) = Some W_69a0c.
Proof. vm_refl. Qed.
Lemma D_69a0c : decode_any W_69a0c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a10 : bv 32 := 0x02053583.
Lemma F_69a10 : fetch_word Asan.M.loaded_segments (0x69a10 : word) = Some W_69a10.
Proof. vm_refl. Qed.
Lemma D_69a10 : decode_any W_69a10 = Some (Load SZ8 true 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a14 : bv 32 := 0x01853603.
Lemma F_69a14 : fetch_word Asan.M.loaded_segments (0x69a14 : word) = Some W_69a14.
Proof. vm_refl. Qed.
Lemma D_69a14 : decode_any W_69a14 = Some (Load SZ8 true 12 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a18 : bv 32 := 0x00f10693.
Lemma F_69a18 : fetch_word Asan.M.loaded_segments (0x69a18 : word) = Some W_69a18.
Proof. vm_refl. Qed.
Lemma D_69a18 : decode_any W_69a18 = Some (OpImm ALU_ADD 13 2 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a1c : bv 32 := 0x00b6b733.
Lemma F_69a1c : fetch_word Asan.M.loaded_segments (0x69a1c : word) = Some W_69a1c.
Proof. vm_refl. Qed.
Lemma D_69a1c : decode_any W_69a1c = Some (Op ALU_SLTU 14 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a20 : bv 32 := 0xfff74713.
Lemma F_69a20 : fetch_word Asan.M.loaded_segments (0x69a20 : word) = Some W_69a20.
Proof. vm_refl. Qed.
Lemma D_69a20 : decode_any W_69a20 = Some (OpImm ALU_XOR 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a24 : bv 32 := 0x00c6b633.
Lemma F_69a24 : fetch_word Asan.M.loaded_segments (0x69a24 : word) = Some W_69a24.
Proof. vm_refl. Qed.
Lemma D_69a24 : decode_any W_69a24 = Some (Op ALU_SLTU 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a28 : bv 32 := 0x00c77633.
Lemma F_69a28 : fetch_word Asan.M.loaded_segments (0x69a28 : word) = Some W_69a28.
Proof. vm_refl. Qed.
Lemma D_69a28 : decode_any W_69a28 = Some (Op ALU_AND 12 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a2c : bv 32 := 0x01010113.
Lemma F_69a2c : fetch_word Asan.M.loaded_segments (0x69a2c : word) = Some W_69a2c.
Proof. vm_refl. Qed.
Lemma D_69a2c : decode_any W_69a2c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a30 : bv 32 := 0x00061463.
Lemma F_69a30 : fetch_word Asan.M.loaded_segments (0x69a30 : word) = Some W_69a30.
Proof. vm_refl. Qed.
Lemma D_69a30 : decode_any W_69a30 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a34 : bv 32 := 0x01053583.
Lemma F_69a34 : fetch_word Asan.M.loaded_segments (0x69a34 : word) = Some W_69a34.
Proof. vm_refl. Qed.
Lemma D_69a34 : decode_any W_69a34 = Some (Load SZ8 true 11 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a38 : bv 32 := 0x00058513.
Lemma F_69a38 : fetch_word Asan.M.loaded_segments (0x69a38 : word) = Some W_69a38.
Proof. vm_refl. Qed.
Lemma D_69a38 : decode_any W_69a38 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a3c : bv 32 := 0x00008067.
Lemma F_69a3c : fetch_word Asan.M.loaded_segments (0x69a3c : word) = Some W_69a3c.
Proof. vm_refl. Qed.
Lemma D_69a3c : decode_any W_69a3c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a40 : bv 32 := 0x00853583.
Lemma F_69a40 : fetch_word Asan.M.loaded_segments (0x69a40 : word) = Some W_69a40.
Proof. vm_refl. Qed.
Lemma D_69a40 : decode_any W_69a40 = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a44 : bv 32 := 0x01053503.
Lemma F_69a44 : fetch_word Asan.M.loaded_segments (0x69a44 : word) = Some W_69a44.
Proof. vm_refl. Qed.
Lemma D_69a44 : decode_any W_69a44 = Some (Load SZ8 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a48 : bv 32 := 0x00b535b3.
Lemma F_69a48 : fetch_word Asan.M.loaded_segments (0x69a48 : word) = Some W_69a48.
Proof. vm_refl. Qed.
Lemma D_69a48 : decode_any W_69a48 = Some (Op ALU_SLTU 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a4c : bv 32 := 0x40b005b3.
Lemma F_69a4c : fetch_word Asan.M.loaded_segments (0x69a4c : word) = Some W_69a4c.
Proof. vm_refl. Qed.
Lemma D_69a4c : decode_any W_69a4c = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a50 : bv 32 := 0x00a5f533.
Lemma F_69a50 : fetch_word Asan.M.loaded_segments (0x69a50 : word) = Some W_69a50.
Proof. vm_refl. Qed.
Lemma D_69a50 : decode_any W_69a50 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_69a54 : bv 32 := 0x00008067.
Lemma F_69a54 : fetch_word Asan.M.loaded_segments (0x69a54 : word) = Some W_69a54.
Proof. vm_refl. Qed.
Lemma D_69a54 : decode_any W_69a54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
