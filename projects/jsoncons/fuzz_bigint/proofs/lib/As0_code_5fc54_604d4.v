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

Definition W_5fc54 : bv 32 := 0x0100006f.
Lemma F_5fc54 : fetch_word Asan.M.loaded_segments (0x5fc54 : word) = Some W_5fc54.
Proof. vm_refl. Qed.
Lemma D_5fc54 : decode_any W_5fc54 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc58 : bv 32 := 0x1dc0006f.
Lemma F_5fc58 : fetch_word Asan.M.loaded_segments (0x5fc58 : word) = Some W_5fc58.
Proof. vm_refl. Qed.
Lemma D_5fc58 : decode_any W_5fc58 = Some (Jal 0 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc5c : bv 32 := 0x4000006f.
Lemma F_5fc5c : fetch_word Asan.M.loaded_segments (0x5fc5c : word) = Some W_5fc5c.
Proof. vm_refl. Qed.
Lemma D_5fc5c : decode_any W_5fc5c = Some (Jal 0 1024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc60 : bv 32 := 0x7400006f.
Lemma F_5fc60 : fetch_word Asan.M.loaded_segments (0x5fc60 : word) = Some W_5fc60.
Proof. vm_refl. Qed.
Lemma D_5fc60 : decode_any W_5fc60 = Some (Jal 0 1856, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc64 : bv 32 := 0x81010113.
Lemma F_5fc64 : fetch_word Asan.M.loaded_segments (0x5fc64 : word) = Some W_5fc64.
Proof. vm_refl. Qed.
Lemma D_5fc64 : decode_any W_5fc64 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc68 : bv 32 := 0x7e113423.
Lemma F_5fc68 : fetch_word Asan.M.loaded_segments (0x5fc68 : word) = Some W_5fc68.
Proof. vm_refl. Qed.
Lemma D_5fc68 : decode_any W_5fc68 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc6c : bv 32 := 0x7e813023.
Lemma F_5fc6c : fetch_word Asan.M.loaded_segments (0x5fc6c : word) = Some W_5fc6c.
Proof. vm_refl. Qed.
Lemma D_5fc6c : decode_any W_5fc6c = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc70 : bv 32 := 0x7c913c23.
Lemma F_5fc70 : fetch_word Asan.M.loaded_segments (0x5fc70 : word) = Some W_5fc70.
Proof. vm_refl. Qed.
Lemma D_5fc70 : decode_any W_5fc70 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc74 : bv 32 := 0x7d213823.
Lemma F_5fc74 : fetch_word Asan.M.loaded_segments (0x5fc74 : word) = Some W_5fc74.
Proof. vm_refl. Qed.
Lemma D_5fc74 : decode_any W_5fc74 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc78 : bv 32 := 0x7d313423.
Lemma F_5fc78 : fetch_word Asan.M.loaded_segments (0x5fc78 : word) = Some W_5fc78.
Proof. vm_refl. Qed.
Lemma D_5fc78 : decode_any W_5fc78 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc7c : bv 32 := 0x7d413023.
Lemma F_5fc7c : fetch_word Asan.M.loaded_segments (0x5fc7c : word) = Some W_5fc7c.
Proof. vm_refl. Qed.
Lemma D_5fc7c : decode_any W_5fc7c = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc80 : bv 32 := 0x7b513c23.
Lemma F_5fc80 : fetch_word Asan.M.loaded_segments (0x5fc80 : word) = Some W_5fc80.
Proof. vm_refl. Qed.
Lemma D_5fc80 : decode_any W_5fc80 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc84 : bv 32 := 0x7f010413.
Lemma F_5fc84 : fetch_word Asan.M.loaded_segments (0x5fc84 : word) = Some W_5fc84.
Proof. vm_refl. Qed.
Lemma D_5fc84 : decode_any W_5fc84 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc88 : bv 32 := 0xfa010113.
Lemma F_5fc88 : fetch_word Asan.M.loaded_segments (0x5fc88 : word) = Some W_5fc88.
Proof. vm_refl. Qed.
Lemma D_5fc88 : decode_any W_5fc88 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc8c : bv 32 := 0x00008913.
Lemma F_5fc8c : fetch_word Asan.M.loaded_segments (0x5fc8c : word) = Some W_5fc8c.
Proof. vm_refl. Qed.
Lemma D_5fc8c : decode_any W_5fc8c = Some (OpImm ALU_ADD 18 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc90 : bv 32 := 0x00050493.
Lemma F_5fc90 : fetch_word Asan.M.loaded_segments (0x5fc90 : word) = Some W_5fc90.
Proof. vm_refl. Qed.
Lemma D_5fc90 : decode_any W_5fc90 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc94 : bv 32 := 0x3cd0b0ef.
Lemma F_5fc94 : fetch_word Asan.M.loaded_segments (0x5fc94 : word) = Some W_5fc94.
Proof. vm_refl. Qed.
Lemma D_5fc94 : decode_any W_5fc94 = Some (Jal 1 48076, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc98 : bv 32 := 0x02f4d593.
Lemma F_5fc98 : fetch_word Asan.M.loaded_segments (0x5fc98 : word) = Some W_5fc98.
Proof. vm_refl. Qed.
Lemma D_5fc98 : decode_any W_5fc98 = Some (ShiftImm ALU_SRL 11 9 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fc9c : bv 32 := 0x0a059063.
Lemma F_5fc9c : fetch_word Asan.M.loaded_segments (0x5fc9c : word) = Some W_5fc9c.
Proof. vm_refl. Qed.
Lemma D_5fc9c : decode_any W_5fc9c = Some (Branch BC_NE 11 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fca0 : bv 32 := 0x0204d593.
Lemma F_5fca0 : fetch_word Asan.M.loaded_segments (0x5fca0 : word) = Some W_5fca0.
Proof. vm_refl. Qed.
Lemma D_5fca0 : decode_any W_5fca0 = Some (ShiftImm ALU_SRL 11 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fca4 : bv 32 := 0x00359613.
Lemma F_5fca4 : fetch_word Asan.M.loaded_segments (0x5fca4 : word) = Some W_5fca4.
Proof. vm_refl. Qed.
Lemma D_5fca4 : decode_any W_5fca4 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fca8 : bv 32 := 0x00c50633.
Lemma F_5fca8 : fetch_word Asan.M.loaded_segments (0x5fca8 : word) = Some W_5fca8.
Proof. vm_refl. Qed.
Lemma D_5fca8 : decode_any W_5fca8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcac : bv 32 := 0x00863683.
Lemma F_5fcac : fetch_word Asan.M.loaded_segments (0x5fcac : word) = Some W_5fcac.
Proof. vm_refl. Qed.
Lemma D_5fcac : decode_any W_5fcac = Some (Load SZ8 true 13 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcb0 : bv 32 := 0x0230000f.
Lemma F_5fcb0 : fetch_word Asan.M.loaded_segments (0x5fcb0 : word) = Some W_5fcb0.
Proof. vm_refl. Qed.
Lemma D_5fcb0 : decode_any W_5fcb0 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcb4 : bv 32 := 0x08068463.
Lemma F_5fcb4 : fetch_word Asan.M.loaded_segments (0x5fcb4 : word) = Some W_5fcb4.
Proof. vm_refl. Qed.
Lemma D_5fcb4 : decode_any W_5fcb4 = Some (Branch BC_EQ 13 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcb8 : bv 32 := 0x00863603.
Lemma F_5fcb8 : fetch_word Asan.M.loaded_segments (0x5fcb8 : word) = Some W_5fcb8.
Proof. vm_refl. Qed.
Lemma D_5fcb8 : decode_any W_5fcb8 = Some (Load SZ8 true 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcbc : bv 32 := 0x0144d993.
Lemma F_5fcbc : fetch_word Asan.M.loaded_segments (0x5fcbc : word) = Some W_5fcbc.
Proof. vm_refl. Qed.
Lemma D_5fcbc : decode_any W_5fcbc = Some (ShiftImm ALU_SRL 19 9 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcc0 : bv 32 := 0x06060063.
Lemma F_5fcc0 : fetch_word Asan.M.loaded_segments (0x5fcc0 : word) = Some W_5fcc0.
Proof. vm_refl. Qed.
Lemma D_5fcc0 : decode_any W_5fcc0 = Some (Branch BC_EQ 12 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcc4 : bv 32 := 0x03499993.
Lemma F_5fcc4 : fetch_word Asan.M.loaded_segments (0x5fcc4 : word) = Some W_5fcc4.
Proof. vm_refl. Qed.
Lemma D_5fcc4 : decode_any W_5fcc4 = Some (ShiftImm ALU_SLL 19 19 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcc8 : bv 32 := 0x0349d513.
Lemma F_5fcc8 : fetch_word Asan.M.loaded_segments (0x5fcc8 : word) = Some W_5fcc8.
Proof. vm_refl. Qed.
Lemma D_5fcc8 : decode_any W_5fcc8 = Some (ShiftImm ALU_SRL 10 19 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fccc : bv 32 := 0x00a60533.
Lemma F_5fccc : fetch_word Asan.M.loaded_segments (0x5fccc : word) = Some W_5fccc.
Proof. vm_refl. Qed.
Lemma D_5fccc : decode_any W_5fccc = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcd0 : bv 32 := 0x00054503.
Lemma F_5fcd0 : fetch_word Asan.M.loaded_segments (0x5fcd0 : word) = Some W_5fcd0.
Proof. vm_refl. Qed.
Lemma D_5fcd0 : decode_any W_5fcd0 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcd4 : bv 32 := 0x06050463.
Lemma F_5fcd4 : fetch_word Asan.M.loaded_segments (0x5fcd4 : word) = Some W_5fcd4.
Proof. vm_refl. Qed.
Lemma D_5fcd4 : decode_any W_5fcd4 = Some (Branch BC_EQ 10 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcd8 : bv 32 := 0x3890b0ef.
Lemma F_5fcd8 : fetch_word Asan.M.loaded_segments (0x5fcd8 : word) = Some W_5fcd8.
Proof. vm_refl. Qed.
Lemma D_5fcd8 : decode_any W_5fcd8 = Some (Jal 1 48008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcdc : bv 32 := 0x00048593.
Lemma F_5fcdc : fetch_word Asan.M.loaded_segments (0x5fcdc : word) = Some W_5fcdc.
Proof. vm_refl. Qed.
Lemma D_5fcdc : decode_any W_5fcdc = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fce0 : bv 32 := 0x0f9000ef.
Lemma F_5fce0 : fetch_word Asan.M.loaded_segments (0x5fce0 : word) = Some W_5fce0.
Proof. vm_refl. Qed.
Lemma D_5fce0 : decode_any W_5fce0 = Some (Jal 1 2296, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fce4 : bv 32 := 0x00050593.
Lemma F_5fce4 : fetch_word Asan.M.loaded_segments (0x5fce4 : word) = Some W_5fce4.
Proof. vm_refl. Qed.
Lemma D_5fce4 : decode_any W_5fce4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fce8 : bv 32 := 0x00048513.
Lemma F_5fce8 : fetch_word Asan.M.loaded_segments (0x5fce8 : word) = Some W_5fce8.
Proof. vm_refl. Qed.
Lemma D_5fce8 : decode_any W_5fce8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcec : bv 32 := 0x6702a0ef.
Lemma F_5fcec : fetch_word Asan.M.loaded_segments (0x5fcec : word) = Some W_5fcec.
Proof. vm_refl. Qed.
Lemma D_5fcec : decode_any W_5fcec = Some (Jal 1 173680, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcf0 : bv 32 := 0x00048513.
Lemma F_5fcf0 : fetch_word Asan.M.loaded_segments (0x5fcf0 : word) = Some W_5fcf0.
Proof. vm_refl. Qed.
Lemma D_5fcf0 : decode_any W_5fcf0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcf4 : bv 32 := 0x00000593.
Lemma F_5fcf4 : fetch_word Asan.M.loaded_segments (0x5fcf4 : word) = Some W_5fcf4.
Proof. vm_refl. Qed.
Lemma D_5fcf4 : decode_any W_5fcf4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcf8 : bv 32 := 0x06010113.
Lemma F_5fcf8 : fetch_word Asan.M.loaded_segments (0x5fcf8 : word) = Some W_5fcf8.
Proof. vm_refl. Qed.
Lemma D_5fcf8 : decode_any W_5fcf8 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fcfc : bv 32 := 0x7e813083.
Lemma F_5fcfc : fetch_word Asan.M.loaded_segments (0x5fcfc : word) = Some W_5fcfc.
Proof. vm_refl. Qed.
Lemma D_5fcfc : decode_any W_5fcfc = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd00 : bv 32 := 0x7e013403.
Lemma F_5fd00 : fetch_word Asan.M.loaded_segments (0x5fd00 : word) = Some W_5fd00.
Proof. vm_refl. Qed.
Lemma D_5fd00 : decode_any W_5fd00 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd04 : bv 32 := 0x7d813483.
Lemma F_5fd04 : fetch_word Asan.M.loaded_segments (0x5fd04 : word) = Some W_5fd04.
Proof. vm_refl. Qed.
Lemma D_5fd04 : decode_any W_5fd04 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd08 : bv 32 := 0x7d013903.
Lemma F_5fd08 : fetch_word Asan.M.loaded_segments (0x5fd08 : word) = Some W_5fd08.
Proof. vm_refl. Qed.
Lemma D_5fd08 : decode_any W_5fd08 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd0c : bv 32 := 0x7c813983.
Lemma F_5fd0c : fetch_word Asan.M.loaded_segments (0x5fd0c : word) = Some W_5fd0c.
Proof. vm_refl. Qed.
Lemma D_5fd0c : decode_any W_5fd0c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd10 : bv 32 := 0x7c013a03.
Lemma F_5fd10 : fetch_word Asan.M.loaded_segments (0x5fd10 : word) = Some W_5fd10.
Proof. vm_refl. Qed.
Lemma D_5fd10 : decode_any W_5fd10 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd14 : bv 32 := 0x7b813a83.
Lemma F_5fd14 : fetch_word Asan.M.loaded_segments (0x5fd14 : word) = Some W_5fd14.
Proof. vm_refl. Qed.
Lemma D_5fd14 : decode_any W_5fd14 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd18 : bv 32 := 0x7f010113.
Lemma F_5fd18 : fetch_word Asan.M.loaded_segments (0x5fd18 : word) = Some W_5fd18.
Proof. vm_refl. Qed.
Lemma D_5fd18 : decode_any W_5fd18 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd1c : bv 32 := 0x5c10b06f.
Lemma F_5fd1c : fetch_word Asan.M.loaded_segments (0x5fd1c : word) = Some W_5fd1c.
Proof. vm_refl. Qed.
Lemma D_5fd1c : decode_any W_5fd1c = Some (Jal 0 48576, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd20 : bv 32 := 0x7b8000ef.
Lemma F_5fd20 : fetch_word Asan.M.loaded_segments (0x5fd20 : word) = Some W_5fd20.
Proof. vm_refl. Qed.
Lemma D_5fd20 : decode_any W_5fd20 = Some (Jal 1 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd24 : bv 32 := 0x00050613.
Lemma F_5fd24 : fetch_word Asan.M.loaded_segments (0x5fd24 : word) = Some W_5fd24.
Proof. vm_refl. Qed.
Lemma D_5fd24 : decode_any W_5fd24 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd28 : bv 32 := 0x03499993.
Lemma F_5fd28 : fetch_word Asan.M.loaded_segments (0x5fd28 : word) = Some W_5fd28.
Proof. vm_refl. Qed.
Lemma D_5fd28 : decode_any W_5fd28 = Some (ShiftImm ALU_SLL 19 19 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd2c : bv 32 := 0x0349d513.
Lemma F_5fd2c : fetch_word Asan.M.loaded_segments (0x5fd2c : word) = Some W_5fd2c.
Proof. vm_refl. Qed.
Lemma D_5fd2c : decode_any W_5fd2c = Some (ShiftImm ALU_SRL 10 19 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd30 : bv 32 := 0x00a60533.
Lemma F_5fd30 : fetch_word Asan.M.loaded_segments (0x5fd30 : word) = Some W_5fd30.
Proof. vm_refl. Qed.
Lemma D_5fd30 : decode_any W_5fd30 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd34 : bv 32 := 0x00054503.
Lemma F_5fd34 : fetch_word Asan.M.loaded_segments (0x5fd34 : word) = Some W_5fd34.
Proof. vm_refl. Qed.
Lemma D_5fd34 : decode_any W_5fd34 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd38 : bv 32 := 0xfa0510e3.
Lemma F_5fd38 : fetch_word Asan.M.loaded_segments (0x5fd38 : word) = Some W_5fd38.
Proof. vm_refl. Qed.
Lemma D_5fd38 : decode_any W_5fd38 = Some (Branch BC_NE 10 0 8096, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd3c : bv 32 := 0x80040a13.
Lemma F_5fd3c : fetch_word Asan.M.loaded_segments (0x5fd3c : word) = Some W_5fd3c.
Proof. vm_refl. Qed.
Lemma D_5fd3c : decode_any W_5fd3c = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd40 : bv 32 := 0xfb0a0a13.
Lemma F_5fd40 : fetch_word Asan.M.loaded_segments (0x5fd40 : word) = Some W_5fd40.
Proof. vm_refl. Qed.
Lemma D_5fd40 : decode_any W_5fd40 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd44 : bv 32 := 0x80040513.
Lemma F_5fd44 : fetch_word Asan.M.loaded_segments (0x5fd44 : word) = Some W_5fd44.
Proof. vm_refl. Qed.
Lemma D_5fd44 : decode_any W_5fd44 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd48 : bv 32 := 0xfc050513.
Lemma F_5fd48 : fetch_word Asan.M.loaded_segments (0x5fd48 : word) = Some W_5fd48.
Proof. vm_refl. Qed.
Lemma D_5fd48 : decode_any W_5fd48 = Some (OpImm ALU_ADD 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd4c : bv 32 := 0x7ffa0a93.
Lemma F_5fd4c : fetch_word Asan.M.loaded_segments (0x5fd4c : word) = Some W_5fd4c.
Proof. vm_refl. Qed.
Lemma D_5fd4c : decode_any W_5fd4c = Some (OpImm ALU_ADD 21 20 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd50 : bv 32 := 0x000ab4a3.
Lemma F_5fd50 : fetch_word Asan.M.loaded_segments (0x5fd50 : word) = Some W_5fd50.
Proof. vm_refl. Qed.
Lemma D_5fd50 : decode_any W_5fd50 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd54 : bv 32 := 0x00aa3023.
Lemma F_5fd54 : fetch_word Asan.M.loaded_segments (0x5fd54 : word) = Some W_5fd54.
Proof. vm_refl. Qed.
Lemma D_5fd54 : decode_any W_5fd54 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd58 : bv 32 := 0x000a3423.
Lemma F_5fd58 : fetch_word Asan.M.loaded_segments (0x5fd58 : word) = Some W_5fd58.
Proof. vm_refl. Qed.
Lemma D_5fd58 : decode_any W_5fd58 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd5c : bv 32 := 0x010080ef.
Lemma F_5fd5c : fetch_word Asan.M.loaded_segments (0x5fd5c : word) = Some W_5fd5c.
Proof. vm_refl. Qed.
Lemma D_5fd5c : decode_any W_5fd5c = Some (Jal 1 32784, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd60 : bv 32 := 0x00200593.
Lemma F_5fd60 : fetch_word Asan.M.loaded_segments (0x5fd60 : word) = Some W_5fd60.
Proof. vm_refl. Qed.
Lemma D_5fd60 : decode_any W_5fd60 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd64 : bv 32 := 0x02a5ea63.
Lemma F_5fd64 : fetch_word Asan.M.loaded_segments (0x5fd64 : word) = Some W_5fd64.
Proof. vm_refl. Qed.
Lemma D_5fd64 : decode_any W_5fd64 = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd68 : bv 32 := 0x004080ef.
Lemma F_5fd68 : fetch_word Asan.M.loaded_segments (0x5fd68 : word) = Some W_5fd68.
Proof. vm_refl. Qed.
Lemma D_5fd68 : decode_any W_5fd68 = Some (Jal 1 32772, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd6c : bv 32 := 0x00aa2423.
Lemma F_5fd6c : fetch_word Asan.M.loaded_segments (0x5fd6c : word) = Some W_5fd6c.
Proof. vm_refl. Qed.
Lemma D_5fd6c : decode_any W_5fd6c = Some (Store SZ4 20 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd70 : bv 32 := 0x7fd070ef.
Lemma F_5fd70 : fetch_word Asan.M.loaded_segments (0x5fd70 : word) = Some W_5fd70.
Proof. vm_refl. Qed.
Lemma D_5fd70 : decode_any W_5fd70 = Some (Jal 1 32764, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd74 : bv 32 := 0x08050263.
Lemma F_5fd74 : fetch_word Asan.M.loaded_segments (0x5fd74 : word) = Some W_5fd74.
Proof. vm_refl. Qed.
Lemma D_5fd74 : decode_any W_5fd74 = Some (Branch BC_EQ 10 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd78 : bv 32 := 0x008ab4a3.
Lemma F_5fd78 : fetch_word Asan.M.loaded_segments (0x5fd78 : word) = Some W_5fd78.
Proof. vm_refl. Qed.
Lemma D_5fd78 : decode_any W_5fd78 = Some (Store SZ8 21 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd7c : bv 32 := 0x2b1200ef.
Lemma F_5fd7c : fetch_word Asan.M.loaded_segments (0x5fd7c : word) = Some W_5fd7c.
Proof. vm_refl. Qed.
Lemma D_5fd7c : decode_any W_5fd7c = Some (Jal 1 133808, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd80 : bv 32 := 0x00aa3823.
Lemma F_5fd80 : fetch_word Asan.M.loaded_segments (0x5fd80 : word) = Some W_5fd80.
Proof. vm_refl. Qed.
Lemma D_5fd80 : decode_any W_5fd80 = Some (Store SZ8 20 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd84 : bv 32 := 0x7e9070ef.
Lemma F_5fd84 : fetch_word Asan.M.loaded_segments (0x5fd84 : word) = Some W_5fd84.
Proof. vm_refl. Qed.
Lemma D_5fd84 : decode_any W_5fd84 = Some (Jal 1 32744, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd88 : bv 32 := 0x00200593.
Lemma F_5fd88 : fetch_word Asan.M.loaded_segments (0x5fd88 : word) = Some W_5fd88.
Proof. vm_refl. Qed.
Lemma D_5fd88 : decode_any W_5fd88 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd8c : bv 32 := 0x06b56663.
Lemma F_5fd8c : fetch_word Asan.M.loaded_segments (0x5fd8c : word) = Some W_5fd8c.
Proof. vm_refl. Qed.
Lemma D_5fd8c : decode_any W_5fd8c = Some (Branch BC_LTU 10 11 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd90 : bv 32 := 0x012a3c23.
Lemma F_5fd90 : fetch_word Asan.M.loaded_segments (0x5fd90 : word) = Some W_5fd90.
Proof. vm_refl. Qed.
Lemma D_5fd90 : decode_any W_5fd90 = Some (Store SZ8 20 18 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd94 : bv 32 := 0x0640006f.
Lemma F_5fd94 : fetch_word Asan.M.loaded_segments (0x5fd94 : word) = Some W_5fd94.
Proof. vm_refl. Qed.
Lemma D_5fd94 : decode_any W_5fd94 = Some (Jal 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd98 : bv 32 := 0x295200ef.
Lemma F_5fd98 : fetch_word Asan.M.loaded_segments (0x5fd98 : word) = Some W_5fd98.
Proof. vm_refl. Qed.
Lemma D_5fd98 : decode_any W_5fd98 = Some (Jal 1 133780, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fd9c : bv 32 := 0x00076597.
Lemma F_5fd9c : fetch_word Asan.M.loaded_segments (0x5fd9c : word) = Some W_5fd9c.
Proof. vm_refl. Qed.
Lemma D_5fd9c : decode_any W_5fd9c = Some (Auipc 11 118, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fda0 : bv 32 := 0xb0c5b583.
Lemma F_5fda0 : fetch_word Asan.M.loaded_segments (0x5fda0 : word) = Some W_5fda0.
Proof. vm_refl. Qed.
Lemma D_5fda0 : decode_any W_5fda0 = Some (Load SZ8 true 11 11 2828, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fda4 : bv 32 := 0x0225c983.
Lemma F_5fda4 : fetch_word Asan.M.loaded_segments (0x5fda4 : word) = Some W_5fda4.
Proof. vm_refl. Qed.
Lemma D_5fda4 : decode_any W_5fda4 = Some (Load SZ1 false 19 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fda8 : bv 32 := 0x00050913.
Lemma F_5fda8 : fetch_word Asan.M.loaded_segments (0x5fda8 : word) = Some W_5fda8.
Proof. vm_refl. Qed.
Lemma D_5fda8 : decode_any W_5fda8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fdac : bv 32 := 0x7c1070ef.
Lemma F_5fdac : fetch_word Asan.M.loaded_segments (0x5fdac : word) = Some W_5fdac.
Proof. vm_refl. Qed.
Lemma D_5fdac : decode_any W_5fdac = Some (Jal 1 32704, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fdb0 : bv 32 := 0x00050793.
Lemma F_5fdb0 : fetch_word Asan.M.loaded_segments (0x5fdb0 : word) = Some W_5fdb0.
Proof. vm_refl. Qed.
Lemma D_5fdb0 : decode_any W_5fdb0 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fdb4 : bv 32 := 0x00153513.
Lemma F_5fdb4 : fetch_word Asan.M.loaded_segments (0x5fdb4 : word) = Some W_5fdb4.
Proof. vm_refl. Qed.
Lemma D_5fdb4 : decode_any W_5fdb4 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fdb8 : bv 32 := 0xfff50513.
Lemma F_5fdb8 : fetch_word Asan.M.loaded_segments (0x5fdb8 : word) = Some W_5fdb8.
Proof. vm_refl. Qed.
Lemma D_5fdb8 : decode_any W_5fdb8 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fdbc : bv 32 := 0x008575b3.
Lemma F_5fdbc : fetch_word Asan.M.loaded_segments (0x5fdbc : word) = Some W_5fdbc.
Proof. vm_refl. Qed.
Lemma D_5fdbc : decode_any W_5fdbc = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fdc0 : bv 32 := 0x00100513.
Lemma F_5fdc0 : fetch_word Asan.M.loaded_segments (0x5fdc0 : word) = Some W_5fdc0.
Proof. vm_refl. Qed.
Lemma D_5fdc0 : decode_any W_5fdc0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fdc4 : bv 32 := 0x00bab4a3.
Lemma F_5fdc4 : fetch_word Asan.M.loaded_segments (0x5fdc4 : word) = Some W_5fdc4.
Proof. vm_refl. Qed.
Lemma D_5fdc4 : decode_any W_5fdc4 = Some (Store SZ8 21 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fdc8 : bv 32 := 0x00f56a63.
Lemma F_5fdc8 : fetch_word Asan.M.loaded_segments (0x5fdc8 : word) = Some W_5fdc8.
Proof. vm_refl. Qed.
Lemma D_5fdc8 : decode_any W_5fdc8 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fdcc : bv 32 := 0x00a79463.
Lemma F_5fdcc : fetch_word Asan.M.loaded_segments (0x5fdcc : word) = Some W_5fdcc.
Proof. vm_refl. Qed.
Lemma D_5fdcc : decode_any W_5fdcc = Some (Branch BC_NE 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fdd0 : bv 32 := 0x012a3823.
Lemma F_5fdd0 : fetch_word Asan.M.loaded_segments (0x5fdd0 : word) = Some W_5fdd0.
Proof. vm_refl. Qed.
Lemma D_5fdd0 : decode_any W_5fdd0 = Some (Store SZ8 20 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fdd4 : bv 32 := 0x00fa2423.
Lemma F_5fdd4 : fetch_word Asan.M.loaded_segments (0x5fdd4 : word) = Some W_5fdd4.
Proof. vm_refl. Qed.
Lemma D_5fdd4 : decode_any W_5fdd4 = Some (Store SZ4 20 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fdd8 : bv 32 := 0x0200006f.
Lemma F_5fdd8 : fetch_word Asan.M.loaded_segments (0x5fdd8 : word) = Some W_5fdd8.
Proof. vm_refl. Qed.
Lemma D_5fdd8 : decode_any W_5fdd8 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fddc : bv 32 := 0x80040513.
Lemma F_5fddc : fetch_word Asan.M.loaded_segments (0x5fddc : word) = Some W_5fddc.
Proof. vm_refl. Qed.
Lemma D_5fddc : decode_any W_5fddc = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fde0 : bv 32 := 0xfb050513.
Lemma F_5fde0 : fetch_word Asan.M.loaded_segments (0x5fde0 : word) = Some W_5fde0.
Proof. vm_refl. Qed.
Lemma D_5fde0 : decode_any W_5fde0 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fde4 : bv 32 := 0x00090593.
Lemma F_5fde4 : fetch_word Asan.M.loaded_segments (0x5fde4 : word) = Some W_5fde4.
Proof. vm_refl. Qed.
Lemma D_5fde4 : decode_any W_5fde4 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fde8 : bv 32 := 0x00040613.
Lemma F_5fde8 : fetch_word Asan.M.loaded_segments (0x5fde8 : word) = Some W_5fde8.
Proof. vm_refl. Qed.
Lemma D_5fde8 : decode_any W_5fde8 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fdec : bv 32 := 0x00000693.
Lemma F_5fdec : fetch_word Asan.M.loaded_segments (0x5fdec : word) = Some W_5fdec.
Proof. vm_refl. Qed.
Lemma D_5fdec : decode_any W_5fdec = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fdf0 : bv 32 := 0x00098713.
Lemma F_5fdf0 : fetch_word Asan.M.loaded_segments (0x5fdf0 : word) = Some W_5fdf0.
Proof. vm_refl. Qed.
Lemma D_5fdf0 : decode_any W_5fdf0 = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fdf4 : bv 32 := 0x789070ef.
Lemma F_5fdf4 : fetch_word Asan.M.loaded_segments (0x5fdf4 : word) = Some W_5fdf4.
Proof. vm_refl. Qed.
Lemma D_5fdf4 : decode_any W_5fdf4 = Some (Jal 1 32648, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fdf8 : bv 32 := 0x80040593.
Lemma F_5fdf8 : fetch_word Asan.M.loaded_segments (0x5fdf8 : word) = Some W_5fdf8.
Proof. vm_refl. Qed.
Lemma D_5fdf8 : decode_any W_5fdf8 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fdfc : bv 32 := 0xfb058593.
Lemma F_5fdfc : fetch_word Asan.M.loaded_segments (0x5fdfc : word) = Some W_5fdfc.
Proof. vm_refl. Qed.
Lemma D_5fdfc : decode_any W_5fdfc = Some (OpImm ALU_ADD 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe00 : bv 32 := 0x00100613.
Lemma F_5fe00 : fetch_word Asan.M.loaded_segments (0x5fe00 : word) = Some W_5fe00.
Proof. vm_refl. Qed.
Lemma D_5fe00 : decode_any W_5fe00 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe04 : bv 32 := 0x00048513.
Lemma F_5fe04 : fetch_word Asan.M.loaded_segments (0x5fe04 : word) = Some W_5fe04.
Proof. vm_refl. Qed.
Lemma D_5fe04 : decode_any W_5fe04 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe08 : bv 32 := 0xa2cdd0ef.
Lemma F_5fe08 : fetch_word Asan.M.loaded_segments (0x5fe08 : word) = Some W_5fe08.
Proof. vm_refl. Qed.
Lemma D_5fe08 : decode_any W_5fe08 = Some (Jal 1 1954348, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe0c : bv 32 := 0x06010113.
Lemma F_5fe0c : fetch_word Asan.M.loaded_segments (0x5fe0c : word) = Some W_5fe0c.
Proof. vm_refl. Qed.
Lemma D_5fe0c : decode_any W_5fe0c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe10 : bv 32 := 0x7e813083.
Lemma F_5fe10 : fetch_word Asan.M.loaded_segments (0x5fe10 : word) = Some W_5fe10.
Proof. vm_refl. Qed.
Lemma D_5fe10 : decode_any W_5fe10 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe14 : bv 32 := 0x7e013403.
Lemma F_5fe14 : fetch_word Asan.M.loaded_segments (0x5fe14 : word) = Some W_5fe14.
Proof. vm_refl. Qed.
Lemma D_5fe14 : decode_any W_5fe14 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe18 : bv 32 := 0x7d813483.
Lemma F_5fe18 : fetch_word Asan.M.loaded_segments (0x5fe18 : word) = Some W_5fe18.
Proof. vm_refl. Qed.
Lemma D_5fe18 : decode_any W_5fe18 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe1c : bv 32 := 0x7d013903.
Lemma F_5fe1c : fetch_word Asan.M.loaded_segments (0x5fe1c : word) = Some W_5fe1c.
Proof. vm_refl. Qed.
Lemma D_5fe1c : decode_any W_5fe1c = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe20 : bv 32 := 0x7c813983.
Lemma F_5fe20 : fetch_word Asan.M.loaded_segments (0x5fe20 : word) = Some W_5fe20.
Proof. vm_refl. Qed.
Lemma D_5fe20 : decode_any W_5fe20 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe24 : bv 32 := 0x7c013a03.
Lemma F_5fe24 : fetch_word Asan.M.loaded_segments (0x5fe24 : word) = Some W_5fe24.
Proof. vm_refl. Qed.
Lemma D_5fe24 : decode_any W_5fe24 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe28 : bv 32 := 0x7b813a83.
Lemma F_5fe28 : fetch_word Asan.M.loaded_segments (0x5fe28 : word) = Some W_5fe28.
Proof. vm_refl. Qed.
Lemma D_5fe28 : decode_any W_5fe28 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe2c : bv 32 := 0x7f010113.
Lemma F_5fe2c : fetch_word Asan.M.loaded_segments (0x5fe2c : word) = Some W_5fe2c.
Proof. vm_refl. Qed.
Lemma D_5fe2c : decode_any W_5fe2c = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe30 : bv 32 := 0x00008067.
Lemma F_5fe30 : fetch_word Asan.M.loaded_segments (0x5fe30 : word) = Some W_5fe30.
Proof. vm_refl. Qed.
Lemma D_5fe30 : decode_any W_5fe30 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe34 : bv 32 := 0x81010113.
Lemma F_5fe34 : fetch_word Asan.M.loaded_segments (0x5fe34 : word) = Some W_5fe34.
Proof. vm_refl. Qed.
Lemma D_5fe34 : decode_any W_5fe34 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe38 : bv 32 := 0x7e113423.
Lemma F_5fe38 : fetch_word Asan.M.loaded_segments (0x5fe38 : word) = Some W_5fe38.
Proof. vm_refl. Qed.
Lemma D_5fe38 : decode_any W_5fe38 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe3c : bv 32 := 0x7e813023.
Lemma F_5fe3c : fetch_word Asan.M.loaded_segments (0x5fe3c : word) = Some W_5fe3c.
Proof. vm_refl. Qed.
Lemma D_5fe3c : decode_any W_5fe3c = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe40 : bv 32 := 0x7c913c23.
Lemma F_5fe40 : fetch_word Asan.M.loaded_segments (0x5fe40 : word) = Some W_5fe40.
Proof. vm_refl. Qed.
Lemma D_5fe40 : decode_any W_5fe40 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe44 : bv 32 := 0x7d213823.
Lemma F_5fe44 : fetch_word Asan.M.loaded_segments (0x5fe44 : word) = Some W_5fe44.
Proof. vm_refl. Qed.
Lemma D_5fe44 : decode_any W_5fe44 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe48 : bv 32 := 0x7d313423.
Lemma F_5fe48 : fetch_word Asan.M.loaded_segments (0x5fe48 : word) = Some W_5fe48.
Proof. vm_refl. Qed.
Lemma D_5fe48 : decode_any W_5fe48 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe4c : bv 32 := 0x7d413023.
Lemma F_5fe4c : fetch_word Asan.M.loaded_segments (0x5fe4c : word) = Some W_5fe4c.
Proof. vm_refl. Qed.
Lemma D_5fe4c : decode_any W_5fe4c = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe50 : bv 32 := 0x7b513c23.
Lemma F_5fe50 : fetch_word Asan.M.loaded_segments (0x5fe50 : word) = Some W_5fe50.
Proof. vm_refl. Qed.
Lemma D_5fe50 : decode_any W_5fe50 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe54 : bv 32 := 0x7f010413.
Lemma F_5fe54 : fetch_word Asan.M.loaded_segments (0x5fe54 : word) = Some W_5fe54.
Proof. vm_refl. Qed.
Lemma D_5fe54 : decode_any W_5fe54 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe58 : bv 32 := 0xfa010113.
Lemma F_5fe58 : fetch_word Asan.M.loaded_segments (0x5fe58 : word) = Some W_5fe58.
Proof. vm_refl. Qed.
Lemma D_5fe58 : decode_any W_5fe58 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe5c : bv 32 := 0x00008913.
Lemma F_5fe5c : fetch_word Asan.M.loaded_segments (0x5fe5c : word) = Some W_5fe5c.
Proof. vm_refl. Qed.
Lemma D_5fe5c : decode_any W_5fe5c = Some (OpImm ALU_ADD 18 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe60 : bv 32 := 0x00050493.
Lemma F_5fe60 : fetch_word Asan.M.loaded_segments (0x5fe60 : word) = Some W_5fe60.
Proof. vm_refl. Qed.
Lemma D_5fe60 : decode_any W_5fe60 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe64 : bv 32 := 0x180070ef.
Lemma F_5fe64 : fetch_word Asan.M.loaded_segments (0x5fe64 : word) = Some W_5fe64.
Proof. vm_refl. Qed.
Lemma D_5fe64 : decode_any W_5fe64 = Some (Jal 1 29056, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe68 : bv 32 := 0x06050063.
Lemma F_5fe68 : fetch_word Asan.M.loaded_segments (0x5fe68 : word) = Some W_5fe68.
Proof. vm_refl. Qed.
Lemma D_5fe68 : decode_any W_5fe68 = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe6c : bv 32 := 0x80040a13.
Lemma F_5fe6c : fetch_word Asan.M.loaded_segments (0x5fe6c : word) = Some W_5fe6c.
Proof. vm_refl. Qed.
Lemma D_5fe6c : decode_any W_5fe6c = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe70 : bv 32 := 0xfb0a0a13.
Lemma F_5fe70 : fetch_word Asan.M.loaded_segments (0x5fe70 : word) = Some W_5fe70.
Proof. vm_refl. Qed.
Lemma D_5fe70 : decode_any W_5fe70 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe74 : bv 32 := 0x80040513.
Lemma F_5fe74 : fetch_word Asan.M.loaded_segments (0x5fe74 : word) = Some W_5fe74.
Proof. vm_refl. Qed.
Lemma D_5fe74 : decode_any W_5fe74 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe78 : bv 32 := 0xfc050513.
Lemma F_5fe78 : fetch_word Asan.M.loaded_segments (0x5fe78 : word) = Some W_5fe78.
Proof. vm_refl. Qed.
Lemma D_5fe78 : decode_any W_5fe78 = Some (OpImm ALU_ADD 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe7c : bv 32 := 0x7ffa0a93.
Lemma F_5fe7c : fetch_word Asan.M.loaded_segments (0x5fe7c : word) = Some W_5fe7c.
Proof. vm_refl. Qed.
Lemma D_5fe7c : decode_any W_5fe7c = Some (OpImm ALU_ADD 21 20 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe80 : bv 32 := 0x000ab4a3.
Lemma F_5fe80 : fetch_word Asan.M.loaded_segments (0x5fe80 : word) = Some W_5fe80.
Proof. vm_refl. Qed.
Lemma D_5fe80 : decode_any W_5fe80 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe84 : bv 32 := 0x00aa3023.
Lemma F_5fe84 : fetch_word Asan.M.loaded_segments (0x5fe84 : word) = Some W_5fe84.
Proof. vm_refl. Qed.
Lemma D_5fe84 : decode_any W_5fe84 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe88 : bv 32 := 0x000a3423.
Lemma F_5fe88 : fetch_word Asan.M.loaded_segments (0x5fe88 : word) = Some W_5fe88.
Proof. vm_refl. Qed.
Lemma D_5fe88 : decode_any W_5fe88 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe8c : bv 32 := 0x6e1070ef.
Lemma F_5fe8c : fetch_word Asan.M.loaded_segments (0x5fe8c : word) = Some W_5fe8c.
Proof. vm_refl. Qed.
Lemma D_5fe8c : decode_any W_5fe8c = Some (Jal 1 32480, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe90 : bv 32 := 0x00200593.
Lemma F_5fe90 : fetch_word Asan.M.loaded_segments (0x5fe90 : word) = Some W_5fe90.
Proof. vm_refl. Qed.
Lemma D_5fe90 : decode_any W_5fe90 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe94 : bv 32 := 0x06a5e263.
Lemma F_5fe94 : fetch_word Asan.M.loaded_segments (0x5fe94 : word) = Some W_5fe94.
Proof. vm_refl. Qed.
Lemma D_5fe94 : decode_any W_5fe94 = Some (Branch BC_LTU 11 10 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe98 : bv 32 := 0x6d5070ef.
Lemma F_5fe98 : fetch_word Asan.M.loaded_segments (0x5fe98 : word) = Some W_5fe98.
Proof. vm_refl. Qed.
Lemma D_5fe98 : decode_any W_5fe98 = Some (Jal 1 32468, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fe9c : bv 32 := 0x00aa2423.
Lemma F_5fe9c : fetch_word Asan.M.loaded_segments (0x5fe9c : word) = Some W_5fe9c.
Proof. vm_refl. Qed.
Lemma D_5fe9c : decode_any W_5fe9c = Some (Store SZ4 20 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fea0 : bv 32 := 0x6cd070ef.
Lemma F_5fea0 : fetch_word Asan.M.loaded_segments (0x5fea0 : word) = Some W_5fea0.
Proof. vm_refl. Qed.
Lemma D_5fea0 : decode_any W_5fea0 = Some (Jal 1 32460, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fea4 : bv 32 := 0x0a050a63.
Lemma F_5fea4 : fetch_word Asan.M.loaded_segments (0x5fea4 : word) = Some W_5fea4.
Proof. vm_refl. Qed.
Lemma D_5fea4 : decode_any W_5fea4 = Some (Branch BC_EQ 10 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fea8 : bv 32 := 0x008ab4a3.
Lemma F_5fea8 : fetch_word Asan.M.loaded_segments (0x5fea8 : word) = Some W_5fea8.
Proof. vm_refl. Qed.
Lemma D_5fea8 : decode_any W_5fea8 = Some (Store SZ8 21 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5feac : bv 32 := 0x181200ef.
Lemma F_5feac : fetch_word Asan.M.loaded_segments (0x5feac : word) = Some W_5feac.
Proof. vm_refl. Qed.
Lemma D_5feac : decode_any W_5feac = Some (Jal 1 133504, 4%Z).
Proof. vm_refl. Qed.

Definition W_5feb0 : bv 32 := 0x00aa3823.
Lemma F_5feb0 : fetch_word Asan.M.loaded_segments (0x5feb0 : word) = Some W_5feb0.
Proof. vm_refl. Qed.
Lemma D_5feb0 : decode_any W_5feb0 = Some (Store SZ8 20 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5feb4 : bv 32 := 0x6b9070ef.
Lemma F_5feb4 : fetch_word Asan.M.loaded_segments (0x5feb4 : word) = Some W_5feb4.
Proof. vm_refl. Qed.
Lemma D_5feb4 : decode_any W_5feb4 = Some (Jal 1 32440, 4%Z).
Proof. vm_refl. Qed.

Definition W_5feb8 : bv 32 := 0x00200593.
Lemma F_5feb8 : fetch_word Asan.M.loaded_segments (0x5feb8 : word) = Some W_5feb8.
Proof. vm_refl. Qed.
Lemma D_5feb8 : decode_any W_5feb8 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5febc : bv 32 := 0x08b56e63.
Lemma F_5febc : fetch_word Asan.M.loaded_segments (0x5febc : word) = Some W_5febc.
Proof. vm_refl. Qed.
Lemma D_5febc : decode_any W_5febc = Some (Branch BC_LTU 10 11 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fec0 : bv 32 := 0x012a3c23.
Lemma F_5fec0 : fetch_word Asan.M.loaded_segments (0x5fec0 : word) = Some W_5fec0.
Proof. vm_refl. Qed.
Lemma D_5fec0 : decode_any W_5fec0 = Some (Store SZ8 20 18 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fec4 : bv 32 := 0x0940006f.
Lemma F_5fec4 : fetch_word Asan.M.loaded_segments (0x5fec4 : word) = Some W_5fec4.
Proof. vm_refl. Qed.
Lemma D_5fec4 : decode_any W_5fec4 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fec8 : bv 32 := 0x00800593.
Lemma F_5fec8 : fetch_word Asan.M.loaded_segments (0x5fec8 : word) = Some W_5fec8.
Proof. vm_refl. Qed.
Lemma D_5fec8 : decode_any W_5fec8 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fecc : bv 32 := 0x00048513.
Lemma F_5fecc : fetch_word Asan.M.loaded_segments (0x5fecc : word) = Some W_5fecc.
Proof. vm_refl. Qed.
Lemma D_5fecc : decode_any W_5fecc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fed0 : bv 32 := 0x06010113.
Lemma F_5fed0 : fetch_word Asan.M.loaded_segments (0x5fed0 : word) = Some W_5fed0.
Proof. vm_refl. Qed.
Lemma D_5fed0 : decode_any W_5fed0 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fed4 : bv 32 := 0x7e813083.
Lemma F_5fed4 : fetch_word Asan.M.loaded_segments (0x5fed4 : word) = Some W_5fed4.
Proof. vm_refl. Qed.
Lemma D_5fed4 : decode_any W_5fed4 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fed8 : bv 32 := 0x7e013403.
Lemma F_5fed8 : fetch_word Asan.M.loaded_segments (0x5fed8 : word) = Some W_5fed8.
Proof. vm_refl. Qed.
Lemma D_5fed8 : decode_any W_5fed8 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fedc : bv 32 := 0x7d813483.
Lemma F_5fedc : fetch_word Asan.M.loaded_segments (0x5fedc : word) = Some W_5fedc.
Proof. vm_refl. Qed.
Lemma D_5fedc : decode_any W_5fedc = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fee0 : bv 32 := 0x7d013903.
Lemma F_5fee0 : fetch_word Asan.M.loaded_segments (0x5fee0 : word) = Some W_5fee0.
Proof. vm_refl. Qed.
Lemma D_5fee0 : decode_any W_5fee0 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fee4 : bv 32 := 0x7c813983.
Lemma F_5fee4 : fetch_word Asan.M.loaded_segments (0x5fee4 : word) = Some W_5fee4.
Proof. vm_refl. Qed.
Lemma D_5fee4 : decode_any W_5fee4 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fee8 : bv 32 := 0x7c013a03.
Lemma F_5fee8 : fetch_word Asan.M.loaded_segments (0x5fee8 : word) = Some W_5fee8.
Proof. vm_refl. Qed.
Lemma D_5fee8 : decode_any W_5fee8 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5feec : bv 32 := 0x7b813a83.
Lemma F_5feec : fetch_word Asan.M.loaded_segments (0x5feec : word) = Some W_5feec.
Proof. vm_refl. Qed.
Lemma D_5feec : decode_any W_5feec = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fef0 : bv 32 := 0x7f010113.
Lemma F_5fef0 : fetch_word Asan.M.loaded_segments (0x5fef0 : word) = Some W_5fef0.
Proof. vm_refl. Qed.
Lemma D_5fef0 : decode_any W_5fef0 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fef4 : bv 32 := 0x09c0006f.
Lemma F_5fef4 : fetch_word Asan.M.loaded_segments (0x5fef4 : word) = Some W_5fef4.
Proof. vm_refl. Qed.
Lemma D_5fef4 : decode_any W_5fef4 = Some (Jal 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fef8 : bv 32 := 0x135200ef.
Lemma F_5fef8 : fetch_word Asan.M.loaded_segments (0x5fef8 : word) = Some W_5fef8.
Proof. vm_refl. Qed.
Lemma D_5fef8 : decode_any W_5fef8 = Some (Jal 1 133428, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fefc : bv 32 := 0x00076597.
Lemma F_5fefc : fetch_word Asan.M.loaded_segments (0x5fefc : word) = Some W_5fefc.
Proof. vm_refl. Qed.
Lemma D_5fefc : decode_any W_5fefc = Some (Auipc 11 118, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff00 : bv 32 := 0x9ac5b583.
Lemma F_5ff00 : fetch_word Asan.M.loaded_segments (0x5ff00 : word) = Some W_5ff00.
Proof. vm_refl. Qed.
Lemma D_5ff00 : decode_any W_5ff00 = Some (Load SZ8 true 11 11 2476, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff04 : bv 32 := 0x0225c983.
Lemma F_5ff04 : fetch_word Asan.M.loaded_segments (0x5ff04 : word) = Some W_5ff04.
Proof. vm_refl. Qed.
Lemma D_5ff04 : decode_any W_5ff04 = Some (Load SZ1 false 19 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff08 : bv 32 := 0x00050913.
Lemma F_5ff08 : fetch_word Asan.M.loaded_segments (0x5ff08 : word) = Some W_5ff08.
Proof. vm_refl. Qed.
Lemma D_5ff08 : decode_any W_5ff08 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff0c : bv 32 := 0x661070ef.
Lemma F_5ff0c : fetch_word Asan.M.loaded_segments (0x5ff0c : word) = Some W_5ff0c.
Proof. vm_refl. Qed.
Lemma D_5ff0c : decode_any W_5ff0c = Some (Jal 1 32352, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff10 : bv 32 := 0x00050793.
Lemma F_5ff10 : fetch_word Asan.M.loaded_segments (0x5ff10 : word) = Some W_5ff10.
Proof. vm_refl. Qed.
Lemma D_5ff10 : decode_any W_5ff10 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff14 : bv 32 := 0x00153513.
Lemma F_5ff14 : fetch_word Asan.M.loaded_segments (0x5ff14 : word) = Some W_5ff14.
Proof. vm_refl. Qed.
Lemma D_5ff14 : decode_any W_5ff14 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff18 : bv 32 := 0xfff50513.
Lemma F_5ff18 : fetch_word Asan.M.loaded_segments (0x5ff18 : word) = Some W_5ff18.
Proof. vm_refl. Qed.
Lemma D_5ff18 : decode_any W_5ff18 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff1c : bv 32 := 0x008575b3.
Lemma F_5ff1c : fetch_word Asan.M.loaded_segments (0x5ff1c : word) = Some W_5ff1c.
Proof. vm_refl. Qed.
Lemma D_5ff1c : decode_any W_5ff1c = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff20 : bv 32 := 0x00100513.
Lemma F_5ff20 : fetch_word Asan.M.loaded_segments (0x5ff20 : word) = Some W_5ff20.
Proof. vm_refl. Qed.
Lemma D_5ff20 : decode_any W_5ff20 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff24 : bv 32 := 0x00bab4a3.
Lemma F_5ff24 : fetch_word Asan.M.loaded_segments (0x5ff24 : word) = Some W_5ff24.
Proof. vm_refl. Qed.
Lemma D_5ff24 : decode_any W_5ff24 = Some (Store SZ8 21 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff28 : bv 32 := 0x00f56a63.
Lemma F_5ff28 : fetch_word Asan.M.loaded_segments (0x5ff28 : word) = Some W_5ff28.
Proof. vm_refl. Qed.
Lemma D_5ff28 : decode_any W_5ff28 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff2c : bv 32 := 0x00a79463.
Lemma F_5ff2c : fetch_word Asan.M.loaded_segments (0x5ff2c : word) = Some W_5ff2c.
Proof. vm_refl. Qed.
Lemma D_5ff2c : decode_any W_5ff2c = Some (Branch BC_NE 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff30 : bv 32 := 0x012a3823.
Lemma F_5ff30 : fetch_word Asan.M.loaded_segments (0x5ff30 : word) = Some W_5ff30.
Proof. vm_refl. Qed.
Lemma D_5ff30 : decode_any W_5ff30 = Some (Store SZ8 20 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff34 : bv 32 := 0x00fa2423.
Lemma F_5ff34 : fetch_word Asan.M.loaded_segments (0x5ff34 : word) = Some W_5ff34.
Proof. vm_refl. Qed.
Lemma D_5ff34 : decode_any W_5ff34 = Some (Store SZ4 20 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff38 : bv 32 := 0x0200006f.
Lemma F_5ff38 : fetch_word Asan.M.loaded_segments (0x5ff38 : word) = Some W_5ff38.
Proof. vm_refl. Qed.
Lemma D_5ff38 : decode_any W_5ff38 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff3c : bv 32 := 0x80040513.
Lemma F_5ff3c : fetch_word Asan.M.loaded_segments (0x5ff3c : word) = Some W_5ff3c.
Proof. vm_refl. Qed.
Lemma D_5ff3c : decode_any W_5ff3c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff40 : bv 32 := 0xfb050513.
Lemma F_5ff40 : fetch_word Asan.M.loaded_segments (0x5ff40 : word) = Some W_5ff40.
Proof. vm_refl. Qed.
Lemma D_5ff40 : decode_any W_5ff40 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff44 : bv 32 := 0x00090593.
Lemma F_5ff44 : fetch_word Asan.M.loaded_segments (0x5ff44 : word) = Some W_5ff44.
Proof. vm_refl. Qed.
Lemma D_5ff44 : decode_any W_5ff44 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff48 : bv 32 := 0x00040613.
Lemma F_5ff48 : fetch_word Asan.M.loaded_segments (0x5ff48 : word) = Some W_5ff48.
Proof. vm_refl. Qed.
Lemma D_5ff48 : decode_any W_5ff48 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff4c : bv 32 := 0x00000693.
Lemma F_5ff4c : fetch_word Asan.M.loaded_segments (0x5ff4c : word) = Some W_5ff4c.
Proof. vm_refl. Qed.
Lemma D_5ff4c : decode_any W_5ff4c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff50 : bv 32 := 0x00098713.
Lemma F_5ff50 : fetch_word Asan.M.loaded_segments (0x5ff50 : word) = Some W_5ff50.
Proof. vm_refl. Qed.
Lemma D_5ff50 : decode_any W_5ff50 = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff54 : bv 32 := 0x629070ef.
Lemma F_5ff54 : fetch_word Asan.M.loaded_segments (0x5ff54 : word) = Some W_5ff54.
Proof. vm_refl. Qed.
Lemma D_5ff54 : decode_any W_5ff54 = Some (Jal 1 32296, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff58 : bv 32 := 0x80040593.
Lemma F_5ff58 : fetch_word Asan.M.loaded_segments (0x5ff58 : word) = Some W_5ff58.
Proof. vm_refl. Qed.
Lemma D_5ff58 : decode_any W_5ff58 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff5c : bv 32 := 0xfb058593.
Lemma F_5ff5c : fetch_word Asan.M.loaded_segments (0x5ff5c : word) = Some W_5ff5c.
Proof. vm_refl. Qed.
Lemma D_5ff5c : decode_any W_5ff5c = Some (OpImm ALU_ADD 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff60 : bv 32 := 0x00048513.
Lemma F_5ff60 : fetch_word Asan.M.loaded_segments (0x5ff60 : word) = Some W_5ff60.
Proof. vm_refl. Qed.
Lemma D_5ff60 : decode_any W_5ff60 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff64 : bv 32 := 0xbb0dd0ef.
Lemma F_5ff64 : fetch_word Asan.M.loaded_segments (0x5ff64 : word) = Some W_5ff64.
Proof. vm_refl. Qed.
Lemma D_5ff64 : decode_any W_5ff64 = Some (Jal 1 1954736, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff68 : bv 32 := 0x06010113.
Lemma F_5ff68 : fetch_word Asan.M.loaded_segments (0x5ff68 : word) = Some W_5ff68.
Proof. vm_refl. Qed.
Lemma D_5ff68 : decode_any W_5ff68 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff6c : bv 32 := 0x7e813083.
Lemma F_5ff6c : fetch_word Asan.M.loaded_segments (0x5ff6c : word) = Some W_5ff6c.
Proof. vm_refl. Qed.
Lemma D_5ff6c : decode_any W_5ff6c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff70 : bv 32 := 0x7e013403.
Lemma F_5ff70 : fetch_word Asan.M.loaded_segments (0x5ff70 : word) = Some W_5ff70.
Proof. vm_refl. Qed.
Lemma D_5ff70 : decode_any W_5ff70 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff74 : bv 32 := 0x7d813483.
Lemma F_5ff74 : fetch_word Asan.M.loaded_segments (0x5ff74 : word) = Some W_5ff74.
Proof. vm_refl. Qed.
Lemma D_5ff74 : decode_any W_5ff74 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff78 : bv 32 := 0x7d013903.
Lemma F_5ff78 : fetch_word Asan.M.loaded_segments (0x5ff78 : word) = Some W_5ff78.
Proof. vm_refl. Qed.
Lemma D_5ff78 : decode_any W_5ff78 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff7c : bv 32 := 0x7c813983.
Lemma F_5ff7c : fetch_word Asan.M.loaded_segments (0x5ff7c : word) = Some W_5ff7c.
Proof. vm_refl. Qed.
Lemma D_5ff7c : decode_any W_5ff7c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff80 : bv 32 := 0x7c013a03.
Lemma F_5ff80 : fetch_word Asan.M.loaded_segments (0x5ff80 : word) = Some W_5ff80.
Proof. vm_refl. Qed.
Lemma D_5ff80 : decode_any W_5ff80 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff84 : bv 32 := 0x7b813a83.
Lemma F_5ff84 : fetch_word Asan.M.loaded_segments (0x5ff84 : word) = Some W_5ff84.
Proof. vm_refl. Qed.
Lemma D_5ff84 : decode_any W_5ff84 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff88 : bv 32 := 0x7f010113.
Lemma F_5ff88 : fetch_word Asan.M.loaded_segments (0x5ff88 : word) = Some W_5ff88.
Proof. vm_refl. Qed.
Lemma D_5ff88 : decode_any W_5ff88 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff8c : bv 32 := 0x00008067.
Lemma F_5ff8c : fetch_word Asan.M.loaded_segments (0x5ff8c : word) = Some W_5ff8c.
Proof. vm_refl. Qed.
Lemma D_5ff8c : decode_any W_5ff8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff90 : bv 32 := 0xfe010113.
Lemma F_5ff90 : fetch_word Asan.M.loaded_segments (0x5ff90 : word) = Some W_5ff90.
Proof. vm_refl. Qed.
Lemma D_5ff90 : decode_any W_5ff90 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff94 : bv 32 := 0x00113c23.
Lemma F_5ff94 : fetch_word Asan.M.loaded_segments (0x5ff94 : word) = Some W_5ff94.
Proof. vm_refl. Qed.
Lemma D_5ff94 : decode_any W_5ff94 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff98 : bv 32 := 0x00813823.
Lemma F_5ff98 : fetch_word Asan.M.loaded_segments (0x5ff98 : word) = Some W_5ff98.
Proof. vm_refl. Qed.
Lemma D_5ff98 : decode_any W_5ff98 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ff9c : bv 32 := 0x00913423.
Lemma F_5ff9c : fetch_word Asan.M.loaded_segments (0x5ff9c : word) = Some W_5ff9c.
Proof. vm_refl. Qed.
Lemma D_5ff9c : decode_any W_5ff9c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffa0 : bv 32 := 0x00058613.
Lemma F_5ffa0 : fetch_word Asan.M.loaded_segments (0x5ffa0 : word) = Some W_5ffa0.
Proof. vm_refl. Qed.
Lemma D_5ffa0 : decode_any W_5ffa0 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffa4 : bv 32 := 0x00000593.
Lemma F_5ffa4 : fetch_word Asan.M.loaded_segments (0x5ffa4 : word) = Some W_5ffa4.
Proof. vm_refl. Qed.
Lemma D_5ffa4 : decode_any W_5ffa4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffa8 : bv 32 := 0x2110b0ef.
Lemma F_5ffa8 : fetch_word Asan.M.loaded_segments (0x5ffa8 : word) = Some W_5ffa8.
Proof. vm_refl. Qed.
Lemma D_5ffa8 : decode_any W_5ffa8 = Some (Jal 1 47632, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffac : bv 32 := 0x00050413.
Lemma F_5ffac : fetch_word Asan.M.loaded_segments (0x5ffac : word) = Some W_5ffac.
Proof. vm_refl. Qed.
Lemma D_5ffac : decode_any W_5ffac = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffb0 : bv 32 := 0x0b10b0ef.
Lemma F_5ffb0 : fetch_word Asan.M.loaded_segments (0x5ffb0 : word) = Some W_5ffb0.
Proof. vm_refl. Qed.
Lemma D_5ffb0 : decode_any W_5ffb0 = Some (Jal 1 47280, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffb4 : bv 32 := 0x02f45593.
Lemma F_5ffb4 : fetch_word Asan.M.loaded_segments (0x5ffb4 : word) = Some W_5ffb4.
Proof. vm_refl. Qed.
Lemma D_5ffb4 : decode_any W_5ffb4 = Some (ShiftImm ALU_SRL 11 8 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffb8 : bv 32 := 0x08059263.
Lemma F_5ffb8 : fetch_word Asan.M.loaded_segments (0x5ffb8 : word) = Some W_5ffb8.
Proof. vm_refl. Qed.
Lemma D_5ffb8 : decode_any W_5ffb8 = Some (Branch BC_NE 11 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffbc : bv 32 := 0x02045593.
Lemma F_5ffbc : fetch_word Asan.M.loaded_segments (0x5ffbc : word) = Some W_5ffbc.
Proof. vm_refl. Qed.
Lemma D_5ffbc : decode_any W_5ffbc = Some (ShiftImm ALU_SRL 11 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffc0 : bv 32 := 0x00359613.
Lemma F_5ffc0 : fetch_word Asan.M.loaded_segments (0x5ffc0 : word) = Some W_5ffc0.
Proof. vm_refl. Qed.
Lemma D_5ffc0 : decode_any W_5ffc0 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffc4 : bv 32 := 0x00c50633.
Lemma F_5ffc4 : fetch_word Asan.M.loaded_segments (0x5ffc4 : word) = Some W_5ffc4.
Proof. vm_refl. Qed.
Lemma D_5ffc4 : decode_any W_5ffc4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffc8 : bv 32 := 0x00863683.
Lemma F_5ffc8 : fetch_word Asan.M.loaded_segments (0x5ffc8 : word) = Some W_5ffc8.
Proof. vm_refl. Qed.
Lemma D_5ffc8 : decode_any W_5ffc8 = Some (Load SZ8 true 13 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffcc : bv 32 := 0x0230000f.
Lemma F_5ffcc : fetch_word Asan.M.loaded_segments (0x5ffcc : word) = Some W_5ffcc.
Proof. vm_refl. Qed.
Lemma D_5ffcc : decode_any W_5ffcc = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffd0 : bv 32 := 0x06068663.
Lemma F_5ffd0 : fetch_word Asan.M.loaded_segments (0x5ffd0 : word) = Some W_5ffd0.
Proof. vm_refl. Qed.
Lemma D_5ffd0 : decode_any W_5ffd0 = Some (Branch BC_EQ 13 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffd4 : bv 32 := 0x00863603.
Lemma F_5ffd4 : fetch_word Asan.M.loaded_segments (0x5ffd4 : word) = Some W_5ffd4.
Proof. vm_refl. Qed.
Lemma D_5ffd4 : decode_any W_5ffd4 = Some (Load SZ8 true 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffd8 : bv 32 := 0x01445493.
Lemma F_5ffd8 : fetch_word Asan.M.loaded_segments (0x5ffd8 : word) = Some W_5ffd8.
Proof. vm_refl. Qed.
Lemma D_5ffd8 : decode_any W_5ffd8 = Some (ShiftImm ALU_SRL 9 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffdc : bv 32 := 0x04060463.
Lemma F_5ffdc : fetch_word Asan.M.loaded_segments (0x5ffdc : word) = Some W_5ffdc.
Proof. vm_refl. Qed.
Lemma D_5ffdc : decode_any W_5ffdc = Some (Branch BC_EQ 12 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffe0 : bv 32 := 0x03449493.
Lemma F_5ffe0 : fetch_word Asan.M.loaded_segments (0x5ffe0 : word) = Some W_5ffe0.
Proof. vm_refl. Qed.
Lemma D_5ffe0 : decode_any W_5ffe0 = Some (ShiftImm ALU_SLL 9 9 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffe4 : bv 32 := 0x0344d493.
Lemma F_5ffe4 : fetch_word Asan.M.loaded_segments (0x5ffe4 : word) = Some W_5ffe4.
Proof. vm_refl. Qed.
Lemma D_5ffe4 : decode_any W_5ffe4 = Some (ShiftImm ALU_SRL 9 9 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffe8 : bv 32 := 0x00960633.
Lemma F_5ffe8 : fetch_word Asan.M.loaded_segments (0x5ffe8 : word) = Some W_5ffe8.
Proof. vm_refl. Qed.
Lemma D_5ffe8 : decode_any W_5ffe8 = Some (Op ALU_ADD 12 12 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ffec : bv 32 := 0x00064503.
Lemma F_5ffec : fetch_word Asan.M.loaded_segments (0x5ffec : word) = Some W_5ffec.
Proof. vm_refl. Qed.
Lemma D_5ffec : decode_any W_5ffec = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fff0 : bv 32 := 0x04050663.
Lemma F_5fff0 : fetch_word Asan.M.loaded_segments (0x5fff0 : word) = Some W_5fff0.
Proof. vm_refl. Qed.
Lemma D_5fff0 : decode_any W_5fff0 = Some (Branch BC_EQ 10 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fff4 : bv 32 := 0x06d0b0ef.
Lemma F_5fff4 : fetch_word Asan.M.loaded_segments (0x5fff4 : word) = Some W_5fff4.
Proof. vm_refl. Qed.
Lemma D_5fff4 : decode_any W_5fff4 = Some (Jal 1 47212, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fff8 : bv 32 := 0x00040593.
Lemma F_5fff8 : fetch_word Asan.M.loaded_segments (0x5fff8 : word) = Some W_5fff8.
Proof. vm_refl. Qed.
Lemma D_5fff8 : decode_any W_5fff8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5fffc : bv 32 := 0x5dc000ef.
Lemma F_5fffc : fetch_word Asan.M.loaded_segments (0x5fffc : word) = Some W_5fffc.
Proof. vm_refl. Qed.
Lemma D_5fffc : decode_any W_5fffc = Some (Jal 1 1500, 4%Z).
Proof. vm_refl. Qed.

Definition W_60000 : bv 32 := 0x00050593.
Lemma F_60000 : fetch_word Asan.M.loaded_segments (0x60000 : word) = Some W_60000.
Proof. vm_refl. Qed.
Lemma D_60000 : decode_any W_60000 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60004 : bv 32 := 0x00040513.
Lemma F_60004 : fetch_word Asan.M.loaded_segments (0x60004 : word) = Some W_60004.
Proof. vm_refl. Qed.
Lemma D_60004 : decode_any W_60004 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60008 : bv 32 := 0x0242a0ef.
Lemma F_60008 : fetch_word Asan.M.loaded_segments (0x60008 : word) = Some W_60008.
Proof. vm_refl. Qed.
Lemma D_60008 : decode_any W_60008 = Some (Jal 1 172068, 4%Z).
Proof. vm_refl. Qed.

Definition W_6000c : bv 32 := 0x00040513.
Lemma F_6000c : fetch_word Asan.M.loaded_segments (0x6000c : word) = Some W_6000c.
Proof. vm_refl. Qed.
Lemma D_6000c : decode_any W_6000c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60010 : bv 32 := 0x01813083.
Lemma F_60010 : fetch_word Asan.M.loaded_segments (0x60010 : word) = Some W_60010.
Proof. vm_refl. Qed.
Lemma D_60010 : decode_any W_60010 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_60014 : bv 32 := 0x01013403.
Lemma F_60014 : fetch_word Asan.M.loaded_segments (0x60014 : word) = Some W_60014.
Proof. vm_refl. Qed.
Lemma D_60014 : decode_any W_60014 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_60018 : bv 32 := 0x00813483.
Lemma F_60018 : fetch_word Asan.M.loaded_segments (0x60018 : word) = Some W_60018.
Proof. vm_refl. Qed.
Lemma D_60018 : decode_any W_60018 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6001c : bv 32 := 0x02010113.
Lemma F_6001c : fetch_word Asan.M.loaded_segments (0x6001c : word) = Some W_6001c.
Proof. vm_refl. Qed.
Lemma D_6001c : decode_any W_6001c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_60020 : bv 32 := 0x00008067.
Lemma F_60020 : fetch_word Asan.M.loaded_segments (0x60020 : word) = Some W_60020.
Proof. vm_refl. Qed.
Lemma D_60020 : decode_any W_60020 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60024 : bv 32 := 0x4b4000ef.
Lemma F_60024 : fetch_word Asan.M.loaded_segments (0x60024 : word) = Some W_60024.
Proof. vm_refl. Qed.
Lemma D_60024 : decode_any W_60024 = Some (Jal 1 1204, 4%Z).
Proof. vm_refl. Qed.

Definition W_60028 : bv 32 := 0x03449493.
Lemma F_60028 : fetch_word Asan.M.loaded_segments (0x60028 : word) = Some W_60028.
Proof. vm_refl. Qed.
Lemma D_60028 : decode_any W_60028 = Some (ShiftImm ALU_SLL 9 9 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_6002c : bv 32 := 0x0344d493.
Lemma F_6002c : fetch_word Asan.M.loaded_segments (0x6002c : word) = Some W_6002c.
Proof. vm_refl. Qed.
Lemma D_6002c : decode_any W_6002c = Some (ShiftImm ALU_SRL 9 9 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_60030 : bv 32 := 0x00950633.
Lemma F_60030 : fetch_word Asan.M.loaded_segments (0x60030 : word) = Some W_60030.
Proof. vm_refl. Qed.
Lemma D_60030 : decode_any W_60030 = Some (Op ALU_ADD 12 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_60034 : bv 32 := 0x00064503.
Lemma F_60034 : fetch_word Asan.M.loaded_segments (0x60034 : word) = Some W_60034.
Proof. vm_refl. Qed.
Lemma D_60034 : decode_any W_60034 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60038 : bv 32 := 0xfa051ee3.
Lemma F_60038 : fetch_word Asan.M.loaded_segments (0x60038 : word) = Some W_60038.
Proof. vm_refl. Qed.
Lemma D_60038 : decode_any W_60038 = Some (Branch BC_NE 10 0 8124, 4%Z).
Proof. vm_refl. Qed.

Definition W_6003c : bv 32 := 0xfffbc517.
Lemma F_6003c : fetch_word Asan.M.loaded_segments (0x6003c : word) = Some W_6003c.
Proof. vm_refl. Qed.
Lemma D_6003c : decode_any W_6003c = Some (Auipc 10 1048508, 4%Z).
Proof. vm_refl. Qed.

Definition W_60040 : bv 32 := 0xfffb3597.
Lemma F_60040 : fetch_word Asan.M.loaded_segments (0x60040 : word) = Some W_60040.
Proof. vm_refl. Qed.
Lemma D_60040 : decode_any W_60040 = Some (Auipc 11 1048499, 4%Z).
Proof. vm_refl. Qed.

Definition W_60044 : bv 32 := 0x45750513.
Lemma F_60044 : fetch_word Asan.M.loaded_segments (0x60044 : word) = Some W_60044.
Proof. vm_refl. Qed.
Lemma D_60044 : decode_any W_60044 = Some (OpImm ALU_ADD 10 10 1111, 4%Z).
Proof. vm_refl. Qed.

Definition W_60048 : bv 32 := 0xaaa58613.
Lemma F_60048 : fetch_word Asan.M.loaded_segments (0x60048 : word) = Some W_60048.
Proof. vm_refl. Qed.
Lemma D_60048 : decode_any W_60048 = Some (OpImm ALU_ADD 12 11 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_6004c : bv 32 := 0x02600593.
Lemma F_6004c : fetch_word Asan.M.loaded_segments (0x6004c : word) = Some W_6004c.
Proof. vm_refl. Qed.
Lemma D_6004c : decode_any W_6004c = Some (OpImm ALU_ADD 11 0 38, 4%Z).
Proof. vm_refl. Qed.

Definition W_60050 : bv 32 := 0x00000693.
Lemma F_60050 : fetch_word Asan.M.loaded_segments (0x60050 : word) = Some W_60050.
Proof. vm_refl. Qed.
Lemma D_60050 : decode_any W_60050 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60054 : bv 32 := 0x00000713.
Lemma F_60054 : fetch_word Asan.M.loaded_segments (0x60054 : word) = Some W_60054.
Proof. vm_refl. Qed.
Lemma D_60054 : decode_any W_60054 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60058 : bv 32 := 0x010190ef.
Lemma F_60058 : fetch_word Asan.M.loaded_segments (0x60058 : word) = Some W_60058.
Proof. vm_refl. Qed.
Lemma D_60058 : decode_any W_60058 = Some (Jal 1 102416, 4%Z).
Proof. vm_refl. Qed.

Definition W_6005c : bv 32 := 0x81010113.
Lemma F_6005c : fetch_word Asan.M.loaded_segments (0x6005c : word) = Some W_6005c.
Proof. vm_refl. Qed.
Lemma D_6005c : decode_any W_6005c = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_60060 : bv 32 := 0x7e113423.
Lemma F_60060 : fetch_word Asan.M.loaded_segments (0x60060 : word) = Some W_60060.
Proof. vm_refl. Qed.
Lemma D_60060 : decode_any W_60060 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_60064 : bv 32 := 0x7e813023.
Lemma F_60064 : fetch_word Asan.M.loaded_segments (0x60064 : word) = Some W_60064.
Proof. vm_refl. Qed.
Lemma D_60064 : decode_any W_60064 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_60068 : bv 32 := 0x7c913c23.
Lemma F_60068 : fetch_word Asan.M.loaded_segments (0x60068 : word) = Some W_60068.
Proof. vm_refl. Qed.
Lemma D_60068 : decode_any W_60068 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6006c : bv 32 := 0x7d213823.
Lemma F_6006c : fetch_word Asan.M.loaded_segments (0x6006c : word) = Some W_6006c.
Proof. vm_refl. Qed.
Lemma D_6006c : decode_any W_6006c = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_60070 : bv 32 := 0x7d313423.
Lemma F_60070 : fetch_word Asan.M.loaded_segments (0x60070 : word) = Some W_60070.
Proof. vm_refl. Qed.
Lemma D_60070 : decode_any W_60070 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_60074 : bv 32 := 0x7d413023.
Lemma F_60074 : fetch_word Asan.M.loaded_segments (0x60074 : word) = Some W_60074.
Proof. vm_refl. Qed.
Lemma D_60074 : decode_any W_60074 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_60078 : bv 32 := 0x7b513c23.
Lemma F_60078 : fetch_word Asan.M.loaded_segments (0x60078 : word) = Some W_60078.
Proof. vm_refl. Qed.
Lemma D_60078 : decode_any W_60078 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_6007c : bv 32 := 0x7b613823.
Lemma F_6007c : fetch_word Asan.M.loaded_segments (0x6007c : word) = Some W_6007c.
Proof. vm_refl. Qed.
Lemma D_6007c : decode_any W_6007c = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_60080 : bv 32 := 0x7f010413.
Lemma F_60080 : fetch_word Asan.M.loaded_segments (0x60080 : word) = Some W_60080.
Proof. vm_refl. Qed.
Lemma D_60080 : decode_any W_60080 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_60084 : bv 32 := 0xf9010113.
Lemma F_60084 : fetch_word Asan.M.loaded_segments (0x60084 : word) = Some W_60084.
Proof. vm_refl. Qed.
Lemma D_60084 : decode_any W_60084 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_60088 : bv 32 := 0x00008993.
Lemma F_60088 : fetch_word Asan.M.loaded_segments (0x60088 : word) = Some W_60088.
Proof. vm_refl. Qed.
Lemma D_60088 : decode_any W_60088 = Some (OpImm ALU_ADD 19 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6008c : bv 32 := 0x00058493.
Lemma F_6008c : fetch_word Asan.M.loaded_segments (0x6008c : word) = Some W_6008c.
Proof. vm_refl. Qed.
Lemma D_6008c : decode_any W_6008c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60090 : bv 32 := 0x00050913.
Lemma F_60090 : fetch_word Asan.M.loaded_segments (0x60090 : word) = Some W_60090.
Proof. vm_refl. Qed.
Lemma D_60090 : decode_any W_60090 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60094 : bv 32 := 0x751060ef.
Lemma F_60094 : fetch_word Asan.M.loaded_segments (0x60094 : word) = Some W_60094.
Proof. vm_refl. Qed.
Lemma D_60094 : decode_any W_60094 = Some (Jal 1 28496, 4%Z).
Proof. vm_refl. Qed.

Definition W_60098 : bv 32 := 0x04050463.
Lemma F_60098 : fetch_word Asan.M.loaded_segments (0x60098 : word) = Some W_60098.
Proof. vm_refl. Qed.
Lemma D_60098 : decode_any W_60098 = Some (Branch BC_EQ 10 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_6009c : bv 32 := 0x7c40b0ef.
Lemma F_6009c : fetch_word Asan.M.loaded_segments (0x6009c : word) = Some W_6009c.
Proof. vm_refl. Qed.
Lemma D_6009c : decode_any W_6009c = Some (Jal 1 47044, 4%Z).
Proof. vm_refl. Qed.

Definition W_600a0 : bv 32 := 0x02f95593.
Lemma F_600a0 : fetch_word Asan.M.loaded_segments (0x600a0 : word) = Some W_600a0.
Proof. vm_refl. Qed.
Lemma D_600a0 : decode_any W_600a0 = Some (ShiftImm ALU_SRL 11 18 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_600a4 : bv 32 := 0x08059663.
Lemma F_600a4 : fetch_word Asan.M.loaded_segments (0x600a4 : word) = Some W_600a4.
Proof. vm_refl. Qed.
Lemma D_600a4 : decode_any W_600a4 = Some (Branch BC_NE 11 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_600a8 : bv 32 := 0x02095593.
Lemma F_600a8 : fetch_word Asan.M.loaded_segments (0x600a8 : word) = Some W_600a8.
Proof. vm_refl. Qed.
Lemma D_600a8 : decode_any W_600a8 = Some (ShiftImm ALU_SRL 11 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_600ac : bv 32 := 0x00359613.
Lemma F_600ac : fetch_word Asan.M.loaded_segments (0x600ac : word) = Some W_600ac.
Proof. vm_refl. Qed.
Lemma D_600ac : decode_any W_600ac = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_600b0 : bv 32 := 0x00c50633.
Lemma F_600b0 : fetch_word Asan.M.loaded_segments (0x600b0 : word) = Some W_600b0.
Proof. vm_refl. Qed.
Lemma D_600b0 : decode_any W_600b0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_600b4 : bv 32 := 0x00863683.
Lemma F_600b4 : fetch_word Asan.M.loaded_segments (0x600b4 : word) = Some W_600b4.
Proof. vm_refl. Qed.
Lemma D_600b4 : decode_any W_600b4 = Some (Load SZ8 true 13 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_600b8 : bv 32 := 0x0230000f.
Lemma F_600b8 : fetch_word Asan.M.loaded_segments (0x600b8 : word) = Some W_600b8.
Proof. vm_refl. Qed.
Lemma D_600b8 : decode_any W_600b8 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_600bc : bv 32 := 0x06068a63.
Lemma F_600bc : fetch_word Asan.M.loaded_segments (0x600bc : word) = Some W_600bc.
Proof. vm_refl. Qed.
Lemma D_600bc : decode_any W_600bc = Some (Branch BC_EQ 13 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_600c0 : bv 32 := 0x00863603.
Lemma F_600c0 : fetch_word Asan.M.loaded_segments (0x600c0 : word) = Some W_600c0.
Proof. vm_refl. Qed.
Lemma D_600c0 : decode_any W_600c0 = Some (Load SZ8 true 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_600c4 : bv 32 := 0x01495a13.
Lemma F_600c4 : fetch_word Asan.M.loaded_segments (0x600c4 : word) = Some W_600c4.
Proof. vm_refl. Qed.
Lemma D_600c4 : decode_any W_600c4 = Some (ShiftImm ALU_SRL 20 18 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_600c8 : bv 32 := 0x04060663.
Lemma F_600c8 : fetch_word Asan.M.loaded_segments (0x600c8 : word) = Some W_600c8.
Proof. vm_refl. Qed.
Lemma D_600c8 : decode_any W_600c8 = Some (Branch BC_EQ 12 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_600cc : bv 32 := 0x034a1a13.
Lemma F_600cc : fetch_word Asan.M.loaded_segments (0x600cc : word) = Some W_600cc.
Proof. vm_refl. Qed.
Lemma D_600cc : decode_any W_600cc = Some (ShiftImm ALU_SLL 20 20 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_600d0 : bv 32 := 0x034a5513.
Lemma F_600d0 : fetch_word Asan.M.loaded_segments (0x600d0 : word) = Some W_600d0.
Proof. vm_refl. Qed.
Lemma D_600d0 : decode_any W_600d0 = Some (ShiftImm ALU_SRL 10 20 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_600d4 : bv 32 := 0x00a60533.
Lemma F_600d4 : fetch_word Asan.M.loaded_segments (0x600d4 : word) = Some W_600d4.
Proof. vm_refl. Qed.
Lemma D_600d4 : decode_any W_600d4 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_600d8 : bv 32 := 0x00054503.
Lemma F_600d8 : fetch_word Asan.M.loaded_segments (0x600d8 : word) = Some W_600d8.
Proof. vm_refl. Qed.
Lemma D_600d8 : decode_any W_600d8 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_600dc : bv 32 := 0x04050a63.
Lemma F_600dc : fetch_word Asan.M.loaded_segments (0x600dc : word) = Some W_600dc.
Proof. vm_refl. Qed.
Lemma D_600dc : decode_any W_600dc = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_600e0 : bv 32 := 0x00090513.
Lemma F_600e0 : fetch_word Asan.M.loaded_segments (0x600e0 : word) = Some W_600e0.
Proof. vm_refl. Qed.
Lemma D_600e0 : decode_any W_600e0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_600e4 : bv 32 := 0x00048593.
Lemma F_600e4 : fetch_word Asan.M.loaded_segments (0x600e4 : word) = Some W_600e4.
Proof. vm_refl. Qed.
Lemma D_600e4 : decode_any W_600e4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_600e8 : bv 32 := 0x07010113.
Lemma F_600e8 : fetch_word Asan.M.loaded_segments (0x600e8 : word) = Some W_600e8.
Proof. vm_refl. Qed.
Lemma D_600e8 : decode_any W_600e8 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_600ec : bv 32 := 0x7e813083.
Lemma F_600ec : fetch_word Asan.M.loaded_segments (0x600ec : word) = Some W_600ec.
Proof. vm_refl. Qed.
Lemma D_600ec : decode_any W_600ec = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_600f0 : bv 32 := 0x7e013403.
Lemma F_600f0 : fetch_word Asan.M.loaded_segments (0x600f0 : word) = Some W_600f0.
Proof. vm_refl. Qed.
Lemma D_600f0 : decode_any W_600f0 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_600f4 : bv 32 := 0x7d813483.
Lemma F_600f4 : fetch_word Asan.M.loaded_segments (0x600f4 : word) = Some W_600f4.
Proof. vm_refl. Qed.
Lemma D_600f4 : decode_any W_600f4 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_600f8 : bv 32 := 0x7d013903.
Lemma F_600f8 : fetch_word Asan.M.loaded_segments (0x600f8 : word) = Some W_600f8.
Proof. vm_refl. Qed.
Lemma D_600f8 : decode_any W_600f8 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_600fc : bv 32 := 0x7c813983.
Lemma F_600fc : fetch_word Asan.M.loaded_segments (0x600fc : word) = Some W_600fc.
Proof. vm_refl. Qed.
Lemma D_600fc : decode_any W_600fc = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_60100 : bv 32 := 0x7c013a03.
Lemma F_60100 : fetch_word Asan.M.loaded_segments (0x60100 : word) = Some W_60100.
Proof. vm_refl. Qed.
Lemma D_60100 : decode_any W_60100 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_60104 : bv 32 := 0x7b813a83.
Lemma F_60104 : fetch_word Asan.M.loaded_segments (0x60104 : word) = Some W_60104.
Proof. vm_refl. Qed.
Lemma D_60104 : decode_any W_60104 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_60108 : bv 32 := 0x7b013b03.
Lemma F_60108 : fetch_word Asan.M.loaded_segments (0x60108 : word) = Some W_60108.
Proof. vm_refl. Qed.
Lemma D_60108 : decode_any W_60108 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_6010c : bv 32 := 0x7f010113.
Lemma F_6010c : fetch_word Asan.M.loaded_segments (0x6010c : word) = Some W_6010c.
Proof. vm_refl. Qed.
Lemma D_6010c : decode_any W_6010c = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_60110 : bv 32 := 0x1240006f.
Lemma F_60110 : fetch_word Asan.M.loaded_segments (0x60110 : word) = Some W_60110.
Proof. vm_refl. Qed.
Lemma D_60110 : decode_any W_60110 = Some (Jal 0 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_60114 : bv 32 := 0x3c4000ef.
Lemma F_60114 : fetch_word Asan.M.loaded_segments (0x60114 : word) = Some W_60114.
Proof. vm_refl. Qed.
Lemma D_60114 : decode_any W_60114 = Some (Jal 1 964, 4%Z).
Proof. vm_refl. Qed.

Definition W_60118 : bv 32 := 0x00050613.
Lemma F_60118 : fetch_word Asan.M.loaded_segments (0x60118 : word) = Some W_60118.
Proof. vm_refl. Qed.
Lemma D_60118 : decode_any W_60118 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6011c : bv 32 := 0x034a1a13.
Lemma F_6011c : fetch_word Asan.M.loaded_segments (0x6011c : word) = Some W_6011c.
Proof. vm_refl. Qed.
Lemma D_6011c : decode_any W_6011c = Some (ShiftImm ALU_SLL 20 20 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_60120 : bv 32 := 0x034a5513.
Lemma F_60120 : fetch_word Asan.M.loaded_segments (0x60120 : word) = Some W_60120.
Proof. vm_refl. Qed.
Lemma D_60120 : decode_any W_60120 = Some (ShiftImm ALU_SRL 10 20 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_60124 : bv 32 := 0x00a60533.
Lemma F_60124 : fetch_word Asan.M.loaded_segments (0x60124 : word) = Some W_60124.
Proof. vm_refl. Qed.
Lemma D_60124 : decode_any W_60124 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_60128 : bv 32 := 0x00054503.
Lemma F_60128 : fetch_word Asan.M.loaded_segments (0x60128 : word) = Some W_60128.
Proof. vm_refl. Qed.
Lemma D_60128 : decode_any W_60128 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6012c : bv 32 := 0xfa051ae3.
Lemma F_6012c : fetch_word Asan.M.loaded_segments (0x6012c : word) = Some W_6012c.
Proof. vm_refl. Qed.
Lemma D_6012c : decode_any W_6012c = Some (Branch BC_NE 10 0 8116, 4%Z).
Proof. vm_refl. Qed.

Definition W_60130 : bv 32 := 0x80040a93.
Lemma F_60130 : fetch_word Asan.M.loaded_segments (0x60130 : word) = Some W_60130.
Proof. vm_refl. Qed.
Lemma D_60130 : decode_any W_60130 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_60134 : bv 32 := 0xfa8a8a93.
Lemma F_60134 : fetch_word Asan.M.loaded_segments (0x60134 : word) = Some W_60134.
Proof. vm_refl. Qed.
Lemma D_60134 : decode_any W_60134 = Some (OpImm ALU_ADD 21 21 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_60138 : bv 32 := 0x80040513.
Lemma F_60138 : fetch_word Asan.M.loaded_segments (0x60138 : word) = Some W_60138.
Proof. vm_refl. Qed.
Lemma D_60138 : decode_any W_60138 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6013c : bv 32 := 0xfb850513.
Lemma F_6013c : fetch_word Asan.M.loaded_segments (0x6013c : word) = Some W_6013c.
Proof. vm_refl. Qed.
Lemma D_6013c : decode_any W_6013c = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_60140 : bv 32 := 0x80040593.
Lemma F_60140 : fetch_word Asan.M.loaded_segments (0x60140 : word) = Some W_60140.
Proof. vm_refl. Qed.
Lemma D_60140 : decode_any W_60140 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_60144 : bv 32 := 0xfa858593.
Lemma F_60144 : fetch_word Asan.M.loaded_segments (0x60144 : word) = Some W_60144.
Proof. vm_refl. Qed.
Lemma D_60144 : decode_any W_60144 = Some (OpImm ALU_ADD 11 11 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_60148 : bv 32 := 0x7ff58b13.
Lemma F_60148 : fetch_word Asan.M.loaded_segments (0x60148 : word) = Some W_60148.
Proof. vm_refl. Qed.
Lemma D_60148 : decode_any W_60148 = Some (OpImm ALU_ADD 22 11 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_6014c : bv 32 := 0x000b34a3.
Lemma F_6014c : fetch_word Asan.M.loaded_segments (0x6014c : word) = Some W_6014c.
Proof. vm_refl. Qed.
Lemma D_6014c : decode_any W_6014c = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_60150 : bv 32 := 0x00aab023.
Lemma F_60150 : fetch_word Asan.M.loaded_segments (0x60150 : word) = Some W_60150.
Proof. vm_refl. Qed.
Lemma D_60150 : decode_any W_60150 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60154 : bv 32 := 0x000ab423.
Lemma F_60154 : fetch_word Asan.M.loaded_segments (0x60154 : word) = Some W_60154.
Proof. vm_refl. Qed.
Lemma D_60154 : decode_any W_60154 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_60158 : bv 32 := 0x415070ef.
Lemma F_60158 : fetch_word Asan.M.loaded_segments (0x60158 : word) = Some W_60158.
Proof. vm_refl. Qed.
Lemma D_60158 : decode_any W_60158 = Some (Jal 1 31764, 4%Z).
Proof. vm_refl. Qed.

Definition W_6015c : bv 32 := 0x00200593.
Lemma F_6015c : fetch_word Asan.M.loaded_segments (0x6015c : word) = Some W_6015c.
Proof. vm_refl. Qed.
Lemma D_6015c : decode_any W_6015c = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_60160 : bv 32 := 0x02a5ea63.
Lemma F_60160 : fetch_word Asan.M.loaded_segments (0x60160 : word) = Some W_60160.
Proof. vm_refl. Qed.
Lemma D_60160 : decode_any W_60160 = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_60164 : bv 32 := 0x409070ef.
Lemma F_60164 : fetch_word Asan.M.loaded_segments (0x60164 : word) = Some W_60164.
Proof. vm_refl. Qed.
Lemma D_60164 : decode_any W_60164 = Some (Jal 1 31752, 4%Z).
Proof. vm_refl. Qed.

Definition W_60168 : bv 32 := 0x00aaa423.
Lemma F_60168 : fetch_word Asan.M.loaded_segments (0x60168 : word) = Some W_60168.
Proof. vm_refl. Qed.
Lemma D_60168 : decode_any W_60168 = Some (Store SZ4 21 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6016c : bv 32 := 0x401070ef.
Lemma F_6016c : fetch_word Asan.M.loaded_segments (0x6016c : word) = Some W_6016c.
Proof. vm_refl. Qed.
Lemma D_6016c : decode_any W_6016c = Some (Jal 1 31744, 4%Z).
Proof. vm_refl. Qed.

Definition W_60170 : bv 32 := 0x08050263.
Lemma F_60170 : fetch_word Asan.M.loaded_segments (0x60170 : word) = Some W_60170.
Proof. vm_refl. Qed.
Lemma D_60170 : decode_any W_60170 = Some (Branch BC_EQ 10 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_60174 : bv 32 := 0x008b34a3.
Lemma F_60174 : fetch_word Asan.M.loaded_segments (0x60174 : word) = Some W_60174.
Proof. vm_refl. Qed.
Lemma D_60174 : decode_any W_60174 = Some (Store SZ8 22 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_60178 : bv 32 := 0x6b4200ef.
Lemma F_60178 : fetch_word Asan.M.loaded_segments (0x60178 : word) = Some W_60178.
Proof. vm_refl. Qed.
Lemma D_60178 : decode_any W_60178 = Some (Jal 1 132788, 4%Z).
Proof. vm_refl. Qed.

Definition W_6017c : bv 32 := 0x00aab823.
Lemma F_6017c : fetch_word Asan.M.loaded_segments (0x6017c : word) = Some W_6017c.
Proof. vm_refl. Qed.
Lemma D_6017c : decode_any W_6017c = Some (Store SZ8 21 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_60180 : bv 32 := 0x3ed070ef.
Lemma F_60180 : fetch_word Asan.M.loaded_segments (0x60180 : word) = Some W_60180.
Proof. vm_refl. Qed.
Lemma D_60180 : decode_any W_60180 = Some (Jal 1 31724, 4%Z).
Proof. vm_refl. Qed.

Definition W_60184 : bv 32 := 0x00200593.
Lemma F_60184 : fetch_word Asan.M.loaded_segments (0x60184 : word) = Some W_60184.
Proof. vm_refl. Qed.
Lemma D_60184 : decode_any W_60184 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_60188 : bv 32 := 0x06b56663.
Lemma F_60188 : fetch_word Asan.M.loaded_segments (0x60188 : word) = Some W_60188.
Proof. vm_refl. Qed.
Lemma D_60188 : decode_any W_60188 = Some (Branch BC_LTU 10 11 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_6018c : bv 32 := 0x013abc23.
Lemma F_6018c : fetch_word Asan.M.loaded_segments (0x6018c : word) = Some W_6018c.
Proof. vm_refl. Qed.
Lemma D_6018c : decode_any W_6018c = Some (Store SZ8 21 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_60190 : bv 32 := 0x0640006f.
Lemma F_60190 : fetch_word Asan.M.loaded_segments (0x60190 : word) = Some W_60190.
Proof. vm_refl. Qed.
Lemma D_60190 : decode_any W_60190 = Some (Jal 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_60194 : bv 32 := 0x698200ef.
Lemma F_60194 : fetch_word Asan.M.loaded_segments (0x60194 : word) = Some W_60194.
Proof. vm_refl. Qed.
Lemma D_60194 : decode_any W_60194 = Some (Jal 1 132760, 4%Z).
Proof. vm_refl. Qed.

Definition W_60198 : bv 32 := 0x00075597.
Lemma F_60198 : fetch_word Asan.M.loaded_segments (0x60198 : word) = Some W_60198.
Proof. vm_refl. Qed.
Lemma D_60198 : decode_any W_60198 = Some (Auipc 11 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_6019c : bv 32 := 0x7105b583.
Lemma F_6019c : fetch_word Asan.M.loaded_segments (0x6019c : word) = Some W_6019c.
Proof. vm_refl. Qed.
Lemma D_6019c : decode_any W_6019c = Some (Load SZ8 true 11 11 1808, 4%Z).
Proof. vm_refl. Qed.

Definition W_601a0 : bv 32 := 0x0225ca03.
Lemma F_601a0 : fetch_word Asan.M.loaded_segments (0x601a0 : word) = Some W_601a0.
Proof. vm_refl. Qed.
Lemma D_601a0 : decode_any W_601a0 = Some (Load SZ1 false 20 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_601a4 : bv 32 := 0x00050993.
Lemma F_601a4 : fetch_word Asan.M.loaded_segments (0x601a4 : word) = Some W_601a4.
Proof. vm_refl. Qed.
Lemma D_601a4 : decode_any W_601a4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_601a8 : bv 32 := 0x3c5070ef.
Lemma F_601a8 : fetch_word Asan.M.loaded_segments (0x601a8 : word) = Some W_601a8.
Proof. vm_refl. Qed.
Lemma D_601a8 : decode_any W_601a8 = Some (Jal 1 31684, 4%Z).
Proof. vm_refl. Qed.

Definition W_601ac : bv 32 := 0x00050793.
Lemma F_601ac : fetch_word Asan.M.loaded_segments (0x601ac : word) = Some W_601ac.
Proof. vm_refl. Qed.
Lemma D_601ac : decode_any W_601ac = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_601b0 : bv 32 := 0x00153513.
Lemma F_601b0 : fetch_word Asan.M.loaded_segments (0x601b0 : word) = Some W_601b0.
Proof. vm_refl. Qed.
Lemma D_601b0 : decode_any W_601b0 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_601b4 : bv 32 := 0xfff50513.
Lemma F_601b4 : fetch_word Asan.M.loaded_segments (0x601b4 : word) = Some W_601b4.
Proof. vm_refl. Qed.
Lemma D_601b4 : decode_any W_601b4 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_601b8 : bv 32 := 0x008575b3.
Lemma F_601b8 : fetch_word Asan.M.loaded_segments (0x601b8 : word) = Some W_601b8.
Proof. vm_refl. Qed.
Lemma D_601b8 : decode_any W_601b8 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_601bc : bv 32 := 0x00100513.
Lemma F_601bc : fetch_word Asan.M.loaded_segments (0x601bc : word) = Some W_601bc.
Proof. vm_refl. Qed.
Lemma D_601bc : decode_any W_601bc = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_601c0 : bv 32 := 0x00bb34a3.
Lemma F_601c0 : fetch_word Asan.M.loaded_segments (0x601c0 : word) = Some W_601c0.
Proof. vm_refl. Qed.
Lemma D_601c0 : decode_any W_601c0 = Some (Store SZ8 22 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_601c4 : bv 32 := 0x00f56a63.
Lemma F_601c4 : fetch_word Asan.M.loaded_segments (0x601c4 : word) = Some W_601c4.
Proof. vm_refl. Qed.
Lemma D_601c4 : decode_any W_601c4 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_601c8 : bv 32 := 0x00a79463.
Lemma F_601c8 : fetch_word Asan.M.loaded_segments (0x601c8 : word) = Some W_601c8.
Proof. vm_refl. Qed.
Lemma D_601c8 : decode_any W_601c8 = Some (Branch BC_NE 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_601cc : bv 32 := 0x013ab823.
Lemma F_601cc : fetch_word Asan.M.loaded_segments (0x601cc : word) = Some W_601cc.
Proof. vm_refl. Qed.
Lemma D_601cc : decode_any W_601cc = Some (Store SZ8 21 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_601d0 : bv 32 := 0x00faa423.
Lemma F_601d0 : fetch_word Asan.M.loaded_segments (0x601d0 : word) = Some W_601d0.
Proof. vm_refl. Qed.
Lemma D_601d0 : decode_any W_601d0 = Some (Store SZ4 21 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_601d4 : bv 32 := 0x0200006f.
Lemma F_601d4 : fetch_word Asan.M.loaded_segments (0x601d4 : word) = Some W_601d4.
Proof. vm_refl. Qed.
Lemma D_601d4 : decode_any W_601d4 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_601d8 : bv 32 := 0x80040513.
Lemma F_601d8 : fetch_word Asan.M.loaded_segments (0x601d8 : word) = Some W_601d8.
Proof. vm_refl. Qed.
Lemma D_601d8 : decode_any W_601d8 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_601dc : bv 32 := 0xfa850513.
Lemma F_601dc : fetch_word Asan.M.loaded_segments (0x601dc : word) = Some W_601dc.
Proof. vm_refl. Qed.
Lemma D_601dc : decode_any W_601dc = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_601e0 : bv 32 := 0x00098593.
Lemma F_601e0 : fetch_word Asan.M.loaded_segments (0x601e0 : word) = Some W_601e0.
Proof. vm_refl. Qed.
Lemma D_601e0 : decode_any W_601e0 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_601e4 : bv 32 := 0x00040613.
Lemma F_601e4 : fetch_word Asan.M.loaded_segments (0x601e4 : word) = Some W_601e4.
Proof. vm_refl. Qed.
Lemma D_601e4 : decode_any W_601e4 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_601e8 : bv 32 := 0x00000693.
Lemma F_601e8 : fetch_word Asan.M.loaded_segments (0x601e8 : word) = Some W_601e8.
Proof. vm_refl. Qed.
Lemma D_601e8 : decode_any W_601e8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_601ec : bv 32 := 0x000a0713.
Lemma F_601ec : fetch_word Asan.M.loaded_segments (0x601ec : word) = Some W_601ec.
Proof. vm_refl. Qed.
Lemma D_601ec : decode_any W_601ec = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_601f0 : bv 32 := 0x38d070ef.
Lemma F_601f0 : fetch_word Asan.M.loaded_segments (0x601f0 : word) = Some W_601f0.
Proof. vm_refl. Qed.
Lemma D_601f0 : decode_any W_601f0 = Some (Jal 1 31628, 4%Z).
Proof. vm_refl. Qed.

Definition W_601f4 : bv 32 := 0x80040613.
Lemma F_601f4 : fetch_word Asan.M.loaded_segments (0x601f4 : word) = Some W_601f4.
Proof. vm_refl. Qed.
Lemma D_601f4 : decode_any W_601f4 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_601f8 : bv 32 := 0xfa860613.
Lemma F_601f8 : fetch_word Asan.M.loaded_segments (0x601f8 : word) = Some W_601f8.
Proof. vm_refl. Qed.
Lemma D_601f8 : decode_any W_601f8 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_601fc : bv 32 := 0x00090513.
Lemma F_601fc : fetch_word Asan.M.loaded_segments (0x601fc : word) = Some W_601fc.
Proof. vm_refl. Qed.
Lemma D_601fc : decode_any W_601fc = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60200 : bv 32 := 0x00048593.
Lemma F_60200 : fetch_word Asan.M.loaded_segments (0x60200 : word) = Some W_60200.
Proof. vm_refl. Qed.
Lemma D_60200 : decode_any W_60200 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60204 : bv 32 := 0xaf5dd0ef.
Lemma F_60204 : fetch_word Asan.M.loaded_segments (0x60204 : word) = Some W_60204.
Proof. vm_refl. Qed.
Lemma D_60204 : decode_any W_60204 = Some (Jal 1 1956596, 4%Z).
Proof. vm_refl. Qed.

Definition W_60208 : bv 32 := 0x07010113.
Lemma F_60208 : fetch_word Asan.M.loaded_segments (0x60208 : word) = Some W_60208.
Proof. vm_refl. Qed.
Lemma D_60208 : decode_any W_60208 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_6020c : bv 32 := 0x7e813083.
Lemma F_6020c : fetch_word Asan.M.loaded_segments (0x6020c : word) = Some W_6020c.
Proof. vm_refl. Qed.
Lemma D_6020c : decode_any W_6020c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_60210 : bv 32 := 0x7e013403.
Lemma F_60210 : fetch_word Asan.M.loaded_segments (0x60210 : word) = Some W_60210.
Proof. vm_refl. Qed.
Lemma D_60210 : decode_any W_60210 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_60214 : bv 32 := 0x7d813483.
Lemma F_60214 : fetch_word Asan.M.loaded_segments (0x60214 : word) = Some W_60214.
Proof. vm_refl. Qed.
Lemma D_60214 : decode_any W_60214 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_60218 : bv 32 := 0x7d013903.
Lemma F_60218 : fetch_word Asan.M.loaded_segments (0x60218 : word) = Some W_60218.
Proof. vm_refl. Qed.
Lemma D_60218 : decode_any W_60218 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_6021c : bv 32 := 0x7c813983.
Lemma F_6021c : fetch_word Asan.M.loaded_segments (0x6021c : word) = Some W_6021c.
Proof. vm_refl. Qed.
Lemma D_6021c : decode_any W_6021c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_60220 : bv 32 := 0x7c013a03.
Lemma F_60220 : fetch_word Asan.M.loaded_segments (0x60220 : word) = Some W_60220.
Proof. vm_refl. Qed.
Lemma D_60220 : decode_any W_60220 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_60224 : bv 32 := 0x7b813a83.
Lemma F_60224 : fetch_word Asan.M.loaded_segments (0x60224 : word) = Some W_60224.
Proof. vm_refl. Qed.
Lemma D_60224 : decode_any W_60224 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_60228 : bv 32 := 0x7b013b03.
Lemma F_60228 : fetch_word Asan.M.loaded_segments (0x60228 : word) = Some W_60228.
Proof. vm_refl. Qed.
Lemma D_60228 : decode_any W_60228 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_6022c : bv 32 := 0x7f010113.
Lemma F_6022c : fetch_word Asan.M.loaded_segments (0x6022c : word) = Some W_6022c.
Proof. vm_refl. Qed.
Lemma D_6022c : decode_any W_6022c = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_60230 : bv 32 := 0x00008067.
Lemma F_60230 : fetch_word Asan.M.loaded_segments (0x60230 : word) = Some W_60230.
Proof. vm_refl. Qed.
Lemma D_60230 : decode_any W_60230 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60234 : bv 32 := 0xfd010113.
Lemma F_60234 : fetch_word Asan.M.loaded_segments (0x60234 : word) = Some W_60234.
Proof. vm_refl. Qed.
Lemma D_60234 : decode_any W_60234 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_60238 : bv 32 := 0x02113423.
Lemma F_60238 : fetch_word Asan.M.loaded_segments (0x60238 : word) = Some W_60238.
Proof. vm_refl. Qed.
Lemma D_60238 : decode_any W_60238 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6023c : bv 32 := 0x02813023.
Lemma F_6023c : fetch_word Asan.M.loaded_segments (0x6023c : word) = Some W_6023c.
Proof. vm_refl. Qed.
Lemma D_6023c : decode_any W_6023c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_60240 : bv 32 := 0x00913c23.
Lemma F_60240 : fetch_word Asan.M.loaded_segments (0x60240 : word) = Some W_60240.
Proof. vm_refl. Qed.
Lemma D_60240 : decode_any W_60240 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_60244 : bv 32 := 0x01213823.
Lemma F_60244 : fetch_word Asan.M.loaded_segments (0x60244 : word) = Some W_60244.
Proof. vm_refl. Qed.
Lemma D_60244 : decode_any W_60244 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_60248 : bv 32 := 0x01313423.
Lemma F_60248 : fetch_word Asan.M.loaded_segments (0x60248 : word) = Some W_60248.
Proof. vm_refl. Qed.
Lemma D_60248 : decode_any W_60248 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6024c : bv 32 := 0x00058493.
Lemma F_6024c : fetch_word Asan.M.loaded_segments (0x6024c : word) = Some W_6024c.
Proof. vm_refl. Qed.
Lemma D_6024c : decode_any W_6024c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60250 : bv 32 := 0x0a050a63.
Lemma F_60250 : fetch_word Asan.M.loaded_segments (0x60250 : word) = Some W_60250.
Proof. vm_refl. Qed.
Lemma D_60250 : decode_any W_60250 = Some (Branch BC_EQ 10 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_60254 : bv 32 := 0x00050413.
Lemma F_60254 : fetch_word Asan.M.loaded_segments (0x60254 : word) = Some W_60254.
Proof. vm_refl. Qed.
Lemma D_60254 : decode_any W_60254 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60258 : bv 32 := 0x6080b0ef.
Lemma F_60258 : fetch_word Asan.M.loaded_segments (0x60258 : word) = Some W_60258.
Proof. vm_refl. Qed.
Lemma D_60258 : decode_any W_60258 = Some (Jal 1 46600, 4%Z).
Proof. vm_refl. Qed.

Definition W_6025c : bv 32 := 0x02f45593.
Lemma F_6025c : fetch_word Asan.M.loaded_segments (0x6025c : word) = Some W_6025c.
Proof. vm_refl. Qed.
Lemma D_6025c : decode_any W_6025c = Some (ShiftImm ALU_SRL 11 8 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_60260 : bv 32 := 0x12059063.
Lemma F_60260 : fetch_word Asan.M.loaded_segments (0x60260 : word) = Some W_60260.
Proof. vm_refl. Qed.
Lemma D_60260 : decode_any W_60260 = Some (Branch BC_NE 11 0 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_60264 : bv 32 := 0x02045593.
Lemma F_60264 : fetch_word Asan.M.loaded_segments (0x60264 : word) = Some W_60264.
Proof. vm_refl. Qed.
Lemma D_60264 : decode_any W_60264 = Some (ShiftImm ALU_SRL 11 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_60268 : bv 32 := 0x00359613.
Lemma F_60268 : fetch_word Asan.M.loaded_segments (0x60268 : word) = Some W_60268.
Proof. vm_refl. Qed.
Lemma D_60268 : decode_any W_60268 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6026c : bv 32 := 0x00c50633.
Lemma F_6026c : fetch_word Asan.M.loaded_segments (0x6026c : word) = Some W_6026c.
Proof. vm_refl. Qed.
Lemma D_6026c : decode_any W_6026c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_60270 : bv 32 := 0x00863683.
Lemma F_60270 : fetch_word Asan.M.loaded_segments (0x60270 : word) = Some W_60270.
Proof. vm_refl. Qed.
Lemma D_60270 : decode_any W_60270 = Some (Load SZ8 true 13 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_60274 : bv 32 := 0x0230000f.
Lemma F_60274 : fetch_word Asan.M.loaded_segments (0x60274 : word) = Some W_60274.
Proof. vm_refl. Qed.
Lemma D_60274 : decode_any W_60274 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60278 : bv 32 := 0x10068463.
Lemma F_60278 : fetch_word Asan.M.loaded_segments (0x60278 : word) = Some W_60278.
Proof. vm_refl. Qed.
Lemma D_60278 : decode_any W_60278 = Some (Branch BC_EQ 13 0 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_6027c : bv 32 := 0x00863603.
Lemma F_6027c : fetch_word Asan.M.loaded_segments (0x6027c : word) = Some W_6027c.
Proof. vm_refl. Qed.
Lemma D_6027c : decode_any W_6027c = Some (Load SZ8 true 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_60280 : bv 32 := 0x01445913.
Lemma F_60280 : fetch_word Asan.M.loaded_segments (0x60280 : word) = Some W_60280.
Proof. vm_refl. Qed.
Lemma D_60280 : decode_any W_60280 = Some (ShiftImm ALU_SRL 18 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_60284 : bv 32 := 0x0e060063.
Lemma F_60284 : fetch_word Asan.M.loaded_segments (0x60284 : word) = Some W_60284.
Proof. vm_refl. Qed.
Lemma D_60284 : decode_any W_60284 = Some (Branch BC_EQ 12 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_60288 : bv 32 := 0x03491913.
Lemma F_60288 : fetch_word Asan.M.loaded_segments (0x60288 : word) = Some W_60288.
Proof. vm_refl. Qed.
Lemma D_60288 : decode_any W_60288 = Some (ShiftImm ALU_SLL 18 18 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_6028c : bv 32 := 0x03495513.
Lemma F_6028c : fetch_word Asan.M.loaded_segments (0x6028c : word) = Some W_6028c.
Proof. vm_refl. Qed.
Lemma D_6028c : decode_any W_6028c = Some (ShiftImm ALU_SRL 10 18 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_60290 : bv 32 := 0x00a60533.
Lemma F_60290 : fetch_word Asan.M.loaded_segments (0x60290 : word) = Some W_60290.
Proof. vm_refl. Qed.
Lemma D_60290 : decode_any W_60290 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_60294 : bv 32 := 0x00054503.
Lemma F_60294 : fetch_word Asan.M.loaded_segments (0x60294 : word) = Some W_60294.
Proof. vm_refl. Qed.
Lemma D_60294 : decode_any W_60294 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60298 : bv 32 := 0x0e050463.
Lemma F_60298 : fetch_word Asan.M.loaded_segments (0x60298 : word) = Some W_60298.
Proof. vm_refl. Qed.
Lemma D_60298 : decode_any W_60298 = Some (Branch BC_EQ 10 0 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_6029c : bv 32 := 0x5c40b0ef.
Lemma F_6029c : fetch_word Asan.M.loaded_segments (0x6029c : word) = Some W_6029c.
Proof. vm_refl. Qed.
Lemma D_6029c : decode_any W_6029c = Some (Jal 1 46532, 4%Z).
Proof. vm_refl. Qed.

Definition W_602a0 : bv 32 := 0x00040593.
Lemma F_602a0 : fetch_word Asan.M.loaded_segments (0x602a0 : word) = Some W_602a0.
Proof. vm_refl. Qed.
Lemma D_602a0 : decode_any W_602a0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_602a4 : bv 32 := 0x334000ef.
Lemma F_602a4 : fetch_word Asan.M.loaded_segments (0x602a4 : word) = Some W_602a4.
Proof. vm_refl. Qed.
Lemma D_602a4 : decode_any W_602a4 = Some (Jal 1 820, 4%Z).
Proof. vm_refl. Qed.

Definition W_602a8 : bv 32 := 0x00050993.
Lemma F_602a8 : fetch_word Asan.M.loaded_segments (0x602a8 : word) = Some W_602a8.
Proof. vm_refl. Qed.
Lemma D_602a8 : decode_any W_602a8 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_602ac : bv 32 := 0x06048e63.
Lemma F_602ac : fetch_word Asan.M.loaded_segments (0x602ac : word) = Some W_602ac.
Proof. vm_refl. Qed.
Lemma D_602ac : decode_any W_602ac = Some (Branch BC_EQ 9 0 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_602b0 : bv 32 := 0x00800593.
Lemma F_602b0 : fetch_word Asan.M.loaded_segments (0x602b0 : word) = Some W_602b0.
Proof. vm_refl. Qed.
Lemma D_602b0 : decode_any W_602b0 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_602b4 : bv 32 := 0x00048513.
Lemma F_602b4 : fetch_word Asan.M.loaded_segments (0x602b4 : word) = Some W_602b4.
Proof. vm_refl. Qed.
Lemma D_602b4 : decode_any W_602b4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_602b8 : bv 32 := 0xcd9ff0ef.
Lemma F_602b8 : fetch_word Asan.M.loaded_segments (0x602b8 : word) = Some W_602b8.
Proof. vm_refl. Qed.
Lemma D_602b8 : decode_any W_602b8 = Some (Jal 1 2096344, 4%Z).
Proof. vm_refl. Qed.

Definition W_602bc : bv 32 := 0x00050913.
Lemma F_602bc : fetch_word Asan.M.loaded_segments (0x602bc : word) = Some W_602bc.
Proof. vm_refl. Qed.
Lemma D_602bc : decode_any W_602bc = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_602c0 : bv 32 := 0x00050e63.
Lemma F_602c0 : fetch_word Asan.M.loaded_segments (0x602c0 : word) = Some W_602c0.
Proof. vm_refl. Qed.
Lemma D_602c0 : decode_any W_602c0 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_602c4 : bv 32 := 0x0134e463.
Lemma F_602c4 : fetch_word Asan.M.loaded_segments (0x602c4 : word) = Some W_602c4.
Proof. vm_refl. Qed.
Lemma D_602c4 : decode_any W_602c4 = Some (Branch BC_LTU 9 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_602c8 : bv 32 := 0x00098493.
Lemma F_602c8 : fetch_word Asan.M.loaded_segments (0x602c8 : word) = Some W_602c8.
Proof. vm_refl. Qed.
Lemma D_602c8 : decode_any W_602c8 = Some (OpImm ALU_ADD 9 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_602cc : bv 32 := 0x00090513.
Lemma F_602cc : fetch_word Asan.M.loaded_segments (0x602cc : word) = Some W_602cc.
Proof. vm_refl. Qed.
Lemma D_602cc : decode_any W_602cc = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_602d0 : bv 32 := 0x00040593.
Lemma F_602d0 : fetch_word Asan.M.loaded_segments (0x602d0 : word) = Some W_602d0.
Proof. vm_refl. Qed.
Lemma D_602d0 : decode_any W_602d0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_602d4 : bv 32 := 0x00048613.
Lemma F_602d4 : fetch_word Asan.M.loaded_segments (0x602d4 : word) = Some W_602d4.
Proof. vm_refl. Qed.
Lemma D_602d4 : decode_any W_602d4 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_602d8 : bv 32 := 0x00c110ef.
Lemma F_602d8 : fetch_word Asan.M.loaded_segments (0x602d8 : word) = Some W_602d8.
Proof. vm_refl. Qed.
Lemma D_602d8 : decode_any W_602d8 = Some (Jal 1 69644, 4%Z).
Proof. vm_refl. Qed.

Definition W_602dc : bv 32 := 0x5840b0ef.
Lemma F_602dc : fetch_word Asan.M.loaded_segments (0x602dc : word) = Some W_602dc.
Proof. vm_refl. Qed.
Lemma D_602dc : decode_any W_602dc = Some (Jal 1 46468, 4%Z).
Proof. vm_refl. Qed.

Definition W_602e0 : bv 32 := 0x00040593.
Lemma F_602e0 : fetch_word Asan.M.loaded_segments (0x602e0 : word) = Some W_602e0.
Proof. vm_refl. Qed.
Lemma D_602e0 : decode_any W_602e0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_602e4 : bv 32 := 0x2f4000ef.
Lemma F_602e4 : fetch_word Asan.M.loaded_segments (0x602e4 : word) = Some W_602e4.
Proof. vm_refl. Qed.
Lemma D_602e4 : decode_any W_602e4 = Some (Jal 1 756, 4%Z).
Proof. vm_refl. Qed.

Definition W_602e8 : bv 32 := 0x00050593.
Lemma F_602e8 : fetch_word Asan.M.loaded_segments (0x602e8 : word) = Some W_602e8.
Proof. vm_refl. Qed.
Lemma D_602e8 : decode_any W_602e8 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_602ec : bv 32 := 0x00040513.
Lemma F_602ec : fetch_word Asan.M.loaded_segments (0x602ec : word) = Some W_602ec.
Proof. vm_refl. Qed.
Lemma D_602ec : decode_any W_602ec = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_602f0 : bv 32 := 0x06c2a0ef.
Lemma F_602f0 : fetch_word Asan.M.loaded_segments (0x602f0 : word) = Some W_602f0.
Proof. vm_refl. Qed.
Lemma D_602f0 : decode_any W_602f0 = Some (Jal 1 172140, 4%Z).
Proof. vm_refl. Qed.

Definition W_602f4 : bv 32 := 0x00040513.
Lemma F_602f4 : fetch_word Asan.M.loaded_segments (0x602f4 : word) = Some W_602f4.
Proof. vm_refl. Qed.
Lemma D_602f4 : decode_any W_602f4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_602f8 : bv 32 := 0x00000593.
Lemma F_602f8 : fetch_word Asan.M.loaded_segments (0x602f8 : word) = Some W_602f8.
Proof. vm_refl. Qed.
Lemma D_602f8 : decode_any W_602f8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_602fc : bv 32 := 0x7e00b0ef.
Lemma F_602fc : fetch_word Asan.M.loaded_segments (0x602fc : word) = Some W_602fc.
Proof. vm_refl. Qed.
Lemma D_602fc : decode_any W_602fc = Some (Jal 1 47072, 4%Z).
Proof. vm_refl. Qed.

Definition W_60300 : bv 32 := 0x0440006f.
Lemma F_60300 : fetch_word Asan.M.loaded_segments (0x60300 : word) = Some W_60300.
Proof. vm_refl. Qed.
Lemma D_60300 : decode_any W_60300 = Some (Jal 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_60304 : bv 32 := 0x00800593.
Lemma F_60304 : fetch_word Asan.M.loaded_segments (0x60304 : word) = Some W_60304.
Proof. vm_refl. Qed.
Lemma D_60304 : decode_any W_60304 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_60308 : bv 32 := 0x00048513.
Lemma F_60308 : fetch_word Asan.M.loaded_segments (0x60308 : word) = Some W_60308.
Proof. vm_refl. Qed.
Lemma D_60308 : decode_any W_60308 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6030c : bv 32 := 0x02813083.
Lemma F_6030c : fetch_word Asan.M.loaded_segments (0x6030c : word) = Some W_6030c.
Proof. vm_refl. Qed.
Lemma D_6030c : decode_any W_6030c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_60310 : bv 32 := 0x02013403.
Lemma F_60310 : fetch_word Asan.M.loaded_segments (0x60310 : word) = Some W_60310.
Proof. vm_refl. Qed.
Lemma D_60310 : decode_any W_60310 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_60314 : bv 32 := 0x01813483.
Lemma F_60314 : fetch_word Asan.M.loaded_segments (0x60314 : word) = Some W_60314.
Proof. vm_refl. Qed.
Lemma D_60314 : decode_any W_60314 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_60318 : bv 32 := 0x01013903.
Lemma F_60318 : fetch_word Asan.M.loaded_segments (0x60318 : word) = Some W_60318.
Proof. vm_refl. Qed.
Lemma D_60318 : decode_any W_60318 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6031c : bv 32 := 0x00813983.
Lemma F_6031c : fetch_word Asan.M.loaded_segments (0x6031c : word) = Some W_6031c.
Proof. vm_refl. Qed.
Lemma D_6031c : decode_any W_6031c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_60320 : bv 32 := 0x03010113.
Lemma F_60320 : fetch_word Asan.M.loaded_segments (0x60320 : word) = Some W_60320.
Proof. vm_refl. Qed.
Lemma D_60320 : decode_any W_60320 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_60324 : bv 32 := 0xc6dff06f.
Lemma F_60324 : fetch_word Asan.M.loaded_segments (0x60324 : word) = Some W_60324.
Proof. vm_refl. Qed.
Lemma D_60324 : decode_any W_60324 = Some (Jal 0 2096236, 4%Z).
Proof. vm_refl. Qed.

Definition W_60328 : bv 32 := 0x00040513.
Lemma F_60328 : fetch_word Asan.M.loaded_segments (0x60328 : word) = Some W_60328.
Proof. vm_refl. Qed.
Lemma D_60328 : decode_any W_60328 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6032c : bv 32 := 0x00098593.
Lemma F_6032c : fetch_word Asan.M.loaded_segments (0x6032c : word) = Some W_6032c.
Proof. vm_refl. Qed.
Lemma D_6032c : decode_any W_6032c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60330 : bv 32 := 0x02c2a0ef.
Lemma F_60330 : fetch_word Asan.M.loaded_segments (0x60330 : word) = Some W_60330.
Proof. vm_refl. Qed.
Lemma D_60330 : decode_any W_60330 = Some (Jal 1 172076, 4%Z).
Proof. vm_refl. Qed.

Definition W_60334 : bv 32 := 0x00040513.
Lemma F_60334 : fetch_word Asan.M.loaded_segments (0x60334 : word) = Some W_60334.
Proof. vm_refl. Qed.
Lemma D_60334 : decode_any W_60334 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60338 : bv 32 := 0x00000593.
Lemma F_60338 : fetch_word Asan.M.loaded_segments (0x60338 : word) = Some W_60338.
Proof. vm_refl. Qed.
Lemma D_60338 : decode_any W_60338 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6033c : bv 32 := 0x7a00b0ef.
Lemma F_6033c : fetch_word Asan.M.loaded_segments (0x6033c : word) = Some W_6033c.
Proof. vm_refl. Qed.
Lemma D_6033c : decode_any W_6033c = Some (Jal 1 47008, 4%Z).
Proof. vm_refl. Qed.

Definition W_60340 : bv 32 := 0x00000913.
Lemma F_60340 : fetch_word Asan.M.loaded_segments (0x60340 : word) = Some W_60340.
Proof. vm_refl. Qed.
Lemma D_60340 : decode_any W_60340 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60344 : bv 32 := 0x00090513.
Lemma F_60344 : fetch_word Asan.M.loaded_segments (0x60344 : word) = Some W_60344.
Proof. vm_refl. Qed.
Lemma D_60344 : decode_any W_60344 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60348 : bv 32 := 0x02813083.
Lemma F_60348 : fetch_word Asan.M.loaded_segments (0x60348 : word) = Some W_60348.
Proof. vm_refl. Qed.
Lemma D_60348 : decode_any W_60348 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_6034c : bv 32 := 0x02013403.
Lemma F_6034c : fetch_word Asan.M.loaded_segments (0x6034c : word) = Some W_6034c.
Proof. vm_refl. Qed.
Lemma D_6034c : decode_any W_6034c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_60350 : bv 32 := 0x01813483.
Lemma F_60350 : fetch_word Asan.M.loaded_segments (0x60350 : word) = Some W_60350.
Proof. vm_refl. Qed.
Lemma D_60350 : decode_any W_60350 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_60354 : bv 32 := 0x01013903.
Lemma F_60354 : fetch_word Asan.M.loaded_segments (0x60354 : word) = Some W_60354.
Proof. vm_refl. Qed.
Lemma D_60354 : decode_any W_60354 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_60358 : bv 32 := 0x00813983.
Lemma F_60358 : fetch_word Asan.M.loaded_segments (0x60358 : word) = Some W_60358.
Proof. vm_refl. Qed.
Lemma D_60358 : decode_any W_60358 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6035c : bv 32 := 0x03010113.
Lemma F_6035c : fetch_word Asan.M.loaded_segments (0x6035c : word) = Some W_6035c.
Proof. vm_refl. Qed.
Lemma D_6035c : decode_any W_6035c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_60360 : bv 32 := 0x00008067.
Lemma F_60360 : fetch_word Asan.M.loaded_segments (0x60360 : word) = Some W_60360.
Proof. vm_refl. Qed.
Lemma D_60360 : decode_any W_60360 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60364 : bv 32 := 0x174000ef.
Lemma F_60364 : fetch_word Asan.M.loaded_segments (0x60364 : word) = Some W_60364.
Proof. vm_refl. Qed.
Lemma D_60364 : decode_any W_60364 = Some (Jal 1 372, 4%Z).
Proof. vm_refl. Qed.

Definition W_60368 : bv 32 := 0x00050613.
Lemma F_60368 : fetch_word Asan.M.loaded_segments (0x60368 : word) = Some W_60368.
Proof. vm_refl. Qed.
Lemma D_60368 : decode_any W_60368 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6036c : bv 32 := 0x03491913.
Lemma F_6036c : fetch_word Asan.M.loaded_segments (0x6036c : word) = Some W_6036c.
Proof. vm_refl. Qed.
Lemma D_6036c : decode_any W_6036c = Some (ShiftImm ALU_SLL 18 18 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_60370 : bv 32 := 0x03495513.
Lemma F_60370 : fetch_word Asan.M.loaded_segments (0x60370 : word) = Some W_60370.
Proof. vm_refl. Qed.
Lemma D_60370 : decode_any W_60370 = Some (ShiftImm ALU_SRL 10 18 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_60374 : bv 32 := 0x00a60533.
Lemma F_60374 : fetch_word Asan.M.loaded_segments (0x60374 : word) = Some W_60374.
Proof. vm_refl. Qed.
Lemma D_60374 : decode_any W_60374 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_60378 : bv 32 := 0x00054503.
Lemma F_60378 : fetch_word Asan.M.loaded_segments (0x60378 : word) = Some W_60378.
Proof. vm_refl. Qed.
Lemma D_60378 : decode_any W_60378 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6037c : bv 32 := 0xf20510e3.
Lemma F_6037c : fetch_word Asan.M.loaded_segments (0x6037c : word) = Some W_6037c.
Proof. vm_refl. Qed.
Lemma D_6037c : decode_any W_6037c = Some (Branch BC_NE 10 0 7968, 4%Z).
Proof. vm_refl. Qed.

Definition W_60380 : bv 32 := 0xfffbc517.
Lemma F_60380 : fetch_word Asan.M.loaded_segments (0x60380 : word) = Some W_60380.
Proof. vm_refl. Qed.
Lemma D_60380 : decode_any W_60380 = Some (Auipc 10 1048508, 4%Z).
Proof. vm_refl. Qed.

Definition W_60384 : bv 32 := 0xfffb2597.
Lemma F_60384 : fetch_word Asan.M.loaded_segments (0x60384 : word) = Some W_60384.
Proof. vm_refl. Qed.
Lemma D_60384 : decode_any W_60384 = Some (Auipc 11 1048498, 4%Z).
Proof. vm_refl. Qed.

Definition W_60388 : bv 32 := 0x11350513.
Lemma F_60388 : fetch_word Asan.M.loaded_segments (0x60388 : word) = Some W_60388.
Proof. vm_refl. Qed.
Lemma D_60388 : decode_any W_60388 = Some (OpImm ALU_ADD 10 10 275, 4%Z).
Proof. vm_refl. Qed.

Definition W_6038c : bv 32 := 0x76658613.
Lemma F_6038c : fetch_word Asan.M.loaded_segments (0x6038c : word) = Some W_6038c.
Proof. vm_refl. Qed.
Lemma D_6038c : decode_any W_6038c = Some (OpImm ALU_ADD 12 11 1894, 4%Z).
Proof. vm_refl. Qed.

Definition W_60390 : bv 32 := 0x03b00593.
Lemma F_60390 : fetch_word Asan.M.loaded_segments (0x60390 : word) = Some W_60390.
Proof. vm_refl. Qed.
Lemma D_60390 : decode_any W_60390 = Some (OpImm ALU_ADD 11 0 59, 4%Z).
Proof. vm_refl. Qed.

Definition W_60394 : bv 32 := 0x00000693.
Lemma F_60394 : fetch_word Asan.M.loaded_segments (0x60394 : word) = Some W_60394.
Proof. vm_refl. Qed.
Lemma D_60394 : decode_any W_60394 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60398 : bv 32 := 0x00000713.
Lemma F_60398 : fetch_word Asan.M.loaded_segments (0x60398 : word) = Some W_60398.
Proof. vm_refl. Qed.
Lemma D_60398 : decode_any W_60398 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6039c : bv 32 := 0x4cd180ef.
Lemma F_6039c : fetch_word Asan.M.loaded_segments (0x6039c : word) = Some W_6039c.
Proof. vm_refl. Qed.
Lemma D_6039c : decode_any W_6039c = Some (Jal 1 101580, 4%Z).
Proof. vm_refl. Qed.

Definition W_603a0 : bv 32 := 0x81010113.
Lemma F_603a0 : fetch_word Asan.M.loaded_segments (0x603a0 : word) = Some W_603a0.
Proof. vm_refl. Qed.
Lemma D_603a0 : decode_any W_603a0 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_603a4 : bv 32 := 0x7e113423.
Lemma F_603a4 : fetch_word Asan.M.loaded_segments (0x603a4 : word) = Some W_603a4.
Proof. vm_refl. Qed.
Lemma D_603a4 : decode_any W_603a4 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_603a8 : bv 32 := 0x7e813023.
Lemma F_603a8 : fetch_word Asan.M.loaded_segments (0x603a8 : word) = Some W_603a8.
Proof. vm_refl. Qed.
Lemma D_603a8 : decode_any W_603a8 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_603ac : bv 32 := 0x7c913c23.
Lemma F_603ac : fetch_word Asan.M.loaded_segments (0x603ac : word) = Some W_603ac.
Proof. vm_refl. Qed.
Lemma D_603ac : decode_any W_603ac = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_603b0 : bv 32 := 0x7d213823.
Lemma F_603b0 : fetch_word Asan.M.loaded_segments (0x603b0 : word) = Some W_603b0.
Proof. vm_refl. Qed.
Lemma D_603b0 : decode_any W_603b0 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_603b4 : bv 32 := 0x7d313423.
Lemma F_603b4 : fetch_word Asan.M.loaded_segments (0x603b4 : word) = Some W_603b4.
Proof. vm_refl. Qed.
Lemma D_603b4 : decode_any W_603b4 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_603b8 : bv 32 := 0x7d413023.
Lemma F_603b8 : fetch_word Asan.M.loaded_segments (0x603b8 : word) = Some W_603b8.
Proof. vm_refl. Qed.
Lemma D_603b8 : decode_any W_603b8 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_603bc : bv 32 := 0x7b513c23.
Lemma F_603bc : fetch_word Asan.M.loaded_segments (0x603bc : word) = Some W_603bc.
Proof. vm_refl. Qed.
Lemma D_603bc : decode_any W_603bc = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_603c0 : bv 32 := 0x7b613823.
Lemma F_603c0 : fetch_word Asan.M.loaded_segments (0x603c0 : word) = Some W_603c0.
Proof. vm_refl. Qed.
Lemma D_603c0 : decode_any W_603c0 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_603c4 : bv 32 := 0x7f010413.
Lemma F_603c4 : fetch_word Asan.M.loaded_segments (0x603c4 : word) = Some W_603c4.
Proof. vm_refl. Qed.
Lemma D_603c4 : decode_any W_603c4 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_603c8 : bv 32 := 0xf9010113.
Lemma F_603c8 : fetch_word Asan.M.loaded_segments (0x603c8 : word) = Some W_603c8.
Proof. vm_refl. Qed.
Lemma D_603c8 : decode_any W_603c8 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_603cc : bv 32 := 0x00008993.
Lemma F_603cc : fetch_word Asan.M.loaded_segments (0x603cc : word) = Some W_603cc.
Proof. vm_refl. Qed.
Lemma D_603cc : decode_any W_603cc = Some (OpImm ALU_ADD 19 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_603d0 : bv 32 := 0x00058493.
Lemma F_603d0 : fetch_word Asan.M.loaded_segments (0x603d0 : word) = Some W_603d0.
Proof. vm_refl. Qed.
Lemma D_603d0 : decode_any W_603d0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_603d4 : bv 32 := 0x00050913.
Lemma F_603d4 : fetch_word Asan.M.loaded_segments (0x603d4 : word) = Some W_603d4.
Proof. vm_refl. Qed.
Lemma D_603d4 : decode_any W_603d4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_603d8 : bv 32 := 0x80040a93.
Lemma F_603d8 : fetch_word Asan.M.loaded_segments (0x603d8 : word) = Some W_603d8.
Proof. vm_refl. Qed.
Lemma D_603d8 : decode_any W_603d8 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_603dc : bv 32 := 0xfa8a8a93.
Lemma F_603dc : fetch_word Asan.M.loaded_segments (0x603dc : word) = Some W_603dc.
Proof. vm_refl. Qed.
Lemma D_603dc : decode_any W_603dc = Some (OpImm ALU_ADD 21 21 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_603e0 : bv 32 := 0x80040513.
Lemma F_603e0 : fetch_word Asan.M.loaded_segments (0x603e0 : word) = Some W_603e0.
Proof. vm_refl. Qed.
Lemma D_603e0 : decode_any W_603e0 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_603e4 : bv 32 := 0xfb850513.
Lemma F_603e4 : fetch_word Asan.M.loaded_segments (0x603e4 : word) = Some W_603e4.
Proof. vm_refl. Qed.
Lemma D_603e4 : decode_any W_603e4 = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_603e8 : bv 32 := 0x7ffa8b13.
Lemma F_603e8 : fetch_word Asan.M.loaded_segments (0x603e8 : word) = Some W_603e8.
Proof. vm_refl. Qed.
Lemma D_603e8 : decode_any W_603e8 = Some (OpImm ALU_ADD 22 21 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_603ec : bv 32 := 0x000b34a3.
Lemma F_603ec : fetch_word Asan.M.loaded_segments (0x603ec : word) = Some W_603ec.
Proof. vm_refl. Qed.
Lemma D_603ec : decode_any W_603ec = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_603f0 : bv 32 := 0x00aab023.
Lemma F_603f0 : fetch_word Asan.M.loaded_segments (0x603f0 : word) = Some W_603f0.
Proof. vm_refl. Qed.
Lemma D_603f0 : decode_any W_603f0 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_603f4 : bv 32 := 0x000ab423.
Lemma F_603f4 : fetch_word Asan.M.loaded_segments (0x603f4 : word) = Some W_603f4.
Proof. vm_refl. Qed.
Lemma D_603f4 : decode_any W_603f4 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_603f8 : bv 32 := 0x175070ef.
Lemma F_603f8 : fetch_word Asan.M.loaded_segments (0x603f8 : word) = Some W_603f8.
Proof. vm_refl. Qed.
Lemma D_603f8 : decode_any W_603f8 = Some (Jal 1 31092, 4%Z).
Proof. vm_refl. Qed.

Definition W_603fc : bv 32 := 0x00200593.
Lemma F_603fc : fetch_word Asan.M.loaded_segments (0x603fc : word) = Some W_603fc.
Proof. vm_refl. Qed.
Lemma D_603fc : decode_any W_603fc = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_60400 : bv 32 := 0x02a5ea63.
Lemma F_60400 : fetch_word Asan.M.loaded_segments (0x60400 : word) = Some W_60400.
Proof. vm_refl. Qed.
Lemma D_60400 : decode_any W_60400 = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_60404 : bv 32 := 0x169070ef.
Lemma F_60404 : fetch_word Asan.M.loaded_segments (0x60404 : word) = Some W_60404.
Proof. vm_refl. Qed.
Lemma D_60404 : decode_any W_60404 = Some (Jal 1 31080, 4%Z).
Proof. vm_refl. Qed.

Definition W_60408 : bv 32 := 0x00aaa423.
Lemma F_60408 : fetch_word Asan.M.loaded_segments (0x60408 : word) = Some W_60408.
Proof. vm_refl. Qed.
Lemma D_60408 : decode_any W_60408 = Some (Store SZ4 21 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6040c : bv 32 := 0x161070ef.
Lemma F_6040c : fetch_word Asan.M.loaded_segments (0x6040c : word) = Some W_6040c.
Proof. vm_refl. Qed.
Lemma D_6040c : decode_any W_6040c = Some (Jal 1 31072, 4%Z).
Proof. vm_refl. Qed.

Definition W_60410 : bv 32 := 0x08050263.
Lemma F_60410 : fetch_word Asan.M.loaded_segments (0x60410 : word) = Some W_60410.
Proof. vm_refl. Qed.
Lemma D_60410 : decode_any W_60410 = Some (Branch BC_EQ 10 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_60414 : bv 32 := 0x008b34a3.
Lemma F_60414 : fetch_word Asan.M.loaded_segments (0x60414 : word) = Some W_60414.
Proof. vm_refl. Qed.
Lemma D_60414 : decode_any W_60414 = Some (Store SZ8 22 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_60418 : bv 32 := 0x414200ef.
Lemma F_60418 : fetch_word Asan.M.loaded_segments (0x60418 : word) = Some W_60418.
Proof. vm_refl. Qed.
Lemma D_60418 : decode_any W_60418 = Some (Jal 1 132116, 4%Z).
Proof. vm_refl. Qed.

Definition W_6041c : bv 32 := 0x00aab823.
Lemma F_6041c : fetch_word Asan.M.loaded_segments (0x6041c : word) = Some W_6041c.
Proof. vm_refl. Qed.
Lemma D_6041c : decode_any W_6041c = Some (Store SZ8 21 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_60420 : bv 32 := 0x14d070ef.
Lemma F_60420 : fetch_word Asan.M.loaded_segments (0x60420 : word) = Some W_60420.
Proof. vm_refl. Qed.
Lemma D_60420 : decode_any W_60420 = Some (Jal 1 31052, 4%Z).
Proof. vm_refl. Qed.

Definition W_60424 : bv 32 := 0x00200593.
Lemma F_60424 : fetch_word Asan.M.loaded_segments (0x60424 : word) = Some W_60424.
Proof. vm_refl. Qed.
Lemma D_60424 : decode_any W_60424 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_60428 : bv 32 := 0x06b56663.
Lemma F_60428 : fetch_word Asan.M.loaded_segments (0x60428 : word) = Some W_60428.
Proof. vm_refl. Qed.
Lemma D_60428 : decode_any W_60428 = Some (Branch BC_LTU 10 11 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_6042c : bv 32 := 0x013abc23.
Lemma F_6042c : fetch_word Asan.M.loaded_segments (0x6042c : word) = Some W_6042c.
Proof. vm_refl. Qed.
Lemma D_6042c : decode_any W_6042c = Some (Store SZ8 21 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_60430 : bv 32 := 0x0640006f.
Lemma F_60430 : fetch_word Asan.M.loaded_segments (0x60430 : word) = Some W_60430.
Proof. vm_refl. Qed.
Lemma D_60430 : decode_any W_60430 = Some (Jal 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_60434 : bv 32 := 0x3f8200ef.
Lemma F_60434 : fetch_word Asan.M.loaded_segments (0x60434 : word) = Some W_60434.
Proof. vm_refl. Qed.
Lemma D_60434 : decode_any W_60434 = Some (Jal 1 132088, 4%Z).
Proof. vm_refl. Qed.

Definition W_60438 : bv 32 := 0x00075597.
Lemma F_60438 : fetch_word Asan.M.loaded_segments (0x60438 : word) = Some W_60438.
Proof. vm_refl. Qed.
Lemma D_60438 : decode_any W_60438 = Some (Auipc 11 117, 4%Z).
Proof. vm_refl. Qed.

Definition W_6043c : bv 32 := 0x4705b583.
Lemma F_6043c : fetch_word Asan.M.loaded_segments (0x6043c : word) = Some W_6043c.
Proof. vm_refl. Qed.
Lemma D_6043c : decode_any W_6043c = Some (Load SZ8 true 11 11 1136, 4%Z).
Proof. vm_refl. Qed.

Definition W_60440 : bv 32 := 0x0225ca03.
Lemma F_60440 : fetch_word Asan.M.loaded_segments (0x60440 : word) = Some W_60440.
Proof. vm_refl. Qed.
Lemma D_60440 : decode_any W_60440 = Some (Load SZ1 false 20 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_60444 : bv 32 := 0x00050993.
Lemma F_60444 : fetch_word Asan.M.loaded_segments (0x60444 : word) = Some W_60444.
Proof. vm_refl. Qed.
Lemma D_60444 : decode_any W_60444 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60448 : bv 32 := 0x125070ef.
Lemma F_60448 : fetch_word Asan.M.loaded_segments (0x60448 : word) = Some W_60448.
Proof. vm_refl. Qed.
Lemma D_60448 : decode_any W_60448 = Some (Jal 1 31012, 4%Z).
Proof. vm_refl. Qed.

Definition W_6044c : bv 32 := 0x00050793.
Lemma F_6044c : fetch_word Asan.M.loaded_segments (0x6044c : word) = Some W_6044c.
Proof. vm_refl. Qed.
Lemma D_6044c : decode_any W_6044c = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60450 : bv 32 := 0x00153513.
Lemma F_60450 : fetch_word Asan.M.loaded_segments (0x60450 : word) = Some W_60450.
Proof. vm_refl. Qed.
Lemma D_60450 : decode_any W_60450 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_60454 : bv 32 := 0xfff50513.
Lemma F_60454 : fetch_word Asan.M.loaded_segments (0x60454 : word) = Some W_60454.
Proof. vm_refl. Qed.
Lemma D_60454 : decode_any W_60454 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_60458 : bv 32 := 0x008575b3.
Lemma F_60458 : fetch_word Asan.M.loaded_segments (0x60458 : word) = Some W_60458.
Proof. vm_refl. Qed.
Lemma D_60458 : decode_any W_60458 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6045c : bv 32 := 0x00100513.
Lemma F_6045c : fetch_word Asan.M.loaded_segments (0x6045c : word) = Some W_6045c.
Proof. vm_refl. Qed.
Lemma D_6045c : decode_any W_6045c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_60460 : bv 32 := 0x00bb34a3.
Lemma F_60460 : fetch_word Asan.M.loaded_segments (0x60460 : word) = Some W_60460.
Proof. vm_refl. Qed.
Lemma D_60460 : decode_any W_60460 = Some (Store SZ8 22 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_60464 : bv 32 := 0x00f56a63.
Lemma F_60464 : fetch_word Asan.M.loaded_segments (0x60464 : word) = Some W_60464.
Proof. vm_refl. Qed.
Lemma D_60464 : decode_any W_60464 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_60468 : bv 32 := 0x00a79463.
Lemma F_60468 : fetch_word Asan.M.loaded_segments (0x60468 : word) = Some W_60468.
Proof. vm_refl. Qed.
Lemma D_60468 : decode_any W_60468 = Some (Branch BC_NE 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6046c : bv 32 := 0x013ab823.
Lemma F_6046c : fetch_word Asan.M.loaded_segments (0x6046c : word) = Some W_6046c.
Proof. vm_refl. Qed.
Lemma D_6046c : decode_any W_6046c = Some (Store SZ8 21 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_60470 : bv 32 := 0x00faa423.
Lemma F_60470 : fetch_word Asan.M.loaded_segments (0x60470 : word) = Some W_60470.
Proof. vm_refl. Qed.
Lemma D_60470 : decode_any W_60470 = Some (Store SZ4 21 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_60474 : bv 32 := 0x0200006f.
Lemma F_60474 : fetch_word Asan.M.loaded_segments (0x60474 : word) = Some W_60474.
Proof. vm_refl. Qed.
Lemma D_60474 : decode_any W_60474 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_60478 : bv 32 := 0x80040513.
Lemma F_60478 : fetch_word Asan.M.loaded_segments (0x60478 : word) = Some W_60478.
Proof. vm_refl. Qed.
Lemma D_60478 : decode_any W_60478 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6047c : bv 32 := 0xfa850513.
Lemma F_6047c : fetch_word Asan.M.loaded_segments (0x6047c : word) = Some W_6047c.
Proof. vm_refl. Qed.
Lemma D_6047c : decode_any W_6047c = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_60480 : bv 32 := 0x00098593.
Lemma F_60480 : fetch_word Asan.M.loaded_segments (0x60480 : word) = Some W_60480.
Proof. vm_refl. Qed.
Lemma D_60480 : decode_any W_60480 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60484 : bv 32 := 0x00040613.
Lemma F_60484 : fetch_word Asan.M.loaded_segments (0x60484 : word) = Some W_60484.
Proof. vm_refl. Qed.
Lemma D_60484 : decode_any W_60484 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60488 : bv 32 := 0x00000693.
Lemma F_60488 : fetch_word Asan.M.loaded_segments (0x60488 : word) = Some W_60488.
Proof. vm_refl. Qed.
Lemma D_60488 : decode_any W_60488 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6048c : bv 32 := 0x000a0713.
Lemma F_6048c : fetch_word Asan.M.loaded_segments (0x6048c : word) = Some W_6048c.
Proof. vm_refl. Qed.
Lemma D_6048c : decode_any W_6048c = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_60490 : bv 32 := 0x0ed070ef.
Lemma F_60490 : fetch_word Asan.M.loaded_segments (0x60490 : word) = Some W_60490.
Proof. vm_refl. Qed.
Lemma D_60490 : decode_any W_60490 = Some (Jal 1 30956, 4%Z).
Proof. vm_refl. Qed.

Definition W_60494 : bv 32 := 0x80040613.
Lemma F_60494 : fetch_word Asan.M.loaded_segments (0x60494 : word) = Some W_60494.
Proof. vm_refl. Qed.
Lemma D_60494 : decode_any W_60494 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_60498 : bv 32 := 0xfa860613.
Lemma F_60498 : fetch_word Asan.M.loaded_segments (0x60498 : word) = Some W_60498.
Proof. vm_refl. Qed.
Lemma D_60498 : decode_any W_60498 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6049c : bv 32 := 0x00090513.
Lemma F_6049c : fetch_word Asan.M.loaded_segments (0x6049c : word) = Some W_6049c.
Proof. vm_refl. Qed.
Lemma D_6049c : decode_any W_6049c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_604a0 : bv 32 := 0x00048593.
Lemma F_604a0 : fetch_word Asan.M.loaded_segments (0x604a0 : word) = Some W_604a0.
Proof. vm_refl. Qed.
Lemma D_604a0 : decode_any W_604a0 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_604a4 : bv 32 := 0xa61dd0ef.
Lemma F_604a4 : fetch_word Asan.M.loaded_segments (0x604a4 : word) = Some W_604a4.
Proof. vm_refl. Qed.
Lemma D_604a4 : decode_any W_604a4 = Some (Jal 1 1956448, 4%Z).
Proof. vm_refl. Qed.

Definition W_604a8 : bv 32 := 0x07010113.
Lemma F_604a8 : fetch_word Asan.M.loaded_segments (0x604a8 : word) = Some W_604a8.
Proof. vm_refl. Qed.
Lemma D_604a8 : decode_any W_604a8 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_604ac : bv 32 := 0x7e813083.
Lemma F_604ac : fetch_word Asan.M.loaded_segments (0x604ac : word) = Some W_604ac.
Proof. vm_refl. Qed.
Lemma D_604ac : decode_any W_604ac = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_604b0 : bv 32 := 0x7e013403.
Lemma F_604b0 : fetch_word Asan.M.loaded_segments (0x604b0 : word) = Some W_604b0.
Proof. vm_refl. Qed.
Lemma D_604b0 : decode_any W_604b0 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_604b4 : bv 32 := 0x7d813483.
Lemma F_604b4 : fetch_word Asan.M.loaded_segments (0x604b4 : word) = Some W_604b4.
Proof. vm_refl. Qed.
Lemma D_604b4 : decode_any W_604b4 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_604b8 : bv 32 := 0x7d013903.
Lemma F_604b8 : fetch_word Asan.M.loaded_segments (0x604b8 : word) = Some W_604b8.
Proof. vm_refl. Qed.
Lemma D_604b8 : decode_any W_604b8 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_604bc : bv 32 := 0x7c813983.
Lemma F_604bc : fetch_word Asan.M.loaded_segments (0x604bc : word) = Some W_604bc.
Proof. vm_refl. Qed.
Lemma D_604bc : decode_any W_604bc = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_604c0 : bv 32 := 0x7c013a03.
Lemma F_604c0 : fetch_word Asan.M.loaded_segments (0x604c0 : word) = Some W_604c0.
Proof. vm_refl. Qed.
Lemma D_604c0 : decode_any W_604c0 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_604c4 : bv 32 := 0x7b813a83.
Lemma F_604c4 : fetch_word Asan.M.loaded_segments (0x604c4 : word) = Some W_604c4.
Proof. vm_refl. Qed.
Lemma D_604c4 : decode_any W_604c4 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_604c8 : bv 32 := 0x7b013b03.
Lemma F_604c8 : fetch_word Asan.M.loaded_segments (0x604c8 : word) = Some W_604c8.
Proof. vm_refl. Qed.
Lemma D_604c8 : decode_any W_604c8 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_604cc : bv 32 := 0x7f010113.
Lemma F_604cc : fetch_word Asan.M.loaded_segments (0x604cc : word) = Some W_604cc.
Proof. vm_refl. Qed.
Lemma D_604cc : decode_any W_604cc = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_604d0 : bv 32 := 0x00008067.
Lemma F_604d0 : fetch_word Asan.M.loaded_segments (0x604d0 : word) = Some W_604d0.
Proof. vm_refl. Qed.
Lemma D_604d0 : decode_any W_604d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
