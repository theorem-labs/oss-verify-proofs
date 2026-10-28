(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_a143c : bv 32 := 0x160c36af.

Definition W_a1440 : bv 32 := 0x00c69663.

Definition W_a1444 : bv 32 := 0x1aec37af.

Definition W_a17ac : bv 32 := 0x160c332f.

Definition W_a17b0 : bv 32 := 0x00a31663.

Definition W_a17b4 : bv 32 := 0x1a5c33af.

Definition W_163af0 : bv 32 := 0x1606a72f.

Definition W_163af4 : bv 32 := 0x00b71663.

Definition W_163af8 : bv 32 := 0x1ec6a7af.

Definition W_163e28 : bv 32 := 0xfffff5b7.
Lemma F_163e28 : fetch_word AsanUbsan.M.loaded_segments (0x1657d0 : word) = Some W_163e28.
Proof. vm_refl. Qed.
Lemma D_163e28 : decode_any W_163e28 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_163e2c : bv 32 := 0x0015859b.
Lemma F_163e2c : fetch_word AsanUbsan.M.loaded_segments (0x1657d4 : word) = Some W_163e2c.
Proof. vm_refl. Qed.
Lemma D_163e2c : decode_any W_163e2c = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_163e30 : bv 32 := 0x02b56663.
Lemma F_163e30 : fetch_word AsanUbsan.M.loaded_segments (0x1657d8 : word) = Some W_163e30.
Proof. vm_refl. Qed.
Lemma D_163e30 : decode_any W_163e30 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_163e5c : bv 32 := 0x00008067.
Lemma F_163e5c : fetch_word AsanUbsan.M.loaded_segments (0x165804 : word) = Some W_163e5c.
Proof. vm_refl. Qed.
Lemma D_163e5c : decode_any W_163e5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b4b4 : bv 32 := 0x975f80ef.
Lemma F_16b4b4 : fetch_word AsanUbsan.M.loaded_segments (0x16ce5c : word) = Some W_16b4b4.
Proof. vm_refl. Qed.
Lemma D_16b4b4 : decode_any W_16b4b4 = Some (Jal 1 2066804, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b4b8 : bv 32 := 0x09651863.
Lemma F_16b4b8 : fetch_word AsanUbsan.M.loaded_segments (0x16ce60 : word) = Some W_16b4b8.
Proof. vm_refl. Qed.
Lemma D_16b4b8 : decode_any W_16b4b8 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b4bc : bv 32 := 0x0584b503.
Lemma F_16b4bc : fetch_word AsanUbsan.M.loaded_segments (0x16ce64 : word) = Some W_16b4bc.
Proof. vm_refl. Qed.
Lemma D_16b4bc : decode_any W_16b4bc = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b4c0 : bv 32 := 0x0604b583.
Lemma F_16b4c0 : fetch_word AsanUbsan.M.loaded_segments (0x16ce68 : word) = Some W_16b4c0.
Proof. vm_refl. Qed.
Lemma D_16b4c0 : decode_any W_16b4c0 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b4c4 : bv 32 := 0x00b505b3.
Lemma F_16b4c4 : fetch_word AsanUbsan.M.loaded_segments (0x16ce6c : word) = Some W_16b4c4.
Proof. vm_refl. Qed.
Lemma D_16b4c4 : decode_any W_16b4c4 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b4c8 : bv 32 := 0x02b4b023.
Lemma F_16b4c8 : fetch_word AsanUbsan.M.loaded_segments (0x16ce70 : word) = Some W_16b4c8.
Proof. vm_refl. Qed.
Lemma D_16b4c8 : decode_any W_16b4c8 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b4cc : bv 32 := 0x02a4b423.
Lemma F_16b4cc : fetch_word AsanUbsan.M.loaded_segments (0x16ce74 : word) = Some W_16b4cc.
Proof. vm_refl. Qed.
Lemma D_16b4cc : decode_any W_16b4cc = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b4d0 : bv 32 := 0x02a4bc23.
Lemma F_16b4d0 : fetch_word AsanUbsan.M.loaded_segments (0x16ce78 : word) = Some W_16b4d0.
Proof. vm_refl. Qed.
Lemma D_16b4d0 : decode_any W_16b4d0 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b4d4 : bv 32 := 0x00040513.
Lemma F_16b4d4 : fetch_word AsanUbsan.M.loaded_segments (0x16ce7c : word) = Some W_16b4d4.
Proof. vm_refl. Qed.
Lemma D_16b4d4 : decode_any W_16b4d4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b4d8 : bv 32 := 0x000ab583.
Lemma F_16b4d8 : fetch_word AsanUbsan.M.loaded_segments (0x16ce80 : word) = Some W_16b4d8.
Proof. vm_refl. Qed.
Lemma D_16b4d8 : decode_any W_16b4d8 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b4dc : bv 32 := 0x02813603.
Lemma F_16b4dc : fetch_word AsanUbsan.M.loaded_segments (0x16ce84 : word) = Some W_16b4dc.
Proof. vm_refl. Qed.
Lemma D_16b4dc : decode_any W_16b4dc = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b4e0 : bv 32 := 0x0cc59a63.
Lemma F_16b4e0 : fetch_word AsanUbsan.M.loaded_segments (0x16ce88 : word) = Some W_16b4e0.
Proof. vm_refl. Qed.
Lemma D_16b4e0 : decode_any W_16b4e0 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b4e4 : bv 32 := 0x06813083.
Lemma F_16b4e4 : fetch_word AsanUbsan.M.loaded_segments (0x16ce8c : word) = Some W_16b4e4.
Proof. vm_refl. Qed.
Lemma D_16b4e4 : decode_any W_16b4e4 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b4e8 : bv 32 := 0x06013403.
Lemma F_16b4e8 : fetch_word AsanUbsan.M.loaded_segments (0x16ce90 : word) = Some W_16b4e8.
Proof. vm_refl. Qed.
Lemma D_16b4e8 : decode_any W_16b4e8 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b4ec : bv 32 := 0x05813483.
Lemma F_16b4ec : fetch_word AsanUbsan.M.loaded_segments (0x16ce94 : word) = Some W_16b4ec.
Proof. vm_refl. Qed.
Lemma D_16b4ec : decode_any W_16b4ec = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b4f0 : bv 32 := 0x05013903.
Lemma F_16b4f0 : fetch_word AsanUbsan.M.loaded_segments (0x16ce98 : word) = Some W_16b4f0.
Proof. vm_refl. Qed.
Lemma D_16b4f0 : decode_any W_16b4f0 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b4f4 : bv 32 := 0x04813983.
Lemma F_16b4f4 : fetch_word AsanUbsan.M.loaded_segments (0x16ce9c : word) = Some W_16b4f4.
Proof. vm_refl. Qed.
Lemma D_16b4f4 : decode_any W_16b4f4 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b4f8 : bv 32 := 0x04013a03.
Lemma F_16b4f8 : fetch_word AsanUbsan.M.loaded_segments (0x16cea0 : word) = Some W_16b4f8.
Proof. vm_refl. Qed.
Lemma D_16b4f8 : decode_any W_16b4f8 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b4fc : bv 32 := 0x03813a83.
Lemma F_16b4fc : fetch_word AsanUbsan.M.loaded_segments (0x16cea4 : word) = Some W_16b4fc.
Proof. vm_refl. Qed.
Lemma D_16b4fc : decode_any W_16b4fc = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b500 : bv 32 := 0x03013b03.
Lemma F_16b500 : fetch_word AsanUbsan.M.loaded_segments (0x16cea8 : word) = Some W_16b500.
Proof. vm_refl. Qed.
Lemma D_16b500 : decode_any W_16b500 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b504 : bv 32 := 0x07010113.
Lemma F_16b504 : fetch_word AsanUbsan.M.loaded_segments (0x16ceac : word) = Some W_16b504.
Proof. vm_refl. Qed.
Lemma D_16b504 : decode_any W_16b504 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b508 : bv 32 := 0x00008067.
Lemma F_16b508 : fetch_word AsanUbsan.M.loaded_segments (0x16ceb0 : word) = Some W_16b508.
Proof. vm_refl. Qed.
Lemma D_16b508 : decode_any W_16b508 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b50c : bv 32 := 0x00800713.
Lemma F_16b50c : fetch_word AsanUbsan.M.loaded_segments (0x16ceb4 : word) = Some W_16b50c.
Proof. vm_refl. Qed.
Lemma D_16b50c : decode_any W_16b50c = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b510 : bv 32 := 0x000a0593.
Lemma F_16b510 : fetch_word AsanUbsan.M.loaded_segments (0x16ceb8 : word) = Some W_16b510.
Proof. vm_refl. Qed.
Lemma D_16b510 : decode_any W_16b510 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b514 : bv 32 := 0x00e98733.
Lemma F_16b514 : fetch_word AsanUbsan.M.loaded_segments (0x16cebc : word) = Some W_16b514.
Proof. vm_refl. Qed.
Lemma D_16b514 : decode_any W_16b514 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b518 : bv 32 := 0x00073783.
Lemma F_16b518 : fetch_word AsanUbsan.M.loaded_segments (0x16cec0 : word) = Some W_16b518.
Proof. vm_refl. Qed.
Lemma D_16b518 : decode_any W_16b518 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b51c : bv 32 := 0x40ab0b33.
Lemma F_16b51c : fetch_word AsanUbsan.M.loaded_segments (0x16cec4 : word) = Some W_16b51c.
Proof. vm_refl. Qed.
Lemma D_16b51c : decode_any W_16b51c = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b520 : bv 32 := 0x0784a503.
Lemma F_16b520 : fetch_word AsanUbsan.M.loaded_segments (0x16cec8 : word) = Some W_16b520.
Proof. vm_refl. Qed.
Lemma D_16b520 : decode_any W_16b520 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b524 : bv 32 := 0x40c9093b.
Lemma F_16b524 : fetch_word AsanUbsan.M.loaded_segments (0x16cecc : word) = Some W_16b524.
Proof. vm_refl. Qed.
Lemma D_16b524 : decode_any W_16b524 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b528 : bv 32 := 0x40d787b3.
Lemma F_16b528 : fetch_word AsanUbsan.M.loaded_segments (0x16ced0 : word) = Some W_16b528.
Proof. vm_refl. Qed.
Lemma D_16b528 : decode_any W_16b528 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b52c : bv 32 := 0x00f73023.
Lemma F_16b52c : fetch_word AsanUbsan.M.loaded_segments (0x16ced4 : word) = Some W_16b52c.
Proof. vm_refl. Qed.
Lemma D_16b52c : decode_any W_16b52c = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b530 : bv 32 := 0x04200893.
Lemma F_16b530 : fetch_word AsanUbsan.M.loaded_segments (0x16ced8 : word) = Some W_16b530.
Proof. vm_refl. Qed.
Lemma D_16b530 : decode_any W_16b530 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b534 : bv 32 := 0x00090613.
Lemma F_16b534 : fetch_word AsanUbsan.M.loaded_segments (0x16cedc : word) = Some W_16b534.
Proof. vm_refl. Qed.
Lemma D_16b534 : decode_any W_16b534 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b53c : bv 32 := 0x8edf80ef.
Lemma F_16b53c : fetch_word AsanUbsan.M.loaded_segments (0x16cee4 : word) = Some W_16b53c.
Proof. vm_refl. Qed.
Lemma D_16b53c : decode_any W_16b53c = Some (Jal 1 2066668, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b540 : bv 32 := 0x000a0993.
Lemma F_16b540 : fetch_word AsanUbsan.M.loaded_segments (0x16cee8 : word) = Some W_16b540.
Proof. vm_refl. Qed.
Lemma D_16b540 : decode_any W_16b540 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b544 : bv 32 := 0xf7650ce3.
Lemma F_16b544 : fetch_word AsanUbsan.M.loaded_segments (0x16ceec : word) = Some W_16b544.
Proof. vm_refl. Qed.
Lemma D_16b544 : decode_any W_16b544 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b548 : bv 32 := 0x02054c63.
Lemma F_16b548 : fetch_word AsanUbsan.M.loaded_segments (0x16cef0 : word) = Some W_16b548.
Proof. vm_refl. Qed.
Lemma D_16b548 : decode_any W_16b548 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b54c : bv 32 := 0x0089b583.
Lemma F_16b54c : fetch_word AsanUbsan.M.loaded_segments (0x16cef4 : word) = Some W_16b54c.
Proof. vm_refl. Qed.
Lemma D_16b54c : decode_any W_16b54c = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b550 : bv 32 := 0x00a5b633.
Lemma F_16b550 : fetch_word AsanUbsan.M.loaded_segments (0x16cef8 : word) = Some W_16b550.
Proof. vm_refl. Qed.
Lemma D_16b550 : decode_any W_16b550 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b554 : bv 32 := 0x00461a13.
Lemma F_16b554 : fetch_word AsanUbsan.M.loaded_segments (0x16cefc : word) = Some W_16b554.
Proof. vm_refl. Qed.
Lemma D_16b554 : decode_any W_16b554 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b558 : bv 32 := 0x01498a33.
Lemma F_16b558 : fetch_word AsanUbsan.M.loaded_segments (0x16cf00 : word) = Some W_16b558.
Proof. vm_refl. Qed.
Lemma D_16b558 : decode_any W_16b558 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b55c : bv 32 := 0x000a3703.
Lemma F_16b55c : fetch_word AsanUbsan.M.loaded_segments (0x16cf04 : word) = Some W_16b55c.
Proof. vm_refl. Qed.
Lemma D_16b55c : decode_any W_16b55c = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b560 : bv 32 := 0x40c006b3.
Lemma F_16b560 : fetch_word AsanUbsan.M.loaded_segments (0x16cf08 : word) = Some W_16b560.
Proof. vm_refl. Qed.
Lemma D_16b560 : decode_any W_16b560 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b564 : bv 32 := 0x00b6f6b3.
Lemma F_16b564 : fetch_word AsanUbsan.M.loaded_segments (0x16cf0c : word) = Some W_16b564.
Proof. vm_refl. Qed.
Lemma D_16b564 : decode_any W_16b564 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b568 : bv 32 := 0x40d506b3.
Lemma F_16b568 : fetch_word AsanUbsan.M.loaded_segments (0x16cf10 : word) = Some W_16b568.
Proof. vm_refl. Qed.
Lemma D_16b568 : decode_any W_16b568 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b56c : bv 32 := 0x00d70733.
Lemma F_16b56c : fetch_word AsanUbsan.M.loaded_segments (0x16cf14 : word) = Some W_16b56c.
Proof. vm_refl. Qed.
Lemma D_16b56c : decode_any W_16b56c = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b570 : bv 32 := 0x00ea3023.
Lemma F_16b570 : fetch_word AsanUbsan.M.loaded_segments (0x16cf18 : word) = Some W_16b570.
Proof. vm_refl. Qed.
Lemma D_16b570 : decode_any W_16b570 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b574 : bv 32 := 0xf8a5fce3.
Lemma F_16b574 : fetch_word AsanUbsan.M.loaded_segments (0x16cf1c : word) = Some W_16b574.
Proof. vm_refl. Qed.
Lemma D_16b574 : decode_any W_16b574 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b578 : bv 32 := 0x01800713.
Lemma F_16b578 : fetch_word AsanUbsan.M.loaded_segments (0x16cf20 : word) = Some W_16b578.
Proof. vm_refl. Qed.
Lemma D_16b578 : decode_any W_16b578 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_16b57c : bv 32 := 0xf95ff06f.
Lemma F_16b57c : fetch_word AsanUbsan.M.loaded_segments (0x16cf24 : word) = Some W_16b57c.
Proof. vm_refl. Qed.
Lemma D_16b57c : decode_any W_16b57c = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.
