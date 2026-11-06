(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_1264f8 : bv 32 := 0x0284b503.
Lemma F_1264f8 : fetch_word AsanUbsan.M.loaded_segments (0x12653c : word) = Some W_1264f8.
Proof. vm_refl. Qed.
Lemma D_1264f8 : decode_any W_1264f8 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1264fc : bv 32 := 0x0384b603.
Lemma F_1264fc : fetch_word AsanUbsan.M.loaded_segments (0x126540 : word) = Some W_1264fc.
Proof. vm_refl. Qed.
Lemma D_1264fc : decode_any W_1264fc = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_126500 : bv 32 := 0x40c50b33.
Lemma F_126500 : fetch_word AsanUbsan.M.loaded_segments (0x126544 : word) = Some W_126500.
Proof. vm_refl. Qed.
Lemma D_126500 : decode_any W_126500 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_126504 : bv 32 := 0x00c546b3.
Lemma F_126504 : fetch_word AsanUbsan.M.loaded_segments (0x126548 : word) = Some W_126504.
Proof. vm_refl. Qed.
Lemma D_126504 : decode_any W_126504 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_126508 : bv 32 := 0x00c13423.
Lemma F_126508 : fetch_word AsanUbsan.M.loaded_segments (0x12654c : word) = Some W_126508.
Proof. vm_refl. Qed.
Lemma D_126508 : decode_any W_126508 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_12650c : bv 32 := 0x01613823.
Lemma F_12650c : fetch_word AsanUbsan.M.loaded_segments (0x126550 : word) = Some W_12650c.
Proof. vm_refl. Qed.
Lemma D_12650c : decode_any W_12650c = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_126510 : bv 32 := 0x00b13c23.
Lemma F_126510 : fetch_word AsanUbsan.M.loaded_segments (0x126554 : word) = Some W_126510.
Proof. vm_refl. Qed.
Lemma D_126510 : decode_any W_126510 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_126514 : bv 32 := 0x02813023.
Lemma F_126514 : fetch_word AsanUbsan.M.loaded_segments (0x126558 : word) = Some W_126514.
Proof. vm_refl. Qed.
Lemma D_126514 : decode_any W_126514 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_126518 : bv 32 := 0x008b0b33.
Lemma F_126518 : fetch_word AsanUbsan.M.loaded_segments (0x12655c : word) = Some W_126518.
Proof. vm_refl. Qed.
Lemma D_126518 : decode_any W_126518 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_12651c : bv 32 := 0x00d03933.
Lemma F_12651c : fetch_word AsanUbsan.M.loaded_segments (0x126560 : word) = Some W_12651c.
Proof. vm_refl. Qed.
Lemma D_12651c : decode_any W_12651c = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_126520 : bv 32 := 0x00c50663.
Lemma F_126520 : fetch_word AsanUbsan.M.loaded_segments (0x126564 : word) = Some W_126520.
Proof. vm_refl. Qed.
Lemma D_126520 : decode_any W_126520 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_126524 : bv 32 := 0x00810993.
Lemma F_126524 : fetch_word AsanUbsan.M.loaded_segments (0x126568 : word) = Some W_126524.
Proof. vm_refl. Qed.
Lemma D_126524 : decode_any W_126524 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_126528 : bv 32 := 0x0080006f.
Lemma F_126528 : fetch_word AsanUbsan.M.loaded_segments (0x12656c : word) = Some W_126528.
Proof. vm_refl. Qed.
Lemma D_126528 : decode_any W_126528 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_12652c : bv 32 := 0x01810993.
Lemma F_12652c : fetch_word AsanUbsan.M.loaded_segments (0x126570 : word) = Some W_12652c.
Proof. vm_refl. Qed.
Lemma D_12652c : decode_any W_12652c = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_126530 : bv 32 := 0x0784a503.
Lemma F_126530 : fetch_word AsanUbsan.M.loaded_segments (0x126574 : word) = Some W_126530.
Proof. vm_refl. Qed.
Lemma D_126530 : decode_any W_126530 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_126534 : bv 32 := 0x00190913.
Lemma F_126534 : fetch_word AsanUbsan.M.loaded_segments (0x126578 : word) = Some W_126534.
Proof. vm_refl. Qed.
Lemma D_126534 : decode_any W_126534 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_126538 : bv 32 := 0x04200893.
Lemma F_126538 : fetch_word AsanUbsan.M.loaded_segments (0x12657c : word) = Some W_126538.
Proof. vm_refl. Qed.
Lemma D_126538 : decode_any W_126538 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_12653c : bv 32 := 0x00098593.
Lemma F_12653c : fetch_word AsanUbsan.M.loaded_segments (0x126580 : word) = Some W_12653c.
Proof. vm_refl. Qed.
Lemma D_12653c : decode_any W_12653c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_126540 : bv 32 := 0x00090613.
Lemma F_126540 : fetch_word AsanUbsan.M.loaded_segments (0x126584 : word) = Some W_126540.
Proof. vm_refl. Qed.
Lemma D_126540 : decode_any W_126540 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_126548 : bv 32 := 0x971f80ef.
Lemma F_126548 : fetch_word AsanUbsan.M.loaded_segments (0x12658c : word) = Some W_126548.
Proof. vm_refl. Qed.
Lemma D_126548 : decode_any W_126548 = Some (Jal 1 2066800, 4%Z).
Proof. vm_refl. Qed.

Definition W_12654c : bv 32 := 0x09651863.
Lemma F_12654c : fetch_word AsanUbsan.M.loaded_segments (0x126590 : word) = Some W_12654c.
Proof. vm_refl. Qed.
Lemma D_12654c : decode_any W_12654c = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265a0 : bv 32 := 0x00800713.
Lemma F_1265a0 : fetch_word AsanUbsan.M.loaded_segments (0x1265e4 : word) = Some W_1265a0.
Proof. vm_refl. Qed.
Lemma D_1265a0 : decode_any W_1265a0 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265a4 : bv 32 := 0x000a0593.
Lemma F_1265a4 : fetch_word AsanUbsan.M.loaded_segments (0x1265e8 : word) = Some W_1265a4.
Proof. vm_refl. Qed.
Lemma D_1265a4 : decode_any W_1265a4 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265a8 : bv 32 := 0x00e98733.
Lemma F_1265a8 : fetch_word AsanUbsan.M.loaded_segments (0x1265ec : word) = Some W_1265a8.
Proof. vm_refl. Qed.
Lemma D_1265a8 : decode_any W_1265a8 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265ac : bv 32 := 0x00073783.
Lemma F_1265ac : fetch_word AsanUbsan.M.loaded_segments (0x1265f0 : word) = Some W_1265ac.
Proof. vm_refl. Qed.
Lemma D_1265ac : decode_any W_1265ac = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265b0 : bv 32 := 0x40ab0b33.
Lemma F_1265b0 : fetch_word AsanUbsan.M.loaded_segments (0x1265f4 : word) = Some W_1265b0.
Proof. vm_refl. Qed.
Lemma D_1265b0 : decode_any W_1265b0 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265b4 : bv 32 := 0x0784a503.
Lemma F_1265b4 : fetch_word AsanUbsan.M.loaded_segments (0x1265f8 : word) = Some W_1265b4.
Proof. vm_refl. Qed.
Lemma D_1265b4 : decode_any W_1265b4 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265b8 : bv 32 := 0x40c9093b.
Lemma F_1265b8 : fetch_word AsanUbsan.M.loaded_segments (0x1265fc : word) = Some W_1265b8.
Proof. vm_refl. Qed.
Lemma D_1265b8 : decode_any W_1265b8 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265bc : bv 32 := 0x40d787b3.
Lemma F_1265bc : fetch_word AsanUbsan.M.loaded_segments (0x126600 : word) = Some W_1265bc.
Proof. vm_refl. Qed.
Lemma D_1265bc : decode_any W_1265bc = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265c0 : bv 32 := 0x00f73023.
Lemma F_1265c0 : fetch_word AsanUbsan.M.loaded_segments (0x126604 : word) = Some W_1265c0.
Proof. vm_refl. Qed.
Lemma D_1265c0 : decode_any W_1265c0 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265c4 : bv 32 := 0x04200893.
Lemma F_1265c4 : fetch_word AsanUbsan.M.loaded_segments (0x126608 : word) = Some W_1265c4.
Proof. vm_refl. Qed.
Lemma D_1265c4 : decode_any W_1265c4 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265c8 : bv 32 := 0x00090613.
Lemma F_1265c8 : fetch_word AsanUbsan.M.loaded_segments (0x12660c : word) = Some W_1265c8.
Proof. vm_refl. Qed.
Lemma D_1265c8 : decode_any W_1265c8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265d0 : bv 32 := 0x8e9f80ef.
Lemma F_1265d0 : fetch_word AsanUbsan.M.loaded_segments (0x126614 : word) = Some W_1265d0.
Proof. vm_refl. Qed.
Lemma D_1265d0 : decode_any W_1265d0 = Some (Jal 1 2066664, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265d4 : bv 32 := 0x000a0993.
Lemma F_1265d4 : fetch_word AsanUbsan.M.loaded_segments (0x126618 : word) = Some W_1265d4.
Proof. vm_refl. Qed.
Lemma D_1265d4 : decode_any W_1265d4 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265d8 : bv 32 := 0xf7650ce3.
Lemma F_1265d8 : fetch_word AsanUbsan.M.loaded_segments (0x12661c : word) = Some W_1265d8.
Proof. vm_refl. Qed.
Lemma D_1265d8 : decode_any W_1265d8 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265dc : bv 32 := 0x02054c63.
Lemma F_1265dc : fetch_word AsanUbsan.M.loaded_segments (0x126620 : word) = Some W_1265dc.
Proof. vm_refl. Qed.
Lemma D_1265dc : decode_any W_1265dc = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265e0 : bv 32 := 0x0089b583.
Lemma F_1265e0 : fetch_word AsanUbsan.M.loaded_segments (0x126624 : word) = Some W_1265e0.
Proof. vm_refl. Qed.
Lemma D_1265e0 : decode_any W_1265e0 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265e4 : bv 32 := 0x00a5b633.
Lemma F_1265e4 : fetch_word AsanUbsan.M.loaded_segments (0x126628 : word) = Some W_1265e4.
Proof. vm_refl. Qed.
Lemma D_1265e4 : decode_any W_1265e4 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265e8 : bv 32 := 0x00461a13.
Lemma F_1265e8 : fetch_word AsanUbsan.M.loaded_segments (0x12662c : word) = Some W_1265e8.
Proof. vm_refl. Qed.
Lemma D_1265e8 : decode_any W_1265e8 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265ec : bv 32 := 0x01498a33.
Lemma F_1265ec : fetch_word AsanUbsan.M.loaded_segments (0x126630 : word) = Some W_1265ec.
Proof. vm_refl. Qed.
Lemma D_1265ec : decode_any W_1265ec = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265f0 : bv 32 := 0x000a3703.
Lemma F_1265f0 : fetch_word AsanUbsan.M.loaded_segments (0x126634 : word) = Some W_1265f0.
Proof. vm_refl. Qed.
Lemma D_1265f0 : decode_any W_1265f0 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265f4 : bv 32 := 0x40c006b3.
Lemma F_1265f4 : fetch_word AsanUbsan.M.loaded_segments (0x126638 : word) = Some W_1265f4.
Proof. vm_refl. Qed.
Lemma D_1265f4 : decode_any W_1265f4 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265f8 : bv 32 := 0x00b6f6b3.
Lemma F_1265f8 : fetch_word AsanUbsan.M.loaded_segments (0x12663c : word) = Some W_1265f8.
Proof. vm_refl. Qed.
Lemma D_1265f8 : decode_any W_1265f8 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_1265fc : bv 32 := 0x40d506b3.
Lemma F_1265fc : fetch_word AsanUbsan.M.loaded_segments (0x126640 : word) = Some W_1265fc.
Proof. vm_refl. Qed.
Lemma D_1265fc : decode_any W_1265fc = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_126600 : bv 32 := 0x00d70733.
Lemma F_126600 : fetch_word AsanUbsan.M.loaded_segments (0x126644 : word) = Some W_126600.
Proof. vm_refl. Qed.
Lemma D_126600 : decode_any W_126600 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_126604 : bv 32 := 0x00ea3023.
Lemma F_126604 : fetch_word AsanUbsan.M.loaded_segments (0x126648 : word) = Some W_126604.
Proof. vm_refl. Qed.
Lemma D_126604 : decode_any W_126604 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_126608 : bv 32 := 0xf8a5fce3.
Lemma F_126608 : fetch_word AsanUbsan.M.loaded_segments (0x12664c : word) = Some W_126608.
Proof. vm_refl. Qed.
Lemma D_126608 : decode_any W_126608 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_12660c : bv 32 := 0x01800713.
Lemma F_12660c : fetch_word AsanUbsan.M.loaded_segments (0x126650 : word) = Some W_12660c.
Proof. vm_refl. Qed.
Lemma D_12660c : decode_any W_12660c = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_126610 : bv 32 := 0xf95ff06f.
Lemma F_126610 : fetch_word AsanUbsan.M.loaded_segments (0x126654 : word) = Some W_126610.
Proof. vm_refl. Qed.
Lemma D_126610 : decode_any W_126610 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.
