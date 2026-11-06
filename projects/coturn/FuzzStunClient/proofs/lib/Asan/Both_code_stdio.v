(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_99298 : bv 32 := 0xfffff5b7.
Lemma F_99298 : fetch_word AsanUbsan.M.loaded_segments (0x99298 : word) = Some W_99298.
Proof. vm_refl. Qed.
Lemma D_99298 : decode_any W_99298 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9929c : bv 32 := 0x0015859b.
Lemma F_9929c : fetch_word AsanUbsan.M.loaded_segments (0x9929c : word) = Some W_9929c.
Proof. vm_refl. Qed.
Lemma D_9929c : decode_any W_9929c = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_992a0 : bv 32 := 0x02b56663.
Lemma F_992a0 : fetch_word AsanUbsan.M.loaded_segments (0x992a0 : word) = Some W_992a0.
Proof. vm_refl. Qed.
Lemma D_992a0 : decode_any W_992a0 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_992a4 : bv 32 := 0xff010113.
Lemma F_992a4 : fetch_word AsanUbsan.M.loaded_segments (0x992a4 : word) = Some W_992a4.
Proof. vm_refl. Qed.
Lemma D_992a4 : decode_any W_992a4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_992a8 : bv 32 := 0x00113423.
Lemma F_992a8 : fetch_word AsanUbsan.M.loaded_segments (0x992a8 : word) = Some W_992a8.
Proof. vm_refl. Qed.
Lemma D_992a8 : decode_any W_992a8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_992ac : bv 32 := 0x00813023.
Lemma F_992ac : fetch_word AsanUbsan.M.loaded_segments (0x992ac : word) = Some W_992ac.
Proof. vm_refl. Qed.
Lemma D_992ac : decode_any W_992ac = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_992b0 : bv 32 := 0x40a0043b.
Lemma F_992b0 : fetch_word AsanUbsan.M.loaded_segments (0x992b0 : word) = Some W_992b0.
Proof. vm_refl. Qed.
Lemma D_992b0 : decode_any W_992b0 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_992b4 : bv 32 := 0x981ff0ef.
Lemma F_992b4 : fetch_word AsanUbsan.M.loaded_segments (0x992b4 : word) = Some W_992b4.
Proof. vm_refl. Qed.
Lemma D_992b4 : decode_any W_992b4 = Some (Jal 1 2095488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_992b8 : bv 32 := 0x00852023.
Lemma F_992b8 : fetch_word AsanUbsan.M.loaded_segments (0x992b8 : word) = Some W_992b8.
Proof. vm_refl. Qed.
Lemma D_992b8 : decode_any W_992b8 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_992bc : bv 32 := 0xfff00513.
Lemma F_992bc : fetch_word AsanUbsan.M.loaded_segments (0x992bc : word) = Some W_992bc.
Proof. vm_refl. Qed.
Lemma D_992bc : decode_any W_992bc = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_992c0 : bv 32 := 0x00813083.
Lemma F_992c0 : fetch_word AsanUbsan.M.loaded_segments (0x992c0 : word) = Some W_992c0.
Proof. vm_refl. Qed.
Lemma D_992c0 : decode_any W_992c0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_992c4 : bv 32 := 0x00013403.
Lemma F_992c4 : fetch_word AsanUbsan.M.loaded_segments (0x992c4 : word) = Some W_992c4.
Proof. vm_refl. Qed.
Lemma D_992c4 : decode_any W_992c4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_992c8 : bv 32 := 0x01010113.
Lemma F_992c8 : fetch_word AsanUbsan.M.loaded_segments (0x992c8 : word) = Some W_992c8.
Proof. vm_refl. Qed.
Lemma D_992c8 : decode_any W_992c8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_992cc : bv 32 := 0x00008067.
Lemma F_992cc : fetch_word AsanUbsan.M.loaded_segments (0x992cc : word) = Some W_992cc.
Proof. vm_refl. Qed.
Lemma D_992cc : decode_any W_992cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e4e0 : bv 32 := 0xf9010113.
Lemma F_9e4e0 : fetch_word AsanUbsan.M.loaded_segments (0x9e4e0 : word) = Some W_9e4e0.
Proof. vm_refl. Qed.
Lemma D_9e4e0 : decode_any W_9e4e0 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e4e4 : bv 32 := 0x06113423.
Lemma F_9e4e4 : fetch_word AsanUbsan.M.loaded_segments (0x9e4e4 : word) = Some W_9e4e4.
Proof. vm_refl. Qed.
Lemma D_9e4e4 : decode_any W_9e4e4 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e4e8 : bv 32 := 0x06813023.
Lemma F_9e4e8 : fetch_word AsanUbsan.M.loaded_segments (0x9e4e8 : word) = Some W_9e4e8.
Proof. vm_refl. Qed.
Lemma D_9e4e8 : decode_any W_9e4e8 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e4ec : bv 32 := 0x04913c23.
Lemma F_9e4ec : fetch_word AsanUbsan.M.loaded_segments (0x9e4ec : word) = Some W_9e4ec.
Proof. vm_refl. Qed.
Lemma D_9e4ec : decode_any W_9e4ec = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e4f0 : bv 32 := 0x05213823.
Lemma F_9e4f0 : fetch_word AsanUbsan.M.loaded_segments (0x9e4f0 : word) = Some W_9e4f0.
Proof. vm_refl. Qed.
Lemma D_9e4f0 : decode_any W_9e4f0 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e4f4 : bv 32 := 0x05313423.
Lemma F_9e4f4 : fetch_word AsanUbsan.M.loaded_segments (0x9e4f4 : word) = Some W_9e4f4.
Proof. vm_refl. Qed.
Lemma D_9e4f4 : decode_any W_9e4f4 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e4f8 : bv 32 := 0x05413023.
Lemma F_9e4f8 : fetch_word AsanUbsan.M.loaded_segments (0x9e4f8 : word) = Some W_9e4f8.
Proof. vm_refl. Qed.
Lemma D_9e4f8 : decode_any W_9e4f8 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e4fc : bv 32 := 0x03513c23.
Lemma F_9e4fc : fetch_word AsanUbsan.M.loaded_segments (0x9e4fc : word) = Some W_9e4fc.
Proof. vm_refl. Qed.
Lemma D_9e4fc : decode_any W_9e4fc = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e500 : bv 32 := 0x03613823.
Lemma F_9e500 : fetch_word AsanUbsan.M.loaded_segments (0x9e500 : word) = Some W_9e500.
Proof. vm_refl. Qed.
Lemma D_9e500 : decode_any W_9e500 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e504 : bv 32 := 0x00060413.
Lemma F_9e504 : fetch_word AsanUbsan.M.loaded_segments (0x9e504 : word) = Some W_9e504.
Proof. vm_refl. Qed.
Lemma D_9e504 : decode_any W_9e504 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e508 : bv 32 := 0x00050493.
Lemma F_9e508 : fetch_word AsanUbsan.M.loaded_segments (0x9e508 : word) = Some W_9e508.
Proof. vm_refl. Qed.
Lemma D_9e508 : decode_any W_9e508 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e50c : bv 32 := 0x0000c517.
Lemma F_9e50c : fetch_word AsanUbsan.M.loaded_segments (0x9e50c : word) = Some W_9e50c.
Proof. vm_refl. Qed.
Lemma D_9e50c : decode_any W_9e50c = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e510 : bv 32 := 0xc3453a83.
Lemma F_9e510 : fetch_word AsanUbsan.M.loaded_segments (0x9e510 : word) = Some W_9e510.
Proof. vm_refl. Qed.
Lemma D_9e510 : decode_any W_9e510 = Some (Load SZ8 true 21 10 3124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e514 : bv 32 := 0x000ab503.
Lemma F_9e514 : fetch_word AsanUbsan.M.loaded_segments (0x9e514 : word) = Some W_9e514.
Proof. vm_refl. Qed.
Lemma D_9e514 : decode_any W_9e514 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e518 : bv 32 := 0x02a13423.
Lemma F_9e518 : fetch_word AsanUbsan.M.loaded_segments (0x9e518 : word) = Some W_9e518.
Proof. vm_refl. Qed.
Lemma D_9e518 : decode_any W_9e518 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e51c : bv 32 := 0x0284b503.
Lemma F_9e51c : fetch_word AsanUbsan.M.loaded_segments (0x9e51c : word) = Some W_9e51c.
Proof. vm_refl. Qed.
Lemma D_9e51c : decode_any W_9e51c = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e520 : bv 32 := 0x0384b603.
Lemma F_9e520 : fetch_word AsanUbsan.M.loaded_segments (0x9e520 : word) = Some W_9e520.
Proof. vm_refl. Qed.
Lemma D_9e520 : decode_any W_9e520 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e524 : bv 32 := 0x40c50b33.
Lemma F_9e524 : fetch_word AsanUbsan.M.loaded_segments (0x9e524 : word) = Some W_9e524.
Proof. vm_refl. Qed.
Lemma D_9e524 : decode_any W_9e524 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e528 : bv 32 := 0x00c546b3.
Lemma F_9e528 : fetch_word AsanUbsan.M.loaded_segments (0x9e528 : word) = Some W_9e528.
Proof. vm_refl. Qed.
Lemma D_9e528 : decode_any W_9e528 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e52c : bv 32 := 0x00c13423.
Lemma F_9e52c : fetch_word AsanUbsan.M.loaded_segments (0x9e52c : word) = Some W_9e52c.
Proof. vm_refl. Qed.
Lemma D_9e52c : decode_any W_9e52c = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e530 : bv 32 := 0x01613823.
Lemma F_9e530 : fetch_word AsanUbsan.M.loaded_segments (0x9e530 : word) = Some W_9e530.
Proof. vm_refl. Qed.
Lemma D_9e530 : decode_any W_9e530 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e534 : bv 32 := 0x00b13c23.
Lemma F_9e534 : fetch_word AsanUbsan.M.loaded_segments (0x9e534 : word) = Some W_9e534.
Proof. vm_refl. Qed.
Lemma D_9e534 : decode_any W_9e534 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e538 : bv 32 := 0x02813023.
Lemma F_9e538 : fetch_word AsanUbsan.M.loaded_segments (0x9e538 : word) = Some W_9e538.
Proof. vm_refl. Qed.
Lemma D_9e538 : decode_any W_9e538 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e53c : bv 32 := 0x008b0b33.
Lemma F_9e53c : fetch_word AsanUbsan.M.loaded_segments (0x9e53c : word) = Some W_9e53c.
Proof. vm_refl. Qed.
Lemma D_9e53c : decode_any W_9e53c = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e540 : bv 32 := 0x00d03933.
Lemma F_9e540 : fetch_word AsanUbsan.M.loaded_segments (0x9e540 : word) = Some W_9e540.
Proof. vm_refl. Qed.
Lemma D_9e540 : decode_any W_9e540 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e544 : bv 32 := 0x00c50663.
Lemma F_9e544 : fetch_word AsanUbsan.M.loaded_segments (0x9e544 : word) = Some W_9e544.
Proof. vm_refl. Qed.
Lemma D_9e544 : decode_any W_9e544 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e548 : bv 32 := 0x00810993.
Lemma F_9e548 : fetch_word AsanUbsan.M.loaded_segments (0x9e548 : word) = Some W_9e548.
Proof. vm_refl. Qed.
Lemma D_9e548 : decode_any W_9e548 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e54c : bv 32 := 0x0080006f.
Lemma F_9e54c : fetch_word AsanUbsan.M.loaded_segments (0x9e54c : word) = Some W_9e54c.
Proof. vm_refl. Qed.
Lemma D_9e54c : decode_any W_9e54c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e550 : bv 32 := 0x01810993.
Lemma F_9e550 : fetch_word AsanUbsan.M.loaded_segments (0x9e550 : word) = Some W_9e550.
Proof. vm_refl. Qed.
Lemma D_9e550 : decode_any W_9e550 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e554 : bv 32 := 0x0784a503.
Lemma F_9e554 : fetch_word AsanUbsan.M.loaded_segments (0x9e554 : word) = Some W_9e554.
Proof. vm_refl. Qed.
Lemma D_9e554 : decode_any W_9e554 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e558 : bv 32 := 0x00190913.
Lemma F_9e558 : fetch_word AsanUbsan.M.loaded_segments (0x9e558 : word) = Some W_9e558.
Proof. vm_refl. Qed.
Lemma D_9e558 : decode_any W_9e558 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e55c : bv 32 := 0x04200893.
Lemma F_9e55c : fetch_word AsanUbsan.M.loaded_segments (0x9e55c : word) = Some W_9e55c.
Proof. vm_refl. Qed.
Lemma D_9e55c : decode_any W_9e55c = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e560 : bv 32 := 0x00098593.
Lemma F_9e560 : fetch_word AsanUbsan.M.loaded_segments (0x9e560 : word) = Some W_9e560.
Proof. vm_refl. Qed.
Lemma D_9e560 : decode_any W_9e560 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e564 : bv 32 := 0x00090613.
Lemma F_9e564 : fetch_word AsanUbsan.M.loaded_segments (0x9e564 : word) = Some W_9e564.
Proof. vm_refl. Qed.
Lemma D_9e564 : decode_any W_9e564 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e568 : bv 32 := 0x00000073.
Lemma F_9e568 : fetch_word AsanUbsan.M.loaded_segments (0x9e568 : word) = Some W_9e568.
Proof. vm_refl. Qed.
Lemma D_9e568 : decode_any W_9e568 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9e568 : is_ecall W_9e568 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_9e56c : bv 32 := 0xd2dfa0ef.
Lemma F_9e56c : fetch_word AsanUbsan.M.loaded_segments (0x9e56c : word) = Some W_9e56c.
Proof. vm_refl. Qed.
Lemma D_9e56c : decode_any W_9e56c = Some (Jal 1 2075948, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e570 : bv 32 := 0x09651863.
Lemma F_9e570 : fetch_word AsanUbsan.M.loaded_segments (0x9e570 : word) = Some W_9e570.
Proof. vm_refl. Qed.
Lemma D_9e570 : decode_any W_9e570 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e574 : bv 32 := 0x0584b503.
Lemma F_9e574 : fetch_word AsanUbsan.M.loaded_segments (0x9e574 : word) = Some W_9e574.
Proof. vm_refl. Qed.
Lemma D_9e574 : decode_any W_9e574 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e578 : bv 32 := 0x0604b583.
Lemma F_9e578 : fetch_word AsanUbsan.M.loaded_segments (0x9e578 : word) = Some W_9e578.
Proof. vm_refl. Qed.
Lemma D_9e578 : decode_any W_9e578 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e57c : bv 32 := 0x00b505b3.
Lemma F_9e57c : fetch_word AsanUbsan.M.loaded_segments (0x9e57c : word) = Some W_9e57c.
Proof. vm_refl. Qed.
Lemma D_9e57c : decode_any W_9e57c = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e580 : bv 32 := 0x02b4b023.
Lemma F_9e580 : fetch_word AsanUbsan.M.loaded_segments (0x9e580 : word) = Some W_9e580.
Proof. vm_refl. Qed.
Lemma D_9e580 : decode_any W_9e580 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e584 : bv 32 := 0x02a4b423.
Lemma F_9e584 : fetch_word AsanUbsan.M.loaded_segments (0x9e584 : word) = Some W_9e584.
Proof. vm_refl. Qed.
Lemma D_9e584 : decode_any W_9e584 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e588 : bv 32 := 0x02a4bc23.
Lemma F_9e588 : fetch_word AsanUbsan.M.loaded_segments (0x9e588 : word) = Some W_9e588.
Proof. vm_refl. Qed.
Lemma D_9e588 : decode_any W_9e588 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e58c : bv 32 := 0x00040513.
Lemma F_9e58c : fetch_word AsanUbsan.M.loaded_segments (0x9e58c : word) = Some W_9e58c.
Proof. vm_refl. Qed.
Lemma D_9e58c : decode_any W_9e58c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e590 : bv 32 := 0x000ab583.
Lemma F_9e590 : fetch_word AsanUbsan.M.loaded_segments (0x9e590 : word) = Some W_9e590.
Proof. vm_refl. Qed.
Lemma D_9e590 : decode_any W_9e590 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e594 : bv 32 := 0x02813603.
Lemma F_9e594 : fetch_word AsanUbsan.M.loaded_segments (0x9e594 : word) = Some W_9e594.
Proof. vm_refl. Qed.
Lemma D_9e594 : decode_any W_9e594 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e598 : bv 32 := 0x0cc59a63.
Lemma F_9e598 : fetch_word AsanUbsan.M.loaded_segments (0x9e598 : word) = Some W_9e598.
Proof. vm_refl. Qed.
Lemma D_9e598 : decode_any W_9e598 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e59c : bv 32 := 0x06813083.
Lemma F_9e59c : fetch_word AsanUbsan.M.loaded_segments (0x9e59c : word) = Some W_9e59c.
Proof. vm_refl. Qed.
Lemma D_9e59c : decode_any W_9e59c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5a0 : bv 32 := 0x06013403.
Lemma F_9e5a0 : fetch_word AsanUbsan.M.loaded_segments (0x9e5a0 : word) = Some W_9e5a0.
Proof. vm_refl. Qed.
Lemma D_9e5a0 : decode_any W_9e5a0 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5a4 : bv 32 := 0x05813483.
Lemma F_9e5a4 : fetch_word AsanUbsan.M.loaded_segments (0x9e5a4 : word) = Some W_9e5a4.
Proof. vm_refl. Qed.
Lemma D_9e5a4 : decode_any W_9e5a4 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5a8 : bv 32 := 0x05013903.
Lemma F_9e5a8 : fetch_word AsanUbsan.M.loaded_segments (0x9e5a8 : word) = Some W_9e5a8.
Proof. vm_refl. Qed.
Lemma D_9e5a8 : decode_any W_9e5a8 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5ac : bv 32 := 0x04813983.
Lemma F_9e5ac : fetch_word AsanUbsan.M.loaded_segments (0x9e5ac : word) = Some W_9e5ac.
Proof. vm_refl. Qed.
Lemma D_9e5ac : decode_any W_9e5ac = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5b0 : bv 32 := 0x04013a03.
Lemma F_9e5b0 : fetch_word AsanUbsan.M.loaded_segments (0x9e5b0 : word) = Some W_9e5b0.
Proof. vm_refl. Qed.
Lemma D_9e5b0 : decode_any W_9e5b0 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5b4 : bv 32 := 0x03813a83.
Lemma F_9e5b4 : fetch_word AsanUbsan.M.loaded_segments (0x9e5b4 : word) = Some W_9e5b4.
Proof. vm_refl. Qed.
Lemma D_9e5b4 : decode_any W_9e5b4 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5b8 : bv 32 := 0x03013b03.
Lemma F_9e5b8 : fetch_word AsanUbsan.M.loaded_segments (0x9e5b8 : word) = Some W_9e5b8.
Proof. vm_refl. Qed.
Lemma D_9e5b8 : decode_any W_9e5b8 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5bc : bv 32 := 0x07010113.
Lemma F_9e5bc : fetch_word AsanUbsan.M.loaded_segments (0x9e5bc : word) = Some W_9e5bc.
Proof. vm_refl. Qed.
Lemma D_9e5bc : decode_any W_9e5bc = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5c0 : bv 32 := 0x00008067.
Lemma F_9e5c0 : fetch_word AsanUbsan.M.loaded_segments (0x9e5c0 : word) = Some W_9e5c0.
Proof. vm_refl. Qed.
Lemma D_9e5c0 : decode_any W_9e5c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5c4 : bv 32 := 0x00800713.
Lemma F_9e5c4 : fetch_word AsanUbsan.M.loaded_segments (0x9e5c4 : word) = Some W_9e5c4.
Proof. vm_refl. Qed.
Lemma D_9e5c4 : decode_any W_9e5c4 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5c8 : bv 32 := 0x000a0593.
Lemma F_9e5c8 : fetch_word AsanUbsan.M.loaded_segments (0x9e5c8 : word) = Some W_9e5c8.
Proof. vm_refl. Qed.
Lemma D_9e5c8 : decode_any W_9e5c8 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5cc : bv 32 := 0x00e98733.
Lemma F_9e5cc : fetch_word AsanUbsan.M.loaded_segments (0x9e5cc : word) = Some W_9e5cc.
Proof. vm_refl. Qed.
Lemma D_9e5cc : decode_any W_9e5cc = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5d0 : bv 32 := 0x00073783.
Lemma F_9e5d0 : fetch_word AsanUbsan.M.loaded_segments (0x9e5d0 : word) = Some W_9e5d0.
Proof. vm_refl. Qed.
Lemma D_9e5d0 : decode_any W_9e5d0 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5d4 : bv 32 := 0x40ab0b33.
Lemma F_9e5d4 : fetch_word AsanUbsan.M.loaded_segments (0x9e5d4 : word) = Some W_9e5d4.
Proof. vm_refl. Qed.
Lemma D_9e5d4 : decode_any W_9e5d4 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5d8 : bv 32 := 0x0784a503.
Lemma F_9e5d8 : fetch_word AsanUbsan.M.loaded_segments (0x9e5d8 : word) = Some W_9e5d8.
Proof. vm_refl. Qed.
Lemma D_9e5d8 : decode_any W_9e5d8 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5dc : bv 32 := 0x40c9093b.
Lemma F_9e5dc : fetch_word AsanUbsan.M.loaded_segments (0x9e5dc : word) = Some W_9e5dc.
Proof. vm_refl. Qed.
Lemma D_9e5dc : decode_any W_9e5dc = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5e0 : bv 32 := 0x40d787b3.
Lemma F_9e5e0 : fetch_word AsanUbsan.M.loaded_segments (0x9e5e0 : word) = Some W_9e5e0.
Proof. vm_refl. Qed.
Lemma D_9e5e0 : decode_any W_9e5e0 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5e4 : bv 32 := 0x00f73023.
Lemma F_9e5e4 : fetch_word AsanUbsan.M.loaded_segments (0x9e5e4 : word) = Some W_9e5e4.
Proof. vm_refl. Qed.
Lemma D_9e5e4 : decode_any W_9e5e4 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5e8 : bv 32 := 0x04200893.
Lemma F_9e5e8 : fetch_word AsanUbsan.M.loaded_segments (0x9e5e8 : word) = Some W_9e5e8.
Proof. vm_refl. Qed.
Lemma D_9e5e8 : decode_any W_9e5e8 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5ec : bv 32 := 0x00090613.
Lemma F_9e5ec : fetch_word AsanUbsan.M.loaded_segments (0x9e5ec : word) = Some W_9e5ec.
Proof. vm_refl. Qed.
Lemma D_9e5ec : decode_any W_9e5ec = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5f0 : bv 32 := 0x00000073.
Lemma F_9e5f0 : fetch_word AsanUbsan.M.loaded_segments (0x9e5f0 : word) = Some W_9e5f0.
Proof. vm_refl. Qed.
Lemma D_9e5f0 : decode_any W_9e5f0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9e5f0 : is_ecall W_9e5f0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_9e5f4 : bv 32 := 0xca5fa0ef.
Lemma F_9e5f4 : fetch_word AsanUbsan.M.loaded_segments (0x9e5f4 : word) = Some W_9e5f4.
Proof. vm_refl. Qed.
Lemma D_9e5f4 : decode_any W_9e5f4 = Some (Jal 1 2075812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5f8 : bv 32 := 0x000a0993.
Lemma F_9e5f8 : fetch_word AsanUbsan.M.loaded_segments (0x9e5f8 : word) = Some W_9e5f8.
Proof. vm_refl. Qed.
Lemma D_9e5f8 : decode_any W_9e5f8 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e5fc : bv 32 := 0xf7650ce3.
Lemma F_9e5fc : fetch_word AsanUbsan.M.loaded_segments (0x9e5fc : word) = Some W_9e5fc.
Proof. vm_refl. Qed.
Lemma D_9e5fc : decode_any W_9e5fc = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e600 : bv 32 := 0x02054c63.
Lemma F_9e600 : fetch_word AsanUbsan.M.loaded_segments (0x9e600 : word) = Some W_9e600.
Proof. vm_refl. Qed.
Lemma D_9e600 : decode_any W_9e600 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e604 : bv 32 := 0x0089b583.
Lemma F_9e604 : fetch_word AsanUbsan.M.loaded_segments (0x9e604 : word) = Some W_9e604.
Proof. vm_refl. Qed.
Lemma D_9e604 : decode_any W_9e604 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e608 : bv 32 := 0x00a5b633.
Lemma F_9e608 : fetch_word AsanUbsan.M.loaded_segments (0x9e608 : word) = Some W_9e608.
Proof. vm_refl. Qed.
Lemma D_9e608 : decode_any W_9e608 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e60c : bv 32 := 0x00461a13.
Lemma F_9e60c : fetch_word AsanUbsan.M.loaded_segments (0x9e60c : word) = Some W_9e60c.
Proof. vm_refl. Qed.
Lemma D_9e60c : decode_any W_9e60c = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e610 : bv 32 := 0x01498a33.
Lemma F_9e610 : fetch_word AsanUbsan.M.loaded_segments (0x9e610 : word) = Some W_9e610.
Proof. vm_refl. Qed.
Lemma D_9e610 : decode_any W_9e610 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e614 : bv 32 := 0x000a3703.
Lemma F_9e614 : fetch_word AsanUbsan.M.loaded_segments (0x9e614 : word) = Some W_9e614.
Proof. vm_refl. Qed.
Lemma D_9e614 : decode_any W_9e614 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e618 : bv 32 := 0x40c006b3.
Lemma F_9e618 : fetch_word AsanUbsan.M.loaded_segments (0x9e618 : word) = Some W_9e618.
Proof. vm_refl. Qed.
Lemma D_9e618 : decode_any W_9e618 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e61c : bv 32 := 0x00b6f6b3.
Lemma F_9e61c : fetch_word AsanUbsan.M.loaded_segments (0x9e61c : word) = Some W_9e61c.
Proof. vm_refl. Qed.
Lemma D_9e61c : decode_any W_9e61c = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e620 : bv 32 := 0x40d506b3.
Lemma F_9e620 : fetch_word AsanUbsan.M.loaded_segments (0x9e620 : word) = Some W_9e620.
Proof. vm_refl. Qed.
Lemma D_9e620 : decode_any W_9e620 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e624 : bv 32 := 0x00d70733.
Lemma F_9e624 : fetch_word AsanUbsan.M.loaded_segments (0x9e624 : word) = Some W_9e624.
Proof. vm_refl. Qed.
Lemma D_9e624 : decode_any W_9e624 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e628 : bv 32 := 0x00ea3023.
Lemma F_9e628 : fetch_word AsanUbsan.M.loaded_segments (0x9e628 : word) = Some W_9e628.
Proof. vm_refl. Qed.
Lemma D_9e628 : decode_any W_9e628 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e62c : bv 32 := 0xf8a5fce3.
Lemma F_9e62c : fetch_word AsanUbsan.M.loaded_segments (0x9e62c : word) = Some W_9e62c.
Proof. vm_refl. Qed.
Lemma D_9e62c : decode_any W_9e62c = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e630 : bv 32 := 0x01800713.
Lemma F_9e630 : fetch_word AsanUbsan.M.loaded_segments (0x9e630 : word) = Some W_9e630.
Proof. vm_refl. Qed.
Lemma D_9e630 : decode_any W_9e630 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e634 : bv 32 := 0xf95ff06f.
Lemma F_9e634 : fetch_word AsanUbsan.M.loaded_segments (0x9e634 : word) = Some W_9e634.
Proof. vm_refl. Qed.
Lemma D_9e634 : decode_any W_9e634 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e638 : bv 32 := 0x00000513.
Lemma F_9e638 : fetch_word AsanUbsan.M.loaded_segments (0x9e638 : word) = Some W_9e638.
Proof. vm_refl. Qed.
Lemma D_9e638 : decode_any W_9e638 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e63c : bv 32 := 0x0004a583.
Lemma F_9e63c : fetch_word AsanUbsan.M.loaded_segments (0x9e63c : word) = Some W_9e63c.
Proof. vm_refl. Qed.
Lemma D_9e63c : decode_any W_9e63c = Some (Load SZ4 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e640 : bv 32 := 0x0009091b.
Lemma F_9e640 : fetch_word AsanUbsan.M.loaded_segments (0x9e640 : word) = Some W_9e640.
Proof. vm_refl. Qed.
Lemma D_9e640 : decode_any W_9e640 = Some (OpImm32 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e644 : bv 32 := 0x00200613.
Lemma F_9e644 : fetch_word AsanUbsan.M.loaded_segments (0x9e644 : word) = Some W_9e644.
Proof. vm_refl. Qed.
Lemma D_9e644 : decode_any W_9e644 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e648 : bv 32 := 0x0205e593.
Lemma F_9e648 : fetch_word AsanUbsan.M.loaded_segments (0x9e648 : word) = Some W_9e648.
Proof. vm_refl. Qed.
Lemma D_9e648 : decode_any W_9e648 = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e64c : bv 32 := 0x00b4a023.
Lemma F_9e64c : fetch_word AsanUbsan.M.loaded_segments (0x9e64c : word) = Some W_9e64c.
Proof. vm_refl. Qed.
Lemma D_9e64c : decode_any W_9e64c = Some (Store SZ4 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e650 : bv 32 := 0x0204b023.
Lemma F_9e650 : fetch_word AsanUbsan.M.loaded_segments (0x9e650 : word) = Some W_9e650.
Proof. vm_refl. Qed.
Lemma D_9e650 : decode_any W_9e650 = Some (Store SZ8 9 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e654 : bv 32 := 0x0204b423.
Lemma F_9e654 : fetch_word AsanUbsan.M.loaded_segments (0x9e654 : word) = Some W_9e654.
Proof. vm_refl. Qed.
Lemma D_9e654 : decode_any W_9e654 = Some (Store SZ8 9 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e658 : bv 32 := 0x0204bc23.
Lemma F_9e658 : fetch_word AsanUbsan.M.loaded_segments (0x9e658 : word) = Some W_9e658.
Proof. vm_refl. Qed.
Lemma D_9e658 : decode_any W_9e658 = Some (Store SZ8 9 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e65c : bv 32 := 0xf2c90ae3.
Lemma F_9e65c : fetch_word AsanUbsan.M.loaded_segments (0x9e65c : word) = Some W_9e65c.
Proof. vm_refl. Qed.
Lemma D_9e65c : decode_any W_9e65c = Some (Branch BC_EQ 18 12 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e660 : bv 32 := 0x0089b503.
Lemma F_9e660 : fetch_word AsanUbsan.M.loaded_segments (0x9e660 : word) = Some W_9e660.
Proof. vm_refl. Qed.
Lemma D_9e660 : decode_any W_9e660 = Some (Load SZ8 true 10 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e664 : bv 32 := 0x40a40533.
Lemma F_9e664 : fetch_word AsanUbsan.M.loaded_segments (0x9e664 : word) = Some W_9e664.
Proof. vm_refl. Qed.
Lemma D_9e664 : decode_any W_9e664 = Some (Op ALU_SUB 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e668 : bv 32 := 0xf29ff06f.
Lemma F_9e668 : fetch_word AsanUbsan.M.loaded_segments (0x9e668 : word) = Some W_9e668.
Proof. vm_refl. Qed.
Lemma D_9e668 : decode_any W_9e668 = Some (Jal 0 2096936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9e66c : bv 32 := 0xdc0fa0ef.
Lemma F_9e66c : fetch_word AsanUbsan.M.loaded_segments (0x9e66c : word) = Some W_9e66c.
Proof. vm_refl. Qed.
Lemma D_9e66c : decode_any W_9e66c = Some (Jal 1 2074048, 4%Z).
Proof. vm_refl. Qed.
