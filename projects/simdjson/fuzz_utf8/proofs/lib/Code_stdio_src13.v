(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_b84a0 : bv 32 := 0xf9010113.
Lemma F_b84a0 : fetch_word Plain.M.loaded_segments (0xb8658 : word) = Some W_b84a0.
Proof. vm_refl. Qed.
Lemma D_b84a0 : decode_any W_b84a0 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84a4 : bv 32 := 0x06113423.
Lemma F_b84a4 : fetch_word Plain.M.loaded_segments (0xb865c : word) = Some W_b84a4.
Proof. vm_refl. Qed.
Lemma D_b84a4 : decode_any W_b84a4 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84a8 : bv 32 := 0x06813023.
Lemma F_b84a8 : fetch_word Plain.M.loaded_segments (0xb8660 : word) = Some W_b84a8.
Proof. vm_refl. Qed.
Lemma D_b84a8 : decode_any W_b84a8 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84ac : bv 32 := 0x04913c23.
Lemma F_b84ac : fetch_word Plain.M.loaded_segments (0xb8664 : word) = Some W_b84ac.
Proof. vm_refl. Qed.
Lemma D_b84ac : decode_any W_b84ac = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84b0 : bv 32 := 0x05213823.
Lemma F_b84b0 : fetch_word Plain.M.loaded_segments (0xb8668 : word) = Some W_b84b0.
Proof. vm_refl. Qed.
Lemma D_b84b0 : decode_any W_b84b0 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84b4 : bv 32 := 0x05313423.
Lemma F_b84b4 : fetch_word Plain.M.loaded_segments (0xb866c : word) = Some W_b84b4.
Proof. vm_refl. Qed.
Lemma D_b84b4 : decode_any W_b84b4 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84b8 : bv 32 := 0x05413023.
Lemma F_b84b8 : fetch_word Plain.M.loaded_segments (0xb8670 : word) = Some W_b84b8.
Proof. vm_refl. Qed.
Lemma D_b84b8 : decode_any W_b84b8 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84bc : bv 32 := 0x03513c23.
Lemma F_b84bc : fetch_word Plain.M.loaded_segments (0xb8674 : word) = Some W_b84bc.
Proof. vm_refl. Qed.
Lemma D_b84bc : decode_any W_b84bc = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84c0 : bv 32 := 0x03613823.
Lemma F_b84c0 : fetch_word Plain.M.loaded_segments (0xb8678 : word) = Some W_b84c0.
Proof. vm_refl. Qed.
Lemma D_b84c0 : decode_any W_b84c0 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84c4 : bv 32 := 0x00060413.
Lemma F_b84c4 : fetch_word Plain.M.loaded_segments (0xb867c : word) = Some W_b84c4.
Proof. vm_refl. Qed.
Lemma D_b84c4 : decode_any W_b84c4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84c8 : bv 32 := 0x00050493.
Lemma F_b84c8 : fetch_word Plain.M.loaded_segments (0xb8680 : word) = Some W_b84c8.
Proof. vm_refl. Qed.
Lemma D_b84c8 : decode_any W_b84c8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84cc : bv 32 := 0x00018517.
Lemma F_b84cc : fetch_word Plain.M.loaded_segments (0xb8684 : word) = Some W_b84cc.
Proof. vm_refl. Qed.
Lemma D_b84cc : decode_any W_b84cc = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84d0 : bv 32 := 0x83453a83.
Lemma F_b84d0 : fetch_word Plain.M.loaded_segments (0xb8688 : word) = Some W_b84d0.
Proof. vm_refl. Qed.
Lemma D_b84d0 : decode_any W_b84d0 = Some (Load SZ8 true 21 10 2100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84d4 : bv 32 := 0x000ab503.
Lemma F_b84d4 : fetch_word Plain.M.loaded_segments (0xb868c : word) = Some W_b84d4.
Proof. vm_refl. Qed.
Lemma D_b84d4 : decode_any W_b84d4 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84d8 : bv 32 := 0x02a13423.
Lemma F_b84d8 : fetch_word Plain.M.loaded_segments (0xb8690 : word) = Some W_b84d8.
Proof. vm_refl. Qed.
Lemma D_b84d8 : decode_any W_b84d8 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84dc : bv 32 := 0x0284b503.
Lemma F_b84dc : fetch_word Plain.M.loaded_segments (0xb8694 : word) = Some W_b84dc.
Proof. vm_refl. Qed.
Lemma D_b84dc : decode_any W_b84dc = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84e0 : bv 32 := 0x0384b603.
Lemma F_b84e0 : fetch_word Plain.M.loaded_segments (0xb8698 : word) = Some W_b84e0.
Proof. vm_refl. Qed.
Lemma D_b84e0 : decode_any W_b84e0 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84e4 : bv 32 := 0x40c50b33.
Lemma F_b84e4 : fetch_word Plain.M.loaded_segments (0xb869c : word) = Some W_b84e4.
Proof. vm_refl. Qed.
Lemma D_b84e4 : decode_any W_b84e4 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84e8 : bv 32 := 0x00c546b3.
Lemma F_b84e8 : fetch_word Plain.M.loaded_segments (0xb86a0 : word) = Some W_b84e8.
Proof. vm_refl. Qed.
Lemma D_b84e8 : decode_any W_b84e8 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84ec : bv 32 := 0x00c13423.
Lemma F_b84ec : fetch_word Plain.M.loaded_segments (0xb86a4 : word) = Some W_b84ec.
Proof. vm_refl. Qed.
Lemma D_b84ec : decode_any W_b84ec = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84f0 : bv 32 := 0x01613823.
Lemma F_b84f0 : fetch_word Plain.M.loaded_segments (0xb86a8 : word) = Some W_b84f0.
Proof. vm_refl. Qed.
Lemma D_b84f0 : decode_any W_b84f0 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84f4 : bv 32 := 0x00b13c23.
Lemma F_b84f4 : fetch_word Plain.M.loaded_segments (0xb86ac : word) = Some W_b84f4.
Proof. vm_refl. Qed.
Lemma D_b84f4 : decode_any W_b84f4 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84f8 : bv 32 := 0x02813023.
Lemma F_b84f8 : fetch_word Plain.M.loaded_segments (0xb86b0 : word) = Some W_b84f8.
Proof. vm_refl. Qed.
Lemma D_b84f8 : decode_any W_b84f8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b84fc : bv 32 := 0x008b0b33.
Lemma F_b84fc : fetch_word Plain.M.loaded_segments (0xb86b4 : word) = Some W_b84fc.
Proof. vm_refl. Qed.
Lemma D_b84fc : decode_any W_b84fc = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8500 : bv 32 := 0x00d03933.
Lemma F_b8500 : fetch_word Plain.M.loaded_segments (0xb86b8 : word) = Some W_b8500.
Proof. vm_refl. Qed.
Lemma D_b8500 : decode_any W_b8500 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8504 : bv 32 := 0x00c50663.
Lemma F_b8504 : fetch_word Plain.M.loaded_segments (0xb86bc : word) = Some W_b8504.
Proof. vm_refl. Qed.
Lemma D_b8504 : decode_any W_b8504 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8508 : bv 32 := 0x00810993.
Lemma F_b8508 : fetch_word Plain.M.loaded_segments (0xb86c0 : word) = Some W_b8508.
Proof. vm_refl. Qed.
Lemma D_b8508 : decode_any W_b8508 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b850c : bv 32 := 0x0080006f.
Lemma F_b850c : fetch_word Plain.M.loaded_segments (0xb86c4 : word) = Some W_b850c.
Proof. vm_refl. Qed.
Lemma D_b850c : decode_any W_b850c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8510 : bv 32 := 0x01810993.
Lemma F_b8510 : fetch_word Plain.M.loaded_segments (0xb86c8 : word) = Some W_b8510.
Proof. vm_refl. Qed.
Lemma D_b8510 : decode_any W_b8510 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8514 : bv 32 := 0x0784a503.
Lemma F_b8514 : fetch_word Plain.M.loaded_segments (0xb86cc : word) = Some W_b8514.
Proof. vm_refl. Qed.
Lemma D_b8514 : decode_any W_b8514 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8518 : bv 32 := 0x00190913.
Lemma F_b8518 : fetch_word Plain.M.loaded_segments (0xb86d0 : word) = Some W_b8518.
Proof. vm_refl. Qed.
Lemma D_b8518 : decode_any W_b8518 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b851c : bv 32 := 0x04200893.
Lemma F_b851c : fetch_word Plain.M.loaded_segments (0xb86d4 : word) = Some W_b851c.
Proof. vm_refl. Qed.
Lemma D_b851c : decode_any W_b851c = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8520 : bv 32 := 0x00098593.
Lemma F_b8520 : fetch_word Plain.M.loaded_segments (0xb86d8 : word) = Some W_b8520.
Proof. vm_refl. Qed.
Lemma D_b8520 : decode_any W_b8520 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8524 : bv 32 := 0x00090613.
Lemma F_b8524 : fetch_word Plain.M.loaded_segments (0xb86dc : word) = Some W_b8524.
Proof. vm_refl. Qed.
Lemma D_b8524 : decode_any W_b8524 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8528 : bv 32 := 0x00000073.
Lemma F_b8528 : fetch_word Plain.M.loaded_segments (0xb86e0 : word) = Some W_b8528.
Proof. vm_refl. Qed.
Lemma D_b8528 : decode_any W_b8528 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_b8528 : is_ecall W_b8528 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_b852c : bv 32 := 0xeb5fa0ef.
Lemma F_b852c : fetch_word Plain.M.loaded_segments (0xb86e4 : word) = Some W_b852c.
Proof. vm_refl. Qed.
Lemma D_b852c : decode_any W_b852c = Some (Jal 1 2076340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8530 : bv 32 := 0x09651863.
Lemma F_b8530 : fetch_word Plain.M.loaded_segments (0xb86e8 : word) = Some W_b8530.
Proof. vm_refl. Qed.
Lemma D_b8530 : decode_any W_b8530 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8534 : bv 32 := 0x0584b503.
Lemma F_b8534 : fetch_word Plain.M.loaded_segments (0xb86ec : word) = Some W_b8534.
Proof. vm_refl. Qed.
Lemma D_b8534 : decode_any W_b8534 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8538 : bv 32 := 0x0604b583.
Lemma F_b8538 : fetch_word Plain.M.loaded_segments (0xb86f0 : word) = Some W_b8538.
Proof. vm_refl. Qed.
Lemma D_b8538 : decode_any W_b8538 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b853c : bv 32 := 0x00b505b3.
Lemma F_b853c : fetch_word Plain.M.loaded_segments (0xb86f4 : word) = Some W_b853c.
Proof. vm_refl. Qed.
Lemma D_b853c : decode_any W_b853c = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8540 : bv 32 := 0x02b4b023.
Lemma F_b8540 : fetch_word Plain.M.loaded_segments (0xb86f8 : word) = Some W_b8540.
Proof. vm_refl. Qed.
Lemma D_b8540 : decode_any W_b8540 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8544 : bv 32 := 0x02a4b423.
Lemma F_b8544 : fetch_word Plain.M.loaded_segments (0xb86fc : word) = Some W_b8544.
Proof. vm_refl. Qed.
Lemma D_b8544 : decode_any W_b8544 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8548 : bv 32 := 0x02a4bc23.
Lemma F_b8548 : fetch_word Plain.M.loaded_segments (0xb8700 : word) = Some W_b8548.
Proof. vm_refl. Qed.
Lemma D_b8548 : decode_any W_b8548 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b854c : bv 32 := 0x00040513.
Lemma F_b854c : fetch_word Plain.M.loaded_segments (0xb8704 : word) = Some W_b854c.
Proof. vm_refl. Qed.
Lemma D_b854c : decode_any W_b854c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8550 : bv 32 := 0x000ab583.
Lemma F_b8550 : fetch_word Plain.M.loaded_segments (0xb8708 : word) = Some W_b8550.
Proof. vm_refl. Qed.
Lemma D_b8550 : decode_any W_b8550 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8554 : bv 32 := 0x02813603.
Lemma F_b8554 : fetch_word Plain.M.loaded_segments (0xb870c : word) = Some W_b8554.
Proof. vm_refl. Qed.
Lemma D_b8554 : decode_any W_b8554 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8558 : bv 32 := 0x0cc59a63.
Lemma F_b8558 : fetch_word Plain.M.loaded_segments (0xb8710 : word) = Some W_b8558.
Proof. vm_refl. Qed.
Lemma D_b8558 : decode_any W_b8558 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b855c : bv 32 := 0x06813083.
Lemma F_b855c : fetch_word Plain.M.loaded_segments (0xb8714 : word) = Some W_b855c.
Proof. vm_refl. Qed.
Lemma D_b855c : decode_any W_b855c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8560 : bv 32 := 0x06013403.
Lemma F_b8560 : fetch_word Plain.M.loaded_segments (0xb8718 : word) = Some W_b8560.
Proof. vm_refl. Qed.
Lemma D_b8560 : decode_any W_b8560 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8564 : bv 32 := 0x05813483.
Lemma F_b8564 : fetch_word Plain.M.loaded_segments (0xb871c : word) = Some W_b8564.
Proof. vm_refl. Qed.
Lemma D_b8564 : decode_any W_b8564 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8568 : bv 32 := 0x05013903.
Lemma F_b8568 : fetch_word Plain.M.loaded_segments (0xb8720 : word) = Some W_b8568.
Proof. vm_refl. Qed.
Lemma D_b8568 : decode_any W_b8568 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b856c : bv 32 := 0x04813983.
Lemma F_b856c : fetch_word Plain.M.loaded_segments (0xb8724 : word) = Some W_b856c.
Proof. vm_refl. Qed.
Lemma D_b856c : decode_any W_b856c = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8570 : bv 32 := 0x04013a03.
Lemma F_b8570 : fetch_word Plain.M.loaded_segments (0xb8728 : word) = Some W_b8570.
Proof. vm_refl. Qed.
Lemma D_b8570 : decode_any W_b8570 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8574 : bv 32 := 0x03813a83.
Lemma F_b8574 : fetch_word Plain.M.loaded_segments (0xb872c : word) = Some W_b8574.
Proof. vm_refl. Qed.
Lemma D_b8574 : decode_any W_b8574 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8578 : bv 32 := 0x03013b03.
Lemma F_b8578 : fetch_word Plain.M.loaded_segments (0xb8730 : word) = Some W_b8578.
Proof. vm_refl. Qed.
Lemma D_b8578 : decode_any W_b8578 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b857c : bv 32 := 0x07010113.
Lemma F_b857c : fetch_word Plain.M.loaded_segments (0xb8734 : word) = Some W_b857c.
Proof. vm_refl. Qed.
Lemma D_b857c : decode_any W_b857c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8580 : bv 32 := 0x00008067.
Lemma F_b8580 : fetch_word Plain.M.loaded_segments (0xb8738 : word) = Some W_b8580.
Proof. vm_refl. Qed.
Lemma D_b8580 : decode_any W_b8580 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8584 : bv 32 := 0x00800713.
Lemma F_b8584 : fetch_word Plain.M.loaded_segments (0xb873c : word) = Some W_b8584.
Proof. vm_refl. Qed.
Lemma D_b8584 : decode_any W_b8584 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8588 : bv 32 := 0x000a0593.
Lemma F_b8588 : fetch_word Plain.M.loaded_segments (0xb8740 : word) = Some W_b8588.
Proof. vm_refl. Qed.
Lemma D_b8588 : decode_any W_b8588 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b858c : bv 32 := 0x00e98733.
Lemma F_b858c : fetch_word Plain.M.loaded_segments (0xb8744 : word) = Some W_b858c.
Proof. vm_refl. Qed.
Lemma D_b858c : decode_any W_b858c = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8590 : bv 32 := 0x00073783.
Lemma F_b8590 : fetch_word Plain.M.loaded_segments (0xb8748 : word) = Some W_b8590.
Proof. vm_refl. Qed.
Lemma D_b8590 : decode_any W_b8590 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8594 : bv 32 := 0x40ab0b33.
Lemma F_b8594 : fetch_word Plain.M.loaded_segments (0xb874c : word) = Some W_b8594.
Proof. vm_refl. Qed.
Lemma D_b8594 : decode_any W_b8594 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8598 : bv 32 := 0x0784a503.
Lemma F_b8598 : fetch_word Plain.M.loaded_segments (0xb8750 : word) = Some W_b8598.
Proof. vm_refl. Qed.
Lemma D_b8598 : decode_any W_b8598 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b859c : bv 32 := 0x40c9093b.
Lemma F_b859c : fetch_word Plain.M.loaded_segments (0xb8754 : word) = Some W_b859c.
Proof. vm_refl. Qed.
Lemma D_b859c : decode_any W_b859c = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85a0 : bv 32 := 0x40d787b3.
Lemma F_b85a0 : fetch_word Plain.M.loaded_segments (0xb8758 : word) = Some W_b85a0.
Proof. vm_refl. Qed.
Lemma D_b85a0 : decode_any W_b85a0 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85a4 : bv 32 := 0x00f73023.
Lemma F_b85a4 : fetch_word Plain.M.loaded_segments (0xb875c : word) = Some W_b85a4.
Proof. vm_refl. Qed.
Lemma D_b85a4 : decode_any W_b85a4 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85a8 : bv 32 := 0x04200893.
Lemma F_b85a8 : fetch_word Plain.M.loaded_segments (0xb8760 : word) = Some W_b85a8.
Proof. vm_refl. Qed.
Lemma D_b85a8 : decode_any W_b85a8 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85ac : bv 32 := 0x00090613.
Lemma F_b85ac : fetch_word Plain.M.loaded_segments (0xb8764 : word) = Some W_b85ac.
Proof. vm_refl. Qed.
Lemma D_b85ac : decode_any W_b85ac = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85b0 : bv 32 := 0x00000073.
Lemma F_b85b0 : fetch_word Plain.M.loaded_segments (0xb8768 : word) = Some W_b85b0.
Proof. vm_refl. Qed.
Lemma D_b85b0 : decode_any W_b85b0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_b85b0 : is_ecall W_b85b0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_b85b4 : bv 32 := 0xe2dfa0ef.
Lemma F_b85b4 : fetch_word Plain.M.loaded_segments (0xb876c : word) = Some W_b85b4.
Proof. vm_refl. Qed.
Lemma D_b85b4 : decode_any W_b85b4 = Some (Jal 1 2076204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85b8 : bv 32 := 0x000a0993.
Lemma F_b85b8 : fetch_word Plain.M.loaded_segments (0xb8770 : word) = Some W_b85b8.
Proof. vm_refl. Qed.
Lemma D_b85b8 : decode_any W_b85b8 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85bc : bv 32 := 0xf7650ce3.
Lemma F_b85bc : fetch_word Plain.M.loaded_segments (0xb8774 : word) = Some W_b85bc.
Proof. vm_refl. Qed.
Lemma D_b85bc : decode_any W_b85bc = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85c0 : bv 32 := 0x02054c63.
Lemma F_b85c0 : fetch_word Plain.M.loaded_segments (0xb8778 : word) = Some W_b85c0.
Proof. vm_refl. Qed.
Lemma D_b85c0 : decode_any W_b85c0 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85c4 : bv 32 := 0x0089b583.
Lemma F_b85c4 : fetch_word Plain.M.loaded_segments (0xb877c : word) = Some W_b85c4.
Proof. vm_refl. Qed.
Lemma D_b85c4 : decode_any W_b85c4 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85c8 : bv 32 := 0x00a5b633.
Lemma F_b85c8 : fetch_word Plain.M.loaded_segments (0xb8780 : word) = Some W_b85c8.
Proof. vm_refl. Qed.
Lemma D_b85c8 : decode_any W_b85c8 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85cc : bv 32 := 0x00461a13.
Lemma F_b85cc : fetch_word Plain.M.loaded_segments (0xb8784 : word) = Some W_b85cc.
Proof. vm_refl. Qed.
Lemma D_b85cc : decode_any W_b85cc = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85d0 : bv 32 := 0x01498a33.
Lemma F_b85d0 : fetch_word Plain.M.loaded_segments (0xb8788 : word) = Some W_b85d0.
Proof. vm_refl. Qed.
Lemma D_b85d0 : decode_any W_b85d0 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85d4 : bv 32 := 0x000a3703.
Lemma F_b85d4 : fetch_word Plain.M.loaded_segments (0xb878c : word) = Some W_b85d4.
Proof. vm_refl. Qed.
Lemma D_b85d4 : decode_any W_b85d4 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85d8 : bv 32 := 0x40c006b3.
Lemma F_b85d8 : fetch_word Plain.M.loaded_segments (0xb8790 : word) = Some W_b85d8.
Proof. vm_refl. Qed.
Lemma D_b85d8 : decode_any W_b85d8 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85dc : bv 32 := 0x00b6f6b3.
Lemma F_b85dc : fetch_word Plain.M.loaded_segments (0xb8794 : word) = Some W_b85dc.
Proof. vm_refl. Qed.
Lemma D_b85dc : decode_any W_b85dc = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85e0 : bv 32 := 0x40d506b3.
Lemma F_b85e0 : fetch_word Plain.M.loaded_segments (0xb8798 : word) = Some W_b85e0.
Proof. vm_refl. Qed.
Lemma D_b85e0 : decode_any W_b85e0 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85e4 : bv 32 := 0x00d70733.
Lemma F_b85e4 : fetch_word Plain.M.loaded_segments (0xb879c : word) = Some W_b85e4.
Proof. vm_refl. Qed.
Lemma D_b85e4 : decode_any W_b85e4 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85e8 : bv 32 := 0x00ea3023.
Lemma F_b85e8 : fetch_word Plain.M.loaded_segments (0xb87a0 : word) = Some W_b85e8.
Proof. vm_refl. Qed.
Lemma D_b85e8 : decode_any W_b85e8 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85ec : bv 32 := 0xf8a5fce3.
Lemma F_b85ec : fetch_word Plain.M.loaded_segments (0xb87a4 : word) = Some W_b85ec.
Proof. vm_refl. Qed.
Lemma D_b85ec : decode_any W_b85ec = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85f0 : bv 32 := 0x01800713.
Lemma F_b85f0 : fetch_word Plain.M.loaded_segments (0xb87a8 : word) = Some W_b85f0.
Proof. vm_refl. Qed.
Lemma D_b85f0 : decode_any W_b85f0 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85f4 : bv 32 := 0xf95ff06f.
Lemma F_b85f4 : fetch_word Plain.M.loaded_segments (0xb87ac : word) = Some W_b85f4.
Proof. vm_refl. Qed.
Lemma D_b85f4 : decode_any W_b85f4 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85f8 : bv 32 := 0x00000513.
Lemma F_b85f8 : fetch_word Plain.M.loaded_segments (0xb87b0 : word) = Some W_b85f8.
Proof. vm_refl. Qed.
Lemma D_b85f8 : decode_any W_b85f8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b85fc : bv 32 := 0x0004a583.
Lemma F_b85fc : fetch_word Plain.M.loaded_segments (0xb87b4 : word) = Some W_b85fc.
Proof. vm_refl. Qed.
Lemma D_b85fc : decode_any W_b85fc = Some (Load SZ4 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8600 : bv 32 := 0x0009091b.
Lemma F_b8600 : fetch_word Plain.M.loaded_segments (0xb87b8 : word) = Some W_b8600.
Proof. vm_refl. Qed.
Lemma D_b8600 : decode_any W_b8600 = Some (OpImm32 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8604 : bv 32 := 0x00200613.
Lemma F_b8604 : fetch_word Plain.M.loaded_segments (0xb87bc : word) = Some W_b8604.
Proof. vm_refl. Qed.
Lemma D_b8604 : decode_any W_b8604 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8608 : bv 32 := 0x0205e593.
Lemma F_b8608 : fetch_word Plain.M.loaded_segments (0xb87c0 : word) = Some W_b8608.
Proof. vm_refl. Qed.
Lemma D_b8608 : decode_any W_b8608 = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b860c : bv 32 := 0x00b4a023.
Lemma F_b860c : fetch_word Plain.M.loaded_segments (0xb87c4 : word) = Some W_b860c.
Proof. vm_refl. Qed.
Lemma D_b860c : decode_any W_b860c = Some (Store SZ4 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8610 : bv 32 := 0x0204b023.
Lemma F_b8610 : fetch_word Plain.M.loaded_segments (0xb87c8 : word) = Some W_b8610.
Proof. vm_refl. Qed.
Lemma D_b8610 : decode_any W_b8610 = Some (Store SZ8 9 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8614 : bv 32 := 0x0204b423.
Lemma F_b8614 : fetch_word Plain.M.loaded_segments (0xb87cc : word) = Some W_b8614.
Proof. vm_refl. Qed.
Lemma D_b8614 : decode_any W_b8614 = Some (Store SZ8 9 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8618 : bv 32 := 0x0204bc23.
Lemma F_b8618 : fetch_word Plain.M.loaded_segments (0xb87d0 : word) = Some W_b8618.
Proof. vm_refl. Qed.
Lemma D_b8618 : decode_any W_b8618 = Some (Store SZ8 9 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b861c : bv 32 := 0xf2c90ae3.
Lemma F_b861c : fetch_word Plain.M.loaded_segments (0xb87d4 : word) = Some W_b861c.
Proof. vm_refl. Qed.
Lemma D_b861c : decode_any W_b861c = Some (Branch BC_EQ 18 12 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8620 : bv 32 := 0x0089b503.
Lemma F_b8620 : fetch_word Plain.M.loaded_segments (0xb87d8 : word) = Some W_b8620.
Proof. vm_refl. Qed.
Lemma D_b8620 : decode_any W_b8620 = Some (Load SZ8 true 10 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8624 : bv 32 := 0x40a40533.
Lemma F_b8624 : fetch_word Plain.M.loaded_segments (0xb87dc : word) = Some W_b8624.
Proof. vm_refl. Qed.
Lemma D_b8624 : decode_any W_b8624 = Some (Op ALU_SUB 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b8628 : bv 32 := 0xf29ff06f.
Lemma F_b8628 : fetch_word Plain.M.loaded_segments (0xb87e0 : word) = Some W_b8628.
Proof. vm_refl. Qed.
Lemma D_b8628 : decode_any W_b8628 = Some (Jal 0 2096936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b862c : bv 32 := 0xdadfa0ef.
Lemma F_b862c : fetch_word Plain.M.loaded_segments (0xb87e4 : word) = Some W_b862c.
Proof. vm_refl. Qed.
Lemma D_b862c : decode_any W_b862c = Some (Jal 1 2076076, 4%Z).
Proof. vm_refl. Qed.
