(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation ASEGS_I := ImgA.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_113470 : bv 32 := 0xf9010113.
Lemma F_113470 : fetch_word ASEGS_I (0x113470 : word) = Some W_113470.
Proof. vm_refl. Qed.
Lemma D_113470 : decode_any W_113470 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113474 : bv 32 := 0x06113423.
Lemma F_113474 : fetch_word ASEGS_I (0x113474 : word) = Some W_113474.
Proof. vm_refl. Qed.
Lemma D_113474 : decode_any W_113474 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113478 : bv 32 := 0x06813023.
Lemma F_113478 : fetch_word ASEGS_I (0x113478 : word) = Some W_113478.
Proof. vm_refl. Qed.
Lemma D_113478 : decode_any W_113478 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11347c : bv 32 := 0x04913c23.
Lemma F_11347c : fetch_word ASEGS_I (0x11347c : word) = Some W_11347c.
Proof. vm_refl. Qed.
Lemma D_11347c : decode_any W_11347c = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113480 : bv 32 := 0x05213823.
Lemma F_113480 : fetch_word ASEGS_I (0x113480 : word) = Some W_113480.
Proof. vm_refl. Qed.
Lemma D_113480 : decode_any W_113480 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113484 : bv 32 := 0x05313423.
Lemma F_113484 : fetch_word ASEGS_I (0x113484 : word) = Some W_113484.
Proof. vm_refl. Qed.
Lemma D_113484 : decode_any W_113484 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113488 : bv 32 := 0x05413023.
Lemma F_113488 : fetch_word ASEGS_I (0x113488 : word) = Some W_113488.
Proof. vm_refl. Qed.
Lemma D_113488 : decode_any W_113488 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11348c : bv 32 := 0x03513c23.
Lemma F_11348c : fetch_word ASEGS_I (0x11348c : word) = Some W_11348c.
Proof. vm_refl. Qed.
Lemma D_11348c : decode_any W_11348c = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113490 : bv 32 := 0x03613823.
Lemma F_113490 : fetch_word ASEGS_I (0x113490 : word) = Some W_113490.
Proof. vm_refl. Qed.
Lemma D_113490 : decode_any W_113490 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113494 : bv 32 := 0x00060413.
Lemma F_113494 : fetch_word ASEGS_I (0x113494 : word) = Some W_113494.
Proof. vm_refl. Qed.
Lemma D_113494 : decode_any W_113494 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113498 : bv 32 := 0x00050493.
Lemma F_113498 : fetch_word ASEGS_I (0x113498 : word) = Some W_113498.
Proof. vm_refl. Qed.
Lemma D_113498 : decode_any W_113498 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11349c : bv 32 := 0x00017517.
Lemma F_11349c : fetch_word ASEGS_I (0x11349c : word) = Some W_11349c.
Proof. vm_refl. Qed.
Lemma D_11349c : decode_any W_11349c = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134a0 : bv 32 := 0x78453a83.
Lemma F_1134a0 : fetch_word ASEGS_I (0x1134a0 : word) = Some W_1134a0.
Proof. vm_refl. Qed.
Lemma D_1134a0 : decode_any W_1134a0 = Some (Load SZ8 true 21 10 1924, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134a4 : bv 32 := 0x000ab503.
Lemma F_1134a4 : fetch_word ASEGS_I (0x1134a4 : word) = Some W_1134a4.
Proof. vm_refl. Qed.
Lemma D_1134a4 : decode_any W_1134a4 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134a8 : bv 32 := 0x02a13423.
Lemma F_1134a8 : fetch_word ASEGS_I (0x1134a8 : word) = Some W_1134a8.
Proof. vm_refl. Qed.
Lemma D_1134a8 : decode_any W_1134a8 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134ac : bv 32 := 0x0284b503.
Lemma F_1134ac : fetch_word ASEGS_I (0x1134ac : word) = Some W_1134ac.
Proof. vm_refl. Qed.
Lemma D_1134ac : decode_any W_1134ac = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134b0 : bv 32 := 0x0384b603.
Lemma F_1134b0 : fetch_word ASEGS_I (0x1134b0 : word) = Some W_1134b0.
Proof. vm_refl. Qed.
Lemma D_1134b0 : decode_any W_1134b0 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134b4 : bv 32 := 0x40c50b33.
Lemma F_1134b4 : fetch_word ASEGS_I (0x1134b4 : word) = Some W_1134b4.
Proof. vm_refl. Qed.
Lemma D_1134b4 : decode_any W_1134b4 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134b8 : bv 32 := 0x00c546b3.
Lemma F_1134b8 : fetch_word ASEGS_I (0x1134b8 : word) = Some W_1134b8.
Proof. vm_refl. Qed.
Lemma D_1134b8 : decode_any W_1134b8 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134bc : bv 32 := 0x00c13423.
Lemma F_1134bc : fetch_word ASEGS_I (0x1134bc : word) = Some W_1134bc.
Proof. vm_refl. Qed.
Lemma D_1134bc : decode_any W_1134bc = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134c0 : bv 32 := 0x01613823.
Lemma F_1134c0 : fetch_word ASEGS_I (0x1134c0 : word) = Some W_1134c0.
Proof. vm_refl. Qed.
Lemma D_1134c0 : decode_any W_1134c0 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134c4 : bv 32 := 0x00b13c23.
Lemma F_1134c4 : fetch_word ASEGS_I (0x1134c4 : word) = Some W_1134c4.
Proof. vm_refl. Qed.
Lemma D_1134c4 : decode_any W_1134c4 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134c8 : bv 32 := 0x02813023.
Lemma F_1134c8 : fetch_word ASEGS_I (0x1134c8 : word) = Some W_1134c8.
Proof. vm_refl. Qed.
Lemma D_1134c8 : decode_any W_1134c8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134cc : bv 32 := 0x008b0b33.
Lemma F_1134cc : fetch_word ASEGS_I (0x1134cc : word) = Some W_1134cc.
Proof. vm_refl. Qed.
Lemma D_1134cc : decode_any W_1134cc = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134d0 : bv 32 := 0x00d03933.
Lemma F_1134d0 : fetch_word ASEGS_I (0x1134d0 : word) = Some W_1134d0.
Proof. vm_refl. Qed.
Lemma D_1134d0 : decode_any W_1134d0 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134d4 : bv 32 := 0x00c50663.
Lemma F_1134d4 : fetch_word ASEGS_I (0x1134d4 : word) = Some W_1134d4.
Proof. vm_refl. Qed.
Lemma D_1134d4 : decode_any W_1134d4 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134d8 : bv 32 := 0x00810993.
Lemma F_1134d8 : fetch_word ASEGS_I (0x1134d8 : word) = Some W_1134d8.
Proof. vm_refl. Qed.
Lemma D_1134d8 : decode_any W_1134d8 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134dc : bv 32 := 0x0080006f.
Lemma F_1134dc : fetch_word ASEGS_I (0x1134dc : word) = Some W_1134dc.
Proof. vm_refl. Qed.
Lemma D_1134dc : decode_any W_1134dc = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134e0 : bv 32 := 0x01810993.
Lemma F_1134e0 : fetch_word ASEGS_I (0x1134e0 : word) = Some W_1134e0.
Proof. vm_refl. Qed.
Lemma D_1134e0 : decode_any W_1134e0 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134e4 : bv 32 := 0x0784a503.
Lemma F_1134e4 : fetch_word ASEGS_I (0x1134e4 : word) = Some W_1134e4.
Proof. vm_refl. Qed.
Lemma D_1134e4 : decode_any W_1134e4 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134e8 : bv 32 := 0x00190913.
Lemma F_1134e8 : fetch_word ASEGS_I (0x1134e8 : word) = Some W_1134e8.
Proof. vm_refl. Qed.
Lemma D_1134e8 : decode_any W_1134e8 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134ec : bv 32 := 0x04200893.
Lemma F_1134ec : fetch_word ASEGS_I (0x1134ec : word) = Some W_1134ec.
Proof. vm_refl. Qed.
Lemma D_1134ec : decode_any W_1134ec = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134f0 : bv 32 := 0x00098593.
Lemma F_1134f0 : fetch_word ASEGS_I (0x1134f0 : word) = Some W_1134f0.
Proof. vm_refl. Qed.
Lemma D_1134f0 : decode_any W_1134f0 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134f4 : bv 32 := 0x00090613.
Lemma F_1134f4 : fetch_word ASEGS_I (0x1134f4 : word) = Some W_1134f4.
Proof. vm_refl. Qed.
Lemma D_1134f4 : decode_any W_1134f4 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1134f8 : bv 32 := 0x00000073.
Lemma F_1134f8 : fetch_word ASEGS_I (0x1134f8 : word) = Some W_1134f8.
Proof. vm_refl. Qed.
Lemma D_1134f8 : decode_any W_1134f8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1134f8 : is_ecall W_1134f8 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_1134fc : bv 32 := 0x971f80ef.
Lemma F_1134fc : fetch_word ASEGS_I (0x1134fc : word) = Some W_1134fc.
Proof. vm_refl. Qed.
Lemma D_1134fc : decode_any W_1134fc = Some (Jal 1 2066800, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113500 : bv 32 := 0x09651863.
Lemma F_113500 : fetch_word ASEGS_I (0x113500 : word) = Some W_113500.
Proof. vm_refl. Qed.
Lemma D_113500 : decode_any W_113500 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113504 : bv 32 := 0x0584b503.
Lemma F_113504 : fetch_word ASEGS_I (0x113504 : word) = Some W_113504.
Proof. vm_refl. Qed.
Lemma D_113504 : decode_any W_113504 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113508 : bv 32 := 0x0604b583.
Lemma F_113508 : fetch_word ASEGS_I (0x113508 : word) = Some W_113508.
Proof. vm_refl. Qed.
Lemma D_113508 : decode_any W_113508 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11350c : bv 32 := 0x00b505b3.
Lemma F_11350c : fetch_word ASEGS_I (0x11350c : word) = Some W_11350c.
Proof. vm_refl. Qed.
Lemma D_11350c : decode_any W_11350c = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113510 : bv 32 := 0x02b4b023.
Lemma F_113510 : fetch_word ASEGS_I (0x113510 : word) = Some W_113510.
Proof. vm_refl. Qed.
Lemma D_113510 : decode_any W_113510 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113514 : bv 32 := 0x02a4b423.
Lemma F_113514 : fetch_word ASEGS_I (0x113514 : word) = Some W_113514.
Proof. vm_refl. Qed.
Lemma D_113514 : decode_any W_113514 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113518 : bv 32 := 0x02a4bc23.
Lemma F_113518 : fetch_word ASEGS_I (0x113518 : word) = Some W_113518.
Proof. vm_refl. Qed.
Lemma D_113518 : decode_any W_113518 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11351c : bv 32 := 0x00040513.
Lemma F_11351c : fetch_word ASEGS_I (0x11351c : word) = Some W_11351c.
Proof. vm_refl. Qed.
Lemma D_11351c : decode_any W_11351c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113520 : bv 32 := 0x000ab583.
Lemma F_113520 : fetch_word ASEGS_I (0x113520 : word) = Some W_113520.
Proof. vm_refl. Qed.
Lemma D_113520 : decode_any W_113520 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113524 : bv 32 := 0x02813603.
Lemma F_113524 : fetch_word ASEGS_I (0x113524 : word) = Some W_113524.
Proof. vm_refl. Qed.
Lemma D_113524 : decode_any W_113524 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113528 : bv 32 := 0x0cc59a63.
Lemma F_113528 : fetch_word ASEGS_I (0x113528 : word) = Some W_113528.
Proof. vm_refl. Qed.
Lemma D_113528 : decode_any W_113528 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11352c : bv 32 := 0x06813083.
Lemma F_11352c : fetch_word ASEGS_I (0x11352c : word) = Some W_11352c.
Proof. vm_refl. Qed.
Lemma D_11352c : decode_any W_11352c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113530 : bv 32 := 0x06013403.
Lemma F_113530 : fetch_word ASEGS_I (0x113530 : word) = Some W_113530.
Proof. vm_refl. Qed.
Lemma D_113530 : decode_any W_113530 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113534 : bv 32 := 0x05813483.
Lemma F_113534 : fetch_word ASEGS_I (0x113534 : word) = Some W_113534.
Proof. vm_refl. Qed.
Lemma D_113534 : decode_any W_113534 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113538 : bv 32 := 0x05013903.
Lemma F_113538 : fetch_word ASEGS_I (0x113538 : word) = Some W_113538.
Proof. vm_refl. Qed.
Lemma D_113538 : decode_any W_113538 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11353c : bv 32 := 0x04813983.
Lemma F_11353c : fetch_word ASEGS_I (0x11353c : word) = Some W_11353c.
Proof. vm_refl. Qed.
Lemma D_11353c : decode_any W_11353c = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113540 : bv 32 := 0x04013a03.
Lemma F_113540 : fetch_word ASEGS_I (0x113540 : word) = Some W_113540.
Proof. vm_refl. Qed.
Lemma D_113540 : decode_any W_113540 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113544 : bv 32 := 0x03813a83.
Lemma F_113544 : fetch_word ASEGS_I (0x113544 : word) = Some W_113544.
Proof. vm_refl. Qed.
Lemma D_113544 : decode_any W_113544 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113548 : bv 32 := 0x03013b03.
Lemma F_113548 : fetch_word ASEGS_I (0x113548 : word) = Some W_113548.
Proof. vm_refl. Qed.
Lemma D_113548 : decode_any W_113548 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11354c : bv 32 := 0x07010113.
Lemma F_11354c : fetch_word ASEGS_I (0x11354c : word) = Some W_11354c.
Proof. vm_refl. Qed.
Lemma D_11354c : decode_any W_11354c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113550 : bv 32 := 0x00008067.
Lemma F_113550 : fetch_word ASEGS_I (0x113550 : word) = Some W_113550.
Proof. vm_refl. Qed.
Lemma D_113550 : decode_any W_113550 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113554 : bv 32 := 0x00800713.
Lemma F_113554 : fetch_word ASEGS_I (0x113554 : word) = Some W_113554.
Proof. vm_refl. Qed.
Lemma D_113554 : decode_any W_113554 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113558 : bv 32 := 0x000a0593.
Lemma F_113558 : fetch_word ASEGS_I (0x113558 : word) = Some W_113558.
Proof. vm_refl. Qed.
Lemma D_113558 : decode_any W_113558 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11355c : bv 32 := 0x00e98733.
Lemma F_11355c : fetch_word ASEGS_I (0x11355c : word) = Some W_11355c.
Proof. vm_refl. Qed.
Lemma D_11355c : decode_any W_11355c = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113560 : bv 32 := 0x00073783.
Lemma F_113560 : fetch_word ASEGS_I (0x113560 : word) = Some W_113560.
Proof. vm_refl. Qed.
Lemma D_113560 : decode_any W_113560 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113564 : bv 32 := 0x40ab0b33.
Lemma F_113564 : fetch_word ASEGS_I (0x113564 : word) = Some W_113564.
Proof. vm_refl. Qed.
Lemma D_113564 : decode_any W_113564 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113568 : bv 32 := 0x0784a503.
Lemma F_113568 : fetch_word ASEGS_I (0x113568 : word) = Some W_113568.
Proof. vm_refl. Qed.
Lemma D_113568 : decode_any W_113568 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11356c : bv 32 := 0x40c9093b.
Lemma F_11356c : fetch_word ASEGS_I (0x11356c : word) = Some W_11356c.
Proof. vm_refl. Qed.
Lemma D_11356c : decode_any W_11356c = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113570 : bv 32 := 0x40d787b3.
Lemma F_113570 : fetch_word ASEGS_I (0x113570 : word) = Some W_113570.
Proof. vm_refl. Qed.
Lemma D_113570 : decode_any W_113570 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113574 : bv 32 := 0x00f73023.
Lemma F_113574 : fetch_word ASEGS_I (0x113574 : word) = Some W_113574.
Proof. vm_refl. Qed.
Lemma D_113574 : decode_any W_113574 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113578 : bv 32 := 0x04200893.
Lemma F_113578 : fetch_word ASEGS_I (0x113578 : word) = Some W_113578.
Proof. vm_refl. Qed.
Lemma D_113578 : decode_any W_113578 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11357c : bv 32 := 0x00090613.
Lemma F_11357c : fetch_word ASEGS_I (0x11357c : word) = Some W_11357c.
Proof. vm_refl. Qed.
Lemma D_11357c : decode_any W_11357c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113580 : bv 32 := 0x00000073.
Lemma F_113580 : fetch_word ASEGS_I (0x113580 : word) = Some W_113580.
Proof. vm_refl. Qed.
Lemma D_113580 : decode_any W_113580 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_113580 : is_ecall W_113580 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_113584 : bv 32 := 0x8e9f80ef.
Lemma F_113584 : fetch_word ASEGS_I (0x113584 : word) = Some W_113584.
Proof. vm_refl. Qed.
Lemma D_113584 : decode_any W_113584 = Some (Jal 1 2066664, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113588 : bv 32 := 0x000a0993.
Lemma F_113588 : fetch_word ASEGS_I (0x113588 : word) = Some W_113588.
Proof. vm_refl. Qed.
Lemma D_113588 : decode_any W_113588 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11358c : bv 32 := 0xf7650ce3.
Lemma F_11358c : fetch_word ASEGS_I (0x11358c : word) = Some W_11358c.
Proof. vm_refl. Qed.
Lemma D_11358c : decode_any W_11358c = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113590 : bv 32 := 0x02054c63.
Lemma F_113590 : fetch_word ASEGS_I (0x113590 : word) = Some W_113590.
Proof. vm_refl. Qed.
Lemma D_113590 : decode_any W_113590 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113594 : bv 32 := 0x0089b583.
Lemma F_113594 : fetch_word ASEGS_I (0x113594 : word) = Some W_113594.
Proof. vm_refl. Qed.
Lemma D_113594 : decode_any W_113594 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113598 : bv 32 := 0x00a5b633.
Lemma F_113598 : fetch_word ASEGS_I (0x113598 : word) = Some W_113598.
Proof. vm_refl. Qed.
Lemma D_113598 : decode_any W_113598 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11359c : bv 32 := 0x00461a13.
Lemma F_11359c : fetch_word ASEGS_I (0x11359c : word) = Some W_11359c.
Proof. vm_refl. Qed.
Lemma D_11359c : decode_any W_11359c = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135a0 : bv 32 := 0x01498a33.
Lemma F_1135a0 : fetch_word ASEGS_I (0x1135a0 : word) = Some W_1135a0.
Proof. vm_refl. Qed.
Lemma D_1135a0 : decode_any W_1135a0 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135a4 : bv 32 := 0x000a3703.
Lemma F_1135a4 : fetch_word ASEGS_I (0x1135a4 : word) = Some W_1135a4.
Proof. vm_refl. Qed.
Lemma D_1135a4 : decode_any W_1135a4 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135a8 : bv 32 := 0x40c006b3.
Lemma F_1135a8 : fetch_word ASEGS_I (0x1135a8 : word) = Some W_1135a8.
Proof. vm_refl. Qed.
Lemma D_1135a8 : decode_any W_1135a8 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135ac : bv 32 := 0x00b6f6b3.
Lemma F_1135ac : fetch_word ASEGS_I (0x1135ac : word) = Some W_1135ac.
Proof. vm_refl. Qed.
Lemma D_1135ac : decode_any W_1135ac = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135b0 : bv 32 := 0x40d506b3.
Lemma F_1135b0 : fetch_word ASEGS_I (0x1135b0 : word) = Some W_1135b0.
Proof. vm_refl. Qed.
Lemma D_1135b0 : decode_any W_1135b0 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135b4 : bv 32 := 0x00d70733.
Lemma F_1135b4 : fetch_word ASEGS_I (0x1135b4 : word) = Some W_1135b4.
Proof. vm_refl. Qed.
Lemma D_1135b4 : decode_any W_1135b4 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135b8 : bv 32 := 0x00ea3023.
Lemma F_1135b8 : fetch_word ASEGS_I (0x1135b8 : word) = Some W_1135b8.
Proof. vm_refl. Qed.
Lemma D_1135b8 : decode_any W_1135b8 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135bc : bv 32 := 0xf8a5fce3.
Lemma F_1135bc : fetch_word ASEGS_I (0x1135bc : word) = Some W_1135bc.
Proof. vm_refl. Qed.
Lemma D_1135bc : decode_any W_1135bc = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135c0 : bv 32 := 0x01800713.
Lemma F_1135c0 : fetch_word ASEGS_I (0x1135c0 : word) = Some W_1135c0.
Proof. vm_refl. Qed.
Lemma D_1135c0 : decode_any W_1135c0 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135c4 : bv 32 := 0xf95ff06f.
Lemma F_1135c4 : fetch_word ASEGS_I (0x1135c4 : word) = Some W_1135c4.
Proof. vm_refl. Qed.
Lemma D_1135c4 : decode_any W_1135c4 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135c8 : bv 32 := 0x00000513.
Lemma F_1135c8 : fetch_word ASEGS_I (0x1135c8 : word) = Some W_1135c8.
Proof. vm_refl. Qed.
Lemma D_1135c8 : decode_any W_1135c8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135cc : bv 32 := 0x0004a583.
Lemma F_1135cc : fetch_word ASEGS_I (0x1135cc : word) = Some W_1135cc.
Proof. vm_refl. Qed.
Lemma D_1135cc : decode_any W_1135cc = Some (Load SZ4 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135d0 : bv 32 := 0x0009091b.
Lemma F_1135d0 : fetch_word ASEGS_I (0x1135d0 : word) = Some W_1135d0.
Proof. vm_refl. Qed.
Lemma D_1135d0 : decode_any W_1135d0 = Some (OpImm32 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135d4 : bv 32 := 0x00200613.
Lemma F_1135d4 : fetch_word ASEGS_I (0x1135d4 : word) = Some W_1135d4.
Proof. vm_refl. Qed.
Lemma D_1135d4 : decode_any W_1135d4 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135d8 : bv 32 := 0x0205e593.
Lemma F_1135d8 : fetch_word ASEGS_I (0x1135d8 : word) = Some W_1135d8.
Proof. vm_refl. Qed.
Lemma D_1135d8 : decode_any W_1135d8 = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135dc : bv 32 := 0x00b4a023.
Lemma F_1135dc : fetch_word ASEGS_I (0x1135dc : word) = Some W_1135dc.
Proof. vm_refl. Qed.
Lemma D_1135dc : decode_any W_1135dc = Some (Store SZ4 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135e0 : bv 32 := 0x0204b023.
Lemma F_1135e0 : fetch_word ASEGS_I (0x1135e0 : word) = Some W_1135e0.
Proof. vm_refl. Qed.
Lemma D_1135e0 : decode_any W_1135e0 = Some (Store SZ8 9 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135e4 : bv 32 := 0x0204b423.
Lemma F_1135e4 : fetch_word ASEGS_I (0x1135e4 : word) = Some W_1135e4.
Proof. vm_refl. Qed.
Lemma D_1135e4 : decode_any W_1135e4 = Some (Store SZ8 9 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135e8 : bv 32 := 0x0204bc23.
Lemma F_1135e8 : fetch_word ASEGS_I (0x1135e8 : word) = Some W_1135e8.
Proof. vm_refl. Qed.
Lemma D_1135e8 : decode_any W_1135e8 = Some (Store SZ8 9 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135ec : bv 32 := 0xf2c90ae3.
Lemma F_1135ec : fetch_word ASEGS_I (0x1135ec : word) = Some W_1135ec.
Proof. vm_refl. Qed.
Lemma D_1135ec : decode_any W_1135ec = Some (Branch BC_EQ 18 12 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135f0 : bv 32 := 0x0089b503.
Lemma F_1135f0 : fetch_word ASEGS_I (0x1135f0 : word) = Some W_1135f0.
Proof. vm_refl. Qed.
Lemma D_1135f0 : decode_any W_1135f0 = Some (Load SZ8 true 10 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135f4 : bv 32 := 0x40a40533.
Lemma F_1135f4 : fetch_word ASEGS_I (0x1135f4 : word) = Some W_1135f4.
Proof. vm_refl. Qed.
Lemma D_1135f4 : decode_any W_1135f4 = Some (Op ALU_SUB 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135f8 : bv 32 := 0xf29ff06f.
Lemma F_1135f8 : fetch_word ASEGS_I (0x1135f8 : word) = Some W_1135f8.
Proof. vm_refl. Qed.
Lemma D_1135f8 : decode_any W_1135f8 = Some (Jal 0 2096936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1135fc : bv 32 := 0x93cf80ef.
Lemma F_1135fc : fetch_word ASEGS_I (0x1135fc : word) = Some W_1135fc.
Proof. vm_refl. Qed.
Lemma D_1135fc : decode_any W_1135fc = Some (Jal 1 2064700, 4%Z).
Proof. vm_refl. Qed.
