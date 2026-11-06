(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_d4500 : bv 32 := 0x0035f693.
Lemma F_d4500 : fetch_word AsanUbsan.M.loaded_segments (0xd4500 : word) = Some W_d4500.
Proof. vm_refl. Qed.
Lemma D_d4500 : decode_any W_d4500 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4504 : bv 32 := 0x10068863.
Lemma F_d4504 : fetch_word AsanUbsan.M.loaded_segments (0xd4504 : word) = Some W_d4504.
Proof. vm_refl. Qed.
Lemma D_d4504 : decode_any W_d4504 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4508 : bv 32 := 0x02060e63.
Lemma F_d4508 : fetch_word AsanUbsan.M.loaded_segments (0xd4508 : word) = Some W_d4508.
Proof. vm_refl. Qed.
Lemma D_d4508 : decode_any W_d4508 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d450c : bv 32 := 0x00158713.
Lemma F_d450c : fetch_word AsanUbsan.M.loaded_segments (0xd450c : word) = Some W_d450c.
Proof. vm_refl. Qed.
Lemma D_d450c : decode_any W_d450c = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4510 : bv 32 := 0x00100793.
Lemma F_d4510 : fetch_word AsanUbsan.M.loaded_segments (0xd4510 : word) = Some W_d4510.
Proof. vm_refl. Qed.
Lemma D_d4510 : decode_any W_d4510 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4514 : bv 32 := 0x00050693.
Lemma F_d4514 : fetch_word AsanUbsan.M.loaded_segments (0xd4514 : word) = Some W_d4514.
Proof. vm_refl. Qed.
Lemma D_d4514 : decode_any W_d4514 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4518 : bv 32 := 0x0005c883.
Lemma F_d4518 : fetch_word AsanUbsan.M.loaded_segments (0xd4518 : word) = Some W_d4518.
Proof. vm_refl. Qed.
Lemma D_d4518 : decode_any W_d4518 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d451c : bv 32 := 0x00060813.
Lemma F_d451c : fetch_word AsanUbsan.M.loaded_segments (0xd451c : word) = Some W_d451c.
Proof. vm_refl. Qed.
Lemma D_d451c : decode_any W_d451c = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4520 : bv 32 := 0x00158593.
Lemma F_d4520 : fetch_word AsanUbsan.M.loaded_segments (0xd4520 : word) = Some W_d4520.
Proof. vm_refl. Qed.
Lemma D_d4520 : decode_any W_d4520 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4524 : bv 32 := 0x00377293.
Lemma F_d4524 : fetch_word AsanUbsan.M.loaded_segments (0xd4524 : word) = Some W_d4524.
Proof. vm_refl. Qed.
Lemma D_d4524 : decode_any W_d4524 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4528 : bv 32 := 0x01168023.
Lemma F_d4528 : fetch_word AsanUbsan.M.loaded_segments (0xd4528 : word) = Some W_d4528.
Proof. vm_refl. Qed.
Lemma D_d4528 : decode_any W_d4528 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d452c : bv 32 := 0x00168693.
Lemma F_d452c : fetch_word AsanUbsan.M.loaded_segments (0xd452c : word) = Some W_d452c.
Proof. vm_refl. Qed.
Lemma D_d452c : decode_any W_d452c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4530 : bv 32 := 0xfff60613.
Lemma F_d4530 : fetch_word AsanUbsan.M.loaded_segments (0xd4530 : word) = Some W_d4530.
Proof. vm_refl. Qed.
Lemma D_d4530 : decode_any W_d4530 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4534 : bv 32 := 0x00028a63.
Lemma F_d4534 : fetch_word AsanUbsan.M.loaded_segments (0xd4534 : word) = Some W_d4534.
Proof. vm_refl. Qed.
Lemma D_d4534 : decode_any W_d4534 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4538 : bv 32 := 0x00170713.
Lemma F_d4538 : fetch_word AsanUbsan.M.loaded_segments (0xd4538 : word) = Some W_d4538.
Proof. vm_refl. Qed.
Lemma D_d4538 : decode_any W_d4538 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d453c : bv 32 := 0xfcf81ee3.
Lemma F_d453c : fetch_word AsanUbsan.M.loaded_segments (0xd453c : word) = Some W_d453c.
Proof. vm_refl. Qed.
Lemma D_d453c : decode_any W_d453c = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4540 : bv 32 := 0x0080006f.
Lemma F_d4540 : fetch_word AsanUbsan.M.loaded_segments (0xd4540 : word) = Some W_d4540.
Proof. vm_refl. Qed.
Lemma D_d4540 : decode_any W_d4540 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4544 : bv 32 := 0x00050693.
Lemma F_d4544 : fetch_word AsanUbsan.M.loaded_segments (0xd4544 : word) = Some W_d4544.
Proof. vm_refl. Qed.
Lemma D_d4544 : decode_any W_d4544 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4548 : bv 32 := 0x0036f793.
Lemma F_d4548 : fetch_word AsanUbsan.M.loaded_segments (0xd4548 : word) = Some W_d4548.
Proof. vm_refl. Qed.
Lemma D_d4548 : decode_any W_d4548 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d454c : bv 32 := 0x0c078a63.
Lemma F_d454c : fetch_word AsanUbsan.M.loaded_segments (0xd454c : word) = Some W_d454c.
Proof. vm_refl. Qed.
Lemma D_d454c : decode_any W_d454c = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4550 : bv 32 := 0x02000713.
Lemma F_d4550 : fetch_word AsanUbsan.M.loaded_segments (0xd4550 : word) = Some W_d4550.
Proof. vm_refl. Qed.
Lemma D_d4550 : decode_any W_d4550 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4554 : bv 32 := 0x02e67063.
Lemma F_d4554 : fetch_word AsanUbsan.M.loaded_segments (0xd4554 : word) = Some W_d4554.
Proof. vm_refl. Qed.
Lemma D_d4554 : decode_any W_d4554 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4558 : bv 32 := 0x01000713.
Lemma F_d4558 : fetch_word AsanUbsan.M.loaded_segments (0xd4558 : word) = Some W_d4558.
Proof. vm_refl. Qed.
Lemma D_d4558 : decode_any W_d4558 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d455c : bv 32 := 0x24e67863.
Lemma F_d455c : fetch_word AsanUbsan.M.loaded_segments (0xd455c : word) = Some W_d455c.
Proof. vm_refl. Qed.
Lemma D_d455c : decode_any W_d455c = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4560 : bv 32 := 0x00867713.
Lemma F_d4560 : fetch_word AsanUbsan.M.loaded_segments (0xd4560 : word) = Some W_d4560.
Proof. vm_refl. Qed.
Lemma D_d4560 : decode_any W_d4560 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4564 : bv 32 := 0x2c071e63.
Lemma F_d4564 : fetch_word AsanUbsan.M.loaded_segments (0xd4564 : word) = Some W_d4564.
Proof. vm_refl. Qed.
Lemma D_d4564 : decode_any W_d4564 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4568 : bv 32 := 0x00467713.
Lemma F_d4568 : fetch_word AsanUbsan.M.loaded_segments (0xd4568 : word) = Some W_d4568.
Proof. vm_refl. Qed.
Lemma D_d4568 : decode_any W_d4568 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d456c : bv 32 := 0x32071463.
Lemma F_d456c : fetch_word AsanUbsan.M.loaded_segments (0xd456c : word) = Some W_d456c.
Proof. vm_refl. Qed.
Lemma D_d456c : decode_any W_d456c = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4570 : bv 32 := 0x3500006f.
Lemma F_d4570 : fetch_word AsanUbsan.M.loaded_segments (0xd4570 : word) = Some W_d4570.
Proof. vm_refl. Qed.
Lemma D_d4570 : decode_any W_d4570 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4574 : bv 32 := 0x0005a703.
Lemma F_d4574 : fetch_word AsanUbsan.M.loaded_segments (0xd4574 : word) = Some W_d4574.
Proof. vm_refl. Qed.
Lemma D_d4574 : decode_any W_d4574 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4578 : bv 32 := 0x00300813.
Lemma F_d4578 : fetch_word AsanUbsan.M.loaded_segments (0xd4578 : word) = Some W_d4578.
Proof. vm_refl. Qed.
Lemma D_d4578 : decode_any W_d4578 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d457c : bv 32 := 0x11078e63.
Lemma F_d457c : fetch_word AsanUbsan.M.loaded_segments (0xd457c : word) = Some W_d457c.
Proof. vm_refl. Qed.
Lemma D_d457c : decode_any W_d457c = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4580 : bv 32 := 0x00200813.
Lemma F_d4580 : fetch_word AsanUbsan.M.loaded_segments (0xd4580 : word) = Some W_d4580.
Proof. vm_refl. Qed.
Lemma D_d4580 : decode_any W_d4580 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4584 : bv 32 := 0x19079c63.
Lemma F_d4584 : fetch_word AsanUbsan.M.loaded_segments (0xd4584 : word) = Some W_d4584.
Proof. vm_refl. Qed.
Lemma D_d4584 : decode_any W_d4584 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4588 : bv 32 := 0x00875793.
Lemma F_d4588 : fetch_word AsanUbsan.M.loaded_segments (0xd4588 : word) = Some W_d4588.
Proof. vm_refl. Qed.
Lemma D_d4588 : decode_any W_d4588 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d458c : bv 32 := 0xffe60613.
Lemma F_d458c : fetch_word AsanUbsan.M.loaded_segments (0xd458c : word) = Some W_d458c.
Proof. vm_refl. Qed.
Lemma D_d458c : decode_any W_d458c = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4590 : bv 32 := 0x00e68023.
Lemma F_d4590 : fetch_word AsanUbsan.M.loaded_segments (0xd4590 : word) = Some W_d4590.
Proof. vm_refl. Qed.
Lemma D_d4590 : decode_any W_d4590 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4594 : bv 32 := 0x00f680a3.
Lemma F_d4594 : fetch_word AsanUbsan.M.loaded_segments (0xd4594 : word) = Some W_d4594.
Proof. vm_refl. Qed.
Lemma D_d4594 : decode_any W_d4594 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4598 : bv 32 := 0x00268693.
Lemma F_d4598 : fetch_word AsanUbsan.M.loaded_segments (0xd4598 : word) = Some W_d4598.
Proof. vm_refl. Qed.
Lemma D_d4598 : decode_any W_d4598 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d459c : bv 32 := 0x01058593.
Lemma F_d459c : fetch_word AsanUbsan.M.loaded_segments (0xd459c : word) = Some W_d459c.
Proof. vm_refl. Qed.
Lemma D_d459c : decode_any W_d459c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45a0 : bv 32 := 0x01100793.
Lemma F_d45a0 : fetch_word AsanUbsan.M.loaded_segments (0xd45a0 : word) = Some W_d45a0.
Proof. vm_refl. Qed.
Lemma D_d45a0 : decode_any W_d45a0 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45a4 : bv 32 := 0x0107581b.
Lemma F_d45a4 : fetch_word AsanUbsan.M.loaded_segments (0xd45a4 : word) = Some W_d45a4.
Proof. vm_refl. Qed.
Lemma D_d45a4 : decode_any W_d45a4 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45a8 : bv 32 := 0xff45a883.
Lemma F_d45a8 : fetch_word AsanUbsan.M.loaded_segments (0xd45a8 : word) = Some W_d45a8.
Proof. vm_refl. Qed.
Lemma D_d45a8 : decode_any W_d45a8 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45ac : bv 32 := 0xff85a283.
Lemma F_d45ac : fetch_word AsanUbsan.M.loaded_segments (0xd45ac : word) = Some W_d45ac.
Proof. vm_refl. Qed.
Lemma D_d45ac : decode_any W_d45ac = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45b0 : bv 32 := 0xffc5a303.
Lemma F_d45b0 : fetch_word AsanUbsan.M.loaded_segments (0xd45b0 : word) = Some W_d45b0.
Proof. vm_refl. Qed.
Lemma D_d45b0 : decode_any W_d45b0 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45b4 : bv 32 := 0x0005a703.
Lemma F_d45b4 : fetch_word AsanUbsan.M.loaded_segments (0xd45b4 : word) = Some W_d45b4.
Proof. vm_refl. Qed.
Lemma D_d45b4 : decode_any W_d45b4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45b8 : bv 32 := 0x01089393.
Lemma F_d45b8 : fetch_word AsanUbsan.M.loaded_segments (0xd45b8 : word) = Some W_d45b8.
Proof. vm_refl. Qed.
Lemma D_d45b8 : decode_any W_d45b8 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45bc : bv 32 := 0x0108d89b.
Lemma F_d45bc : fetch_word AsanUbsan.M.loaded_segments (0xd45bc : word) = Some W_d45bc.
Proof. vm_refl. Qed.
Lemma D_d45bc : decode_any W_d45bc = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45c0 : bv 32 := 0x0103e833.
Lemma F_d45c0 : fetch_word AsanUbsan.M.loaded_segments (0xd45c0 : word) = Some W_d45c0.
Proof. vm_refl. Qed.
Lemma D_d45c0 : decode_any W_d45c0 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45c4 : bv 32 := 0x01029393.
Lemma F_d45c4 : fetch_word AsanUbsan.M.loaded_segments (0xd45c4 : word) = Some W_d45c4.
Proof. vm_refl. Qed.
Lemma D_d45c4 : decode_any W_d45c4 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45c8 : bv 32 := 0x0102d29b.
Lemma F_d45c8 : fetch_word AsanUbsan.M.loaded_segments (0xd45c8 : word) = Some W_d45c8.
Proof. vm_refl. Qed.
Lemma D_d45c8 : decode_any W_d45c8 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45cc : bv 32 := 0x0113e8b3.
Lemma F_d45cc : fetch_word AsanUbsan.M.loaded_segments (0xd45cc : word) = Some W_d45cc.
Proof. vm_refl. Qed.
Lemma D_d45cc : decode_any W_d45cc = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45d0 : bv 32 := 0x01031393.
Lemma F_d45d0 : fetch_word AsanUbsan.M.loaded_segments (0xd45d0 : word) = Some W_d45d0.
Proof. vm_refl. Qed.
Lemma D_d45d0 : decode_any W_d45d0 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45d4 : bv 32 := 0x0103531b.
Lemma F_d45d4 : fetch_word AsanUbsan.M.loaded_segments (0xd45d4 : word) = Some W_d45d4.
Proof. vm_refl. Qed.
Lemma D_d45d4 : decode_any W_d45d4 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45d8 : bv 32 := 0x0053e2b3.
Lemma F_d45d8 : fetch_word AsanUbsan.M.loaded_segments (0xd45d8 : word) = Some W_d45d8.
Proof. vm_refl. Qed.
Lemma D_d45d8 : decode_any W_d45d8 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45dc : bv 32 := 0x01071393.
Lemma F_d45dc : fetch_word AsanUbsan.M.loaded_segments (0xd45dc : word) = Some W_d45dc.
Proof. vm_refl. Qed.
Lemma D_d45dc : decode_any W_d45dc = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45e0 : bv 32 := 0x0063e333.
Lemma F_d45e0 : fetch_word AsanUbsan.M.loaded_segments (0xd45e0 : word) = Some W_d45e0.
Proof. vm_refl. Qed.
Lemma D_d45e0 : decode_any W_d45e0 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45e4 : bv 32 := 0xff060613.
Lemma F_d45e4 : fetch_word AsanUbsan.M.loaded_segments (0xd45e4 : word) = Some W_d45e4.
Proof. vm_refl. Qed.
Lemma D_d45e4 : decode_any W_d45e4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45e8 : bv 32 := 0x0106a023.
Lemma F_d45e8 : fetch_word AsanUbsan.M.loaded_segments (0xd45e8 : word) = Some W_d45e8.
Proof. vm_refl. Qed.
Lemma D_d45e8 : decode_any W_d45e8 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45ec : bv 32 := 0x0116a223.
Lemma F_d45ec : fetch_word AsanUbsan.M.loaded_segments (0xd45ec : word) = Some W_d45ec.
Proof. vm_refl. Qed.
Lemma D_d45ec : decode_any W_d45ec = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45f0 : bv 32 := 0x0056a423.
Lemma F_d45f0 : fetch_word AsanUbsan.M.loaded_segments (0xd45f0 : word) = Some W_d45f0.
Proof. vm_refl. Qed.
Lemma D_d45f0 : decode_any W_d45f0 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45f4 : bv 32 := 0x0066a623.
Lemma F_d45f4 : fetch_word AsanUbsan.M.loaded_segments (0xd45f4 : word) = Some W_d45f4.
Proof. vm_refl. Qed.
Lemma D_d45f4 : decode_any W_d45f4 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45f8 : bv 32 := 0x01068693.
Lemma F_d45f8 : fetch_word AsanUbsan.M.loaded_segments (0xd45f8 : word) = Some W_d45f8.
Proof. vm_refl. Qed.
Lemma D_d45f8 : decode_any W_d45f8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d45fc : bv 32 := 0x01058593.
Lemma F_d45fc : fetch_word AsanUbsan.M.loaded_segments (0xd45fc : word) = Some W_d45fc.
Proof. vm_refl. Qed.
Lemma D_d45fc : decode_any W_d45fc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4600 : bv 32 := 0xfac7e2e3.
Lemma F_d4600 : fetch_word AsanUbsan.M.loaded_segments (0xd4600 : word) = Some W_d4600.
Proof. vm_refl. Qed.
Lemma D_d4600 : decode_any W_d4600 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4604 : bv 32 := 0xff258593.
Lemma F_d4604 : fetch_word AsanUbsan.M.loaded_segments (0xd4604 : word) = Some W_d4604.
Proof. vm_refl. Qed.
Lemma D_d4604 : decode_any W_d4604 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4608 : bv 32 := 0x01000713.
Lemma F_d4608 : fetch_word AsanUbsan.M.loaded_segments (0xd4608 : word) = Some W_d4608.
Proof. vm_refl. Qed.
Lemma D_d4608 : decode_any W_d4608 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d460c : bv 32 := 0xf4e66ae3.
Lemma F_d460c : fetch_word AsanUbsan.M.loaded_segments (0xd460c : word) = Some W_d460c.
Proof. vm_refl. Qed.
Lemma D_d460c : decode_any W_d460c = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4610 : bv 32 := 0x19c0006f.
Lemma F_d4610 : fetch_word AsanUbsan.M.loaded_segments (0xd4610 : word) = Some W_d4610.
Proof. vm_refl. Qed.
Lemma D_d4610 : decode_any W_d4610 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4614 : bv 32 := 0x00050693.
Lemma F_d4614 : fetch_word AsanUbsan.M.loaded_segments (0xd4614 : word) = Some W_d4614.
Proof. vm_refl. Qed.
Lemma D_d4614 : decode_any W_d4614 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4618 : bv 32 := 0x00357793.
Lemma F_d4618 : fetch_word AsanUbsan.M.loaded_segments (0xd4618 : word) = Some W_d4618.
Proof. vm_refl. Qed.
Lemma D_d4618 : decode_any W_d4618 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d461c : bv 32 := 0xf2079ae3.
Lemma F_d461c : fetch_word AsanUbsan.M.loaded_segments (0xd461c : word) = Some W_d461c.
Proof. vm_refl. Qed.
Lemma D_d461c : decode_any W_d461c = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4620 : bv 32 := 0x01000713.
Lemma F_d4620 : fetch_word AsanUbsan.M.loaded_segments (0xd4620 : word) = Some W_d4620.
Proof. vm_refl. Qed.
Lemma D_d4620 : decode_any W_d4620 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4624 : bv 32 := 0x02e66c63.
Lemma F_d4624 : fetch_word AsanUbsan.M.loaded_segments (0xd4624 : word) = Some W_d4624.
Proof. vm_refl. Qed.
Lemma D_d4624 : decode_any W_d4624 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4628 : bv 32 := 0x00f00713.
Lemma F_d4628 : fetch_word AsanUbsan.M.loaded_segments (0xd4628 : word) = Some W_d4628.
Proof. vm_refl. Qed.
Lemma D_d4628 : decode_any W_d4628 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d462c : bv 32 := 0x0005a783.
Lemma F_d462c : fetch_word AsanUbsan.M.loaded_segments (0xd462c : word) = Some W_d462c.
Proof. vm_refl. Qed.
Lemma D_d462c : decode_any W_d462c = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4630 : bv 32 := 0x0045a803.
Lemma F_d4630 : fetch_word AsanUbsan.M.loaded_segments (0xd4630 : word) = Some W_d4630.
Proof. vm_refl. Qed.
Lemma D_d4630 : decode_any W_d4630 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4634 : bv 32 := 0x0085a883.
Lemma F_d4634 : fetch_word AsanUbsan.M.loaded_segments (0xd4634 : word) = Some W_d4634.
Proof. vm_refl. Qed.
Lemma D_d4634 : decode_any W_d4634 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4638 : bv 32 := 0x00c5a283.
Lemma F_d4638 : fetch_word AsanUbsan.M.loaded_segments (0xd4638 : word) = Some W_d4638.
Proof. vm_refl. Qed.
Lemma D_d4638 : decode_any W_d4638 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d463c : bv 32 := 0x01058593.
Lemma F_d463c : fetch_word AsanUbsan.M.loaded_segments (0xd463c : word) = Some W_d463c.
Proof. vm_refl. Qed.
Lemma D_d463c : decode_any W_d463c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4640 : bv 32 := 0xff060613.
Lemma F_d4640 : fetch_word AsanUbsan.M.loaded_segments (0xd4640 : word) = Some W_d4640.
Proof. vm_refl. Qed.
Lemma D_d4640 : decode_any W_d4640 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4644 : bv 32 := 0x00f6a023.
Lemma F_d4644 : fetch_word AsanUbsan.M.loaded_segments (0xd4644 : word) = Some W_d4644.
Proof. vm_refl. Qed.
Lemma D_d4644 : decode_any W_d4644 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4648 : bv 32 := 0x0106a223.
Lemma F_d4648 : fetch_word AsanUbsan.M.loaded_segments (0xd4648 : word) = Some W_d4648.
Proof. vm_refl. Qed.
Lemma D_d4648 : decode_any W_d4648 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d464c : bv 32 := 0x0116a423.
Lemma F_d464c : fetch_word AsanUbsan.M.loaded_segments (0xd464c : word) = Some W_d464c.
Proof. vm_refl. Qed.
Lemma D_d464c : decode_any W_d464c = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4650 : bv 32 := 0x0056a623.
Lemma F_d4650 : fetch_word AsanUbsan.M.loaded_segments (0xd4650 : word) = Some W_d4650.
Proof. vm_refl. Qed.
Lemma D_d4650 : decode_any W_d4650 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4654 : bv 32 := 0x01068693.
Lemma F_d4654 : fetch_word AsanUbsan.M.loaded_segments (0xd4654 : word) = Some W_d4654.
Proof. vm_refl. Qed.
Lemma D_d4654 : decode_any W_d4654 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4658 : bv 32 := 0xfcc76ae3.
Lemma F_d4658 : fetch_word AsanUbsan.M.loaded_segments (0xd4658 : word) = Some W_d4658.
Proof. vm_refl. Qed.
Lemma D_d4658 : decode_any W_d4658 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d465c : bv 32 := 0x00800713.
Lemma F_d465c : fetch_word AsanUbsan.M.loaded_segments (0xd465c : word) = Some W_d465c.
Proof. vm_refl. Qed.
Lemma D_d465c : decode_any W_d465c = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4660 : bv 32 := 0x00e66e63.
Lemma F_d4660 : fetch_word AsanUbsan.M.loaded_segments (0xd4660 : word) = Some W_d4660.
Proof. vm_refl. Qed.
Lemma D_d4660 : decode_any W_d4660 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4664 : bv 32 := 0x0005a703.
Lemma F_d4664 : fetch_word AsanUbsan.M.loaded_segments (0xd4664 : word) = Some W_d4664.
Proof. vm_refl. Qed.
Lemma D_d4664 : decode_any W_d4664 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4668 : bv 32 := 0x0045a783.
Lemma F_d4668 : fetch_word AsanUbsan.M.loaded_segments (0xd4668 : word) = Some W_d4668.
Proof. vm_refl. Qed.
Lemma D_d4668 : decode_any W_d4668 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d466c : bv 32 := 0x00e6a023.
Lemma F_d466c : fetch_word AsanUbsan.M.loaded_segments (0xd466c : word) = Some W_d466c.
Proof. vm_refl. Qed.
Lemma D_d466c : decode_any W_d466c = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4670 : bv 32 := 0x00f6a223.
Lemma F_d4670 : fetch_word AsanUbsan.M.loaded_segments (0xd4670 : word) = Some W_d4670.
Proof. vm_refl. Qed.
Lemma D_d4670 : decode_any W_d4670 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4674 : bv 32 := 0x00868693.
Lemma F_d4674 : fetch_word AsanUbsan.M.loaded_segments (0xd4674 : word) = Some W_d4674.
Proof. vm_refl. Qed.
Lemma D_d4674 : decode_any W_d4674 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4678 : bv 32 := 0x00858593.
Lemma F_d4678 : fetch_word AsanUbsan.M.loaded_segments (0xd4678 : word) = Some W_d4678.
Proof. vm_refl. Qed.
Lemma D_d4678 : decode_any W_d4678 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d467c : bv 32 := 0x00467713.
Lemma F_d467c : fetch_word AsanUbsan.M.loaded_segments (0xd467c : word) = Some W_d467c.
Proof. vm_refl. Qed.
Lemma D_d467c : decode_any W_d467c = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4680 : bv 32 := 0x24070063.
Lemma F_d4680 : fetch_word AsanUbsan.M.loaded_segments (0xd4680 : word) = Some W_d4680.
Proof. vm_refl. Qed.
Lemma D_d4680 : decode_any W_d4680 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4684 : bv 32 := 0x0005a703.
Lemma F_d4684 : fetch_word AsanUbsan.M.loaded_segments (0xd4684 : word) = Some W_d4684.
Proof. vm_refl. Qed.
Lemma D_d4684 : decode_any W_d4684 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4688 : bv 32 := 0x00458593.
Lemma F_d4688 : fetch_word AsanUbsan.M.loaded_segments (0xd4688 : word) = Some W_d4688.
Proof. vm_refl. Qed.
Lemma D_d4688 : decode_any W_d4688 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d468c : bv 32 := 0x00e6a023.
Lemma F_d468c : fetch_word AsanUbsan.M.loaded_segments (0xd468c : word) = Some W_d468c.
Proof. vm_refl. Qed.
Lemma D_d468c : decode_any W_d468c = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4690 : bv 32 := 0x00468693.
Lemma F_d4690 : fetch_word AsanUbsan.M.loaded_segments (0xd4690 : word) = Some W_d4690.
Proof. vm_refl. Qed.
Lemma D_d4690 : decode_any W_d4690 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4694 : bv 32 := 0x22c0006f.
Lemma F_d4694 : fetch_word AsanUbsan.M.loaded_segments (0xd4694 : word) = Some W_d4694.
Proof. vm_refl. Qed.
Lemma D_d4694 : decode_any W_d4694 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4698 : bv 32 := 0x00e68023.
Lemma F_d4698 : fetch_word AsanUbsan.M.loaded_segments (0xd4698 : word) = Some W_d4698.
Proof. vm_refl. Qed.
Lemma D_d4698 : decode_any W_d4698 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d469c : bv 32 := 0x00168693.
Lemma F_d469c : fetch_word AsanUbsan.M.loaded_segments (0xd469c : word) = Some W_d469c.
Proof. vm_refl. Qed.
Lemma D_d469c : decode_any W_d469c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46a0 : bv 32 := 0xfff60613.
Lemma F_d46a0 : fetch_word AsanUbsan.M.loaded_segments (0xd46a0 : word) = Some W_d46a0.
Proof. vm_refl. Qed.
Lemma D_d46a0 : decode_any W_d46a0 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46a4 : bv 32 := 0x01058593.
Lemma F_d46a4 : fetch_word AsanUbsan.M.loaded_segments (0xd46a4 : word) = Some W_d46a4.
Proof. vm_refl. Qed.
Lemma D_d46a4 : decode_any W_d46a4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46a8 : bv 32 := 0x01200793.
Lemma F_d46a8 : fetch_word AsanUbsan.M.loaded_segments (0xd46a8 : word) = Some W_d46a8.
Proof. vm_refl. Qed.
Lemma D_d46a8 : decode_any W_d46a8 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46ac : bv 32 := 0x0087581b.
Lemma F_d46ac : fetch_word AsanUbsan.M.loaded_segments (0xd46ac : word) = Some W_d46ac.
Proof. vm_refl. Qed.
Lemma D_d46ac : decode_any W_d46ac = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46b0 : bv 32 := 0xff45a883.
Lemma F_d46b0 : fetch_word AsanUbsan.M.loaded_segments (0xd46b0 : word) = Some W_d46b0.
Proof. vm_refl. Qed.
Lemma D_d46b0 : decode_any W_d46b0 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46b4 : bv 32 := 0xff85a283.
Lemma F_d46b4 : fetch_word AsanUbsan.M.loaded_segments (0xd46b4 : word) = Some W_d46b4.
Proof. vm_refl. Qed.
Lemma D_d46b4 : decode_any W_d46b4 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46b8 : bv 32 := 0xffc5a303.
Lemma F_d46b8 : fetch_word AsanUbsan.M.loaded_segments (0xd46b8 : word) = Some W_d46b8.
Proof. vm_refl. Qed.
Lemma D_d46b8 : decode_any W_d46b8 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46bc : bv 32 := 0x0005a703.
Lemma F_d46bc : fetch_word AsanUbsan.M.loaded_segments (0xd46bc : word) = Some W_d46bc.
Proof. vm_refl. Qed.
Lemma D_d46bc : decode_any W_d46bc = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46c0 : bv 32 := 0x01889393.
Lemma F_d46c0 : fetch_word AsanUbsan.M.loaded_segments (0xd46c0 : word) = Some W_d46c0.
Proof. vm_refl. Qed.
Lemma D_d46c0 : decode_any W_d46c0 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46c4 : bv 32 := 0x0088d89b.
Lemma F_d46c4 : fetch_word AsanUbsan.M.loaded_segments (0xd46c4 : word) = Some W_d46c4.
Proof. vm_refl. Qed.
Lemma D_d46c4 : decode_any W_d46c4 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46c8 : bv 32 := 0x0103e833.
Lemma F_d46c8 : fetch_word AsanUbsan.M.loaded_segments (0xd46c8 : word) = Some W_d46c8.
Proof. vm_refl. Qed.
Lemma D_d46c8 : decode_any W_d46c8 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46cc : bv 32 := 0x01829393.
Lemma F_d46cc : fetch_word AsanUbsan.M.loaded_segments (0xd46cc : word) = Some W_d46cc.
Proof. vm_refl. Qed.
Lemma D_d46cc : decode_any W_d46cc = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46d0 : bv 32 := 0x0082d29b.
Lemma F_d46d0 : fetch_word AsanUbsan.M.loaded_segments (0xd46d0 : word) = Some W_d46d0.
Proof. vm_refl. Qed.
Lemma D_d46d0 : decode_any W_d46d0 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46d4 : bv 32 := 0x0113e8b3.
Lemma F_d46d4 : fetch_word AsanUbsan.M.loaded_segments (0xd46d4 : word) = Some W_d46d4.
Proof. vm_refl. Qed.
Lemma D_d46d4 : decode_any W_d46d4 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46d8 : bv 32 := 0x01831393.
Lemma F_d46d8 : fetch_word AsanUbsan.M.loaded_segments (0xd46d8 : word) = Some W_d46d8.
Proof. vm_refl. Qed.
Lemma D_d46d8 : decode_any W_d46d8 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46dc : bv 32 := 0x0083531b.
Lemma F_d46dc : fetch_word AsanUbsan.M.loaded_segments (0xd46dc : word) = Some W_d46dc.
Proof. vm_refl. Qed.
Lemma D_d46dc : decode_any W_d46dc = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46e0 : bv 32 := 0x0053e2b3.
Lemma F_d46e0 : fetch_word AsanUbsan.M.loaded_segments (0xd46e0 : word) = Some W_d46e0.
Proof. vm_refl. Qed.
Lemma D_d46e0 : decode_any W_d46e0 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46e4 : bv 32 := 0x01871393.
Lemma F_d46e4 : fetch_word AsanUbsan.M.loaded_segments (0xd46e4 : word) = Some W_d46e4.
Proof. vm_refl. Qed.
Lemma D_d46e4 : decode_any W_d46e4 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46e8 : bv 32 := 0x0063e333.
Lemma F_d46e8 : fetch_word AsanUbsan.M.loaded_segments (0xd46e8 : word) = Some W_d46e8.
Proof. vm_refl. Qed.
Lemma D_d46e8 : decode_any W_d46e8 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46ec : bv 32 := 0xff060613.
Lemma F_d46ec : fetch_word AsanUbsan.M.loaded_segments (0xd46ec : word) = Some W_d46ec.
Proof. vm_refl. Qed.
Lemma D_d46ec : decode_any W_d46ec = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46f0 : bv 32 := 0x0106a023.
Lemma F_d46f0 : fetch_word AsanUbsan.M.loaded_segments (0xd46f0 : word) = Some W_d46f0.
Proof. vm_refl. Qed.
Lemma D_d46f0 : decode_any W_d46f0 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46f4 : bv 32 := 0x0116a223.
Lemma F_d46f4 : fetch_word AsanUbsan.M.loaded_segments (0xd46f4 : word) = Some W_d46f4.
Proof. vm_refl. Qed.
Lemma D_d46f4 : decode_any W_d46f4 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46f8 : bv 32 := 0x0056a423.
Lemma F_d46f8 : fetch_word AsanUbsan.M.loaded_segments (0xd46f8 : word) = Some W_d46f8.
Proof. vm_refl. Qed.
Lemma D_d46f8 : decode_any W_d46f8 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d46fc : bv 32 := 0x0066a623.
Lemma F_d46fc : fetch_word AsanUbsan.M.loaded_segments (0xd46fc : word) = Some W_d46fc.
Proof. vm_refl. Qed.
Lemma D_d46fc : decode_any W_d46fc = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4700 : bv 32 := 0x01068693.
Lemma F_d4700 : fetch_word AsanUbsan.M.loaded_segments (0xd4700 : word) = Some W_d4700.
Proof. vm_refl. Qed.
Lemma D_d4700 : decode_any W_d4700 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4704 : bv 32 := 0x01058593.
Lemma F_d4704 : fetch_word AsanUbsan.M.loaded_segments (0xd4704 : word) = Some W_d4704.
Proof. vm_refl. Qed.
Lemma D_d4704 : decode_any W_d4704 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4708 : bv 32 := 0xfac7e2e3.
Lemma F_d4708 : fetch_word AsanUbsan.M.loaded_segments (0xd4708 : word) = Some W_d4708.
Proof. vm_refl. Qed.
Lemma D_d4708 : decode_any W_d4708 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d470c : bv 32 := 0xff158593.
Lemma F_d470c : fetch_word AsanUbsan.M.loaded_segments (0xd470c : word) = Some W_d470c.
Proof. vm_refl. Qed.
Lemma D_d470c : decode_any W_d470c = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4710 : bv 32 := 0x01000713.
Lemma F_d4710 : fetch_word AsanUbsan.M.loaded_segments (0xd4710 : word) = Some W_d4710.
Proof. vm_refl. Qed.
Lemma D_d4710 : decode_any W_d4710 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4714 : bv 32 := 0xe4e666e3.
Lemma F_d4714 : fetch_word AsanUbsan.M.loaded_segments (0xd4714 : word) = Some W_d4714.
Proof. vm_refl. Qed.
Lemma D_d4714 : decode_any W_d4714 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4718 : bv 32 := 0x0940006f.
Lemma F_d4718 : fetch_word AsanUbsan.M.loaded_segments (0xd4718 : word) = Some W_d4718.
Proof. vm_refl. Qed.
Lemma D_d4718 : decode_any W_d4718 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d471c : bv 32 := 0x00875793.
Lemma F_d471c : fetch_word AsanUbsan.M.loaded_segments (0xd471c : word) = Some W_d471c.
Proof. vm_refl. Qed.
Lemma D_d471c : decode_any W_d471c = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4720 : bv 32 := 0x01075813.
Lemma F_d4720 : fetch_word AsanUbsan.M.loaded_segments (0xd4720 : word) = Some W_d4720.
Proof. vm_refl. Qed.
Lemma D_d4720 : decode_any W_d4720 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4724 : bv 32 := 0xffd60613.
Lemma F_d4724 : fetch_word AsanUbsan.M.loaded_segments (0xd4724 : word) = Some W_d4724.
Proof. vm_refl. Qed.
Lemma D_d4724 : decode_any W_d4724 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4728 : bv 32 := 0x00e68023.
Lemma F_d4728 : fetch_word AsanUbsan.M.loaded_segments (0xd4728 : word) = Some W_d4728.
Proof. vm_refl. Qed.
Lemma D_d4728 : decode_any W_d4728 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d472c : bv 32 := 0x00f680a3.
Lemma F_d472c : fetch_word AsanUbsan.M.loaded_segments (0xd472c : word) = Some W_d472c.
Proof. vm_refl. Qed.
Lemma D_d472c : decode_any W_d472c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4730 : bv 32 := 0x01068123.
Lemma F_d4730 : fetch_word AsanUbsan.M.loaded_segments (0xd4730 : word) = Some W_d4730.
Proof. vm_refl. Qed.
Lemma D_d4730 : decode_any W_d4730 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4734 : bv 32 := 0x00368693.
Lemma F_d4734 : fetch_word AsanUbsan.M.loaded_segments (0xd4734 : word) = Some W_d4734.
Proof. vm_refl. Qed.
Lemma D_d4734 : decode_any W_d4734 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4738 : bv 32 := 0x01058593.
Lemma F_d4738 : fetch_word AsanUbsan.M.loaded_segments (0xd4738 : word) = Some W_d4738.
Proof. vm_refl. Qed.
Lemma D_d4738 : decode_any W_d4738 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d473c : bv 32 := 0x01000793.
Lemma F_d473c : fetch_word AsanUbsan.M.loaded_segments (0xd473c : word) = Some W_d473c.
Proof. vm_refl. Qed.
Lemma D_d473c : decode_any W_d473c = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4740 : bv 32 := 0x0187581b.
Lemma F_d4740 : fetch_word AsanUbsan.M.loaded_segments (0xd4740 : word) = Some W_d4740.
Proof. vm_refl. Qed.
Lemma D_d4740 : decode_any W_d4740 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4744 : bv 32 := 0xff45a883.
Lemma F_d4744 : fetch_word AsanUbsan.M.loaded_segments (0xd4744 : word) = Some W_d4744.
Proof. vm_refl. Qed.
Lemma D_d4744 : decode_any W_d4744 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4748 : bv 32 := 0xff85a283.
Lemma F_d4748 : fetch_word AsanUbsan.M.loaded_segments (0xd4748 : word) = Some W_d4748.
Proof. vm_refl. Qed.
Lemma D_d4748 : decode_any W_d4748 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d474c : bv 32 := 0xffc5a303.
Lemma F_d474c : fetch_word AsanUbsan.M.loaded_segments (0xd474c : word) = Some W_d474c.
Proof. vm_refl. Qed.
Lemma D_d474c : decode_any W_d474c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4750 : bv 32 := 0x0005a703.
Lemma F_d4750 : fetch_word AsanUbsan.M.loaded_segments (0xd4750 : word) = Some W_d4750.
Proof. vm_refl. Qed.
Lemma D_d4750 : decode_any W_d4750 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4754 : bv 32 := 0x00889393.
Lemma F_d4754 : fetch_word AsanUbsan.M.loaded_segments (0xd4754 : word) = Some W_d4754.
Proof. vm_refl. Qed.
Lemma D_d4754 : decode_any W_d4754 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4758 : bv 32 := 0x0188d89b.
Lemma F_d4758 : fetch_word AsanUbsan.M.loaded_segments (0xd4758 : word) = Some W_d4758.
Proof. vm_refl. Qed.
Lemma D_d4758 : decode_any W_d4758 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d475c : bv 32 := 0x0103e833.
Lemma F_d475c : fetch_word AsanUbsan.M.loaded_segments (0xd475c : word) = Some W_d475c.
Proof. vm_refl. Qed.
Lemma D_d475c : decode_any W_d475c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4760 : bv 32 := 0x00829393.
Lemma F_d4760 : fetch_word AsanUbsan.M.loaded_segments (0xd4760 : word) = Some W_d4760.
Proof. vm_refl. Qed.
Lemma D_d4760 : decode_any W_d4760 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4764 : bv 32 := 0x0182d29b.
Lemma F_d4764 : fetch_word AsanUbsan.M.loaded_segments (0xd4764 : word) = Some W_d4764.
Proof. vm_refl. Qed.
Lemma D_d4764 : decode_any W_d4764 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4768 : bv 32 := 0x0113e8b3.
Lemma F_d4768 : fetch_word AsanUbsan.M.loaded_segments (0xd4768 : word) = Some W_d4768.
Proof. vm_refl. Qed.
Lemma D_d4768 : decode_any W_d4768 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d476c : bv 32 := 0x00831393.
Lemma F_d476c : fetch_word AsanUbsan.M.loaded_segments (0xd476c : word) = Some W_d476c.
Proof. vm_refl. Qed.
Lemma D_d476c : decode_any W_d476c = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4770 : bv 32 := 0x0183531b.
Lemma F_d4770 : fetch_word AsanUbsan.M.loaded_segments (0xd4770 : word) = Some W_d4770.
Proof. vm_refl. Qed.
Lemma D_d4770 : decode_any W_d4770 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4774 : bv 32 := 0x0053e2b3.
Lemma F_d4774 : fetch_word AsanUbsan.M.loaded_segments (0xd4774 : word) = Some W_d4774.
Proof. vm_refl. Qed.
Lemma D_d4774 : decode_any W_d4774 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4778 : bv 32 := 0x00871393.
Lemma F_d4778 : fetch_word AsanUbsan.M.loaded_segments (0xd4778 : word) = Some W_d4778.
Proof. vm_refl. Qed.
Lemma D_d4778 : decode_any W_d4778 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d477c : bv 32 := 0x0063e333.
Lemma F_d477c : fetch_word AsanUbsan.M.loaded_segments (0xd477c : word) = Some W_d477c.
Proof. vm_refl. Qed.
Lemma D_d477c : decode_any W_d477c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4780 : bv 32 := 0xff060613.
Lemma F_d4780 : fetch_word AsanUbsan.M.loaded_segments (0xd4780 : word) = Some W_d4780.
Proof. vm_refl. Qed.
Lemma D_d4780 : decode_any W_d4780 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4784 : bv 32 := 0x0106a023.
Lemma F_d4784 : fetch_word AsanUbsan.M.loaded_segments (0xd4784 : word) = Some W_d4784.
Proof. vm_refl. Qed.
Lemma D_d4784 : decode_any W_d4784 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4788 : bv 32 := 0x0116a223.
Lemma F_d4788 : fetch_word AsanUbsan.M.loaded_segments (0xd4788 : word) = Some W_d4788.
Proof. vm_refl. Qed.
Lemma D_d4788 : decode_any W_d4788 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d478c : bv 32 := 0x0056a423.
Lemma F_d478c : fetch_word AsanUbsan.M.loaded_segments (0xd478c : word) = Some W_d478c.
Proof. vm_refl. Qed.
Lemma D_d478c : decode_any W_d478c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4790 : bv 32 := 0x0066a623.
Lemma F_d4790 : fetch_word AsanUbsan.M.loaded_segments (0xd4790 : word) = Some W_d4790.
Proof. vm_refl. Qed.
Lemma D_d4790 : decode_any W_d4790 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4794 : bv 32 := 0x01068693.
Lemma F_d4794 : fetch_word AsanUbsan.M.loaded_segments (0xd4794 : word) = Some W_d4794.
Proof. vm_refl. Qed.
Lemma D_d4794 : decode_any W_d4794 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4798 : bv 32 := 0x01058593.
Lemma F_d4798 : fetch_word AsanUbsan.M.loaded_segments (0xd4798 : word) = Some W_d4798.
Proof. vm_refl. Qed.
Lemma D_d4798 : decode_any W_d4798 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d479c : bv 32 := 0xfac7e2e3.
Lemma F_d479c : fetch_word AsanUbsan.M.loaded_segments (0xd479c : word) = Some W_d479c.
Proof. vm_refl. Qed.
Lemma D_d479c : decode_any W_d479c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47a0 : bv 32 := 0xff358593.
Lemma F_d47a0 : fetch_word AsanUbsan.M.loaded_segments (0xd47a0 : word) = Some W_d47a0.
Proof. vm_refl. Qed.
Lemma D_d47a0 : decode_any W_d47a0 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47a4 : bv 32 := 0x01000713.
Lemma F_d47a4 : fetch_word AsanUbsan.M.loaded_segments (0xd47a4 : word) = Some W_d47a4.
Proof. vm_refl. Qed.
Lemma D_d47a4 : decode_any W_d47a4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47a8 : bv 32 := 0xdae66ce3.
Lemma F_d47a8 : fetch_word AsanUbsan.M.loaded_segments (0xd47a8 : word) = Some W_d47a8.
Proof. vm_refl. Qed.
Lemma D_d47a8 : decode_any W_d47a8 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47ac : bv 32 := 0x0005c703.
Lemma F_d47ac : fetch_word AsanUbsan.M.loaded_segments (0xd47ac : word) = Some W_d47ac.
Proof. vm_refl. Qed.
Lemma D_d47ac : decode_any W_d47ac = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47b0 : bv 32 := 0x0015c783.
Lemma F_d47b0 : fetch_word AsanUbsan.M.loaded_segments (0xd47b0 : word) = Some W_d47b0.
Proof. vm_refl. Qed.
Lemma D_d47b0 : decode_any W_d47b0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47b4 : bv 32 := 0x0025c803.
Lemma F_d47b4 : fetch_word AsanUbsan.M.loaded_segments (0xd47b4 : word) = Some W_d47b4.
Proof. vm_refl. Qed.
Lemma D_d47b4 : decode_any W_d47b4 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47b8 : bv 32 := 0x0035c883.
Lemma F_d47b8 : fetch_word AsanUbsan.M.loaded_segments (0xd47b8 : word) = Some W_d47b8.
Proof. vm_refl. Qed.
Lemma D_d47b8 : decode_any W_d47b8 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47bc : bv 32 := 0x0045c283.
Lemma F_d47bc : fetch_word AsanUbsan.M.loaded_segments (0xd47bc : word) = Some W_d47bc.
Proof. vm_refl. Qed.
Lemma D_d47bc : decode_any W_d47bc = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47c0 : bv 32 := 0x0055c303.
Lemma F_d47c0 : fetch_word AsanUbsan.M.loaded_segments (0xd47c0 : word) = Some W_d47c0.
Proof. vm_refl. Qed.
Lemma D_d47c0 : decode_any W_d47c0 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47c4 : bv 32 := 0x0065c383.
Lemma F_d47c4 : fetch_word AsanUbsan.M.loaded_segments (0xd47c4 : word) = Some W_d47c4.
Proof. vm_refl. Qed.
Lemma D_d47c4 : decode_any W_d47c4 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47c8 : bv 32 := 0x0075ce03.
Lemma F_d47c8 : fetch_word AsanUbsan.M.loaded_segments (0xd47c8 : word) = Some W_d47c8.
Proof. vm_refl. Qed.
Lemma D_d47c8 : decode_any W_d47c8 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47cc : bv 32 := 0x00e68023.
Lemma F_d47cc : fetch_word AsanUbsan.M.loaded_segments (0xd47cc : word) = Some W_d47cc.
Proof. vm_refl. Qed.
Lemma D_d47cc : decode_any W_d47cc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47d0 : bv 32 := 0x00f680a3.
Lemma F_d47d0 : fetch_word AsanUbsan.M.loaded_segments (0xd47d0 : word) = Some W_d47d0.
Proof. vm_refl. Qed.
Lemma D_d47d0 : decode_any W_d47d0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47d4 : bv 32 := 0x01068123.
Lemma F_d47d4 : fetch_word AsanUbsan.M.loaded_segments (0xd47d4 : word) = Some W_d47d4.
Proof. vm_refl. Qed.
Lemma D_d47d4 : decode_any W_d47d4 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47d8 : bv 32 := 0x011681a3.
Lemma F_d47d8 : fetch_word AsanUbsan.M.loaded_segments (0xd47d8 : word) = Some W_d47d8.
Proof. vm_refl. Qed.
Lemma D_d47d8 : decode_any W_d47d8 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47dc : bv 32 := 0x0085c703.
Lemma F_d47dc : fetch_word AsanUbsan.M.loaded_segments (0xd47dc : word) = Some W_d47dc.
Proof. vm_refl. Qed.
Lemma D_d47dc : decode_any W_d47dc = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47e0 : bv 32 := 0x0095c783.
Lemma F_d47e0 : fetch_word AsanUbsan.M.loaded_segments (0xd47e0 : word) = Some W_d47e0.
Proof. vm_refl. Qed.
Lemma D_d47e0 : decode_any W_d47e0 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47e4 : bv 32 := 0x00a5c803.
Lemma F_d47e4 : fetch_word AsanUbsan.M.loaded_segments (0xd47e4 : word) = Some W_d47e4.
Proof. vm_refl. Qed.
Lemma D_d47e4 : decode_any W_d47e4 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47e8 : bv 32 := 0x00b5c883.
Lemma F_d47e8 : fetch_word AsanUbsan.M.loaded_segments (0xd47e8 : word) = Some W_d47e8.
Proof. vm_refl. Qed.
Lemma D_d47e8 : decode_any W_d47e8 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47ec : bv 32 := 0x00568223.
Lemma F_d47ec : fetch_word AsanUbsan.M.loaded_segments (0xd47ec : word) = Some W_d47ec.
Proof. vm_refl. Qed.
Lemma D_d47ec : decode_any W_d47ec = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47f0 : bv 32 := 0x006682a3.
Lemma F_d47f0 : fetch_word AsanUbsan.M.loaded_segments (0xd47f0 : word) = Some W_d47f0.
Proof. vm_refl. Qed.
Lemma D_d47f0 : decode_any W_d47f0 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47f4 : bv 32 := 0x00768323.
Lemma F_d47f4 : fetch_word AsanUbsan.M.loaded_segments (0xd47f4 : word) = Some W_d47f4.
Proof. vm_refl. Qed.
Lemma D_d47f4 : decode_any W_d47f4 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47f8 : bv 32 := 0x01c683a3.
Lemma F_d47f8 : fetch_word AsanUbsan.M.loaded_segments (0xd47f8 : word) = Some W_d47f8.
Proof. vm_refl. Qed.
Lemma D_d47f8 : decode_any W_d47f8 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d47fc : bv 32 := 0x00c5c283.
Lemma F_d47fc : fetch_word AsanUbsan.M.loaded_segments (0xd47fc : word) = Some W_d47fc.
Proof. vm_refl. Qed.
Lemma D_d47fc : decode_any W_d47fc = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4800 : bv 32 := 0x00d5c303.
Lemma F_d4800 : fetch_word AsanUbsan.M.loaded_segments (0xd4800 : word) = Some W_d4800.
Proof. vm_refl. Qed.
Lemma D_d4800 : decode_any W_d4800 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4804 : bv 32 := 0x00e5c383.
Lemma F_d4804 : fetch_word AsanUbsan.M.loaded_segments (0xd4804 : word) = Some W_d4804.
Proof. vm_refl. Qed.
Lemma D_d4804 : decode_any W_d4804 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4808 : bv 32 := 0x00f5ce03.
Lemma F_d4808 : fetch_word AsanUbsan.M.loaded_segments (0xd4808 : word) = Some W_d4808.
Proof. vm_refl. Qed.
Lemma D_d4808 : decode_any W_d4808 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d480c : bv 32 := 0x01058593.
Lemma F_d480c : fetch_word AsanUbsan.M.loaded_segments (0xd480c : word) = Some W_d480c.
Proof. vm_refl. Qed.
Lemma D_d480c : decode_any W_d480c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4810 : bv 32 := 0x00e68423.
Lemma F_d4810 : fetch_word AsanUbsan.M.loaded_segments (0xd4810 : word) = Some W_d4810.
Proof. vm_refl. Qed.
Lemma D_d4810 : decode_any W_d4810 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4814 : bv 32 := 0x00f684a3.
Lemma F_d4814 : fetch_word AsanUbsan.M.loaded_segments (0xd4814 : word) = Some W_d4814.
Proof. vm_refl. Qed.
Lemma D_d4814 : decode_any W_d4814 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4818 : bv 32 := 0x01068523.
Lemma F_d4818 : fetch_word AsanUbsan.M.loaded_segments (0xd4818 : word) = Some W_d4818.
Proof. vm_refl. Qed.
Lemma D_d4818 : decode_any W_d4818 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d481c : bv 32 := 0x011685a3.
Lemma F_d481c : fetch_word AsanUbsan.M.loaded_segments (0xd481c : word) = Some W_d481c.
Proof. vm_refl. Qed.
Lemma D_d481c : decode_any W_d481c = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4820 : bv 32 := 0x01068713.
Lemma F_d4820 : fetch_word AsanUbsan.M.loaded_segments (0xd4820 : word) = Some W_d4820.
Proof. vm_refl. Qed.
Lemma D_d4820 : decode_any W_d4820 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4824 : bv 32 := 0x00568623.
Lemma F_d4824 : fetch_word AsanUbsan.M.loaded_segments (0xd4824 : word) = Some W_d4824.
Proof. vm_refl. Qed.
Lemma D_d4824 : decode_any W_d4824 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4828 : bv 32 := 0x006686a3.
Lemma F_d4828 : fetch_word AsanUbsan.M.loaded_segments (0xd4828 : word) = Some W_d4828.
Proof. vm_refl. Qed.
Lemma D_d4828 : decode_any W_d4828 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d482c : bv 32 := 0x00768723.
Lemma F_d482c : fetch_word AsanUbsan.M.loaded_segments (0xd482c : word) = Some W_d482c.
Proof. vm_refl. Qed.
Lemma D_d482c : decode_any W_d482c = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4830 : bv 32 := 0x01c687a3.
Lemma F_d4830 : fetch_word AsanUbsan.M.loaded_segments (0xd4830 : word) = Some W_d4830.
Proof. vm_refl. Qed.
Lemma D_d4830 : decode_any W_d4830 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4834 : bv 32 := 0x00070693.
Lemma F_d4834 : fetch_word AsanUbsan.M.loaded_segments (0xd4834 : word) = Some W_d4834.
Proof. vm_refl. Qed.
Lemma D_d4834 : decode_any W_d4834 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4838 : bv 32 := 0x00867713.
Lemma F_d4838 : fetch_word AsanUbsan.M.loaded_segments (0xd4838 : word) = Some W_d4838.
Proof. vm_refl. Qed.
Lemma D_d4838 : decode_any W_d4838 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d483c : bv 32 := 0xd20706e3.
Lemma F_d483c : fetch_word AsanUbsan.M.loaded_segments (0xd483c : word) = Some W_d483c.
Proof. vm_refl. Qed.
Lemma D_d483c : decode_any W_d483c = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4840 : bv 32 := 0x0005c703.
Lemma F_d4840 : fetch_word AsanUbsan.M.loaded_segments (0xd4840 : word) = Some W_d4840.
Proof. vm_refl. Qed.
Lemma D_d4840 : decode_any W_d4840 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4844 : bv 32 := 0x0015c783.
Lemma F_d4844 : fetch_word AsanUbsan.M.loaded_segments (0xd4844 : word) = Some W_d4844.
Proof. vm_refl. Qed.
Lemma D_d4844 : decode_any W_d4844 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4848 : bv 32 := 0x0025c803.
Lemma F_d4848 : fetch_word AsanUbsan.M.loaded_segments (0xd4848 : word) = Some W_d4848.
Proof. vm_refl. Qed.
Lemma D_d4848 : decode_any W_d4848 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d484c : bv 32 := 0x0035c883.
Lemma F_d484c : fetch_word AsanUbsan.M.loaded_segments (0xd484c : word) = Some W_d484c.
Proof. vm_refl. Qed.
Lemma D_d484c : decode_any W_d484c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4850 : bv 32 := 0x0045c283.
Lemma F_d4850 : fetch_word AsanUbsan.M.loaded_segments (0xd4850 : word) = Some W_d4850.
Proof. vm_refl. Qed.
Lemma D_d4850 : decode_any W_d4850 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4854 : bv 32 := 0x0055c303.
Lemma F_d4854 : fetch_word AsanUbsan.M.loaded_segments (0xd4854 : word) = Some W_d4854.
Proof. vm_refl. Qed.
Lemma D_d4854 : decode_any W_d4854 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4858 : bv 32 := 0x0065c383.
Lemma F_d4858 : fetch_word AsanUbsan.M.loaded_segments (0xd4858 : word) = Some W_d4858.
Proof. vm_refl. Qed.
Lemma D_d4858 : decode_any W_d4858 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d485c : bv 32 := 0x0075ce03.
Lemma F_d485c : fetch_word AsanUbsan.M.loaded_segments (0xd485c : word) = Some W_d485c.
Proof. vm_refl. Qed.
Lemma D_d485c : decode_any W_d485c = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4860 : bv 32 := 0x00858593.
Lemma F_d4860 : fetch_word AsanUbsan.M.loaded_segments (0xd4860 : word) = Some W_d4860.
Proof. vm_refl. Qed.
Lemma D_d4860 : decode_any W_d4860 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4864 : bv 32 := 0x00e68023.
Lemma F_d4864 : fetch_word AsanUbsan.M.loaded_segments (0xd4864 : word) = Some W_d4864.
Proof. vm_refl. Qed.
Lemma D_d4864 : decode_any W_d4864 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4868 : bv 32 := 0x00f680a3.
Lemma F_d4868 : fetch_word AsanUbsan.M.loaded_segments (0xd4868 : word) = Some W_d4868.
Proof. vm_refl. Qed.
Lemma D_d4868 : decode_any W_d4868 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d486c : bv 32 := 0x01068123.
Lemma F_d486c : fetch_word AsanUbsan.M.loaded_segments (0xd486c : word) = Some W_d486c.
Proof. vm_refl. Qed.
Lemma D_d486c : decode_any W_d486c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4870 : bv 32 := 0x011681a3.
Lemma F_d4870 : fetch_word AsanUbsan.M.loaded_segments (0xd4870 : word) = Some W_d4870.
Proof. vm_refl. Qed.
Lemma D_d4870 : decode_any W_d4870 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4874 : bv 32 := 0x00868713.
Lemma F_d4874 : fetch_word AsanUbsan.M.loaded_segments (0xd4874 : word) = Some W_d4874.
Proof. vm_refl. Qed.
Lemma D_d4874 : decode_any W_d4874 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4878 : bv 32 := 0x00568223.
Lemma F_d4878 : fetch_word AsanUbsan.M.loaded_segments (0xd4878 : word) = Some W_d4878.
Proof. vm_refl. Qed.
Lemma D_d4878 : decode_any W_d4878 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d487c : bv 32 := 0x006682a3.
Lemma F_d487c : fetch_word AsanUbsan.M.loaded_segments (0xd487c : word) = Some W_d487c.
Proof. vm_refl. Qed.
Lemma D_d487c : decode_any W_d487c = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4880 : bv 32 := 0x00768323.
Lemma F_d4880 : fetch_word AsanUbsan.M.loaded_segments (0xd4880 : word) = Some W_d4880.
Proof. vm_refl. Qed.
Lemma D_d4880 : decode_any W_d4880 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4884 : bv 32 := 0x01c683a3.
Lemma F_d4884 : fetch_word AsanUbsan.M.loaded_segments (0xd4884 : word) = Some W_d4884.
Proof. vm_refl. Qed.
Lemma D_d4884 : decode_any W_d4884 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4888 : bv 32 := 0x00070693.
Lemma F_d4888 : fetch_word AsanUbsan.M.loaded_segments (0xd4888 : word) = Some W_d4888.
Proof. vm_refl. Qed.
Lemma D_d4888 : decode_any W_d4888 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d488c : bv 32 := 0x00467713.
Lemma F_d488c : fetch_word AsanUbsan.M.loaded_segments (0xd488c : word) = Some W_d488c.
Proof. vm_refl. Qed.
Lemma D_d488c : decode_any W_d488c = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4890 : bv 32 := 0x02070863.
Lemma F_d4890 : fetch_word AsanUbsan.M.loaded_segments (0xd4890 : word) = Some W_d4890.
Proof. vm_refl. Qed.
Lemma D_d4890 : decode_any W_d4890 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4894 : bv 32 := 0x0005c703.
Lemma F_d4894 : fetch_word AsanUbsan.M.loaded_segments (0xd4894 : word) = Some W_d4894.
Proof. vm_refl. Qed.
Lemma D_d4894 : decode_any W_d4894 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4898 : bv 32 := 0x0015c783.
Lemma F_d4898 : fetch_word AsanUbsan.M.loaded_segments (0xd4898 : word) = Some W_d4898.
Proof. vm_refl. Qed.
Lemma D_d4898 : decode_any W_d4898 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d489c : bv 32 := 0x0025c803.
Lemma F_d489c : fetch_word AsanUbsan.M.loaded_segments (0xd489c : word) = Some W_d489c.
Proof. vm_refl. Qed.
Lemma D_d489c : decode_any W_d489c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48a0 : bv 32 := 0x0035c883.
Lemma F_d48a0 : fetch_word AsanUbsan.M.loaded_segments (0xd48a0 : word) = Some W_d48a0.
Proof. vm_refl. Qed.
Lemma D_d48a0 : decode_any W_d48a0 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48a4 : bv 32 := 0x00458593.
Lemma F_d48a4 : fetch_word AsanUbsan.M.loaded_segments (0xd48a4 : word) = Some W_d48a4.
Proof. vm_refl. Qed.
Lemma D_d48a4 : decode_any W_d48a4 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48a8 : bv 32 := 0x00468293.
Lemma F_d48a8 : fetch_word AsanUbsan.M.loaded_segments (0xd48a8 : word) = Some W_d48a8.
Proof. vm_refl. Qed.
Lemma D_d48a8 : decode_any W_d48a8 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48ac : bv 32 := 0x00e68023.
Lemma F_d48ac : fetch_word AsanUbsan.M.loaded_segments (0xd48ac : word) = Some W_d48ac.
Proof. vm_refl. Qed.
Lemma D_d48ac : decode_any W_d48ac = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48b0 : bv 32 := 0x00f680a3.
Lemma F_d48b0 : fetch_word AsanUbsan.M.loaded_segments (0xd48b0 : word) = Some W_d48b0.
Proof. vm_refl. Qed.
Lemma D_d48b0 : decode_any W_d48b0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48b4 : bv 32 := 0x01068123.
Lemma F_d48b4 : fetch_word AsanUbsan.M.loaded_segments (0xd48b4 : word) = Some W_d48b4.
Proof. vm_refl. Qed.
Lemma D_d48b4 : decode_any W_d48b4 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48b8 : bv 32 := 0x011681a3.
Lemma F_d48b8 : fetch_word AsanUbsan.M.loaded_segments (0xd48b8 : word) = Some W_d48b8.
Proof. vm_refl. Qed.
Lemma D_d48b8 : decode_any W_d48b8 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48bc : bv 32 := 0x00028693.
Lemma F_d48bc : fetch_word AsanUbsan.M.loaded_segments (0xd48bc : word) = Some W_d48bc.
Proof. vm_refl. Qed.
Lemma D_d48bc : decode_any W_d48bc = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48c0 : bv 32 := 0x00267713.
Lemma F_d48c0 : fetch_word AsanUbsan.M.loaded_segments (0xd48c0 : word) = Some W_d48c0.
Proof. vm_refl. Qed.
Lemma D_d48c0 : decode_any W_d48c0 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48c4 : bv 32 := 0x00071863.
Lemma F_d48c4 : fetch_word AsanUbsan.M.loaded_segments (0xd48c4 : word) = Some W_d48c4.
Proof. vm_refl. Qed.
Lemma D_d48c4 : decode_any W_d48c4 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48c8 : bv 32 := 0x00167613.
Lemma F_d48c8 : fetch_word AsanUbsan.M.loaded_segments (0xd48c8 : word) = Some W_d48c8.
Proof. vm_refl. Qed.
Lemma D_d48c8 : decode_any W_d48c8 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48cc : bv 32 := 0x02061663.
Lemma F_d48cc : fetch_word AsanUbsan.M.loaded_segments (0xd48cc : word) = Some W_d48cc.
Proof. vm_refl. Qed.
Lemma D_d48cc : decode_any W_d48cc = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48d0 : bv 32 := 0x00008067.
Lemma F_d48d0 : fetch_word AsanUbsan.M.loaded_segments (0xd48d0 : word) = Some W_d48d0.
Proof. vm_refl. Qed.
Lemma D_d48d0 : decode_any W_d48d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48d4 : bv 32 := 0x0005c703.
Lemma F_d48d4 : fetch_word AsanUbsan.M.loaded_segments (0xd48d4 : word) = Some W_d48d4.
Proof. vm_refl. Qed.
Lemma D_d48d4 : decode_any W_d48d4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48d8 : bv 32 := 0x0015c783.
Lemma F_d48d8 : fetch_word AsanUbsan.M.loaded_segments (0xd48d8 : word) = Some W_d48d8.
Proof. vm_refl. Qed.
Lemma D_d48d8 : decode_any W_d48d8 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48dc : bv 32 := 0x00258593.
Lemma F_d48dc : fetch_word AsanUbsan.M.loaded_segments (0xd48dc : word) = Some W_d48dc.
Proof. vm_refl. Qed.
Lemma D_d48dc : decode_any W_d48dc = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48e0 : bv 32 := 0x00268813.
Lemma F_d48e0 : fetch_word AsanUbsan.M.loaded_segments (0xd48e0 : word) = Some W_d48e0.
Proof. vm_refl. Qed.
Lemma D_d48e0 : decode_any W_d48e0 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48e4 : bv 32 := 0x00e68023.
Lemma F_d48e4 : fetch_word AsanUbsan.M.loaded_segments (0xd48e4 : word) = Some W_d48e4.
Proof. vm_refl. Qed.
Lemma D_d48e4 : decode_any W_d48e4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48e8 : bv 32 := 0x00f680a3.
Lemma F_d48e8 : fetch_word AsanUbsan.M.loaded_segments (0xd48e8 : word) = Some W_d48e8.
Proof. vm_refl. Qed.
Lemma D_d48e8 : decode_any W_d48e8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48ec : bv 32 := 0x00080693.
Lemma F_d48ec : fetch_word AsanUbsan.M.loaded_segments (0xd48ec : word) = Some W_d48ec.
Proof. vm_refl. Qed.
Lemma D_d48ec : decode_any W_d48ec = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48f0 : bv 32 := 0x00167613.
Lemma F_d48f0 : fetch_word AsanUbsan.M.loaded_segments (0xd48f0 : word) = Some W_d48f0.
Proof. vm_refl. Qed.
Lemma D_d48f0 : decode_any W_d48f0 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48f4 : bv 32 := 0xfc060ee3.
Lemma F_d48f4 : fetch_word AsanUbsan.M.loaded_segments (0xd48f4 : word) = Some W_d48f4.
Proof. vm_refl. Qed.
Lemma D_d48f4 : decode_any W_d48f4 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48f8 : bv 32 := 0x0005c583.
Lemma F_d48f8 : fetch_word AsanUbsan.M.loaded_segments (0xd48f8 : word) = Some W_d48f8.
Proof. vm_refl. Qed.
Lemma D_d48f8 : decode_any W_d48f8 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d48fc : bv 32 := 0x00b68023.
Lemma F_d48fc : fetch_word AsanUbsan.M.loaded_segments (0xd48fc : word) = Some W_d48fc.
Proof. vm_refl. Qed.
Lemma D_d48fc : decode_any W_d48fc = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d4900 : bv 32 := 0x00008067.
Lemma F_d4900 : fetch_word AsanUbsan.M.loaded_segments (0xd4900 : word) = Some W_d4900.
Proof. vm_refl. Qed.
Lemma D_d4900 : decode_any W_d4900 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
