(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl_bd :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
(* [comment removed for export] *)
Lemma cl_fetch_bd : forall segs (a : word) (w : bv 32), bool_decide (fetch_word segs a = Some w) = true -> fetch_word segs a = Some w.
Proof. intros segs a w. apply bool_decide_eq_true_1. Qed.
Lemma cl_decode_bd : forall (w : bv 32) x, bool_decide (decode_any w = Some x) = true -> decode_any w = Some x.
Proof. intros w x. apply bool_decide_eq_true_1. Qed.
Local Ltac vm_refl := first [ apply cl_fetch_bd; vm_cast_no_check (@eq_refl bool true)
                            | apply cl_decode_bd; vm_cast_no_check (@eq_refl bool true)
                            | vm_refl_bd ].

(* [comment removed for export] *)
Definition W_d84fc : bv 32 := 0x0e060a63.
Lemma F_d84fc : fetch_word Asan.M.loaded_segments (0xd874c : word) = Some W_d84fc.
Proof. vm_refl. Qed.
Lemma D_d84fc : decode_any W_d84fc = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8500 : bv 32 := 0x00b50023.
Lemma F_d8500 : fetch_word Asan.M.loaded_segments (0xd8750 : word) = Some W_d8500.
Proof. vm_refl. Qed.
Lemma D_d8500 : decode_any W_d8500 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8504 : bv 32 := 0x00c506b3.
Lemma F_d8504 : fetch_word Asan.M.loaded_segments (0xd8754 : word) = Some W_d8504.
Proof. vm_refl. Qed.
Lemma D_d8504 : decode_any W_d8504 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8508 : bv 32 := 0x00300713.
Lemma F_d8508 : fetch_word Asan.M.loaded_segments (0xd8758 : word) = Some W_d8508.
Proof. vm_refl. Qed.
Lemma D_d8508 : decode_any W_d8508 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d850c : bv 32 := 0xfeb68fa3.
Lemma F_d850c : fetch_word Asan.M.loaded_segments (0xd875c : word) = Some W_d850c.
Proof. vm_refl. Qed.
Lemma D_d850c : decode_any W_d850c = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8510 : bv 32 := 0x0ee66063.
Lemma F_d8510 : fetch_word Asan.M.loaded_segments (0xd8760 : word) = Some W_d8510.
Proof. vm_refl. Qed.
Lemma D_d8510 : decode_any W_d8510 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8514 : bv 32 := 0x00b500a3.
Lemma F_d8514 : fetch_word Asan.M.loaded_segments (0xd8764 : word) = Some W_d8514.
Proof. vm_refl. Qed.
Lemma D_d8514 : decode_any W_d8514 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8518 : bv 32 := 0x00b50123.
Lemma F_d8518 : fetch_word Asan.M.loaded_segments (0xd8768 : word) = Some W_d8518.
Proof. vm_refl. Qed.
Lemma D_d8518 : decode_any W_d8518 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d851c : bv 32 := 0x00700713.
Lemma F_d851c : fetch_word Asan.M.loaded_segments (0xd876c : word) = Some W_d851c.
Proof. vm_refl. Qed.
Lemma D_d851c : decode_any W_d851c = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8520 : bv 32 := 0xfeb68ea3.
Lemma F_d8520 : fetch_word Asan.M.loaded_segments (0xd8770 : word) = Some W_d8520.
Proof. vm_refl. Qed.
Lemma D_d8520 : decode_any W_d8520 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8524 : bv 32 := 0xfeb68f23.
Lemma F_d8524 : fetch_word Asan.M.loaded_segments (0xd8774 : word) = Some W_d8524.
Proof. vm_refl. Qed.
Lemma D_d8524 : decode_any W_d8524 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8528 : bv 32 := 0x0ce66463.
Lemma F_d8528 : fetch_word Asan.M.loaded_segments (0xd8778 : word) = Some W_d8528.
Proof. vm_refl. Qed.
Lemma D_d8528 : decode_any W_d8528 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d852c : bv 32 := 0x00b501a3.
Lemma F_d852c : fetch_word Asan.M.loaded_segments (0xd877c : word) = Some W_d852c.
Proof. vm_refl. Qed.
Lemma D_d852c : decode_any W_d852c = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8530 : bv 32 := 0x00900793.
Lemma F_d8530 : fetch_word Asan.M.loaded_segments (0xd8780 : word) = Some W_d8530.
Proof. vm_refl. Qed.
Lemma D_d8530 : decode_any W_d8530 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8534 : bv 32 := 0xfeb68e23.
Lemma F_d8534 : fetch_word Asan.M.loaded_segments (0xd8784 : word) = Some W_d8534.
Proof. vm_refl. Qed.
Lemma D_d8534 : decode_any W_d8534 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8538 : bv 32 := 0x0af66c63.
Lemma F_d8538 : fetch_word Asan.M.loaded_segments (0xd8788 : word) = Some W_d8538.
Proof. vm_refl. Qed.
Lemma D_d8538 : decode_any W_d8538 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d853c : bv 32 := 0x40a006bb.
Lemma F_d853c : fetch_word Asan.M.loaded_segments (0xd878c : word) = Some W_d853c.
Proof. vm_refl. Qed.
Lemma D_d853c : decode_any W_d853c = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8540 : bv 32 := 0x03859813.
Lemma F_d8540 : fetch_word Asan.M.loaded_segments (0xd8790 : word) = Some W_d8540.
Proof. vm_refl. Qed.
Lemma D_d8540 : decode_any W_d8540 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8544 : bv 32 := 0x101015b7.
Lemma F_d8544 : fetch_word Asan.M.loaded_segments (0xd8794 : word) = Some W_d8544.
Proof. vm_refl. Qed.
Lemma D_d8544 : decode_any W_d8544 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8548 : bv 32 := 0x0036f693.
Lemma F_d8548 : fetch_word Asan.M.loaded_segments (0xd8798 : word) = Some W_d8548.
Proof. vm_refl. Qed.
Lemma D_d8548 : decode_any W_d8548 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d854c : bv 32 := 0x00459713.
Lemma F_d854c : fetch_word Asan.M.loaded_segments (0xd879c : word) = Some W_d854c.
Proof. vm_refl. Qed.
Lemma D_d854c : decode_any W_d854c = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8550 : bv 32 := 0x40d60633.
Lemma F_d8550 : fetch_word Asan.M.loaded_segments (0xd87a0 : word) = Some W_d8550.
Proof. vm_refl. Qed.
Lemma D_d8550 : decode_any W_d8550 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8554 : bv 32 := 0x00d505b3.
Lemma F_d8554 : fetch_word Asan.M.loaded_segments (0xd87a4 : word) = Some W_d8554.
Proof. vm_refl. Qed.
Lemma D_d8554 : decode_any W_d8554 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8558 : bv 32 := 0x10070693.
Lemma F_d8558 : fetch_word Asan.M.loaded_segments (0xd87a8 : word) = Some W_d8558.
Proof. vm_refl. Qed.
Lemma D_d8558 : decode_any W_d8558 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d855c : bv 32 := 0xffc67713.
Lemma F_d855c : fetch_word Asan.M.loaded_segments (0xd87ac : word) = Some W_d855c.
Proof. vm_refl. Qed.
Lemma D_d855c : decode_any W_d855c = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8560 : bv 32 := 0x02d83633.
Lemma F_d8560 : fetch_word Asan.M.loaded_segments (0xd87b0 : word) = Some W_d8560.
Proof. vm_refl. Qed.
Lemma D_d8560 : decode_any W_d8560 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8564 : bv 32 := 0x00c5a023.
Lemma F_d8564 : fetch_word Asan.M.loaded_segments (0xd87b4 : word) = Some W_d8564.
Proof. vm_refl. Qed.
Lemma D_d8564 : decode_any W_d8564 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8568 : bv 32 := 0x00e586b3.
Lemma F_d8568 : fetch_word Asan.M.loaded_segments (0xd87b8 : word) = Some W_d8568.
Proof. vm_refl. Qed.
Lemma D_d8568 : decode_any W_d8568 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d856c : bv 32 := 0xfec6ae23.
Lemma F_d856c : fetch_word Asan.M.loaded_segments (0xd87bc : word) = Some W_d856c.
Proof. vm_refl. Qed.
Lemma D_d856c : decode_any W_d856c = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8570 : bv 32 := 0x08f76063.
Lemma F_d8570 : fetch_word Asan.M.loaded_segments (0xd87c0 : word) = Some W_d8570.
Proof. vm_refl. Qed.
Lemma D_d8570 : decode_any W_d8570 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8574 : bv 32 := 0x00c5a223.
Lemma F_d8574 : fetch_word Asan.M.loaded_segments (0xd87c4 : word) = Some W_d8574.
Proof. vm_refl. Qed.
Lemma D_d8574 : decode_any W_d8574 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8578 : bv 32 := 0x00c5a423.
Lemma F_d8578 : fetch_word Asan.M.loaded_segments (0xd87c8 : word) = Some W_d8578.
Proof. vm_refl. Qed.
Lemma D_d8578 : decode_any W_d8578 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d857c : bv 32 := 0x01900793.
Lemma F_d857c : fetch_word Asan.M.loaded_segments (0xd87cc : word) = Some W_d857c.
Proof. vm_refl. Qed.
Lemma D_d857c : decode_any W_d857c = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8580 : bv 32 := 0xfec6aa23.
Lemma F_d8580 : fetch_word Asan.M.loaded_segments (0xd87d0 : word) = Some W_d8580.
Proof. vm_refl. Qed.
Lemma D_d8580 : decode_any W_d8580 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8584 : bv 32 := 0xfec6ac23.
Lemma F_d8584 : fetch_word Asan.M.loaded_segments (0xd87d4 : word) = Some W_d8584.
Proof. vm_refl. Qed.
Lemma D_d8584 : decode_any W_d8584 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8588 : bv 32 := 0x06f76463.
Lemma F_d8588 : fetch_word Asan.M.loaded_segments (0xd87d8 : word) = Some W_d8588.
Proof. vm_refl. Qed.
Lemma D_d8588 : decode_any W_d8588 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d858c : bv 32 := 0x00c5a623.
Lemma F_d858c : fetch_word Asan.M.loaded_segments (0xd87dc : word) = Some W_d858c.
Proof. vm_refl. Qed.
Lemma D_d858c : decode_any W_d858c = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8590 : bv 32 := 0x00c5a823.
Lemma F_d8590 : fetch_word Asan.M.loaded_segments (0xd87e0 : word) = Some W_d8590.
Proof. vm_refl. Qed.
Lemma D_d8590 : decode_any W_d8590 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8594 : bv 32 := 0x00c5aa23.
Lemma F_d8594 : fetch_word Asan.M.loaded_segments (0xd87e4 : word) = Some W_d8594.
Proof. vm_refl. Qed.
Lemma D_d8594 : decode_any W_d8594 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d8598 : bv 32 := 0x00c5ac23.
Lemma F_d8598 : fetch_word Asan.M.loaded_segments (0xd87e8 : word) = Some W_d8598.
Proof. vm_refl. Qed.
Lemma D_d8598 : decode_any W_d8598 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d859c : bv 32 := 0x0045f793.
Lemma F_d859c : fetch_word Asan.M.loaded_segments (0xd87ec : word) = Some W_d859c.
Proof. vm_refl. Qed.
Lemma D_d859c : decode_any W_d859c = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d85a0 : bv 32 := 0x02000813.
Lemma F_d85a0 : fetch_word Asan.M.loaded_segments (0xd87f0 : word) = Some W_d85a0.
Proof. vm_refl. Qed.
Lemma D_d85a0 : decode_any W_d85a0 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d85a4 : bv 32 := 0x01878793.
Lemma F_d85a4 : fetch_word Asan.M.loaded_segments (0xd87f4 : word) = Some W_d85a4.
Proof. vm_refl. Qed.
Lemma D_d85a4 : decode_any W_d85a4 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d85a8 : bv 32 := 0x40f70733.
Lemma F_d85a8 : fetch_word Asan.M.loaded_segments (0xd87f8 : word) = Some W_d85a8.
Proof. vm_refl. Qed.
Lemma D_d85a8 : decode_any W_d85a8 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d85ac : bv 32 := 0xfec6a223.
Lemma F_d85ac : fetch_word Asan.M.loaded_segments (0xd87fc : word) = Some W_d85ac.
Proof. vm_refl. Qed.
Lemma D_d85ac : decode_any W_d85ac = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d85b0 : bv 32 := 0xfec6a423.
Lemma F_d85b0 : fetch_word Asan.M.loaded_segments (0xd8800 : word) = Some W_d85b0.
Proof. vm_refl. Qed.
Lemma D_d85b0 : decode_any W_d85b0 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d85b4 : bv 32 := 0xfec6a623.
Lemma F_d85b4 : fetch_word Asan.M.loaded_segments (0xd8804 : word) = Some W_d85b4.
Proof. vm_refl. Qed.
Lemma D_d85b4 : decode_any W_d85b4 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d85b8 : bv 32 := 0xfec6a823.
Lemma F_d85b8 : fetch_word Asan.M.loaded_segments (0xd8808 : word) = Some W_d85b8.
Proof. vm_refl. Qed.
Lemma D_d85b8 : decode_any W_d85b8 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d85bc : bv 32 := 0x03076a63.
Lemma F_d85bc : fetch_word Asan.M.loaded_segments (0xd880c : word) = Some W_d85bc.
Proof. vm_refl. Qed.
Lemma D_d85bc : decode_any W_d85bc = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d85c0 : bv 32 := 0x02061613.
Lemma F_d85c0 : fetch_word Asan.M.loaded_segments (0xd8810 : word) = Some W_d85c0.
Proof. vm_refl. Qed.
Lemma D_d85c0 : decode_any W_d85c0 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d85c4 : bv 32 := 0x00f585b3.
Lemma F_d85c4 : fetch_word Asan.M.loaded_segments (0xd8814 : word) = Some W_d85c4.
Proof. vm_refl. Qed.
Lemma D_d85c4 : decode_any W_d85c4 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d85c8 : bv 32 := 0x02065693.
Lemma F_d85c8 : fetch_word Asan.M.loaded_segments (0xd8818 : word) = Some W_d85c8.
Proof. vm_refl. Qed.
Lemma D_d85c8 : decode_any W_d85c8 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d85cc : bv 32 := 0x00d66633.
Lemma F_d85cc : fetch_word Asan.M.loaded_segments (0xd881c : word) = Some W_d85cc.
Proof. vm_refl. Qed.
Lemma D_d85cc : decode_any W_d85cc = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d85d0 : bv 32 := 0x01f00693.
Lemma F_d85d0 : fetch_word Asan.M.loaded_segments (0xd8820 : word) = Some W_d85d0.
Proof. vm_refl. Qed.
Lemma D_d85d0 : decode_any W_d85d0 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d85d4 : bv 32 := 0x00c5b023.
Lemma F_d85d4 : fetch_word Asan.M.loaded_segments (0xd8824 : word) = Some W_d85d4.
Proof. vm_refl. Qed.
Lemma D_d85d4 : decode_any W_d85d4 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d85d8 : bv 32 := 0x00c5b423.
Lemma F_d85d8 : fetch_word Asan.M.loaded_segments (0xd8828 : word) = Some W_d85d8.
Proof. vm_refl. Qed.
Lemma D_d85d8 : decode_any W_d85d8 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d85dc : bv 32 := 0x00c5b823.
Lemma F_d85dc : fetch_word Asan.M.loaded_segments (0xd882c : word) = Some W_d85dc.
Proof. vm_refl. Qed.
Lemma D_d85dc : decode_any W_d85dc = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d85e0 : bv 32 := 0x00c5bc23.
Lemma F_d85e0 : fetch_word Asan.M.loaded_segments (0xd8830 : word) = Some W_d85e0.
Proof. vm_refl. Qed.
Lemma D_d85e0 : decode_any W_d85e0 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d85e4 : bv 32 := 0xfe070713.
Lemma F_d85e4 : fetch_word Asan.M.loaded_segments (0xd8834 : word) = Some W_d85e4.
Proof. vm_refl. Qed.
Lemma D_d85e4 : decode_any W_d85e4 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d85e8 : bv 32 := 0x02058593.
Lemma F_d85e8 : fetch_word Asan.M.loaded_segments (0xd8838 : word) = Some W_d85e8.
Proof. vm_refl. Qed.
Lemma D_d85e8 : decode_any W_d85e8 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d85ec : bv 32 := 0xfee6e4e3.
Lemma F_d85ec : fetch_word Asan.M.loaded_segments (0xd883c : word) = Some W_d85ec.
Proof. vm_refl. Qed.
Lemma D_d85ec : decode_any W_d85ec = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d85f0 : bv 32 := 0x00008067.
Lemma F_d85f0 : fetch_word Asan.M.loaded_segments (0xd8840 : word) = Some W_d85f0.
Proof. vm_refl. Qed.
Lemma D_d85f0 : decode_any W_d85f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0xd874c%Z.
Definition Fo_000 := F_d84fc.
Definition Do_000 := D_d84fc.
Definition Fo_004 := F_d8500.
Definition Do_004 := D_d8500.
Definition Fo_008 := F_d8504.
Definition Do_008 := D_d8504.
Definition Fo_00c := F_d8508.
Definition Do_00c := D_d8508.
Definition Fo_010 := F_d850c.
Definition Do_010 := D_d850c.
Definition Fo_014 := F_d8510.
Definition Do_014 := D_d8510.
Definition Fo_018 := F_d8514.
Definition Do_018 := D_d8514.
Definition Fo_01c := F_d8518.
Definition Do_01c := D_d8518.
Definition Fo_020 := F_d851c.
Definition Do_020 := D_d851c.
Definition Fo_024 := F_d8520.
Definition Do_024 := D_d8520.
Definition Fo_028 := F_d8524.
Definition Do_028 := D_d8524.
Definition Fo_02c := F_d8528.
Definition Do_02c := D_d8528.
Definition Fo_030 := F_d852c.
Definition Do_030 := D_d852c.
Definition Fo_034 := F_d8530.
Definition Do_034 := D_d8530.
Definition Fo_038 := F_d8534.
Definition Do_038 := D_d8534.
Definition Fo_03c := F_d8538.
Definition Do_03c := D_d8538.
Definition Fo_040 := F_d853c.
Definition Do_040 := D_d853c.
Definition Fo_044 := F_d8540.
Definition Do_044 := D_d8540.
Definition Fo_048 := F_d8544.
Definition Do_048 := D_d8544.
Definition Fo_04c := F_d8548.
Definition Do_04c := D_d8548.
Definition Fo_050 := F_d854c.
Definition Do_050 := D_d854c.
Definition Fo_054 := F_d8550.
Definition Do_054 := D_d8550.
Definition Fo_058 := F_d8554.
Definition Do_058 := D_d8554.
Definition Fo_05c := F_d8558.
Definition Do_05c := D_d8558.
Definition Fo_060 := F_d855c.
Definition Do_060 := D_d855c.
Definition Fo_064 := F_d8560.
Definition Do_064 := D_d8560.
Definition Fo_068 := F_d8564.
Definition Do_068 := D_d8564.
Definition Fo_06c := F_d8568.
Definition Do_06c := D_d8568.
Definition Fo_070 := F_d856c.
Definition Do_070 := D_d856c.
Definition Fo_074 := F_d8570.
Definition Do_074 := D_d8570.
Definition Fo_078 := F_d8574.
Definition Do_078 := D_d8574.
Definition Fo_07c := F_d8578.
Definition Do_07c := D_d8578.
Definition Fo_080 := F_d857c.
Definition Do_080 := D_d857c.
Definition Fo_084 := F_d8580.
Definition Do_084 := D_d8580.
Definition Fo_088 := F_d8584.
Definition Do_088 := D_d8584.
Definition Fo_08c := F_d8588.
Definition Do_08c := D_d8588.
Definition Fo_090 := F_d858c.
Definition Do_090 := D_d858c.
Definition Fo_094 := F_d8590.
Definition Do_094 := D_d8590.
Definition Fo_098 := F_d8594.
Definition Do_098 := D_d8594.
Definition Fo_09c := F_d8598.
Definition Do_09c := D_d8598.
Definition Fo_0a0 := F_d859c.
Definition Do_0a0 := D_d859c.
Definition Fo_0a4 := F_d85a0.
Definition Do_0a4 := D_d85a0.
Definition Fo_0a8 := F_d85a4.
Definition Do_0a8 := D_d85a4.
Definition Fo_0ac := F_d85a8.
Definition Do_0ac := D_d85a8.
Definition Fo_0b0 := F_d85ac.
Definition Do_0b0 := D_d85ac.
Definition Fo_0b4 := F_d85b0.
Definition Do_0b4 := D_d85b0.
Definition Fo_0b8 := F_d85b4.
Definition Do_0b8 := D_d85b4.
Definition Fo_0bc := F_d85b8.
Definition Do_0bc := D_d85b8.
Definition Fo_0c0 := F_d85bc.
Definition Do_0c0 := D_d85bc.
Definition Fo_0c4 := F_d85c0.
Definition Do_0c4 := D_d85c0.
Definition Fo_0c8 := F_d85c4.
Definition Do_0c8 := D_d85c4.
Definition Fo_0cc := F_d85c8.
Definition Do_0cc := D_d85c8.
Definition Fo_0d0 := F_d85cc.
Definition Do_0d0 := D_d85cc.
Definition Fo_0d4 := F_d85d0.
Definition Do_0d4 := D_d85d0.
Definition Fo_0d8 := F_d85d4.
Definition Do_0d8 := D_d85d4.
Definition Fo_0dc := F_d85d8.
Definition Do_0dc := D_d85d8.
Definition Fo_0e0 := F_d85dc.
Definition Do_0e0 := D_d85dc.
Definition Fo_0e4 := F_d85e0.
Definition Do_0e4 := D_d85e0.
Definition Fo_0e8 := F_d85e4.
Definition Do_0e8 := D_d85e4.
Definition Fo_0ec := F_d85e8.
Definition Do_0ec := D_d85e8.
Definition Fo_0f0 := F_d85ec.
Definition Do_0f0 := D_d85ec.
Definition Fo_0f4 := F_d85f0.
Definition Do_0f4 := D_d85f0.
