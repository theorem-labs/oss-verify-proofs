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
Definition W_c44e8 : bv 32 := 0x0e060a63.
Lemma F_c44e8 : fetch_word Plain.M.loaded_segments (0xc46a0 : word) = Some W_c44e8.
Proof. vm_refl. Qed.
Lemma D_c44e8 : decode_any W_c44e8 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c44ec : bv 32 := 0x00b50023.
Lemma F_c44ec : fetch_word Plain.M.loaded_segments (0xc46a4 : word) = Some W_c44ec.
Proof. vm_refl. Qed.
Lemma D_c44ec : decode_any W_c44ec = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c44f0 : bv 32 := 0x00c506b3.
Lemma F_c44f0 : fetch_word Plain.M.loaded_segments (0xc46a8 : word) = Some W_c44f0.
Proof. vm_refl. Qed.
Lemma D_c44f0 : decode_any W_c44f0 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c44f4 : bv 32 := 0x00300713.
Lemma F_c44f4 : fetch_word Plain.M.loaded_segments (0xc46ac : word) = Some W_c44f4.
Proof. vm_refl. Qed.
Lemma D_c44f4 : decode_any W_c44f4 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c44f8 : bv 32 := 0xfeb68fa3.
Lemma F_c44f8 : fetch_word Plain.M.loaded_segments (0xc46b0 : word) = Some W_c44f8.
Proof. vm_refl. Qed.
Lemma D_c44f8 : decode_any W_c44f8 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c44fc : bv 32 := 0x0ee66063.
Lemma F_c44fc : fetch_word Plain.M.loaded_segments (0xc46b4 : word) = Some W_c44fc.
Proof. vm_refl. Qed.
Lemma D_c44fc : decode_any W_c44fc = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4500 : bv 32 := 0x00b500a3.
Lemma F_c4500 : fetch_word Plain.M.loaded_segments (0xc46b8 : word) = Some W_c4500.
Proof. vm_refl. Qed.
Lemma D_c4500 : decode_any W_c4500 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4504 : bv 32 := 0x00b50123.
Lemma F_c4504 : fetch_word Plain.M.loaded_segments (0xc46bc : word) = Some W_c4504.
Proof. vm_refl. Qed.
Lemma D_c4504 : decode_any W_c4504 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4508 : bv 32 := 0x00700713.
Lemma F_c4508 : fetch_word Plain.M.loaded_segments (0xc46c0 : word) = Some W_c4508.
Proof. vm_refl. Qed.
Lemma D_c4508 : decode_any W_c4508 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c450c : bv 32 := 0xfeb68ea3.
Lemma F_c450c : fetch_word Plain.M.loaded_segments (0xc46c4 : word) = Some W_c450c.
Proof. vm_refl. Qed.
Lemma D_c450c : decode_any W_c450c = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4510 : bv 32 := 0xfeb68f23.
Lemma F_c4510 : fetch_word Plain.M.loaded_segments (0xc46c8 : word) = Some W_c4510.
Proof. vm_refl. Qed.
Lemma D_c4510 : decode_any W_c4510 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4514 : bv 32 := 0x0ce66463.
Lemma F_c4514 : fetch_word Plain.M.loaded_segments (0xc46cc : word) = Some W_c4514.
Proof. vm_refl. Qed.
Lemma D_c4514 : decode_any W_c4514 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4518 : bv 32 := 0x00b501a3.
Lemma F_c4518 : fetch_word Plain.M.loaded_segments (0xc46d0 : word) = Some W_c4518.
Proof. vm_refl. Qed.
Lemma D_c4518 : decode_any W_c4518 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c451c : bv 32 := 0x00900793.
Lemma F_c451c : fetch_word Plain.M.loaded_segments (0xc46d4 : word) = Some W_c451c.
Proof. vm_refl. Qed.
Lemma D_c451c : decode_any W_c451c = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4520 : bv 32 := 0xfeb68e23.
Lemma F_c4520 : fetch_word Plain.M.loaded_segments (0xc46d8 : word) = Some W_c4520.
Proof. vm_refl. Qed.
Lemma D_c4520 : decode_any W_c4520 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4524 : bv 32 := 0x0af66c63.
Lemma F_c4524 : fetch_word Plain.M.loaded_segments (0xc46dc : word) = Some W_c4524.
Proof. vm_refl. Qed.
Lemma D_c4524 : decode_any W_c4524 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4528 : bv 32 := 0x40a006bb.
Lemma F_c4528 : fetch_word Plain.M.loaded_segments (0xc46e0 : word) = Some W_c4528.
Proof. vm_refl. Qed.
Lemma D_c4528 : decode_any W_c4528 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c452c : bv 32 := 0x03859813.
Lemma F_c452c : fetch_word Plain.M.loaded_segments (0xc46e4 : word) = Some W_c452c.
Proof. vm_refl. Qed.
Lemma D_c452c : decode_any W_c452c = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4530 : bv 32 := 0x101015b7.
Lemma F_c4530 : fetch_word Plain.M.loaded_segments (0xc46e8 : word) = Some W_c4530.
Proof. vm_refl. Qed.
Lemma D_c4530 : decode_any W_c4530 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4534 : bv 32 := 0x0036f693.
Lemma F_c4534 : fetch_word Plain.M.loaded_segments (0xc46ec : word) = Some W_c4534.
Proof. vm_refl. Qed.
Lemma D_c4534 : decode_any W_c4534 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4538 : bv 32 := 0x00459713.
Lemma F_c4538 : fetch_word Plain.M.loaded_segments (0xc46f0 : word) = Some W_c4538.
Proof. vm_refl. Qed.
Lemma D_c4538 : decode_any W_c4538 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c453c : bv 32 := 0x40d60633.
Lemma F_c453c : fetch_word Plain.M.loaded_segments (0xc46f4 : word) = Some W_c453c.
Proof. vm_refl. Qed.
Lemma D_c453c : decode_any W_c453c = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4540 : bv 32 := 0x00d505b3.
Lemma F_c4540 : fetch_word Plain.M.loaded_segments (0xc46f8 : word) = Some W_c4540.
Proof. vm_refl. Qed.
Lemma D_c4540 : decode_any W_c4540 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4544 : bv 32 := 0x10070693.
Lemma F_c4544 : fetch_word Plain.M.loaded_segments (0xc46fc : word) = Some W_c4544.
Proof. vm_refl. Qed.
Lemma D_c4544 : decode_any W_c4544 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4548 : bv 32 := 0xffc67713.
Lemma F_c4548 : fetch_word Plain.M.loaded_segments (0xc4700 : word) = Some W_c4548.
Proof. vm_refl. Qed.
Lemma D_c4548 : decode_any W_c4548 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c454c : bv 32 := 0x02d83633.
Lemma F_c454c : fetch_word Plain.M.loaded_segments (0xc4704 : word) = Some W_c454c.
Proof. vm_refl. Qed.
Lemma D_c454c : decode_any W_c454c = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4550 : bv 32 := 0x00c5a023.
Lemma F_c4550 : fetch_word Plain.M.loaded_segments (0xc4708 : word) = Some W_c4550.
Proof. vm_refl. Qed.
Lemma D_c4550 : decode_any W_c4550 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4554 : bv 32 := 0x00e586b3.
Lemma F_c4554 : fetch_word Plain.M.loaded_segments (0xc470c : word) = Some W_c4554.
Proof. vm_refl. Qed.
Lemma D_c4554 : decode_any W_c4554 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4558 : bv 32 := 0xfec6ae23.
Lemma F_c4558 : fetch_word Plain.M.loaded_segments (0xc4710 : word) = Some W_c4558.
Proof. vm_refl. Qed.
Lemma D_c4558 : decode_any W_c4558 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c455c : bv 32 := 0x08f76063.
Lemma F_c455c : fetch_word Plain.M.loaded_segments (0xc4714 : word) = Some W_c455c.
Proof. vm_refl. Qed.
Lemma D_c455c : decode_any W_c455c = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4560 : bv 32 := 0x00c5a223.
Lemma F_c4560 : fetch_word Plain.M.loaded_segments (0xc4718 : word) = Some W_c4560.
Proof. vm_refl. Qed.
Lemma D_c4560 : decode_any W_c4560 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4564 : bv 32 := 0x00c5a423.
Lemma F_c4564 : fetch_word Plain.M.loaded_segments (0xc471c : word) = Some W_c4564.
Proof. vm_refl. Qed.
Lemma D_c4564 : decode_any W_c4564 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4568 : bv 32 := 0x01900793.
Lemma F_c4568 : fetch_word Plain.M.loaded_segments (0xc4720 : word) = Some W_c4568.
Proof. vm_refl. Qed.
Lemma D_c4568 : decode_any W_c4568 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c456c : bv 32 := 0xfec6aa23.
Lemma F_c456c : fetch_word Plain.M.loaded_segments (0xc4724 : word) = Some W_c456c.
Proof. vm_refl. Qed.
Lemma D_c456c : decode_any W_c456c = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4570 : bv 32 := 0xfec6ac23.
Lemma F_c4570 : fetch_word Plain.M.loaded_segments (0xc4728 : word) = Some W_c4570.
Proof. vm_refl. Qed.
Lemma D_c4570 : decode_any W_c4570 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4574 : bv 32 := 0x06f76463.
Lemma F_c4574 : fetch_word Plain.M.loaded_segments (0xc472c : word) = Some W_c4574.
Proof. vm_refl. Qed.
Lemma D_c4574 : decode_any W_c4574 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4578 : bv 32 := 0x00c5a623.
Lemma F_c4578 : fetch_word Plain.M.loaded_segments (0xc4730 : word) = Some W_c4578.
Proof. vm_refl. Qed.
Lemma D_c4578 : decode_any W_c4578 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c457c : bv 32 := 0x00c5a823.
Lemma F_c457c : fetch_word Plain.M.loaded_segments (0xc4734 : word) = Some W_c457c.
Proof. vm_refl. Qed.
Lemma D_c457c : decode_any W_c457c = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4580 : bv 32 := 0x00c5aa23.
Lemma F_c4580 : fetch_word Plain.M.loaded_segments (0xc4738 : word) = Some W_c4580.
Proof. vm_refl. Qed.
Lemma D_c4580 : decode_any W_c4580 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4584 : bv 32 := 0x00c5ac23.
Lemma F_c4584 : fetch_word Plain.M.loaded_segments (0xc473c : word) = Some W_c4584.
Proof. vm_refl. Qed.
Lemma D_c4584 : decode_any W_c4584 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4588 : bv 32 := 0x0045f793.
Lemma F_c4588 : fetch_word Plain.M.loaded_segments (0xc4740 : word) = Some W_c4588.
Proof. vm_refl. Qed.
Lemma D_c4588 : decode_any W_c4588 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c458c : bv 32 := 0x02000813.
Lemma F_c458c : fetch_word Plain.M.loaded_segments (0xc4744 : word) = Some W_c458c.
Proof. vm_refl. Qed.
Lemma D_c458c : decode_any W_c458c = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4590 : bv 32 := 0x01878793.
Lemma F_c4590 : fetch_word Plain.M.loaded_segments (0xc4748 : word) = Some W_c4590.
Proof. vm_refl. Qed.
Lemma D_c4590 : decode_any W_c4590 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4594 : bv 32 := 0x40f70733.
Lemma F_c4594 : fetch_word Plain.M.loaded_segments (0xc474c : word) = Some W_c4594.
Proof. vm_refl. Qed.
Lemma D_c4594 : decode_any W_c4594 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c4598 : bv 32 := 0xfec6a223.
Lemma F_c4598 : fetch_word Plain.M.loaded_segments (0xc4750 : word) = Some W_c4598.
Proof. vm_refl. Qed.
Lemma D_c4598 : decode_any W_c4598 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c459c : bv 32 := 0xfec6a423.
Lemma F_c459c : fetch_word Plain.M.loaded_segments (0xc4754 : word) = Some W_c459c.
Proof. vm_refl. Qed.
Lemma D_c459c : decode_any W_c459c = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c45a0 : bv 32 := 0xfec6a623.
Lemma F_c45a0 : fetch_word Plain.M.loaded_segments (0xc4758 : word) = Some W_c45a0.
Proof. vm_refl. Qed.
Lemma D_c45a0 : decode_any W_c45a0 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c45a4 : bv 32 := 0xfec6a823.
Lemma F_c45a4 : fetch_word Plain.M.loaded_segments (0xc475c : word) = Some W_c45a4.
Proof. vm_refl. Qed.
Lemma D_c45a4 : decode_any W_c45a4 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c45a8 : bv 32 := 0x03076a63.
Lemma F_c45a8 : fetch_word Plain.M.loaded_segments (0xc4760 : word) = Some W_c45a8.
Proof. vm_refl. Qed.
Lemma D_c45a8 : decode_any W_c45a8 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c45ac : bv 32 := 0x02061613.
Lemma F_c45ac : fetch_word Plain.M.loaded_segments (0xc4764 : word) = Some W_c45ac.
Proof. vm_refl. Qed.
Lemma D_c45ac : decode_any W_c45ac = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c45b0 : bv 32 := 0x00f585b3.
Lemma F_c45b0 : fetch_word Plain.M.loaded_segments (0xc4768 : word) = Some W_c45b0.
Proof. vm_refl. Qed.
Lemma D_c45b0 : decode_any W_c45b0 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c45b4 : bv 32 := 0x02065693.
Lemma F_c45b4 : fetch_word Plain.M.loaded_segments (0xc476c : word) = Some W_c45b4.
Proof. vm_refl. Qed.
Lemma D_c45b4 : decode_any W_c45b4 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c45b8 : bv 32 := 0x00d66633.
Lemma F_c45b8 : fetch_word Plain.M.loaded_segments (0xc4770 : word) = Some W_c45b8.
Proof. vm_refl. Qed.
Lemma D_c45b8 : decode_any W_c45b8 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c45bc : bv 32 := 0x01f00693.
Lemma F_c45bc : fetch_word Plain.M.loaded_segments (0xc4774 : word) = Some W_c45bc.
Proof. vm_refl. Qed.
Lemma D_c45bc : decode_any W_c45bc = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c45c0 : bv 32 := 0x00c5b023.
Lemma F_c45c0 : fetch_word Plain.M.loaded_segments (0xc4778 : word) = Some W_c45c0.
Proof. vm_refl. Qed.
Lemma D_c45c0 : decode_any W_c45c0 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c45c4 : bv 32 := 0x00c5b423.
Lemma F_c45c4 : fetch_word Plain.M.loaded_segments (0xc477c : word) = Some W_c45c4.
Proof. vm_refl. Qed.
Lemma D_c45c4 : decode_any W_c45c4 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c45c8 : bv 32 := 0x00c5b823.
Lemma F_c45c8 : fetch_word Plain.M.loaded_segments (0xc4780 : word) = Some W_c45c8.
Proof. vm_refl. Qed.
Lemma D_c45c8 : decode_any W_c45c8 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c45cc : bv 32 := 0x00c5bc23.
Lemma F_c45cc : fetch_word Plain.M.loaded_segments (0xc4784 : word) = Some W_c45cc.
Proof. vm_refl. Qed.
Lemma D_c45cc : decode_any W_c45cc = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c45d0 : bv 32 := 0xfe070713.
Lemma F_c45d0 : fetch_word Plain.M.loaded_segments (0xc4788 : word) = Some W_c45d0.
Proof. vm_refl. Qed.
Lemma D_c45d0 : decode_any W_c45d0 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c45d4 : bv 32 := 0x02058593.
Lemma F_c45d4 : fetch_word Plain.M.loaded_segments (0xc478c : word) = Some W_c45d4.
Proof. vm_refl. Qed.
Lemma D_c45d4 : decode_any W_c45d4 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c45d8 : bv 32 := 0xfee6e4e3.
Lemma F_c45d8 : fetch_word Plain.M.loaded_segments (0xc4790 : word) = Some W_c45d8.
Proof. vm_refl. Qed.
Lemma D_c45d8 : decode_any W_c45d8 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_c45dc : bv 32 := 0x00008067.
Lemma F_c45dc : fetch_word Plain.M.loaded_segments (0xc4794 : word) = Some W_c45dc.
Proof. vm_refl. Qed.
Lemma D_c45dc : decode_any W_c45dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := Plain.M.loaded_segments.
Definition ms_base : Z := 0xc46a0%Z.
Definition Fo_000 := F_c44e8.
Definition Do_000 := D_c44e8.
Definition Fo_004 := F_c44ec.
Definition Do_004 := D_c44ec.
Definition Fo_008 := F_c44f0.
Definition Do_008 := D_c44f0.
Definition Fo_00c := F_c44f4.
Definition Do_00c := D_c44f4.
Definition Fo_010 := F_c44f8.
Definition Do_010 := D_c44f8.
Definition Fo_014 := F_c44fc.
Definition Do_014 := D_c44fc.
Definition Fo_018 := F_c4500.
Definition Do_018 := D_c4500.
Definition Fo_01c := F_c4504.
Definition Do_01c := D_c4504.
Definition Fo_020 := F_c4508.
Definition Do_020 := D_c4508.
Definition Fo_024 := F_c450c.
Definition Do_024 := D_c450c.
Definition Fo_028 := F_c4510.
Definition Do_028 := D_c4510.
Definition Fo_02c := F_c4514.
Definition Do_02c := D_c4514.
Definition Fo_030 := F_c4518.
Definition Do_030 := D_c4518.
Definition Fo_034 := F_c451c.
Definition Do_034 := D_c451c.
Definition Fo_038 := F_c4520.
Definition Do_038 := D_c4520.
Definition Fo_03c := F_c4524.
Definition Do_03c := D_c4524.
Definition Fo_040 := F_c4528.
Definition Do_040 := D_c4528.
Definition Fo_044 := F_c452c.
Definition Do_044 := D_c452c.
Definition Fo_048 := F_c4530.
Definition Do_048 := D_c4530.
Definition Fo_04c := F_c4534.
Definition Do_04c := D_c4534.
Definition Fo_050 := F_c4538.
Definition Do_050 := D_c4538.
Definition Fo_054 := F_c453c.
Definition Do_054 := D_c453c.
Definition Fo_058 := F_c4540.
Definition Do_058 := D_c4540.
Definition Fo_05c := F_c4544.
Definition Do_05c := D_c4544.
Definition Fo_060 := F_c4548.
Definition Do_060 := D_c4548.
Definition Fo_064 := F_c454c.
Definition Do_064 := D_c454c.
Definition Fo_068 := F_c4550.
Definition Do_068 := D_c4550.
Definition Fo_06c := F_c4554.
Definition Do_06c := D_c4554.
Definition Fo_070 := F_c4558.
Definition Do_070 := D_c4558.
Definition Fo_074 := F_c455c.
Definition Do_074 := D_c455c.
Definition Fo_078 := F_c4560.
Definition Do_078 := D_c4560.
Definition Fo_07c := F_c4564.
Definition Do_07c := D_c4564.
Definition Fo_080 := F_c4568.
Definition Do_080 := D_c4568.
Definition Fo_084 := F_c456c.
Definition Do_084 := D_c456c.
Definition Fo_088 := F_c4570.
Definition Do_088 := D_c4570.
Definition Fo_08c := F_c4574.
Definition Do_08c := D_c4574.
Definition Fo_090 := F_c4578.
Definition Do_090 := D_c4578.
Definition Fo_094 := F_c457c.
Definition Do_094 := D_c457c.
Definition Fo_098 := F_c4580.
Definition Do_098 := D_c4580.
Definition Fo_09c := F_c4584.
Definition Do_09c := D_c4584.
Definition Fo_0a0 := F_c4588.
Definition Do_0a0 := D_c4588.
Definition Fo_0a4 := F_c458c.
Definition Do_0a4 := D_c458c.
Definition Fo_0a8 := F_c4590.
Definition Do_0a8 := D_c4590.
Definition Fo_0ac := F_c4594.
Definition Do_0ac := D_c4594.
Definition Fo_0b0 := F_c4598.
Definition Do_0b0 := D_c4598.
Definition Fo_0b4 := F_c459c.
Definition Do_0b4 := D_c459c.
Definition Fo_0b8 := F_c45a0.
Definition Do_0b8 := D_c45a0.
Definition Fo_0bc := F_c45a4.
Definition Do_0bc := D_c45a4.
Definition Fo_0c0 := F_c45a8.
Definition Do_0c0 := D_c45a8.
Definition Fo_0c4 := F_c45ac.
Definition Do_0c4 := D_c45ac.
Definition Fo_0c8 := F_c45b0.
Definition Do_0c8 := D_c45b0.
Definition Fo_0cc := F_c45b4.
Definition Do_0cc := D_c45b4.
Definition Fo_0d0 := F_c45b8.
Definition Do_0d0 := D_c45b8.
Definition Fo_0d4 := F_c45bc.
Definition Do_0d4 := D_c45bc.
Definition Fo_0d8 := F_c45c0.
Definition Do_0d8 := D_c45c0.
Definition Fo_0dc := F_c45c4.
Definition Do_0dc := D_c45c4.
Definition Fo_0e0 := F_c45c8.
Definition Do_0e0 := D_c45c8.
Definition Fo_0e4 := F_c45cc.
Definition Do_0e4 := D_c45cc.
Definition Fo_0e8 := F_c45d0.
Definition Do_0e8 := D_c45d0.
Definition Fo_0ec := F_c45d4.
Definition Do_0ec := D_c45d4.
Definition Fo_0f0 := F_c45d8.
Definition Do_0f0 := D_c45d8.
Definition Fo_0f4 := F_c45dc.
Definition Do_0f4 := D_c45dc.
