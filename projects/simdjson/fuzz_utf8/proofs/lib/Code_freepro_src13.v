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
Definition W_b54e8 : bv 32 := 0x1c050463.
Lemma F_b54e8 : fetch_word Plain.M.loaded_segments (0xb56a0 : word) = Some W_b54e8.
Proof. vm_refl. Qed.
Lemma D_b54e8 : decode_any W_b54e8 = Some (Branch BC_EQ 10 0 456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b54ec : bv 32 := 0xfd010113.
Lemma F_b54ec : fetch_word Plain.M.loaded_segments (0xb56a4 : word) = Some W_b54ec.
Proof. vm_refl. Qed.
Lemma D_b54ec : decode_any W_b54ec = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b54f0 : bv 32 := 0x02113423.
Lemma F_b54f0 : fetch_word Plain.M.loaded_segments (0xb56a8 : word) = Some W_b54f0.
Proof. vm_refl. Qed.
Lemma D_b54f0 : decode_any W_b54f0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b54f4 : bv 32 := 0x02813023.
Lemma F_b54f4 : fetch_word Plain.M.loaded_segments (0xb56ac : word) = Some W_b54f4.
Proof. vm_refl. Qed.
Lemma D_b54f4 : decode_any W_b54f4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b54f8 : bv 32 := 0x00913c23.
Lemma F_b54f8 : fetch_word Plain.M.loaded_segments (0xb56b0 : word) = Some W_b54f8.
Proof. vm_refl. Qed.
Lemma D_b54f8 : decode_any W_b54f8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b54fc : bv 32 := 0x01213823.
Lemma F_b54fc : fetch_word Plain.M.loaded_segments (0xb56b4 : word) = Some W_b54fc.
Proof. vm_refl. Qed.
Lemma D_b54fc : decode_any W_b54fc = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5500 : bv 32 := 0x01313423.
Lemma F_b5500 : fetch_word Plain.M.loaded_segments (0xb56b8 : word) = Some W_b5500.
Proof. vm_refl. Qed.
Lemma D_b5500 : decode_any W_b5500 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5504 : bv 32 := 0x00050493.
Lemma F_b5504 : fetch_word Plain.M.loaded_segments (0xb56bc : word) = Some W_b5504.
Proof. vm_refl. Qed.
Lemma D_b5504 : decode_any W_b5504 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5508 : bv 32 := 0x1ac000ef.
Lemma F_b5508 : fetch_word Plain.M.loaded_segments (0xb56c0 : word) = Some W_b5508.
Proof. vm_refl. Qed.
Lemma D_b5508 : decode_any W_b5508 = Some (Jal 1 428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b550c : bv 32 := 0x02053583.
Lemma F_b550c : fetch_word Plain.M.loaded_segments (0xb56c4 : word) = Some W_b550c.
Proof. vm_refl. Qed.
Lemma D_b550c : decode_any W_b550c = Some (Load SZ8 true 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5510 : bv 32 := 0xffd4c683.
Lemma F_b5510 : fetch_word Plain.M.loaded_segments (0xb56c8 : word) = Some W_b5510.
Proof. vm_refl. Qed.
Lemma D_b5510 : decode_any W_b5510 = Some (Load SZ1 false 13 9 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5514 : bv 32 := 0x00c5d613.
Lemma F_b5514 : fetch_word Plain.M.loaded_segments (0xb56cc : word) = Some W_b5514.
Proof. vm_refl. Qed.
Lemma D_b5514 : decode_any W_b5514 = Some (ShiftImm ALU_SRL 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5518 : bv 32 := 0x01f6f413.
Lemma F_b5518 : fetch_word Plain.M.loaded_segments (0xb56d0 : word) = Some W_b5518.
Proof. vm_refl. Qed.
Lemma D_b5518 : decode_any W_b5518 = Some (OpImm ALU_AND 8 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b551c : bv 32 := 0x00060e63.
Lemma F_b551c : fetch_word Plain.M.loaded_segments (0xb56d4 : word) = Some W_b551c.
Proof. vm_refl. Qed.
Lemma D_b551c : decode_any W_b551c = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5520 : bv 32 := 0x01f5f613.
Lemma F_b5520 : fetch_word Plain.M.loaded_segments (0xb56d8 : word) = Some W_b5520.
Proof. vm_refl. Qed.
Lemma D_b5520 : decode_any W_b5520 = Some (OpImm ALU_AND 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5524 : bv 32 := 0x00061a63.
Lemma F_b5524 : fetch_word Plain.M.loaded_segments (0xb56dc : word) = Some W_b5524.
Proof. vm_refl. Qed.
Lemma D_b5524 : decode_any W_b5524 = Some (Branch BC_NE 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5528 : bv 32 := 0xfffff637.
Lemma F_b5528 : fetch_word Plain.M.loaded_segments (0xb56e0 : word) = Some W_b5528.
Proof. vm_refl. Qed.
Lemma D_b5528 : decode_any W_b5528 = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b552c : bv 32 := 0x00c5f633.
Lemma F_b552c : fetch_word Plain.M.loaded_segments (0xb56e4 : word) = Some W_b552c.
Proof. vm_refl. Qed.
Lemma D_b552c : decode_any W_b552c = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5530 : bv 32 := 0xff060613.
Lemma F_b5530 : fetch_word Plain.M.loaded_segments (0xb56e8 : word) = Some W_b5530.
Proof. vm_refl. Qed.
Lemma D_b5530 : decode_any W_b5530 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5534 : bv 32 := 0x0200006f.
Lemma F_b5534 : fetch_word Plain.M.loaded_segments (0xb56ec : word) = Some W_b5534.
Proof. vm_refl. Qed.
Lemma D_b5534 : decode_any W_b5534 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5538 : bv 32 := 0x0055d613.
Lemma F_b5538 : fetch_word Plain.M.loaded_segments (0xb56f0 : word) = Some W_b5538.
Proof. vm_refl. Qed.
Lemma D_b5538 : decode_any W_b5538 = Some (ShiftImm ALU_SRL 12 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b553c : bv 32 := 0xfff6c717.
Lemma F_b553c : fetch_word Plain.M.loaded_segments (0xb56f4 : word) = Some W_b553c.
Proof. vm_refl. Qed.
Lemma D_b553c : decode_any W_b553c = Some (Auipc 14 1048428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5540 : bv 32 := 0x07e67613.
Lemma F_b5540 : fetch_word Plain.M.loaded_segments (0xb56f8 : word) = Some W_b5540.
Proof. vm_refl. Qed.
Lemma D_b5540 : decode_any W_b5540 = Some (OpImm ALU_AND 12 12 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5544 : bv 32 := 0x15c70713.
Lemma F_b5544 : fetch_word Plain.M.loaded_segments (0xb56fc : word) = Some W_b5544.
Proof. vm_refl. Qed.
Lemma D_b5544 : decode_any W_b5544 = Some (OpImm ALU_ADD 14 14 348, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5548 : bv 32 := 0x00c70633.
Lemma F_b5548 : fetch_word Plain.M.loaded_segments (0xb5700 : word) = Some W_b5548.
Proof. vm_refl. Qed.
Lemma D_b5548 : decode_any W_b5548 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b554c : bv 32 := 0x00065603.
Lemma F_b554c : fetch_word Plain.M.loaded_segments (0xb5704 : word) = Some W_b554c.
Proof. vm_refl. Qed.
Lemma D_b554c : decode_any W_b554c = Some (Load SZ2 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5550 : bv 32 := 0x00461613.
Lemma F_b5550 : fetch_word Plain.M.loaded_segments (0xb5708 : word) = Some W_b5550.
Proof. vm_refl. Qed.
Lemma D_b5550 : decode_any W_b5550 = Some (ShiftImm ALU_SLL 12 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5554 : bv 32 := 0x01053703.
Lemma F_b5554 : fetch_word Plain.M.loaded_segments (0xb570c : word) = Some W_b5554.
Proof. vm_refl. Qed.
Lemma D_b5554 : decode_any W_b5554 = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5558 : bv 32 := 0x028607b3.
Lemma F_b5558 : fetch_word Plain.M.loaded_segments (0xb5710 : word) = Some W_b5558.
Proof. vm_refl. Qed.
Lemma D_b5558 : decode_any W_b5558 = Some (Mul M_MUL 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b555c : bv 32 := 0x0a000813.
Lemma F_b555c : fetch_word Plain.M.loaded_segments (0xb5714 : word) = Some W_b555c.
Proof. vm_refl. Qed.
Lemma D_b555c : decode_any W_b555c = Some (OpImm ALU_ADD 16 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5560 : bv 32 := 0x00c70633.
Lemma F_b5560 : fetch_word Plain.M.loaded_segments (0xb5718 : word) = Some W_b5560.
Proof. vm_refl. Qed.
Lemma D_b5560 : decode_any W_b5560 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5564 : bv 32 := 0x00f607b3.
Lemma F_b5564 : fetch_word Plain.M.loaded_segments (0xb571c : word) = Some W_b5564.
Proof. vm_refl. Qed.
Lemma D_b5564 : decode_any W_b5564 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5568 : bv 32 := 0x00c78613.
Lemma F_b5568 : fetch_word Plain.M.loaded_segments (0xb5720 : word) = Some W_b5568.
Proof. vm_refl. Qed.
Lemma D_b5568 : decode_any W_b5568 = Some (OpImm ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b556c : bv 32 := 0x0056d713.
Lemma F_b556c : fetch_word Plain.M.loaded_segments (0xb5724 : word) = Some W_b556c.
Proof. vm_refl. Qed.
Lemma D_b556c : decode_any W_b556c = Some (ShiftImm ALU_SRL 14 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5570 : bv 32 := 0x0306e663.
Lemma F_b5570 : fetch_word Plain.M.loaded_segments (0xb5728 : word) = Some W_b5570.
Proof. vm_refl. Qed.
Lemma D_b5570 : decode_any W_b5570 = Some (Branch BC_LTU 13 16 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5574 : bv 32 := 0x00500693.
Lemma F_b5574 : fetch_word Plain.M.loaded_segments (0xb572c : word) = Some W_b5574.
Proof. vm_refl. Qed.
Lemma D_b5574 : decode_any W_b5574 = Some (OpImm ALU_ADD 13 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5578 : bv 32 := 0x00d70463.
Lemma F_b5578 : fetch_word Plain.M.loaded_segments (0xb5730 : word) = Some W_b5578.
Proof. vm_refl. Qed.
Lemma D_b5578 : decode_any W_b5578 = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b557c : bv 32 := 0x00000023.
Lemma F_b557c : fetch_word Plain.M.loaded_segments (0xb5734 : word) = Some W_b557c.
Proof. vm_refl. Qed.
Lemma D_b557c : decode_any W_b557c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5580 : bv 32 := 0x0087e703.
Lemma F_b5580 : fetch_word Plain.M.loaded_segments (0xb5738 : word) = Some W_b5580.
Proof. vm_refl. Qed.
Lemma D_b5580 : decode_any W_b5580 = Some (Load SZ4 false 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5584 : bv 32 := 0x00400693.
Lemma F_b5584 : fetch_word Plain.M.loaded_segments (0xb573c : word) = Some W_b5584.
Proof. vm_refl. Qed.
Lemma D_b5584 : decode_any W_b5584 = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5588 : bv 32 := 0x00e6e463.
Lemma F_b5588 : fetch_word Plain.M.loaded_segments (0xb5740 : word) = Some W_b5588.
Proof. vm_refl. Qed.
Lemma D_b5588 : decode_any W_b5588 = Some (Branch BC_LTU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b558c : bv 32 := 0x00000023.
Lemma F_b558c : fetch_word Plain.M.loaded_segments (0xb5744 : word) = Some W_b558c.
Proof. vm_refl. Qed.
Lemma D_b558c : decode_any W_b558c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5590 : bv 32 := 0x0077c683.
Lemma F_b5590 : fetch_word Plain.M.loaded_segments (0xb5748 : word) = Some W_b5590.
Proof. vm_refl. Qed.
Lemma D_b5590 : decode_any W_b5590 = Some (Load SZ1 false 13 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5594 : bv 32 := 0x00068463.
Lemma F_b5594 : fetch_word Plain.M.loaded_segments (0xb574c : word) = Some W_b5594.
Proof. vm_refl. Qed.
Lemma D_b5594 : decode_any W_b5594 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b5598 : bv 32 := 0x00000023.
Lemma F_b5598 : fetch_word Plain.M.loaded_segments (0xb5750 : word) = Some W_b5598.
Proof. vm_refl. Qed.
Lemma D_b5598 : decode_any W_b5598 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b559c : bv 32 := 0x409606b3.
Lemma F_b559c : fetch_word Plain.M.loaded_segments (0xb5754 : word) = Some W_b559c.
Proof. vm_refl. Qed.
Lemma D_b559c : decode_any W_b559c = Some (Op ALU_SUB 13 12 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b55a0 : bv 32 := 0x00e6f463.
Lemma F_b55a0 : fetch_word Plain.M.loaded_segments (0xb5758 : word) = Some W_b55a0.
Proof. vm_refl. Qed.
Lemma D_b55a0 : decode_any W_b55a0 = Some (Branch BC_GEU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b55a4 : bv 32 := 0x00000023.
Lemma F_b55a4 : fetch_word Plain.M.loaded_segments (0xb575c : word) = Some W_b55a4.
Proof. vm_refl. Qed.
Lemma D_b55a4 : decode_any W_b55a4 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b55a8 : bv 32 := 0x40e606b3.
Lemma F_b55a8 : fetch_word Plain.M.loaded_segments (0xb5760 : word) = Some W_b55a8.
Proof. vm_refl. Qed.
Lemma D_b55a8 : decode_any W_b55a8 = Some (Op ALU_SUB 13 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b55ac : bv 32 := 0x0006c683.
Lemma F_b55ac : fetch_word Plain.M.loaded_segments (0xb5764 : word) = Some W_b55ac.
Proof. vm_refl. Qed.
Lemma D_b55ac : decode_any W_b55ac = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b55b0 : bv 32 := 0x00068463.
Lemma F_b55b0 : fetch_word Plain.M.loaded_segments (0xb5768 : word) = Some W_b55b0.
Proof. vm_refl. Qed.
Lemma D_b55b0 : decode_any W_b55b0 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b55b4 : bv 32 := 0x00000023.
Lemma F_b55b4 : fetch_word Plain.M.loaded_segments (0xb576c : word) = Some W_b55b4.
Proof. vm_refl. Qed.
Lemma D_b55b4 : decode_any W_b55b4 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b55b8 : bv 32 := 0x00064603.
Lemma F_b55b8 : fetch_word Plain.M.loaded_segments (0xb5770 : word) = Some W_b55b8.
Proof. vm_refl. Qed.
Lemma D_b55b8 : decode_any W_b55b8 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b55bc : bv 32 := 0x00060463.
Lemma F_b55bc : fetch_word Plain.M.loaded_segments (0xb5774 : word) = Some W_b55bc.
Proof. vm_refl. Qed.
Lemma D_b55bc : decode_any W_b55bc = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b55c0 : bv 32 := 0x00000023.
Lemma F_b55c0 : fetch_word Plain.M.loaded_segments (0xb5778 : word) = Some W_b55c0.
Proof. vm_refl. Qed.
Lemma D_b55c0 : decode_any W_b55c0 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b55c4 : bv 32 := 0x00100613.
Lemma F_b55c4 : fetch_word Plain.M.loaded_segments (0xb577c : word) = Some W_b55c4.
Proof. vm_refl. Qed.
Lemma D_b55c4 : decode_any W_b55c4 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.
