(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_minifyimpl.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_159504 : bv 32 := 0x0e060a63.
Lemma F_159504 : fetch_word Asan.M.loaded_segments (0x159508 : word) = Some W_159504.
Proof. vm_refl. Qed.
Lemma D_159504 : decode_any W_159504 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159508 : bv 32 := 0x00b50023.
Lemma F_159508 : fetch_word Asan.M.loaded_segments (0x15950c : word) = Some W_159508.
Proof. vm_refl. Qed.
Lemma D_159508 : decode_any W_159508 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15950c : bv 32 := 0x00c506b3.
Lemma F_15950c : fetch_word Asan.M.loaded_segments (0x159510 : word) = Some W_15950c.
Proof. vm_refl. Qed.
Lemma D_15950c : decode_any W_15950c = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159510 : bv 32 := 0x00300713.
Lemma F_159510 : fetch_word Asan.M.loaded_segments (0x159514 : word) = Some W_159510.
Proof. vm_refl. Qed.
Lemma D_159510 : decode_any W_159510 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159514 : bv 32 := 0xfeb68fa3.
Lemma F_159514 : fetch_word Asan.M.loaded_segments (0x159518 : word) = Some W_159514.
Proof. vm_refl. Qed.
Lemma D_159514 : decode_any W_159514 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159518 : bv 32 := 0x0ee66063.
Lemma F_159518 : fetch_word Asan.M.loaded_segments (0x15951c : word) = Some W_159518.
Proof. vm_refl. Qed.
Lemma D_159518 : decode_any W_159518 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15951c : bv 32 := 0x00b500a3.
Lemma F_15951c : fetch_word Asan.M.loaded_segments (0x159520 : word) = Some W_15951c.
Proof. vm_refl. Qed.
Lemma D_15951c : decode_any W_15951c = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159520 : bv 32 := 0x00b50123.
Lemma F_159520 : fetch_word Asan.M.loaded_segments (0x159524 : word) = Some W_159520.
Proof. vm_refl. Qed.
Lemma D_159520 : decode_any W_159520 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159524 : bv 32 := 0x00700713.
Lemma F_159524 : fetch_word Asan.M.loaded_segments (0x159528 : word) = Some W_159524.
Proof. vm_refl. Qed.
Lemma D_159524 : decode_any W_159524 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159528 : bv 32 := 0xfeb68ea3.
Lemma F_159528 : fetch_word Asan.M.loaded_segments (0x15952c : word) = Some W_159528.
Proof. vm_refl. Qed.
Lemma D_159528 : decode_any W_159528 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15952c : bv 32 := 0xfeb68f23.
Lemma F_15952c : fetch_word Asan.M.loaded_segments (0x159530 : word) = Some W_15952c.
Proof. vm_refl. Qed.
Lemma D_15952c : decode_any W_15952c = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159530 : bv 32 := 0x0ce66463.
Lemma F_159530 : fetch_word Asan.M.loaded_segments (0x159534 : word) = Some W_159530.
Proof. vm_refl. Qed.
Lemma D_159530 : decode_any W_159530 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159534 : bv 32 := 0x00b501a3.
Lemma F_159534 : fetch_word Asan.M.loaded_segments (0x159538 : word) = Some W_159534.
Proof. vm_refl. Qed.
Lemma D_159534 : decode_any W_159534 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159538 : bv 32 := 0x00900793.
Lemma F_159538 : fetch_word Asan.M.loaded_segments (0x15953c : word) = Some W_159538.
Proof. vm_refl. Qed.
Lemma D_159538 : decode_any W_159538 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15953c : bv 32 := 0xfeb68e23.
Lemma F_15953c : fetch_word Asan.M.loaded_segments (0x159540 : word) = Some W_15953c.
Proof. vm_refl. Qed.
Lemma D_15953c : decode_any W_15953c = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159540 : bv 32 := 0x0af66c63.
Lemma F_159540 : fetch_word Asan.M.loaded_segments (0x159544 : word) = Some W_159540.
Proof. vm_refl. Qed.
Lemma D_159540 : decode_any W_159540 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159544 : bv 32 := 0x40a006bb.
Lemma F_159544 : fetch_word Asan.M.loaded_segments (0x159548 : word) = Some W_159544.
Proof. vm_refl. Qed.
Lemma D_159544 : decode_any W_159544 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159548 : bv 32 := 0x03859813.
Lemma F_159548 : fetch_word Asan.M.loaded_segments (0x15954c : word) = Some W_159548.
Proof. vm_refl. Qed.
Lemma D_159548 : decode_any W_159548 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15954c : bv 32 := 0x101015b7.
Lemma F_15954c : fetch_word Asan.M.loaded_segments (0x159550 : word) = Some W_15954c.
Proof. vm_refl. Qed.
Lemma D_15954c : decode_any W_15954c = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159550 : bv 32 := 0x0036f693.
Lemma F_159550 : fetch_word Asan.M.loaded_segments (0x159554 : word) = Some W_159550.
Proof. vm_refl. Qed.
Lemma D_159550 : decode_any W_159550 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159554 : bv 32 := 0x00459713.
Lemma F_159554 : fetch_word Asan.M.loaded_segments (0x159558 : word) = Some W_159554.
Proof. vm_refl. Qed.
Lemma D_159554 : decode_any W_159554 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159558 : bv 32 := 0x40d60633.
Lemma F_159558 : fetch_word Asan.M.loaded_segments (0x15955c : word) = Some W_159558.
Proof. vm_refl. Qed.
Lemma D_159558 : decode_any W_159558 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15955c : bv 32 := 0x00d505b3.
Lemma F_15955c : fetch_word Asan.M.loaded_segments (0x159560 : word) = Some W_15955c.
Proof. vm_refl. Qed.
Lemma D_15955c : decode_any W_15955c = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159560 : bv 32 := 0x10070693.
Lemma F_159560 : fetch_word Asan.M.loaded_segments (0x159564 : word) = Some W_159560.
Proof. vm_refl. Qed.
Lemma D_159560 : decode_any W_159560 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159564 : bv 32 := 0xffc67713.
Lemma F_159564 : fetch_word Asan.M.loaded_segments (0x159568 : word) = Some W_159564.
Proof. vm_refl. Qed.
Lemma D_159564 : decode_any W_159564 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159568 : bv 32 := 0x02d83633.
Lemma F_159568 : fetch_word Asan.M.loaded_segments (0x15956c : word) = Some W_159568.
Proof. vm_refl. Qed.
Lemma D_159568 : decode_any W_159568 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15956c : bv 32 := 0x00c5a023.
Lemma F_15956c : fetch_word Asan.M.loaded_segments (0x159570 : word) = Some W_15956c.
Proof. vm_refl. Qed.
Lemma D_15956c : decode_any W_15956c = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159570 : bv 32 := 0x00e586b3.
Lemma F_159570 : fetch_word Asan.M.loaded_segments (0x159574 : word) = Some W_159570.
Proof. vm_refl. Qed.
Lemma D_159570 : decode_any W_159570 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159574 : bv 32 := 0xfec6ae23.
Lemma F_159574 : fetch_word Asan.M.loaded_segments (0x159578 : word) = Some W_159574.
Proof. vm_refl. Qed.
Lemma D_159574 : decode_any W_159574 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159578 : bv 32 := 0x08f76063.
Lemma F_159578 : fetch_word Asan.M.loaded_segments (0x15957c : word) = Some W_159578.
Proof. vm_refl. Qed.
Lemma D_159578 : decode_any W_159578 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15957c : bv 32 := 0x00c5a223.
Lemma F_15957c : fetch_word Asan.M.loaded_segments (0x159580 : word) = Some W_15957c.
Proof. vm_refl. Qed.
Lemma D_15957c : decode_any W_15957c = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159580 : bv 32 := 0x00c5a423.
Lemma F_159580 : fetch_word Asan.M.loaded_segments (0x159584 : word) = Some W_159580.
Proof. vm_refl. Qed.
Lemma D_159580 : decode_any W_159580 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159584 : bv 32 := 0x01900793.
Lemma F_159584 : fetch_word Asan.M.loaded_segments (0x159588 : word) = Some W_159584.
Proof. vm_refl. Qed.
Lemma D_159584 : decode_any W_159584 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159588 : bv 32 := 0xfec6aa23.
Lemma F_159588 : fetch_word Asan.M.loaded_segments (0x15958c : word) = Some W_159588.
Proof. vm_refl. Qed.
Lemma D_159588 : decode_any W_159588 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15958c : bv 32 := 0xfec6ac23.
Lemma F_15958c : fetch_word Asan.M.loaded_segments (0x159590 : word) = Some W_15958c.
Proof. vm_refl. Qed.
Lemma D_15958c : decode_any W_15958c = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159590 : bv 32 := 0x06f76463.
Lemma F_159590 : fetch_word Asan.M.loaded_segments (0x159594 : word) = Some W_159590.
Proof. vm_refl. Qed.
Lemma D_159590 : decode_any W_159590 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159594 : bv 32 := 0x00c5a623.
Lemma F_159594 : fetch_word Asan.M.loaded_segments (0x159598 : word) = Some W_159594.
Proof. vm_refl. Qed.
Lemma D_159594 : decode_any W_159594 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159598 : bv 32 := 0x00c5a823.
Lemma F_159598 : fetch_word Asan.M.loaded_segments (0x15959c : word) = Some W_159598.
Proof. vm_refl. Qed.
Lemma D_159598 : decode_any W_159598 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15959c : bv 32 := 0x00c5aa23.
Lemma F_15959c : fetch_word Asan.M.loaded_segments (0x1595a0 : word) = Some W_15959c.
Proof. vm_refl. Qed.
Lemma D_15959c : decode_any W_15959c = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595a0 : bv 32 := 0x00c5ac23.
Lemma F_1595a0 : fetch_word Asan.M.loaded_segments (0x1595a4 : word) = Some W_1595a0.
Proof. vm_refl. Qed.
Lemma D_1595a0 : decode_any W_1595a0 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595a4 : bv 32 := 0x0045f793.
Lemma F_1595a4 : fetch_word Asan.M.loaded_segments (0x1595a8 : word) = Some W_1595a4.
Proof. vm_refl. Qed.
Lemma D_1595a4 : decode_any W_1595a4 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595a8 : bv 32 := 0x02000813.
Lemma F_1595a8 : fetch_word Asan.M.loaded_segments (0x1595ac : word) = Some W_1595a8.
Proof. vm_refl. Qed.
Lemma D_1595a8 : decode_any W_1595a8 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595ac : bv 32 := 0x01878793.
Lemma F_1595ac : fetch_word Asan.M.loaded_segments (0x1595b0 : word) = Some W_1595ac.
Proof. vm_refl. Qed.
Lemma D_1595ac : decode_any W_1595ac = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595b0 : bv 32 := 0x40f70733.
Lemma F_1595b0 : fetch_word Asan.M.loaded_segments (0x1595b4 : word) = Some W_1595b0.
Proof. vm_refl. Qed.
Lemma D_1595b0 : decode_any W_1595b0 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595b4 : bv 32 := 0xfec6a223.
Lemma F_1595b4 : fetch_word Asan.M.loaded_segments (0x1595b8 : word) = Some W_1595b4.
Proof. vm_refl. Qed.
Lemma D_1595b4 : decode_any W_1595b4 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595b8 : bv 32 := 0xfec6a423.
Lemma F_1595b8 : fetch_word Asan.M.loaded_segments (0x1595bc : word) = Some W_1595b8.
Proof. vm_refl. Qed.
Lemma D_1595b8 : decode_any W_1595b8 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595bc : bv 32 := 0xfec6a623.
Lemma F_1595bc : fetch_word Asan.M.loaded_segments (0x1595c0 : word) = Some W_1595bc.
Proof. vm_refl. Qed.
Lemma D_1595bc : decode_any W_1595bc = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595c0 : bv 32 := 0xfec6a823.
Lemma F_1595c0 : fetch_word Asan.M.loaded_segments (0x1595c4 : word) = Some W_1595c0.
Proof. vm_refl. Qed.
Lemma D_1595c0 : decode_any W_1595c0 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595c4 : bv 32 := 0x03076a63.
Lemma F_1595c4 : fetch_word Asan.M.loaded_segments (0x1595c8 : word) = Some W_1595c4.
Proof. vm_refl. Qed.
Lemma D_1595c4 : decode_any W_1595c4 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595c8 : bv 32 := 0x02061613.
Lemma F_1595c8 : fetch_word Asan.M.loaded_segments (0x1595cc : word) = Some W_1595c8.
Proof. vm_refl. Qed.
Lemma D_1595c8 : decode_any W_1595c8 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595cc : bv 32 := 0x00f585b3.
Lemma F_1595cc : fetch_word Asan.M.loaded_segments (0x1595d0 : word) = Some W_1595cc.
Proof. vm_refl. Qed.
Lemma D_1595cc : decode_any W_1595cc = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595d0 : bv 32 := 0x02065693.
Lemma F_1595d0 : fetch_word Asan.M.loaded_segments (0x1595d4 : word) = Some W_1595d0.
Proof. vm_refl. Qed.
Lemma D_1595d0 : decode_any W_1595d0 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595d4 : bv 32 := 0x00d66633.
Lemma F_1595d4 : fetch_word Asan.M.loaded_segments (0x1595d8 : word) = Some W_1595d4.
Proof. vm_refl. Qed.
Lemma D_1595d4 : decode_any W_1595d4 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595d8 : bv 32 := 0x01f00693.
Lemma F_1595d8 : fetch_word Asan.M.loaded_segments (0x1595dc : word) = Some W_1595d8.
Proof. vm_refl. Qed.
Lemma D_1595d8 : decode_any W_1595d8 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595dc : bv 32 := 0x00c5b023.
Lemma F_1595dc : fetch_word Asan.M.loaded_segments (0x1595e0 : word) = Some W_1595dc.
Proof. vm_refl. Qed.
Lemma D_1595dc : decode_any W_1595dc = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595e0 : bv 32 := 0x00c5b423.
Lemma F_1595e0 : fetch_word Asan.M.loaded_segments (0x1595e4 : word) = Some W_1595e0.
Proof. vm_refl. Qed.
Lemma D_1595e0 : decode_any W_1595e0 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595e4 : bv 32 := 0x00c5b823.
Lemma F_1595e4 : fetch_word Asan.M.loaded_segments (0x1595e8 : word) = Some W_1595e4.
Proof. vm_refl. Qed.
Lemma D_1595e4 : decode_any W_1595e4 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595e8 : bv 32 := 0x00c5bc23.
Lemma F_1595e8 : fetch_word Asan.M.loaded_segments (0x1595ec : word) = Some W_1595e8.
Proof. vm_refl. Qed.
Lemma D_1595e8 : decode_any W_1595e8 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595ec : bv 32 := 0xfe070713.
Lemma F_1595ec : fetch_word Asan.M.loaded_segments (0x1595f0 : word) = Some W_1595ec.
Proof. vm_refl. Qed.
Lemma D_1595ec : decode_any W_1595ec = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595f0 : bv 32 := 0x02058593.
Lemma F_1595f0 : fetch_word Asan.M.loaded_segments (0x1595f4 : word) = Some W_1595f0.
Proof. vm_refl. Qed.
Lemma D_1595f0 : decode_any W_1595f0 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595f4 : bv 32 := 0xfee6e4e3.
Lemma F_1595f4 : fetch_word Asan.M.loaded_segments (0x1595f8 : word) = Some W_1595f4.
Proof. vm_refl. Qed.
Lemma D_1595f4 : decode_any W_1595f4 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1595f8 : bv 32 := 0x00008067.
Lemma F_1595f8 : fetch_word Asan.M.loaded_segments (0x1595fc : word) = Some W_1595f8.
Proof. vm_refl. Qed.
Lemma D_1595f8 : decode_any W_1595f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0x159508%Z.
Definition Fo_000 := F_159504.
Definition Do_000 := D_159504.
Definition Fo_004 := F_159508.
Definition Do_004 := D_159508.
Definition Fo_008 := F_15950c.
Definition Do_008 := D_15950c.
Definition Fo_00c := F_159510.
Definition Do_00c := D_159510.
Definition Fo_010 := F_159514.
Definition Do_010 := D_159514.
Definition Fo_014 := F_159518.
Definition Do_014 := D_159518.
Definition Fo_018 := F_15951c.
Definition Do_018 := D_15951c.
Definition Fo_01c := F_159520.
Definition Do_01c := D_159520.
Definition Fo_020 := F_159524.
Definition Do_020 := D_159524.
Definition Fo_024 := F_159528.
Definition Do_024 := D_159528.
Definition Fo_028 := F_15952c.
Definition Do_028 := D_15952c.
Definition Fo_02c := F_159530.
Definition Do_02c := D_159530.
Definition Fo_030 := F_159534.
Definition Do_030 := D_159534.
Definition Fo_034 := F_159538.
Definition Do_034 := D_159538.
Definition Fo_038 := F_15953c.
Definition Do_038 := D_15953c.
Definition Fo_03c := F_159540.
Definition Do_03c := D_159540.
Definition Fo_040 := F_159544.
Definition Do_040 := D_159544.
Definition Fo_044 := F_159548.
Definition Do_044 := D_159548.
Definition Fo_048 := F_15954c.
Definition Do_048 := D_15954c.
Definition Fo_04c := F_159550.
Definition Do_04c := D_159550.
Definition Fo_050 := F_159554.
Definition Do_050 := D_159554.
Definition Fo_054 := F_159558.
Definition Do_054 := D_159558.
Definition Fo_058 := F_15955c.
Definition Do_058 := D_15955c.
Definition Fo_05c := F_159560.
Definition Do_05c := D_159560.
Definition Fo_060 := F_159564.
Definition Do_060 := D_159564.
Definition Fo_064 := F_159568.
Definition Do_064 := D_159568.
Definition Fo_068 := F_15956c.
Definition Do_068 := D_15956c.
Definition Fo_06c := F_159570.
Definition Do_06c := D_159570.
Definition Fo_070 := F_159574.
Definition Do_070 := D_159574.
Definition Fo_074 := F_159578.
Definition Do_074 := D_159578.
Definition Fo_078 := F_15957c.
Definition Do_078 := D_15957c.
Definition Fo_07c := F_159580.
Definition Do_07c := D_159580.
Definition Fo_080 := F_159584.
Definition Do_080 := D_159584.
Definition Fo_084 := F_159588.
Definition Do_084 := D_159588.
Definition Fo_088 := F_15958c.
Definition Do_088 := D_15958c.
Definition Fo_08c := F_159590.
Definition Do_08c := D_159590.
Definition Fo_090 := F_159594.
Definition Do_090 := D_159594.
Definition Fo_094 := F_159598.
Definition Do_094 := D_159598.
Definition Fo_098 := F_15959c.
Definition Do_098 := D_15959c.
Definition Fo_09c := F_1595a0.
Definition Do_09c := D_1595a0.
Definition Fo_0a0 := F_1595a4.
Definition Do_0a0 := D_1595a4.
Definition Fo_0a4 := F_1595a8.
Definition Do_0a4 := D_1595a8.
Definition Fo_0a8 := F_1595ac.
Definition Do_0a8 := D_1595ac.
Definition Fo_0ac := F_1595b0.
Definition Do_0ac := D_1595b0.
Definition Fo_0b0 := F_1595b4.
Definition Do_0b0 := D_1595b4.
Definition Fo_0b4 := F_1595b8.
Definition Do_0b4 := D_1595b8.
Definition Fo_0b8 := F_1595bc.
Definition Do_0b8 := D_1595bc.
Definition Fo_0bc := F_1595c0.
Definition Do_0bc := D_1595c0.
Definition Fo_0c0 := F_1595c4.
Definition Do_0c0 := D_1595c4.
Definition Fo_0c4 := F_1595c8.
Definition Do_0c4 := D_1595c8.
Definition Fo_0c8 := F_1595cc.
Definition Do_0c8 := D_1595cc.
Definition Fo_0cc := F_1595d0.
Definition Do_0cc := D_1595d0.
Definition Fo_0d0 := F_1595d4.
Definition Do_0d0 := D_1595d4.
Definition Fo_0d4 := F_1595d8.
Definition Do_0d4 := D_1595d8.
Definition Fo_0d8 := F_1595dc.
Definition Do_0d8 := D_1595dc.
Definition Fo_0dc := F_1595e0.
Definition Do_0dc := D_1595e0.
Definition Fo_0e0 := F_1595e4.
Definition Do_0e0 := D_1595e4.
Definition Fo_0e4 := F_1595e8.
Definition Do_0e4 := D_1595e8.
Definition Fo_0e8 := F_1595ec.
Definition Do_0e8 := D_1595ec.
Definition Fo_0ec := F_1595f0.
Definition Do_0ec := D_1595f0.
Definition Fo_0f0 := F_1595f4.
Definition Do_0f0 := D_1595f4.
Definition Fo_0f4 := F_1595f8.
Definition Do_0f4 := D_1595f8.
