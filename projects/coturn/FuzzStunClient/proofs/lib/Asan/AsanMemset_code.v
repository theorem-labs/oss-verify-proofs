(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_a45b0 : bv 32 := 0x0e060a63.
Lemma F_a45b0 : fetch_word Asan.M.loaded_segments (0xa45b0 : word) = Some W_a45b0.
Proof. vm_refl. Qed.
Lemma D_a45b0 : decode_any W_a45b0 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a45b4 : bv 32 := 0x00b50023.
Lemma F_a45b4 : fetch_word Asan.M.loaded_segments (0xa45b4 : word) = Some W_a45b4.
Proof. vm_refl. Qed.
Lemma D_a45b4 : decode_any W_a45b4 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a45b8 : bv 32 := 0x00c506b3.
Lemma F_a45b8 : fetch_word Asan.M.loaded_segments (0xa45b8 : word) = Some W_a45b8.
Proof. vm_refl. Qed.
Lemma D_a45b8 : decode_any W_a45b8 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a45bc : bv 32 := 0x00300713.
Lemma F_a45bc : fetch_word Asan.M.loaded_segments (0xa45bc : word) = Some W_a45bc.
Proof. vm_refl. Qed.
Lemma D_a45bc : decode_any W_a45bc = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a45c0 : bv 32 := 0xfeb68fa3.
Lemma F_a45c0 : fetch_word Asan.M.loaded_segments (0xa45c0 : word) = Some W_a45c0.
Proof. vm_refl. Qed.
Lemma D_a45c0 : decode_any W_a45c0 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a45c4 : bv 32 := 0x0ee66063.
Lemma F_a45c4 : fetch_word Asan.M.loaded_segments (0xa45c4 : word) = Some W_a45c4.
Proof. vm_refl. Qed.
Lemma D_a45c4 : decode_any W_a45c4 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a45c8 : bv 32 := 0x00b500a3.
Lemma F_a45c8 : fetch_word Asan.M.loaded_segments (0xa45c8 : word) = Some W_a45c8.
Proof. vm_refl. Qed.
Lemma D_a45c8 : decode_any W_a45c8 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a45cc : bv 32 := 0x00b50123.
Lemma F_a45cc : fetch_word Asan.M.loaded_segments (0xa45cc : word) = Some W_a45cc.
Proof. vm_refl. Qed.
Lemma D_a45cc : decode_any W_a45cc = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a45d0 : bv 32 := 0x00700713.
Lemma F_a45d0 : fetch_word Asan.M.loaded_segments (0xa45d0 : word) = Some W_a45d0.
Proof. vm_refl. Qed.
Lemma D_a45d0 : decode_any W_a45d0 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a45d4 : bv 32 := 0xfeb68ea3.
Lemma F_a45d4 : fetch_word Asan.M.loaded_segments (0xa45d4 : word) = Some W_a45d4.
Proof. vm_refl. Qed.
Lemma D_a45d4 : decode_any W_a45d4 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a45d8 : bv 32 := 0xfeb68f23.
Lemma F_a45d8 : fetch_word Asan.M.loaded_segments (0xa45d8 : word) = Some W_a45d8.
Proof. vm_refl. Qed.
Lemma D_a45d8 : decode_any W_a45d8 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a45dc : bv 32 := 0x0ce66463.
Lemma F_a45dc : fetch_word Asan.M.loaded_segments (0xa45dc : word) = Some W_a45dc.
Proof. vm_refl. Qed.
Lemma D_a45dc : decode_any W_a45dc = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a45e0 : bv 32 := 0x00b501a3.
Lemma F_a45e0 : fetch_word Asan.M.loaded_segments (0xa45e0 : word) = Some W_a45e0.
Proof. vm_refl. Qed.
Lemma D_a45e0 : decode_any W_a45e0 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a45e4 : bv 32 := 0x00900793.
Lemma F_a45e4 : fetch_word Asan.M.loaded_segments (0xa45e4 : word) = Some W_a45e4.
Proof. vm_refl. Qed.
Lemma D_a45e4 : decode_any W_a45e4 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a45e8 : bv 32 := 0xfeb68e23.
Lemma F_a45e8 : fetch_word Asan.M.loaded_segments (0xa45e8 : word) = Some W_a45e8.
Proof. vm_refl. Qed.
Lemma D_a45e8 : decode_any W_a45e8 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a45ec : bv 32 := 0x0af66c63.
Lemma F_a45ec : fetch_word Asan.M.loaded_segments (0xa45ec : word) = Some W_a45ec.
Proof. vm_refl. Qed.
Lemma D_a45ec : decode_any W_a45ec = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a45f0 : bv 32 := 0x40a006bb.
Lemma F_a45f0 : fetch_word Asan.M.loaded_segments (0xa45f0 : word) = Some W_a45f0.
Proof. vm_refl. Qed.
Lemma D_a45f0 : decode_any W_a45f0 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a45f4 : bv 32 := 0x03859813.
Lemma F_a45f4 : fetch_word Asan.M.loaded_segments (0xa45f4 : word) = Some W_a45f4.
Proof. vm_refl. Qed.
Lemma D_a45f4 : decode_any W_a45f4 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a45f8 : bv 32 := 0x101015b7.
Lemma F_a45f8 : fetch_word Asan.M.loaded_segments (0xa45f8 : word) = Some W_a45f8.
Proof. vm_refl. Qed.
Lemma D_a45f8 : decode_any W_a45f8 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a45fc : bv 32 := 0x0036f693.
Lemma F_a45fc : fetch_word Asan.M.loaded_segments (0xa45fc : word) = Some W_a45fc.
Proof. vm_refl. Qed.
Lemma D_a45fc : decode_any W_a45fc = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4600 : bv 32 := 0x00459713.
Lemma F_a4600 : fetch_word Asan.M.loaded_segments (0xa4600 : word) = Some W_a4600.
Proof. vm_refl. Qed.
Lemma D_a4600 : decode_any W_a4600 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4604 : bv 32 := 0x40d60633.
Lemma F_a4604 : fetch_word Asan.M.loaded_segments (0xa4604 : word) = Some W_a4604.
Proof. vm_refl. Qed.
Lemma D_a4604 : decode_any W_a4604 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4608 : bv 32 := 0x00d505b3.
Lemma F_a4608 : fetch_word Asan.M.loaded_segments (0xa4608 : word) = Some W_a4608.
Proof. vm_refl. Qed.
Lemma D_a4608 : decode_any W_a4608 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a460c : bv 32 := 0x10070693.
Lemma F_a460c : fetch_word Asan.M.loaded_segments (0xa460c : word) = Some W_a460c.
Proof. vm_refl. Qed.
Lemma D_a460c : decode_any W_a460c = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4610 : bv 32 := 0xffc67713.
Lemma F_a4610 : fetch_word Asan.M.loaded_segments (0xa4610 : word) = Some W_a4610.
Proof. vm_refl. Qed.
Lemma D_a4610 : decode_any W_a4610 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4614 : bv 32 := 0x02d83633.
Lemma F_a4614 : fetch_word Asan.M.loaded_segments (0xa4614 : word) = Some W_a4614.
Proof. vm_refl. Qed.
Lemma D_a4614 : decode_any W_a4614 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4618 : bv 32 := 0x00c5a023.
Lemma F_a4618 : fetch_word Asan.M.loaded_segments (0xa4618 : word) = Some W_a4618.
Proof. vm_refl. Qed.
Lemma D_a4618 : decode_any W_a4618 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a461c : bv 32 := 0x00e586b3.
Lemma F_a461c : fetch_word Asan.M.loaded_segments (0xa461c : word) = Some W_a461c.
Proof. vm_refl. Qed.
Lemma D_a461c : decode_any W_a461c = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4620 : bv 32 := 0xfec6ae23.
Lemma F_a4620 : fetch_word Asan.M.loaded_segments (0xa4620 : word) = Some W_a4620.
Proof. vm_refl. Qed.
Lemma D_a4620 : decode_any W_a4620 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4624 : bv 32 := 0x08f76063.
Lemma F_a4624 : fetch_word Asan.M.loaded_segments (0xa4624 : word) = Some W_a4624.
Proof. vm_refl. Qed.
Lemma D_a4624 : decode_any W_a4624 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4628 : bv 32 := 0x00c5a223.
Lemma F_a4628 : fetch_word Asan.M.loaded_segments (0xa4628 : word) = Some W_a4628.
Proof. vm_refl. Qed.
Lemma D_a4628 : decode_any W_a4628 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a462c : bv 32 := 0x00c5a423.
Lemma F_a462c : fetch_word Asan.M.loaded_segments (0xa462c : word) = Some W_a462c.
Proof. vm_refl. Qed.
Lemma D_a462c : decode_any W_a462c = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4630 : bv 32 := 0x01900793.
Lemma F_a4630 : fetch_word Asan.M.loaded_segments (0xa4630 : word) = Some W_a4630.
Proof. vm_refl. Qed.
Lemma D_a4630 : decode_any W_a4630 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4634 : bv 32 := 0xfec6aa23.
Lemma F_a4634 : fetch_word Asan.M.loaded_segments (0xa4634 : word) = Some W_a4634.
Proof. vm_refl. Qed.
Lemma D_a4634 : decode_any W_a4634 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4638 : bv 32 := 0xfec6ac23.
Lemma F_a4638 : fetch_word Asan.M.loaded_segments (0xa4638 : word) = Some W_a4638.
Proof. vm_refl. Qed.
Lemma D_a4638 : decode_any W_a4638 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a463c : bv 32 := 0x06f76463.
Lemma F_a463c : fetch_word Asan.M.loaded_segments (0xa463c : word) = Some W_a463c.
Proof. vm_refl. Qed.
Lemma D_a463c : decode_any W_a463c = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4640 : bv 32 := 0x00c5a623.
Lemma F_a4640 : fetch_word Asan.M.loaded_segments (0xa4640 : word) = Some W_a4640.
Proof. vm_refl. Qed.
Lemma D_a4640 : decode_any W_a4640 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4644 : bv 32 := 0x00c5a823.
Lemma F_a4644 : fetch_word Asan.M.loaded_segments (0xa4644 : word) = Some W_a4644.
Proof. vm_refl. Qed.
Lemma D_a4644 : decode_any W_a4644 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4648 : bv 32 := 0x00c5aa23.
Lemma F_a4648 : fetch_word Asan.M.loaded_segments (0xa4648 : word) = Some W_a4648.
Proof. vm_refl. Qed.
Lemma D_a4648 : decode_any W_a4648 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a464c : bv 32 := 0x00c5ac23.
Lemma F_a464c : fetch_word Asan.M.loaded_segments (0xa464c : word) = Some W_a464c.
Proof. vm_refl. Qed.
Lemma D_a464c : decode_any W_a464c = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4650 : bv 32 := 0x0045f793.
Lemma F_a4650 : fetch_word Asan.M.loaded_segments (0xa4650 : word) = Some W_a4650.
Proof. vm_refl. Qed.
Lemma D_a4650 : decode_any W_a4650 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4654 : bv 32 := 0x02000813.
Lemma F_a4654 : fetch_word Asan.M.loaded_segments (0xa4654 : word) = Some W_a4654.
Proof. vm_refl. Qed.
Lemma D_a4654 : decode_any W_a4654 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4658 : bv 32 := 0x01878793.
Lemma F_a4658 : fetch_word Asan.M.loaded_segments (0xa4658 : word) = Some W_a4658.
Proof. vm_refl. Qed.
Lemma D_a4658 : decode_any W_a4658 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a465c : bv 32 := 0x40f70733.
Lemma F_a465c : fetch_word Asan.M.loaded_segments (0xa465c : word) = Some W_a465c.
Proof. vm_refl. Qed.
Lemma D_a465c : decode_any W_a465c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4660 : bv 32 := 0xfec6a223.
Lemma F_a4660 : fetch_word Asan.M.loaded_segments (0xa4660 : word) = Some W_a4660.
Proof. vm_refl. Qed.
Lemma D_a4660 : decode_any W_a4660 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4664 : bv 32 := 0xfec6a423.
Lemma F_a4664 : fetch_word Asan.M.loaded_segments (0xa4664 : word) = Some W_a4664.
Proof. vm_refl. Qed.
Lemma D_a4664 : decode_any W_a4664 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4668 : bv 32 := 0xfec6a623.
Lemma F_a4668 : fetch_word Asan.M.loaded_segments (0xa4668 : word) = Some W_a4668.
Proof. vm_refl. Qed.
Lemma D_a4668 : decode_any W_a4668 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a466c : bv 32 := 0xfec6a823.
Lemma F_a466c : fetch_word Asan.M.loaded_segments (0xa466c : word) = Some W_a466c.
Proof. vm_refl. Qed.
Lemma D_a466c : decode_any W_a466c = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4670 : bv 32 := 0x03076a63.
Lemma F_a4670 : fetch_word Asan.M.loaded_segments (0xa4670 : word) = Some W_a4670.
Proof. vm_refl. Qed.
Lemma D_a4670 : decode_any W_a4670 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4674 : bv 32 := 0x02061613.
Lemma F_a4674 : fetch_word Asan.M.loaded_segments (0xa4674 : word) = Some W_a4674.
Proof. vm_refl. Qed.
Lemma D_a4674 : decode_any W_a4674 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4678 : bv 32 := 0x00f585b3.
Lemma F_a4678 : fetch_word Asan.M.loaded_segments (0xa4678 : word) = Some W_a4678.
Proof. vm_refl. Qed.
Lemma D_a4678 : decode_any W_a4678 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a467c : bv 32 := 0x02065693.
Lemma F_a467c : fetch_word Asan.M.loaded_segments (0xa467c : word) = Some W_a467c.
Proof. vm_refl. Qed.
Lemma D_a467c : decode_any W_a467c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4680 : bv 32 := 0x00d66633.
Lemma F_a4680 : fetch_word Asan.M.loaded_segments (0xa4680 : word) = Some W_a4680.
Proof. vm_refl. Qed.
Lemma D_a4680 : decode_any W_a4680 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4684 : bv 32 := 0x01f00693.
Lemma F_a4684 : fetch_word Asan.M.loaded_segments (0xa4684 : word) = Some W_a4684.
Proof. vm_refl. Qed.
Lemma D_a4684 : decode_any W_a4684 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4688 : bv 32 := 0x00c5b023.
Lemma F_a4688 : fetch_word Asan.M.loaded_segments (0xa4688 : word) = Some W_a4688.
Proof. vm_refl. Qed.
Lemma D_a4688 : decode_any W_a4688 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a468c : bv 32 := 0x00c5b423.
Lemma F_a468c : fetch_word Asan.M.loaded_segments (0xa468c : word) = Some W_a468c.
Proof. vm_refl. Qed.
Lemma D_a468c : decode_any W_a468c = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4690 : bv 32 := 0x00c5b823.
Lemma F_a4690 : fetch_word Asan.M.loaded_segments (0xa4690 : word) = Some W_a4690.
Proof. vm_refl. Qed.
Lemma D_a4690 : decode_any W_a4690 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4694 : bv 32 := 0x00c5bc23.
Lemma F_a4694 : fetch_word Asan.M.loaded_segments (0xa4694 : word) = Some W_a4694.
Proof. vm_refl. Qed.
Lemma D_a4694 : decode_any W_a4694 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4698 : bv 32 := 0xfe070713.
Lemma F_a4698 : fetch_word Asan.M.loaded_segments (0xa4698 : word) = Some W_a4698.
Proof. vm_refl. Qed.
Lemma D_a4698 : decode_any W_a4698 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a469c : bv 32 := 0x02058593.
Lemma F_a469c : fetch_word Asan.M.loaded_segments (0xa469c : word) = Some W_a469c.
Proof. vm_refl. Qed.
Lemma D_a469c : decode_any W_a469c = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a46a0 : bv 32 := 0xfee6e4e3.
Lemma F_a46a0 : fetch_word Asan.M.loaded_segments (0xa46a0 : word) = Some W_a46a0.
Proof. vm_refl. Qed.
Lemma D_a46a0 : decode_any W_a46a0 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a46a4 : bv 32 := 0x00008067.
Lemma F_a46a4 : fetch_word Asan.M.loaded_segments (0xa46a4 : word) = Some W_a46a4.
Proof. vm_refl. Qed.
Lemma D_a46a4 : decode_any W_a46a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0xa45b0%Z.
Definition Fo_000 := F_a45b0.
Definition Do_000 := D_a45b0.
Definition Fo_004 := F_a45b4.
Definition Do_004 := D_a45b4.
Definition Fo_008 := F_a45b8.
Definition Do_008 := D_a45b8.
Definition Fo_00c := F_a45bc.
Definition Do_00c := D_a45bc.
Definition Fo_010 := F_a45c0.
Definition Do_010 := D_a45c0.
Definition Fo_014 := F_a45c4.
Definition Do_014 := D_a45c4.
Definition Fo_018 := F_a45c8.
Definition Do_018 := D_a45c8.
Definition Fo_01c := F_a45cc.
Definition Do_01c := D_a45cc.
Definition Fo_020 := F_a45d0.
Definition Do_020 := D_a45d0.
Definition Fo_024 := F_a45d4.
Definition Do_024 := D_a45d4.
Definition Fo_028 := F_a45d8.
Definition Do_028 := D_a45d8.
Definition Fo_02c := F_a45dc.
Definition Do_02c := D_a45dc.
Definition Fo_030 := F_a45e0.
Definition Do_030 := D_a45e0.
Definition Fo_034 := F_a45e4.
Definition Do_034 := D_a45e4.
Definition Fo_038 := F_a45e8.
Definition Do_038 := D_a45e8.
Definition Fo_03c := F_a45ec.
Definition Do_03c := D_a45ec.
Definition Fo_040 := F_a45f0.
Definition Do_040 := D_a45f0.
Definition Fo_044 := F_a45f4.
Definition Do_044 := D_a45f4.
Definition Fo_048 := F_a45f8.
Definition Do_048 := D_a45f8.
Definition Fo_04c := F_a45fc.
Definition Do_04c := D_a45fc.
Definition Fo_050 := F_a4600.
Definition Do_050 := D_a4600.
Definition Fo_054 := F_a4604.
Definition Do_054 := D_a4604.
Definition Fo_058 := F_a4608.
Definition Do_058 := D_a4608.
Definition Fo_05c := F_a460c.
Definition Do_05c := D_a460c.
Definition Fo_060 := F_a4610.
Definition Do_060 := D_a4610.
Definition Fo_064 := F_a4614.
Definition Do_064 := D_a4614.
Definition Fo_068 := F_a4618.
Definition Do_068 := D_a4618.
Definition Fo_06c := F_a461c.
Definition Do_06c := D_a461c.
Definition Fo_070 := F_a4620.
Definition Do_070 := D_a4620.
Definition Fo_074 := F_a4624.
Definition Do_074 := D_a4624.
Definition Fo_078 := F_a4628.
Definition Do_078 := D_a4628.
Definition Fo_07c := F_a462c.
Definition Do_07c := D_a462c.
Definition Fo_080 := F_a4630.
Definition Do_080 := D_a4630.
Definition Fo_084 := F_a4634.
Definition Do_084 := D_a4634.
Definition Fo_088 := F_a4638.
Definition Do_088 := D_a4638.
Definition Fo_08c := F_a463c.
Definition Do_08c := D_a463c.
Definition Fo_090 := F_a4640.
Definition Do_090 := D_a4640.
Definition Fo_094 := F_a4644.
Definition Do_094 := D_a4644.
Definition Fo_098 := F_a4648.
Definition Do_098 := D_a4648.
Definition Fo_09c := F_a464c.
Definition Do_09c := D_a464c.
Definition Fo_0a0 := F_a4650.
Definition Do_0a0 := D_a4650.
Definition Fo_0a4 := F_a4654.
Definition Do_0a4 := D_a4654.
Definition Fo_0a8 := F_a4658.
Definition Do_0a8 := D_a4658.
Definition Fo_0ac := F_a465c.
Definition Do_0ac := D_a465c.
Definition Fo_0b0 := F_a4660.
Definition Do_0b0 := D_a4660.
Definition Fo_0b4 := F_a4664.
Definition Do_0b4 := D_a4664.
Definition Fo_0b8 := F_a4668.
Definition Do_0b8 := D_a4668.
Definition Fo_0bc := F_a466c.
Definition Do_0bc := D_a466c.
Definition Fo_0c0 := F_a4670.
Definition Do_0c0 := D_a4670.
Definition Fo_0c4 := F_a4674.
Definition Do_0c4 := D_a4674.
Definition Fo_0c8 := F_a4678.
Definition Do_0c8 := D_a4678.
Definition Fo_0cc := F_a467c.
Definition Do_0cc := D_a467c.
Definition Fo_0d0 := F_a4680.
Definition Do_0d0 := D_a4680.
Definition Fo_0d4 := F_a4684.
Definition Do_0d4 := D_a4684.
Definition Fo_0d8 := F_a4688.
Definition Do_0d8 := D_a4688.
Definition Fo_0dc := F_a468c.
Definition Do_0dc := D_a468c.
Definition Fo_0e0 := F_a4690.
Definition Do_0e0 := D_a4690.
Definition Fo_0e4 := F_a4694.
Definition Do_0e4 := D_a4694.
Definition Fo_0e8 := F_a4698.
Definition Do_0e8 := D_a4698.
Definition Fo_0ec := F_a469c.
Definition Do_0ec := D_a469c.
Definition Fo_0f0 := F_a46a0.
Definition Do_0f0 := D_a46a0.
Definition Fo_0f4 := F_a46a4.
Definition Do_0f4 := D_a46a4.
