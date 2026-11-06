(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
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
From OSSVerify.leptonica.fhmtgen_fuzzer.images Require Import Asan.
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
Definition W_da5e0 : bv 32 := 0x0e060a63.
Lemma F_da5e0 : fetch_word Asan.M.loaded_segments (0xda744 : word) = Some W_da5e0.
Proof. vm_refl. Qed.
Lemma D_da5e0 : decode_any W_da5e0 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5e4 : bv 32 := 0x00b50023.
Lemma F_da5e4 : fetch_word Asan.M.loaded_segments (0xda748 : word) = Some W_da5e4.
Proof. vm_refl. Qed.
Lemma D_da5e4 : decode_any W_da5e4 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5e8 : bv 32 := 0x00c506b3.
Lemma F_da5e8 : fetch_word Asan.M.loaded_segments (0xda74c : word) = Some W_da5e8.
Proof. vm_refl. Qed.
Lemma D_da5e8 : decode_any W_da5e8 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5ec : bv 32 := 0x00300713.
Lemma F_da5ec : fetch_word Asan.M.loaded_segments (0xda750 : word) = Some W_da5ec.
Proof. vm_refl. Qed.
Lemma D_da5ec : decode_any W_da5ec = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5f0 : bv 32 := 0xfeb68fa3.
Lemma F_da5f0 : fetch_word Asan.M.loaded_segments (0xda754 : word) = Some W_da5f0.
Proof. vm_refl. Qed.
Lemma D_da5f0 : decode_any W_da5f0 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5f4 : bv 32 := 0x0ee66063.
Lemma F_da5f4 : fetch_word Asan.M.loaded_segments (0xda758 : word) = Some W_da5f4.
Proof. vm_refl. Qed.
Lemma D_da5f4 : decode_any W_da5f4 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5f8 : bv 32 := 0x00b500a3.
Lemma F_da5f8 : fetch_word Asan.M.loaded_segments (0xda75c : word) = Some W_da5f8.
Proof. vm_refl. Qed.
Lemma D_da5f8 : decode_any W_da5f8 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da5fc : bv 32 := 0x00b50123.
Lemma F_da5fc : fetch_word Asan.M.loaded_segments (0xda760 : word) = Some W_da5fc.
Proof. vm_refl. Qed.
Lemma D_da5fc : decode_any W_da5fc = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da600 : bv 32 := 0x00700713.
Lemma F_da600 : fetch_word Asan.M.loaded_segments (0xda764 : word) = Some W_da600.
Proof. vm_refl. Qed.
Lemma D_da600 : decode_any W_da600 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da604 : bv 32 := 0xfeb68ea3.
Lemma F_da604 : fetch_word Asan.M.loaded_segments (0xda768 : word) = Some W_da604.
Proof. vm_refl. Qed.
Lemma D_da604 : decode_any W_da604 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da608 : bv 32 := 0xfeb68f23.
Lemma F_da608 : fetch_word Asan.M.loaded_segments (0xda76c : word) = Some W_da608.
Proof. vm_refl. Qed.
Lemma D_da608 : decode_any W_da608 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da60c : bv 32 := 0x0ce66463.
Lemma F_da60c : fetch_word Asan.M.loaded_segments (0xda770 : word) = Some W_da60c.
Proof. vm_refl. Qed.
Lemma D_da60c : decode_any W_da60c = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da610 : bv 32 := 0x00b501a3.
Lemma F_da610 : fetch_word Asan.M.loaded_segments (0xda774 : word) = Some W_da610.
Proof. vm_refl. Qed.
Lemma D_da610 : decode_any W_da610 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da614 : bv 32 := 0x00900793.
Lemma F_da614 : fetch_word Asan.M.loaded_segments (0xda778 : word) = Some W_da614.
Proof. vm_refl. Qed.
Lemma D_da614 : decode_any W_da614 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da618 : bv 32 := 0xfeb68e23.
Lemma F_da618 : fetch_word Asan.M.loaded_segments (0xda77c : word) = Some W_da618.
Proof. vm_refl. Qed.
Lemma D_da618 : decode_any W_da618 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da61c : bv 32 := 0x0af66c63.
Lemma F_da61c : fetch_word Asan.M.loaded_segments (0xda780 : word) = Some W_da61c.
Proof. vm_refl. Qed.
Lemma D_da61c : decode_any W_da61c = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da620 : bv 32 := 0x40a006bb.
Lemma F_da620 : fetch_word Asan.M.loaded_segments (0xda784 : word) = Some W_da620.
Proof. vm_refl. Qed.
Lemma D_da620 : decode_any W_da620 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da624 : bv 32 := 0x03859813.
Lemma F_da624 : fetch_word Asan.M.loaded_segments (0xda788 : word) = Some W_da624.
Proof. vm_refl. Qed.
Lemma D_da624 : decode_any W_da624 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da628 : bv 32 := 0x101015b7.
Lemma F_da628 : fetch_word Asan.M.loaded_segments (0xda78c : word) = Some W_da628.
Proof. vm_refl. Qed.
Lemma D_da628 : decode_any W_da628 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da62c : bv 32 := 0x0036f693.
Lemma F_da62c : fetch_word Asan.M.loaded_segments (0xda790 : word) = Some W_da62c.
Proof. vm_refl. Qed.
Lemma D_da62c : decode_any W_da62c = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da630 : bv 32 := 0x00459713.
Lemma F_da630 : fetch_word Asan.M.loaded_segments (0xda794 : word) = Some W_da630.
Proof. vm_refl. Qed.
Lemma D_da630 : decode_any W_da630 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da634 : bv 32 := 0x40d60633.
Lemma F_da634 : fetch_word Asan.M.loaded_segments (0xda798 : word) = Some W_da634.
Proof. vm_refl. Qed.
Lemma D_da634 : decode_any W_da634 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da638 : bv 32 := 0x00d505b3.
Lemma F_da638 : fetch_word Asan.M.loaded_segments (0xda79c : word) = Some W_da638.
Proof. vm_refl. Qed.
Lemma D_da638 : decode_any W_da638 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da63c : bv 32 := 0x10070693.
Lemma F_da63c : fetch_word Asan.M.loaded_segments (0xda7a0 : word) = Some W_da63c.
Proof. vm_refl. Qed.
Lemma D_da63c : decode_any W_da63c = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da640 : bv 32 := 0xffc67713.
Lemma F_da640 : fetch_word Asan.M.loaded_segments (0xda7a4 : word) = Some W_da640.
Proof. vm_refl. Qed.
Lemma D_da640 : decode_any W_da640 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da644 : bv 32 := 0x02d83633.
Lemma F_da644 : fetch_word Asan.M.loaded_segments (0xda7a8 : word) = Some W_da644.
Proof. vm_refl. Qed.
Lemma D_da644 : decode_any W_da644 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da648 : bv 32 := 0x00c5a023.
Lemma F_da648 : fetch_word Asan.M.loaded_segments (0xda7ac : word) = Some W_da648.
Proof. vm_refl. Qed.
Lemma D_da648 : decode_any W_da648 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da64c : bv 32 := 0x00e586b3.
Lemma F_da64c : fetch_word Asan.M.loaded_segments (0xda7b0 : word) = Some W_da64c.
Proof. vm_refl. Qed.
Lemma D_da64c : decode_any W_da64c = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da650 : bv 32 := 0xfec6ae23.
Lemma F_da650 : fetch_word Asan.M.loaded_segments (0xda7b4 : word) = Some W_da650.
Proof. vm_refl. Qed.
Lemma D_da650 : decode_any W_da650 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da654 : bv 32 := 0x08f76063.
Lemma F_da654 : fetch_word Asan.M.loaded_segments (0xda7b8 : word) = Some W_da654.
Proof. vm_refl. Qed.
Lemma D_da654 : decode_any W_da654 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da658 : bv 32 := 0x00c5a223.
Lemma F_da658 : fetch_word Asan.M.loaded_segments (0xda7bc : word) = Some W_da658.
Proof. vm_refl. Qed.
Lemma D_da658 : decode_any W_da658 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da65c : bv 32 := 0x00c5a423.
Lemma F_da65c : fetch_word Asan.M.loaded_segments (0xda7c0 : word) = Some W_da65c.
Proof. vm_refl. Qed.
Lemma D_da65c : decode_any W_da65c = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da660 : bv 32 := 0x01900793.
Lemma F_da660 : fetch_word Asan.M.loaded_segments (0xda7c4 : word) = Some W_da660.
Proof. vm_refl. Qed.
Lemma D_da660 : decode_any W_da660 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da664 : bv 32 := 0xfec6aa23.
Lemma F_da664 : fetch_word Asan.M.loaded_segments (0xda7c8 : word) = Some W_da664.
Proof. vm_refl. Qed.
Lemma D_da664 : decode_any W_da664 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da668 : bv 32 := 0xfec6ac23.
Lemma F_da668 : fetch_word Asan.M.loaded_segments (0xda7cc : word) = Some W_da668.
Proof. vm_refl. Qed.
Lemma D_da668 : decode_any W_da668 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da66c : bv 32 := 0x06f76463.
Lemma F_da66c : fetch_word Asan.M.loaded_segments (0xda7d0 : word) = Some W_da66c.
Proof. vm_refl. Qed.
Lemma D_da66c : decode_any W_da66c = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da670 : bv 32 := 0x00c5a623.
Lemma F_da670 : fetch_word Asan.M.loaded_segments (0xda7d4 : word) = Some W_da670.
Proof. vm_refl. Qed.
Lemma D_da670 : decode_any W_da670 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da674 : bv 32 := 0x00c5a823.
Lemma F_da674 : fetch_word Asan.M.loaded_segments (0xda7d8 : word) = Some W_da674.
Proof. vm_refl. Qed.
Lemma D_da674 : decode_any W_da674 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da678 : bv 32 := 0x00c5aa23.
Lemma F_da678 : fetch_word Asan.M.loaded_segments (0xda7dc : word) = Some W_da678.
Proof. vm_refl. Qed.
Lemma D_da678 : decode_any W_da678 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da67c : bv 32 := 0x00c5ac23.
Lemma F_da67c : fetch_word Asan.M.loaded_segments (0xda7e0 : word) = Some W_da67c.
Proof. vm_refl. Qed.
Lemma D_da67c : decode_any W_da67c = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da680 : bv 32 := 0x0045f793.
Lemma F_da680 : fetch_word Asan.M.loaded_segments (0xda7e4 : word) = Some W_da680.
Proof. vm_refl. Qed.
Lemma D_da680 : decode_any W_da680 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da684 : bv 32 := 0x02000813.
Lemma F_da684 : fetch_word Asan.M.loaded_segments (0xda7e8 : word) = Some W_da684.
Proof. vm_refl. Qed.
Lemma D_da684 : decode_any W_da684 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da688 : bv 32 := 0x01878793.
Lemma F_da688 : fetch_word Asan.M.loaded_segments (0xda7ec : word) = Some W_da688.
Proof. vm_refl. Qed.
Lemma D_da688 : decode_any W_da688 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da68c : bv 32 := 0x40f70733.
Lemma F_da68c : fetch_word Asan.M.loaded_segments (0xda7f0 : word) = Some W_da68c.
Proof. vm_refl. Qed.
Lemma D_da68c : decode_any W_da68c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da690 : bv 32 := 0xfec6a223.
Lemma F_da690 : fetch_word Asan.M.loaded_segments (0xda7f4 : word) = Some W_da690.
Proof. vm_refl. Qed.
Lemma D_da690 : decode_any W_da690 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da694 : bv 32 := 0xfec6a423.
Lemma F_da694 : fetch_word Asan.M.loaded_segments (0xda7f8 : word) = Some W_da694.
Proof. vm_refl. Qed.
Lemma D_da694 : decode_any W_da694 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da698 : bv 32 := 0xfec6a623.
Lemma F_da698 : fetch_word Asan.M.loaded_segments (0xda7fc : word) = Some W_da698.
Proof. vm_refl. Qed.
Lemma D_da698 : decode_any W_da698 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da69c : bv 32 := 0xfec6a823.
Lemma F_da69c : fetch_word Asan.M.loaded_segments (0xda800 : word) = Some W_da69c.
Proof. vm_refl. Qed.
Lemma D_da69c : decode_any W_da69c = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da6a0 : bv 32 := 0x03076a63.
Lemma F_da6a0 : fetch_word Asan.M.loaded_segments (0xda804 : word) = Some W_da6a0.
Proof. vm_refl. Qed.
Lemma D_da6a0 : decode_any W_da6a0 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da6a4 : bv 32 := 0x02061613.
Lemma F_da6a4 : fetch_word Asan.M.loaded_segments (0xda808 : word) = Some W_da6a4.
Proof. vm_refl. Qed.
Lemma D_da6a4 : decode_any W_da6a4 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da6a8 : bv 32 := 0x00f585b3.
Lemma F_da6a8 : fetch_word Asan.M.loaded_segments (0xda80c : word) = Some W_da6a8.
Proof. vm_refl. Qed.
Lemma D_da6a8 : decode_any W_da6a8 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da6ac : bv 32 := 0x02065693.
Lemma F_da6ac : fetch_word Asan.M.loaded_segments (0xda810 : word) = Some W_da6ac.
Proof. vm_refl. Qed.
Lemma D_da6ac : decode_any W_da6ac = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da6b0 : bv 32 := 0x00d66633.
Lemma F_da6b0 : fetch_word Asan.M.loaded_segments (0xda814 : word) = Some W_da6b0.
Proof. vm_refl. Qed.
Lemma D_da6b0 : decode_any W_da6b0 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da6b4 : bv 32 := 0x01f00693.
Lemma F_da6b4 : fetch_word Asan.M.loaded_segments (0xda818 : word) = Some W_da6b4.
Proof. vm_refl. Qed.
Lemma D_da6b4 : decode_any W_da6b4 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da6b8 : bv 32 := 0x00c5b023.
Lemma F_da6b8 : fetch_word Asan.M.loaded_segments (0xda81c : word) = Some W_da6b8.
Proof. vm_refl. Qed.
Lemma D_da6b8 : decode_any W_da6b8 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da6bc : bv 32 := 0x00c5b423.
Lemma F_da6bc : fetch_word Asan.M.loaded_segments (0xda820 : word) = Some W_da6bc.
Proof. vm_refl. Qed.
Lemma D_da6bc : decode_any W_da6bc = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da6c0 : bv 32 := 0x00c5b823.
Lemma F_da6c0 : fetch_word Asan.M.loaded_segments (0xda824 : word) = Some W_da6c0.
Proof. vm_refl. Qed.
Lemma D_da6c0 : decode_any W_da6c0 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da6c4 : bv 32 := 0x00c5bc23.
Lemma F_da6c4 : fetch_word Asan.M.loaded_segments (0xda828 : word) = Some W_da6c4.
Proof. vm_refl. Qed.
Lemma D_da6c4 : decode_any W_da6c4 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da6c8 : bv 32 := 0xfe070713.
Lemma F_da6c8 : fetch_word Asan.M.loaded_segments (0xda82c : word) = Some W_da6c8.
Proof. vm_refl. Qed.
Lemma D_da6c8 : decode_any W_da6c8 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da6cc : bv 32 := 0x02058593.
Lemma F_da6cc : fetch_word Asan.M.loaded_segments (0xda830 : word) = Some W_da6cc.
Proof. vm_refl. Qed.
Lemma D_da6cc : decode_any W_da6cc = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da6d0 : bv 32 := 0xfee6e4e3.
Lemma F_da6d0 : fetch_word Asan.M.loaded_segments (0xda834 : word) = Some W_da6d0.
Proof. vm_refl. Qed.
Lemma D_da6d0 : decode_any W_da6d0 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_da6d4 : bv 32 := 0x00008067.
Lemma F_da6d4 : fetch_word Asan.M.loaded_segments (0xda838 : word) = Some W_da6d4.
Proof. vm_refl. Qed.
Lemma D_da6d4 : decode_any W_da6d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0xda744%Z.
Definition Fo_000 := F_da5e0.
Definition Do_000 := D_da5e0.
Definition Fo_004 := F_da5e4.
Definition Do_004 := D_da5e4.
Definition Fo_008 := F_da5e8.
Definition Do_008 := D_da5e8.
Definition Fo_00c := F_da5ec.
Definition Do_00c := D_da5ec.
Definition Fo_010 := F_da5f0.
Definition Do_010 := D_da5f0.
Definition Fo_014 := F_da5f4.
Definition Do_014 := D_da5f4.
Definition Fo_018 := F_da5f8.
Definition Do_018 := D_da5f8.
Definition Fo_01c := F_da5fc.
Definition Do_01c := D_da5fc.
Definition Fo_020 := F_da600.
Definition Do_020 := D_da600.
Definition Fo_024 := F_da604.
Definition Do_024 := D_da604.
Definition Fo_028 := F_da608.
Definition Do_028 := D_da608.
Definition Fo_02c := F_da60c.
Definition Do_02c := D_da60c.
Definition Fo_030 := F_da610.
Definition Do_030 := D_da610.
Definition Fo_034 := F_da614.
Definition Do_034 := D_da614.
Definition Fo_038 := F_da618.
Definition Do_038 := D_da618.
Definition Fo_03c := F_da61c.
Definition Do_03c := D_da61c.
Definition Fo_040 := F_da620.
Definition Do_040 := D_da620.
Definition Fo_044 := F_da624.
Definition Do_044 := D_da624.
Definition Fo_048 := F_da628.
Definition Do_048 := D_da628.
Definition Fo_04c := F_da62c.
Definition Do_04c := D_da62c.
Definition Fo_050 := F_da630.
Definition Do_050 := D_da630.
Definition Fo_054 := F_da634.
Definition Do_054 := D_da634.
Definition Fo_058 := F_da638.
Definition Do_058 := D_da638.
Definition Fo_05c := F_da63c.
Definition Do_05c := D_da63c.
Definition Fo_060 := F_da640.
Definition Do_060 := D_da640.
Definition Fo_064 := F_da644.
Definition Do_064 := D_da644.
Definition Fo_068 := F_da648.
Definition Do_068 := D_da648.
Definition Fo_06c := F_da64c.
Definition Do_06c := D_da64c.
Definition Fo_070 := F_da650.
Definition Do_070 := D_da650.
Definition Fo_074 := F_da654.
Definition Do_074 := D_da654.
Definition Fo_078 := F_da658.
Definition Do_078 := D_da658.
Definition Fo_07c := F_da65c.
Definition Do_07c := D_da65c.
Definition Fo_080 := F_da660.
Definition Do_080 := D_da660.
Definition Fo_084 := F_da664.
Definition Do_084 := D_da664.
Definition Fo_088 := F_da668.
Definition Do_088 := D_da668.
Definition Fo_08c := F_da66c.
Definition Do_08c := D_da66c.
Definition Fo_090 := F_da670.
Definition Do_090 := D_da670.
Definition Fo_094 := F_da674.
Definition Do_094 := D_da674.
Definition Fo_098 := F_da678.
Definition Do_098 := D_da678.
Definition Fo_09c := F_da67c.
Definition Do_09c := D_da67c.
Definition Fo_0a0 := F_da680.
Definition Do_0a0 := D_da680.
Definition Fo_0a4 := F_da684.
Definition Do_0a4 := D_da684.
Definition Fo_0a8 := F_da688.
Definition Do_0a8 := D_da688.
Definition Fo_0ac := F_da68c.
Definition Do_0ac := D_da68c.
Definition Fo_0b0 := F_da690.
Definition Do_0b0 := D_da690.
Definition Fo_0b4 := F_da694.
Definition Do_0b4 := D_da694.
Definition Fo_0b8 := F_da698.
Definition Do_0b8 := D_da698.
Definition Fo_0bc := F_da69c.
Definition Do_0bc := D_da69c.
Definition Fo_0c0 := F_da6a0.
Definition Do_0c0 := D_da6a0.
Definition Fo_0c4 := F_da6a4.
Definition Do_0c4 := D_da6a4.
Definition Fo_0c8 := F_da6a8.
Definition Do_0c8 := D_da6a8.
Definition Fo_0cc := F_da6ac.
Definition Do_0cc := D_da6ac.
Definition Fo_0d0 := F_da6b0.
Definition Do_0d0 := D_da6b0.
Definition Fo_0d4 := F_da6b4.
Definition Do_0d4 := D_da6b4.
Definition Fo_0d8 := F_da6b8.
Definition Do_0d8 := D_da6b8.
Definition Fo_0dc := F_da6bc.
Definition Do_0dc := D_da6bc.
Definition Fo_0e0 := F_da6c0.
Definition Do_0e0 := D_da6c0.
Definition Fo_0e4 := F_da6c4.
Definition Do_0e4 := D_da6c4.
Definition Fo_0e8 := F_da6c8.
Definition Do_0e8 := D_da6c8.
Definition Fo_0ec := F_da6cc.
Definition Do_0ec := D_da6cc.
Definition Fo_0f0 := F_da6d0.
Definition Do_0f0 := D_da6d0.
Definition Fo_0f4 := F_da6d4.
Definition Do_0f4 := D_da6d4.
