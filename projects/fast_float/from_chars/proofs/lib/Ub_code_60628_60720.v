(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_60628 : bv 32 := 0x0e060a63.
Lemma F_60628 : fetch_word Ubsan.M.loaded_segments (0x60628 : word) = Some W_60628.
Proof. vm_refl. Qed.
Lemma D_60628 : decode_any W_60628 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6062c : bv 32 := 0x00b50023.
Lemma F_6062c : fetch_word Ubsan.M.loaded_segments (0x6062c : word) = Some W_6062c.
Proof. vm_refl. Qed.
Lemma D_6062c : decode_any W_6062c = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60630 : bv 32 := 0x00c506b3.
Lemma F_60630 : fetch_word Ubsan.M.loaded_segments (0x60630 : word) = Some W_60630.
Proof. vm_refl. Qed.
Lemma D_60630 : decode_any W_60630 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60634 : bv 32 := 0x00300713.
Lemma F_60634 : fetch_word Ubsan.M.loaded_segments (0x60634 : word) = Some W_60634.
Proof. vm_refl. Qed.
Lemma D_60634 : decode_any W_60634 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60638 : bv 32 := 0xfeb68fa3.
Lemma F_60638 : fetch_word Ubsan.M.loaded_segments (0x60638 : word) = Some W_60638.
Proof. vm_refl. Qed.
Lemma D_60638 : decode_any W_60638 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6063c : bv 32 := 0x0ee66063.
Lemma F_6063c : fetch_word Ubsan.M.loaded_segments (0x6063c : word) = Some W_6063c.
Proof. vm_refl. Qed.
Lemma D_6063c : decode_any W_6063c = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60640 : bv 32 := 0x00b500a3.
Lemma F_60640 : fetch_word Ubsan.M.loaded_segments (0x60640 : word) = Some W_60640.
Proof. vm_refl. Qed.
Lemma D_60640 : decode_any W_60640 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60644 : bv 32 := 0x00b50123.
Lemma F_60644 : fetch_word Ubsan.M.loaded_segments (0x60644 : word) = Some W_60644.
Proof. vm_refl. Qed.
Lemma D_60644 : decode_any W_60644 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60648 : bv 32 := 0x00700713.
Lemma F_60648 : fetch_word Ubsan.M.loaded_segments (0x60648 : word) = Some W_60648.
Proof. vm_refl. Qed.
Lemma D_60648 : decode_any W_60648 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6064c : bv 32 := 0xfeb68ea3.
Lemma F_6064c : fetch_word Ubsan.M.loaded_segments (0x6064c : word) = Some W_6064c.
Proof. vm_refl. Qed.
Lemma D_6064c : decode_any W_6064c = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60650 : bv 32 := 0xfeb68f23.
Lemma F_60650 : fetch_word Ubsan.M.loaded_segments (0x60650 : word) = Some W_60650.
Proof. vm_refl. Qed.
Lemma D_60650 : decode_any W_60650 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60654 : bv 32 := 0x0ce66463.
Lemma F_60654 : fetch_word Ubsan.M.loaded_segments (0x60654 : word) = Some W_60654.
Proof. vm_refl. Qed.
Lemma D_60654 : decode_any W_60654 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60658 : bv 32 := 0x00b501a3.
Lemma F_60658 : fetch_word Ubsan.M.loaded_segments (0x60658 : word) = Some W_60658.
Proof. vm_refl. Qed.
Lemma D_60658 : decode_any W_60658 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6065c : bv 32 := 0x00900793.
Lemma F_6065c : fetch_word Ubsan.M.loaded_segments (0x6065c : word) = Some W_6065c.
Proof. vm_refl. Qed.
Lemma D_6065c : decode_any W_6065c = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60660 : bv 32 := 0xfeb68e23.
Lemma F_60660 : fetch_word Ubsan.M.loaded_segments (0x60660 : word) = Some W_60660.
Proof. vm_refl. Qed.
Lemma D_60660 : decode_any W_60660 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60664 : bv 32 := 0x0af66c63.
Lemma F_60664 : fetch_word Ubsan.M.loaded_segments (0x60664 : word) = Some W_60664.
Proof. vm_refl. Qed.
Lemma D_60664 : decode_any W_60664 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60668 : bv 32 := 0x40a006bb.
Lemma F_60668 : fetch_word Ubsan.M.loaded_segments (0x60668 : word) = Some W_60668.
Proof. vm_refl. Qed.
Lemma D_60668 : decode_any W_60668 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6066c : bv 32 := 0x03859813.
Lemma F_6066c : fetch_word Ubsan.M.loaded_segments (0x6066c : word) = Some W_6066c.
Proof. vm_refl. Qed.
Lemma D_6066c : decode_any W_6066c = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60670 : bv 32 := 0x101015b7.
Lemma F_60670 : fetch_word Ubsan.M.loaded_segments (0x60670 : word) = Some W_60670.
Proof. vm_refl. Qed.
Lemma D_60670 : decode_any W_60670 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60674 : bv 32 := 0x0036f693.
Lemma F_60674 : fetch_word Ubsan.M.loaded_segments (0x60674 : word) = Some W_60674.
Proof. vm_refl. Qed.
Lemma D_60674 : decode_any W_60674 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60678 : bv 32 := 0x00459713.
Lemma F_60678 : fetch_word Ubsan.M.loaded_segments (0x60678 : word) = Some W_60678.
Proof. vm_refl. Qed.
Lemma D_60678 : decode_any W_60678 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6067c : bv 32 := 0x40d60633.
Lemma F_6067c : fetch_word Ubsan.M.loaded_segments (0x6067c : word) = Some W_6067c.
Proof. vm_refl. Qed.
Lemma D_6067c : decode_any W_6067c = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60680 : bv 32 := 0x00d505b3.
Lemma F_60680 : fetch_word Ubsan.M.loaded_segments (0x60680 : word) = Some W_60680.
Proof. vm_refl. Qed.
Lemma D_60680 : decode_any W_60680 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60684 : bv 32 := 0x10070693.
Lemma F_60684 : fetch_word Ubsan.M.loaded_segments (0x60684 : word) = Some W_60684.
Proof. vm_refl. Qed.
Lemma D_60684 : decode_any W_60684 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60688 : bv 32 := 0xffc67713.
Lemma F_60688 : fetch_word Ubsan.M.loaded_segments (0x60688 : word) = Some W_60688.
Proof. vm_refl. Qed.
Lemma D_60688 : decode_any W_60688 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6068c : bv 32 := 0x02d83633.
Lemma F_6068c : fetch_word Ubsan.M.loaded_segments (0x6068c : word) = Some W_6068c.
Proof. vm_refl. Qed.
Lemma D_6068c : decode_any W_6068c = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60690 : bv 32 := 0x00c5a023.
Lemma F_60690 : fetch_word Ubsan.M.loaded_segments (0x60690 : word) = Some W_60690.
Proof. vm_refl. Qed.
Lemma D_60690 : decode_any W_60690 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60694 : bv 32 := 0x00e586b3.
Lemma F_60694 : fetch_word Ubsan.M.loaded_segments (0x60694 : word) = Some W_60694.
Proof. vm_refl. Qed.
Lemma D_60694 : decode_any W_60694 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60698 : bv 32 := 0xfec6ae23.
Lemma F_60698 : fetch_word Ubsan.M.loaded_segments (0x60698 : word) = Some W_60698.
Proof. vm_refl. Qed.
Lemma D_60698 : decode_any W_60698 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6069c : bv 32 := 0x08f76063.
Lemma F_6069c : fetch_word Ubsan.M.loaded_segments (0x6069c : word) = Some W_6069c.
Proof. vm_refl. Qed.
Lemma D_6069c : decode_any W_6069c = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606a0 : bv 32 := 0x00c5a223.
Lemma F_606a0 : fetch_word Ubsan.M.loaded_segments (0x606a0 : word) = Some W_606a0.
Proof. vm_refl. Qed.
Lemma D_606a0 : decode_any W_606a0 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606a4 : bv 32 := 0x00c5a423.
Lemma F_606a4 : fetch_word Ubsan.M.loaded_segments (0x606a4 : word) = Some W_606a4.
Proof. vm_refl. Qed.
Lemma D_606a4 : decode_any W_606a4 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606a8 : bv 32 := 0x01900793.
Lemma F_606a8 : fetch_word Ubsan.M.loaded_segments (0x606a8 : word) = Some W_606a8.
Proof. vm_refl. Qed.
Lemma D_606a8 : decode_any W_606a8 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606ac : bv 32 := 0xfec6aa23.
Lemma F_606ac : fetch_word Ubsan.M.loaded_segments (0x606ac : word) = Some W_606ac.
Proof. vm_refl. Qed.
Lemma D_606ac : decode_any W_606ac = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606b0 : bv 32 := 0xfec6ac23.
Lemma F_606b0 : fetch_word Ubsan.M.loaded_segments (0x606b0 : word) = Some W_606b0.
Proof. vm_refl. Qed.
Lemma D_606b0 : decode_any W_606b0 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606b4 : bv 32 := 0x06f76463.
Lemma F_606b4 : fetch_word Ubsan.M.loaded_segments (0x606b4 : word) = Some W_606b4.
Proof. vm_refl. Qed.
Lemma D_606b4 : decode_any W_606b4 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606b8 : bv 32 := 0x00c5a623.
Lemma F_606b8 : fetch_word Ubsan.M.loaded_segments (0x606b8 : word) = Some W_606b8.
Proof. vm_refl. Qed.
Lemma D_606b8 : decode_any W_606b8 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606bc : bv 32 := 0x00c5a823.
Lemma F_606bc : fetch_word Ubsan.M.loaded_segments (0x606bc : word) = Some W_606bc.
Proof. vm_refl. Qed.
Lemma D_606bc : decode_any W_606bc = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606c0 : bv 32 := 0x00c5aa23.
Lemma F_606c0 : fetch_word Ubsan.M.loaded_segments (0x606c0 : word) = Some W_606c0.
Proof. vm_refl. Qed.
Lemma D_606c0 : decode_any W_606c0 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606c4 : bv 32 := 0x00c5ac23.
Lemma F_606c4 : fetch_word Ubsan.M.loaded_segments (0x606c4 : word) = Some W_606c4.
Proof. vm_refl. Qed.
Lemma D_606c4 : decode_any W_606c4 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606c8 : bv 32 := 0x0045f793.
Lemma F_606c8 : fetch_word Ubsan.M.loaded_segments (0x606c8 : word) = Some W_606c8.
Proof. vm_refl. Qed.
Lemma D_606c8 : decode_any W_606c8 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606cc : bv 32 := 0x02000813.
Lemma F_606cc : fetch_word Ubsan.M.loaded_segments (0x606cc : word) = Some W_606cc.
Proof. vm_refl. Qed.
Lemma D_606cc : decode_any W_606cc = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606d0 : bv 32 := 0x01878793.
Lemma F_606d0 : fetch_word Ubsan.M.loaded_segments (0x606d0 : word) = Some W_606d0.
Proof. vm_refl. Qed.
Lemma D_606d0 : decode_any W_606d0 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606d4 : bv 32 := 0x40f70733.
Lemma F_606d4 : fetch_word Ubsan.M.loaded_segments (0x606d4 : word) = Some W_606d4.
Proof. vm_refl. Qed.
Lemma D_606d4 : decode_any W_606d4 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606d8 : bv 32 := 0xfec6a223.
Lemma F_606d8 : fetch_word Ubsan.M.loaded_segments (0x606d8 : word) = Some W_606d8.
Proof. vm_refl. Qed.
Lemma D_606d8 : decode_any W_606d8 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606dc : bv 32 := 0xfec6a423.
Lemma F_606dc : fetch_word Ubsan.M.loaded_segments (0x606dc : word) = Some W_606dc.
Proof. vm_refl. Qed.
Lemma D_606dc : decode_any W_606dc = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606e0 : bv 32 := 0xfec6a623.
Lemma F_606e0 : fetch_word Ubsan.M.loaded_segments (0x606e0 : word) = Some W_606e0.
Proof. vm_refl. Qed.
Lemma D_606e0 : decode_any W_606e0 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606e4 : bv 32 := 0xfec6a823.
Lemma F_606e4 : fetch_word Ubsan.M.loaded_segments (0x606e4 : word) = Some W_606e4.
Proof. vm_refl. Qed.
Lemma D_606e4 : decode_any W_606e4 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606e8 : bv 32 := 0x03076a63.
Lemma F_606e8 : fetch_word Ubsan.M.loaded_segments (0x606e8 : word) = Some W_606e8.
Proof. vm_refl. Qed.
Lemma D_606e8 : decode_any W_606e8 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606ec : bv 32 := 0x02061613.
Lemma F_606ec : fetch_word Ubsan.M.loaded_segments (0x606ec : word) = Some W_606ec.
Proof. vm_refl. Qed.
Lemma D_606ec : decode_any W_606ec = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606f0 : bv 32 := 0x00f585b3.
Lemma F_606f0 : fetch_word Ubsan.M.loaded_segments (0x606f0 : word) = Some W_606f0.
Proof. vm_refl. Qed.
Lemma D_606f0 : decode_any W_606f0 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606f4 : bv 32 := 0x02065693.
Lemma F_606f4 : fetch_word Ubsan.M.loaded_segments (0x606f4 : word) = Some W_606f4.
Proof. vm_refl. Qed.
Lemma D_606f4 : decode_any W_606f4 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606f8 : bv 32 := 0x00d66633.
Lemma F_606f8 : fetch_word Ubsan.M.loaded_segments (0x606f8 : word) = Some W_606f8.
Proof. vm_refl. Qed.
Lemma D_606f8 : decode_any W_606f8 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606fc : bv 32 := 0x01f00693.
Lemma F_606fc : fetch_word Ubsan.M.loaded_segments (0x606fc : word) = Some W_606fc.
Proof. vm_refl. Qed.
Lemma D_606fc : decode_any W_606fc = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60700 : bv 32 := 0x00c5b023.
Lemma F_60700 : fetch_word Ubsan.M.loaded_segments (0x60700 : word) = Some W_60700.
Proof. vm_refl. Qed.
Lemma D_60700 : decode_any W_60700 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60704 : bv 32 := 0x00c5b423.
Lemma F_60704 : fetch_word Ubsan.M.loaded_segments (0x60704 : word) = Some W_60704.
Proof. vm_refl. Qed.
Lemma D_60704 : decode_any W_60704 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60708 : bv 32 := 0x00c5b823.
Lemma F_60708 : fetch_word Ubsan.M.loaded_segments (0x60708 : word) = Some W_60708.
Proof. vm_refl. Qed.
Lemma D_60708 : decode_any W_60708 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6070c : bv 32 := 0x00c5bc23.
Lemma F_6070c : fetch_word Ubsan.M.loaded_segments (0x6070c : word) = Some W_6070c.
Proof. vm_refl. Qed.
Lemma D_6070c : decode_any W_6070c = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60710 : bv 32 := 0xfe070713.
Lemma F_60710 : fetch_word Ubsan.M.loaded_segments (0x60710 : word) = Some W_60710.
Proof. vm_refl. Qed.
Lemma D_60710 : decode_any W_60710 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60714 : bv 32 := 0x02058593.
Lemma F_60714 : fetch_word Ubsan.M.loaded_segments (0x60714 : word) = Some W_60714.
Proof. vm_refl. Qed.
Lemma D_60714 : decode_any W_60714 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60718 : bv 32 := 0xfee6e4e3.
Lemma F_60718 : fetch_word Ubsan.M.loaded_segments (0x60718 : word) = Some W_60718.
Proof. vm_refl. Qed.
Lemma D_60718 : decode_any W_60718 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6071c : bv 32 := 0x00008067.
Lemma F_6071c : fetch_word Ubsan.M.loaded_segments (0x6071c : word) = Some W_6071c.
Proof. vm_refl. Qed.
Lemma D_6071c : decode_any W_6071c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
