(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_cc740 : bv 32 := 0x0e060a63.
Lemma F_cc740 : fetch_word AsanUbsan.M.loaded_segments (0xcc740 : word) = Some W_cc740.
Proof. vm_refl. Qed.
Lemma D_cc740 : decode_any W_cc740 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc744 : bv 32 := 0x00b50023.
Lemma F_cc744 : fetch_word AsanUbsan.M.loaded_segments (0xcc744 : word) = Some W_cc744.
Proof. vm_refl. Qed.
Lemma D_cc744 : decode_any W_cc744 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc748 : bv 32 := 0x00c506b3.
Lemma F_cc748 : fetch_word AsanUbsan.M.loaded_segments (0xcc748 : word) = Some W_cc748.
Proof. vm_refl. Qed.
Lemma D_cc748 : decode_any W_cc748 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc74c : bv 32 := 0x00300713.
Lemma F_cc74c : fetch_word AsanUbsan.M.loaded_segments (0xcc74c : word) = Some W_cc74c.
Proof. vm_refl. Qed.
Lemma D_cc74c : decode_any W_cc74c = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc750 : bv 32 := 0xfeb68fa3.
Lemma F_cc750 : fetch_word AsanUbsan.M.loaded_segments (0xcc750 : word) = Some W_cc750.
Proof. vm_refl. Qed.
Lemma D_cc750 : decode_any W_cc750 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc754 : bv 32 := 0x0ee66063.
Lemma F_cc754 : fetch_word AsanUbsan.M.loaded_segments (0xcc754 : word) = Some W_cc754.
Proof. vm_refl. Qed.
Lemma D_cc754 : decode_any W_cc754 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc758 : bv 32 := 0x00b500a3.
Lemma F_cc758 : fetch_word AsanUbsan.M.loaded_segments (0xcc758 : word) = Some W_cc758.
Proof. vm_refl. Qed.
Lemma D_cc758 : decode_any W_cc758 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc75c : bv 32 := 0x00b50123.
Lemma F_cc75c : fetch_word AsanUbsan.M.loaded_segments (0xcc75c : word) = Some W_cc75c.
Proof. vm_refl. Qed.
Lemma D_cc75c : decode_any W_cc75c = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc760 : bv 32 := 0x00700713.
Lemma F_cc760 : fetch_word AsanUbsan.M.loaded_segments (0xcc760 : word) = Some W_cc760.
Proof. vm_refl. Qed.
Lemma D_cc760 : decode_any W_cc760 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc764 : bv 32 := 0xfeb68ea3.
Lemma F_cc764 : fetch_word AsanUbsan.M.loaded_segments (0xcc764 : word) = Some W_cc764.
Proof. vm_refl. Qed.
Lemma D_cc764 : decode_any W_cc764 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc768 : bv 32 := 0xfeb68f23.
Lemma F_cc768 : fetch_word AsanUbsan.M.loaded_segments (0xcc768 : word) = Some W_cc768.
Proof. vm_refl. Qed.
Lemma D_cc768 : decode_any W_cc768 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc76c : bv 32 := 0x0ce66463.
Lemma F_cc76c : fetch_word AsanUbsan.M.loaded_segments (0xcc76c : word) = Some W_cc76c.
Proof. vm_refl. Qed.
Lemma D_cc76c : decode_any W_cc76c = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc770 : bv 32 := 0x00b501a3.
Lemma F_cc770 : fetch_word AsanUbsan.M.loaded_segments (0xcc770 : word) = Some W_cc770.
Proof. vm_refl. Qed.
Lemma D_cc770 : decode_any W_cc770 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc774 : bv 32 := 0x00900793.
Lemma F_cc774 : fetch_word AsanUbsan.M.loaded_segments (0xcc774 : word) = Some W_cc774.
Proof. vm_refl. Qed.
Lemma D_cc774 : decode_any W_cc774 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc778 : bv 32 := 0xfeb68e23.
Lemma F_cc778 : fetch_word AsanUbsan.M.loaded_segments (0xcc778 : word) = Some W_cc778.
Proof. vm_refl. Qed.
Lemma D_cc778 : decode_any W_cc778 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc77c : bv 32 := 0x0af66c63.
Lemma F_cc77c : fetch_word AsanUbsan.M.loaded_segments (0xcc77c : word) = Some W_cc77c.
Proof. vm_refl. Qed.
Lemma D_cc77c : decode_any W_cc77c = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc780 : bv 32 := 0x40a006bb.
Lemma F_cc780 : fetch_word AsanUbsan.M.loaded_segments (0xcc780 : word) = Some W_cc780.
Proof. vm_refl. Qed.
Lemma D_cc780 : decode_any W_cc780 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc784 : bv 32 := 0x03859813.
Lemma F_cc784 : fetch_word AsanUbsan.M.loaded_segments (0xcc784 : word) = Some W_cc784.
Proof. vm_refl. Qed.
Lemma D_cc784 : decode_any W_cc784 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc788 : bv 32 := 0x101015b7.
Lemma F_cc788 : fetch_word AsanUbsan.M.loaded_segments (0xcc788 : word) = Some W_cc788.
Proof. vm_refl. Qed.
Lemma D_cc788 : decode_any W_cc788 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc78c : bv 32 := 0x0036f693.
Lemma F_cc78c : fetch_word AsanUbsan.M.loaded_segments (0xcc78c : word) = Some W_cc78c.
Proof. vm_refl. Qed.
Lemma D_cc78c : decode_any W_cc78c = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc790 : bv 32 := 0x00459713.
Lemma F_cc790 : fetch_word AsanUbsan.M.loaded_segments (0xcc790 : word) = Some W_cc790.
Proof. vm_refl. Qed.
Lemma D_cc790 : decode_any W_cc790 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc794 : bv 32 := 0x40d60633.
Lemma F_cc794 : fetch_word AsanUbsan.M.loaded_segments (0xcc794 : word) = Some W_cc794.
Proof. vm_refl. Qed.
Lemma D_cc794 : decode_any W_cc794 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc798 : bv 32 := 0x00d505b3.
Lemma F_cc798 : fetch_word AsanUbsan.M.loaded_segments (0xcc798 : word) = Some W_cc798.
Proof. vm_refl. Qed.
Lemma D_cc798 : decode_any W_cc798 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc79c : bv 32 := 0x10070693.
Lemma F_cc79c : fetch_word AsanUbsan.M.loaded_segments (0xcc79c : word) = Some W_cc79c.
Proof. vm_refl. Qed.
Lemma D_cc79c : decode_any W_cc79c = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7a0 : bv 32 := 0xffc67713.
Lemma F_cc7a0 : fetch_word AsanUbsan.M.loaded_segments (0xcc7a0 : word) = Some W_cc7a0.
Proof. vm_refl. Qed.
Lemma D_cc7a0 : decode_any W_cc7a0 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7a4 : bv 32 := 0x02d83633.
Lemma F_cc7a4 : fetch_word AsanUbsan.M.loaded_segments (0xcc7a4 : word) = Some W_cc7a4.
Proof. vm_refl. Qed.
Lemma D_cc7a4 : decode_any W_cc7a4 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7a8 : bv 32 := 0x00c5a023.
Lemma F_cc7a8 : fetch_word AsanUbsan.M.loaded_segments (0xcc7a8 : word) = Some W_cc7a8.
Proof. vm_refl. Qed.
Lemma D_cc7a8 : decode_any W_cc7a8 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7ac : bv 32 := 0x00e586b3.
Lemma F_cc7ac : fetch_word AsanUbsan.M.loaded_segments (0xcc7ac : word) = Some W_cc7ac.
Proof. vm_refl. Qed.
Lemma D_cc7ac : decode_any W_cc7ac = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7b0 : bv 32 := 0xfec6ae23.
Lemma F_cc7b0 : fetch_word AsanUbsan.M.loaded_segments (0xcc7b0 : word) = Some W_cc7b0.
Proof. vm_refl. Qed.
Lemma D_cc7b0 : decode_any W_cc7b0 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7b4 : bv 32 := 0x08f76063.
Lemma F_cc7b4 : fetch_word AsanUbsan.M.loaded_segments (0xcc7b4 : word) = Some W_cc7b4.
Proof. vm_refl. Qed.
Lemma D_cc7b4 : decode_any W_cc7b4 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7b8 : bv 32 := 0x00c5a223.
Lemma F_cc7b8 : fetch_word AsanUbsan.M.loaded_segments (0xcc7b8 : word) = Some W_cc7b8.
Proof. vm_refl. Qed.
Lemma D_cc7b8 : decode_any W_cc7b8 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7bc : bv 32 := 0x00c5a423.
Lemma F_cc7bc : fetch_word AsanUbsan.M.loaded_segments (0xcc7bc : word) = Some W_cc7bc.
Proof. vm_refl. Qed.
Lemma D_cc7bc : decode_any W_cc7bc = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7c0 : bv 32 := 0x01900793.
Lemma F_cc7c0 : fetch_word AsanUbsan.M.loaded_segments (0xcc7c0 : word) = Some W_cc7c0.
Proof. vm_refl. Qed.
Lemma D_cc7c0 : decode_any W_cc7c0 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7c4 : bv 32 := 0xfec6aa23.
Lemma F_cc7c4 : fetch_word AsanUbsan.M.loaded_segments (0xcc7c4 : word) = Some W_cc7c4.
Proof. vm_refl. Qed.
Lemma D_cc7c4 : decode_any W_cc7c4 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7c8 : bv 32 := 0xfec6ac23.
Lemma F_cc7c8 : fetch_word AsanUbsan.M.loaded_segments (0xcc7c8 : word) = Some W_cc7c8.
Proof. vm_refl. Qed.
Lemma D_cc7c8 : decode_any W_cc7c8 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7cc : bv 32 := 0x06f76463.
Lemma F_cc7cc : fetch_word AsanUbsan.M.loaded_segments (0xcc7cc : word) = Some W_cc7cc.
Proof. vm_refl. Qed.
Lemma D_cc7cc : decode_any W_cc7cc = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7d0 : bv 32 := 0x00c5a623.
Lemma F_cc7d0 : fetch_word AsanUbsan.M.loaded_segments (0xcc7d0 : word) = Some W_cc7d0.
Proof. vm_refl. Qed.
Lemma D_cc7d0 : decode_any W_cc7d0 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7d4 : bv 32 := 0x00c5a823.
Lemma F_cc7d4 : fetch_word AsanUbsan.M.loaded_segments (0xcc7d4 : word) = Some W_cc7d4.
Proof. vm_refl. Qed.
Lemma D_cc7d4 : decode_any W_cc7d4 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7d8 : bv 32 := 0x00c5aa23.
Lemma F_cc7d8 : fetch_word AsanUbsan.M.loaded_segments (0xcc7d8 : word) = Some W_cc7d8.
Proof. vm_refl. Qed.
Lemma D_cc7d8 : decode_any W_cc7d8 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7dc : bv 32 := 0x00c5ac23.
Lemma F_cc7dc : fetch_word AsanUbsan.M.loaded_segments (0xcc7dc : word) = Some W_cc7dc.
Proof. vm_refl. Qed.
Lemma D_cc7dc : decode_any W_cc7dc = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7e0 : bv 32 := 0x0045f793.
Lemma F_cc7e0 : fetch_word AsanUbsan.M.loaded_segments (0xcc7e0 : word) = Some W_cc7e0.
Proof. vm_refl. Qed.
Lemma D_cc7e0 : decode_any W_cc7e0 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7e4 : bv 32 := 0x02000813.
Lemma F_cc7e4 : fetch_word AsanUbsan.M.loaded_segments (0xcc7e4 : word) = Some W_cc7e4.
Proof. vm_refl. Qed.
Lemma D_cc7e4 : decode_any W_cc7e4 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7e8 : bv 32 := 0x01878793.
Lemma F_cc7e8 : fetch_word AsanUbsan.M.loaded_segments (0xcc7e8 : word) = Some W_cc7e8.
Proof. vm_refl. Qed.
Lemma D_cc7e8 : decode_any W_cc7e8 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7ec : bv 32 := 0x40f70733.
Lemma F_cc7ec : fetch_word AsanUbsan.M.loaded_segments (0xcc7ec : word) = Some W_cc7ec.
Proof. vm_refl. Qed.
Lemma D_cc7ec : decode_any W_cc7ec = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7f0 : bv 32 := 0xfec6a223.
Lemma F_cc7f0 : fetch_word AsanUbsan.M.loaded_segments (0xcc7f0 : word) = Some W_cc7f0.
Proof. vm_refl. Qed.
Lemma D_cc7f0 : decode_any W_cc7f0 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7f4 : bv 32 := 0xfec6a423.
Lemma F_cc7f4 : fetch_word AsanUbsan.M.loaded_segments (0xcc7f4 : word) = Some W_cc7f4.
Proof. vm_refl. Qed.
Lemma D_cc7f4 : decode_any W_cc7f4 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7f8 : bv 32 := 0xfec6a623.
Lemma F_cc7f8 : fetch_word AsanUbsan.M.loaded_segments (0xcc7f8 : word) = Some W_cc7f8.
Proof. vm_refl. Qed.
Lemma D_cc7f8 : decode_any W_cc7f8 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc7fc : bv 32 := 0xfec6a823.
Lemma F_cc7fc : fetch_word AsanUbsan.M.loaded_segments (0xcc7fc : word) = Some W_cc7fc.
Proof. vm_refl. Qed.
Lemma D_cc7fc : decode_any W_cc7fc = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc800 : bv 32 := 0x03076a63.
Lemma F_cc800 : fetch_word AsanUbsan.M.loaded_segments (0xcc800 : word) = Some W_cc800.
Proof. vm_refl. Qed.
Lemma D_cc800 : decode_any W_cc800 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc804 : bv 32 := 0x02061613.
Lemma F_cc804 : fetch_word AsanUbsan.M.loaded_segments (0xcc804 : word) = Some W_cc804.
Proof. vm_refl. Qed.
Lemma D_cc804 : decode_any W_cc804 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc808 : bv 32 := 0x00f585b3.
Lemma F_cc808 : fetch_word AsanUbsan.M.loaded_segments (0xcc808 : word) = Some W_cc808.
Proof. vm_refl. Qed.
Lemma D_cc808 : decode_any W_cc808 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc80c : bv 32 := 0x02065693.
Lemma F_cc80c : fetch_word AsanUbsan.M.loaded_segments (0xcc80c : word) = Some W_cc80c.
Proof. vm_refl. Qed.
Lemma D_cc80c : decode_any W_cc80c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc810 : bv 32 := 0x00d66633.
Lemma F_cc810 : fetch_word AsanUbsan.M.loaded_segments (0xcc810 : word) = Some W_cc810.
Proof. vm_refl. Qed.
Lemma D_cc810 : decode_any W_cc810 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc814 : bv 32 := 0x01f00693.
Lemma F_cc814 : fetch_word AsanUbsan.M.loaded_segments (0xcc814 : word) = Some W_cc814.
Proof. vm_refl. Qed.
Lemma D_cc814 : decode_any W_cc814 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc818 : bv 32 := 0x00c5b023.
Lemma F_cc818 : fetch_word AsanUbsan.M.loaded_segments (0xcc818 : word) = Some W_cc818.
Proof. vm_refl. Qed.
Lemma D_cc818 : decode_any W_cc818 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc81c : bv 32 := 0x00c5b423.
Lemma F_cc81c : fetch_word AsanUbsan.M.loaded_segments (0xcc81c : word) = Some W_cc81c.
Proof. vm_refl. Qed.
Lemma D_cc81c : decode_any W_cc81c = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc820 : bv 32 := 0x00c5b823.
Lemma F_cc820 : fetch_word AsanUbsan.M.loaded_segments (0xcc820 : word) = Some W_cc820.
Proof. vm_refl. Qed.
Lemma D_cc820 : decode_any W_cc820 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc824 : bv 32 := 0x00c5bc23.
Lemma F_cc824 : fetch_word AsanUbsan.M.loaded_segments (0xcc824 : word) = Some W_cc824.
Proof. vm_refl. Qed.
Lemma D_cc824 : decode_any W_cc824 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc828 : bv 32 := 0xfe070713.
Lemma F_cc828 : fetch_word AsanUbsan.M.loaded_segments (0xcc828 : word) = Some W_cc828.
Proof. vm_refl. Qed.
Lemma D_cc828 : decode_any W_cc828 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc82c : bv 32 := 0x02058593.
Lemma F_cc82c : fetch_word AsanUbsan.M.loaded_segments (0xcc82c : word) = Some W_cc82c.
Proof. vm_refl. Qed.
Lemma D_cc82c : decode_any W_cc82c = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc830 : bv 32 := 0xfee6e4e3.
Lemma F_cc830 : fetch_word AsanUbsan.M.loaded_segments (0xcc830 : word) = Some W_cc830.
Proof. vm_refl. Qed.
Lemma D_cc830 : decode_any W_cc830 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cc834 : bv 32 := 0x00008067.
Lemma F_cc834 : fetch_word AsanUbsan.M.loaded_segments (0xcc834 : word) = Some W_cc834.
Proof. vm_refl. Qed.
Lemma D_cc834 : decode_any W_cc834 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0xcc740%Z.
Definition Fo_000 := F_cc740.
Definition Do_000 := D_cc740.
Definition Fo_004 := F_cc744.
Definition Do_004 := D_cc744.
Definition Fo_008 := F_cc748.
Definition Do_008 := D_cc748.
Definition Fo_00c := F_cc74c.
Definition Do_00c := D_cc74c.
Definition Fo_010 := F_cc750.
Definition Do_010 := D_cc750.
Definition Fo_014 := F_cc754.
Definition Do_014 := D_cc754.
Definition Fo_018 := F_cc758.
Definition Do_018 := D_cc758.
Definition Fo_01c := F_cc75c.
Definition Do_01c := D_cc75c.
Definition Fo_020 := F_cc760.
Definition Do_020 := D_cc760.
Definition Fo_024 := F_cc764.
Definition Do_024 := D_cc764.
Definition Fo_028 := F_cc768.
Definition Do_028 := D_cc768.
Definition Fo_02c := F_cc76c.
Definition Do_02c := D_cc76c.
Definition Fo_030 := F_cc770.
Definition Do_030 := D_cc770.
Definition Fo_034 := F_cc774.
Definition Do_034 := D_cc774.
Definition Fo_038 := F_cc778.
Definition Do_038 := D_cc778.
Definition Fo_03c := F_cc77c.
Definition Do_03c := D_cc77c.
Definition Fo_040 := F_cc780.
Definition Do_040 := D_cc780.
Definition Fo_044 := F_cc784.
Definition Do_044 := D_cc784.
Definition Fo_048 := F_cc788.
Definition Do_048 := D_cc788.
Definition Fo_04c := F_cc78c.
Definition Do_04c := D_cc78c.
Definition Fo_050 := F_cc790.
Definition Do_050 := D_cc790.
Definition Fo_054 := F_cc794.
Definition Do_054 := D_cc794.
Definition Fo_058 := F_cc798.
Definition Do_058 := D_cc798.
Definition Fo_05c := F_cc79c.
Definition Do_05c := D_cc79c.
Definition Fo_060 := F_cc7a0.
Definition Do_060 := D_cc7a0.
Definition Fo_064 := F_cc7a4.
Definition Do_064 := D_cc7a4.
Definition Fo_068 := F_cc7a8.
Definition Do_068 := D_cc7a8.
Definition Fo_06c := F_cc7ac.
Definition Do_06c := D_cc7ac.
Definition Fo_070 := F_cc7b0.
Definition Do_070 := D_cc7b0.
Definition Fo_074 := F_cc7b4.
Definition Do_074 := D_cc7b4.
Definition Fo_078 := F_cc7b8.
Definition Do_078 := D_cc7b8.
Definition Fo_07c := F_cc7bc.
Definition Do_07c := D_cc7bc.
Definition Fo_080 := F_cc7c0.
Definition Do_080 := D_cc7c0.
Definition Fo_084 := F_cc7c4.
Definition Do_084 := D_cc7c4.
Definition Fo_088 := F_cc7c8.
Definition Do_088 := D_cc7c8.
Definition Fo_08c := F_cc7cc.
Definition Do_08c := D_cc7cc.
Definition Fo_090 := F_cc7d0.
Definition Do_090 := D_cc7d0.
Definition Fo_094 := F_cc7d4.
Definition Do_094 := D_cc7d4.
Definition Fo_098 := F_cc7d8.
Definition Do_098 := D_cc7d8.
Definition Fo_09c := F_cc7dc.
Definition Do_09c := D_cc7dc.
Definition Fo_0a0 := F_cc7e0.
Definition Do_0a0 := D_cc7e0.
Definition Fo_0a4 := F_cc7e4.
Definition Do_0a4 := D_cc7e4.
Definition Fo_0a8 := F_cc7e8.
Definition Do_0a8 := D_cc7e8.
Definition Fo_0ac := F_cc7ec.
Definition Do_0ac := D_cc7ec.
Definition Fo_0b0 := F_cc7f0.
Definition Do_0b0 := D_cc7f0.
Definition Fo_0b4 := F_cc7f4.
Definition Do_0b4 := D_cc7f4.
Definition Fo_0b8 := F_cc7f8.
Definition Do_0b8 := D_cc7f8.
Definition Fo_0bc := F_cc7fc.
Definition Do_0bc := D_cc7fc.
Definition Fo_0c0 := F_cc800.
Definition Do_0c0 := D_cc800.
Definition Fo_0c4 := F_cc804.
Definition Do_0c4 := D_cc804.
Definition Fo_0c8 := F_cc808.
Definition Do_0c8 := D_cc808.
Definition Fo_0cc := F_cc80c.
Definition Do_0cc := D_cc80c.
Definition Fo_0d0 := F_cc810.
Definition Do_0d0 := D_cc810.
Definition Fo_0d4 := F_cc814.
Definition Do_0d4 := D_cc814.
Definition Fo_0d8 := F_cc818.
Definition Do_0d8 := D_cc818.
Definition Fo_0dc := F_cc81c.
Definition Do_0dc := D_cc81c.
Definition Fo_0e0 := F_cc820.
Definition Do_0e0 := D_cc820.
Definition Fo_0e4 := F_cc824.
Definition Do_0e4 := D_cc824.
Definition Fo_0e8 := F_cc828.
Definition Do_0e8 := D_cc828.
Definition Fo_0ec := F_cc82c.
Definition Do_0ec := D_cc82c.
Definition Fo_0f0 := F_cc830.
Definition Do_0f0 := D_cc830.
Definition Fo_0f4 := F_cc834.
Definition Do_0f4 := D_cc834.
