(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.punycode.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_56374c : bv 32 := 0x0e060a63.
Lemma F_56374c : fetch_word AsanUbsan.M.loaded_segments (0x563738 : word) = Some W_56374c.
Proof. vm_refl. Qed.
Lemma D_56374c : decode_any W_56374c = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563750 : bv 32 := 0x00b50023.
Lemma F_563750 : fetch_word AsanUbsan.M.loaded_segments (0x56373c : word) = Some W_563750.
Proof. vm_refl. Qed.
Lemma D_563750 : decode_any W_563750 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563754 : bv 32 := 0x00c506b3.
Lemma F_563754 : fetch_word AsanUbsan.M.loaded_segments (0x563740 : word) = Some W_563754.
Proof. vm_refl. Qed.
Lemma D_563754 : decode_any W_563754 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563758 : bv 32 := 0x00300713.
Lemma F_563758 : fetch_word AsanUbsan.M.loaded_segments (0x563744 : word) = Some W_563758.
Proof. vm_refl. Qed.
Lemma D_563758 : decode_any W_563758 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56375c : bv 32 := 0xfeb68fa3.
Lemma F_56375c : fetch_word AsanUbsan.M.loaded_segments (0x563748 : word) = Some W_56375c.
Proof. vm_refl. Qed.
Lemma D_56375c : decode_any W_56375c = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563760 : bv 32 := 0x0ee66063.
Lemma F_563760 : fetch_word AsanUbsan.M.loaded_segments (0x56374c : word) = Some W_563760.
Proof. vm_refl. Qed.
Lemma D_563760 : decode_any W_563760 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563764 : bv 32 := 0x00b500a3.
Lemma F_563764 : fetch_word AsanUbsan.M.loaded_segments (0x563750 : word) = Some W_563764.
Proof. vm_refl. Qed.
Lemma D_563764 : decode_any W_563764 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563768 : bv 32 := 0x00b50123.
Lemma F_563768 : fetch_word AsanUbsan.M.loaded_segments (0x563754 : word) = Some W_563768.
Proof. vm_refl. Qed.
Lemma D_563768 : decode_any W_563768 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56376c : bv 32 := 0x00700713.
Lemma F_56376c : fetch_word AsanUbsan.M.loaded_segments (0x563758 : word) = Some W_56376c.
Proof. vm_refl. Qed.
Lemma D_56376c : decode_any W_56376c = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563770 : bv 32 := 0xfeb68ea3.
Lemma F_563770 : fetch_word AsanUbsan.M.loaded_segments (0x56375c : word) = Some W_563770.
Proof. vm_refl. Qed.
Lemma D_563770 : decode_any W_563770 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563774 : bv 32 := 0xfeb68f23.
Lemma F_563774 : fetch_word AsanUbsan.M.loaded_segments (0x563760 : word) = Some W_563774.
Proof. vm_refl. Qed.
Lemma D_563774 : decode_any W_563774 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563778 : bv 32 := 0x0ce66463.
Lemma F_563778 : fetch_word AsanUbsan.M.loaded_segments (0x563764 : word) = Some W_563778.
Proof. vm_refl. Qed.
Lemma D_563778 : decode_any W_563778 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56377c : bv 32 := 0x00b501a3.
Lemma F_56377c : fetch_word AsanUbsan.M.loaded_segments (0x563768 : word) = Some W_56377c.
Proof. vm_refl. Qed.
Lemma D_56377c : decode_any W_56377c = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563780 : bv 32 := 0x00900793.
Lemma F_563780 : fetch_word AsanUbsan.M.loaded_segments (0x56376c : word) = Some W_563780.
Proof. vm_refl. Qed.
Lemma D_563780 : decode_any W_563780 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563784 : bv 32 := 0xfeb68e23.
Lemma F_563784 : fetch_word AsanUbsan.M.loaded_segments (0x563770 : word) = Some W_563784.
Proof. vm_refl. Qed.
Lemma D_563784 : decode_any W_563784 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563788 : bv 32 := 0x0af66c63.
Lemma F_563788 : fetch_word AsanUbsan.M.loaded_segments (0x563774 : word) = Some W_563788.
Proof. vm_refl. Qed.
Lemma D_563788 : decode_any W_563788 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56378c : bv 32 := 0x40a006bb.
Lemma F_56378c : fetch_word AsanUbsan.M.loaded_segments (0x563778 : word) = Some W_56378c.
Proof. vm_refl. Qed.
Lemma D_56378c : decode_any W_56378c = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563790 : bv 32 := 0x03859813.
Lemma F_563790 : fetch_word AsanUbsan.M.loaded_segments (0x56377c : word) = Some W_563790.
Proof. vm_refl. Qed.
Lemma D_563790 : decode_any W_563790 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563794 : bv 32 := 0x101015b7.
Lemma F_563794 : fetch_word AsanUbsan.M.loaded_segments (0x563780 : word) = Some W_563794.
Proof. vm_refl. Qed.
Lemma D_563794 : decode_any W_563794 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563798 : bv 32 := 0x0036f693.
Lemma F_563798 : fetch_word AsanUbsan.M.loaded_segments (0x563784 : word) = Some W_563798.
Proof. vm_refl. Qed.
Lemma D_563798 : decode_any W_563798 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56379c : bv 32 := 0x00459713.
Lemma F_56379c : fetch_word AsanUbsan.M.loaded_segments (0x563788 : word) = Some W_56379c.
Proof. vm_refl. Qed.
Lemma D_56379c : decode_any W_56379c = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637a0 : bv 32 := 0x40d60633.
Lemma F_5637a0 : fetch_word AsanUbsan.M.loaded_segments (0x56378c : word) = Some W_5637a0.
Proof. vm_refl. Qed.
Lemma D_5637a0 : decode_any W_5637a0 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637a4 : bv 32 := 0x00d505b3.
Lemma F_5637a4 : fetch_word AsanUbsan.M.loaded_segments (0x563790 : word) = Some W_5637a4.
Proof. vm_refl. Qed.
Lemma D_5637a4 : decode_any W_5637a4 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637a8 : bv 32 := 0x10070693.
Lemma F_5637a8 : fetch_word AsanUbsan.M.loaded_segments (0x563794 : word) = Some W_5637a8.
Proof. vm_refl. Qed.
Lemma D_5637a8 : decode_any W_5637a8 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637ac : bv 32 := 0xffc67713.
Lemma F_5637ac : fetch_word AsanUbsan.M.loaded_segments (0x563798 : word) = Some W_5637ac.
Proof. vm_refl. Qed.
Lemma D_5637ac : decode_any W_5637ac = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637b0 : bv 32 := 0x02d83633.
Lemma F_5637b0 : fetch_word AsanUbsan.M.loaded_segments (0x56379c : word) = Some W_5637b0.
Proof. vm_refl. Qed.
Lemma D_5637b0 : decode_any W_5637b0 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637b4 : bv 32 := 0x00c5a023.
Lemma F_5637b4 : fetch_word AsanUbsan.M.loaded_segments (0x5637a0 : word) = Some W_5637b4.
Proof. vm_refl. Qed.
Lemma D_5637b4 : decode_any W_5637b4 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637b8 : bv 32 := 0x00e586b3.
Lemma F_5637b8 : fetch_word AsanUbsan.M.loaded_segments (0x5637a4 : word) = Some W_5637b8.
Proof. vm_refl. Qed.
Lemma D_5637b8 : decode_any W_5637b8 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637bc : bv 32 := 0xfec6ae23.
Lemma F_5637bc : fetch_word AsanUbsan.M.loaded_segments (0x5637a8 : word) = Some W_5637bc.
Proof. vm_refl. Qed.
Lemma D_5637bc : decode_any W_5637bc = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637c0 : bv 32 := 0x08f76063.
Lemma F_5637c0 : fetch_word AsanUbsan.M.loaded_segments (0x5637ac : word) = Some W_5637c0.
Proof. vm_refl. Qed.
Lemma D_5637c0 : decode_any W_5637c0 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637c4 : bv 32 := 0x00c5a223.
Lemma F_5637c4 : fetch_word AsanUbsan.M.loaded_segments (0x5637b0 : word) = Some W_5637c4.
Proof. vm_refl. Qed.
Lemma D_5637c4 : decode_any W_5637c4 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637c8 : bv 32 := 0x00c5a423.
Lemma F_5637c8 : fetch_word AsanUbsan.M.loaded_segments (0x5637b4 : word) = Some W_5637c8.
Proof. vm_refl. Qed.
Lemma D_5637c8 : decode_any W_5637c8 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637cc : bv 32 := 0x01900793.
Lemma F_5637cc : fetch_word AsanUbsan.M.loaded_segments (0x5637b8 : word) = Some W_5637cc.
Proof. vm_refl. Qed.
Lemma D_5637cc : decode_any W_5637cc = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637d0 : bv 32 := 0xfec6aa23.
Lemma F_5637d0 : fetch_word AsanUbsan.M.loaded_segments (0x5637bc : word) = Some W_5637d0.
Proof. vm_refl. Qed.
Lemma D_5637d0 : decode_any W_5637d0 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637d4 : bv 32 := 0xfec6ac23.
Lemma F_5637d4 : fetch_word AsanUbsan.M.loaded_segments (0x5637c0 : word) = Some W_5637d4.
Proof. vm_refl. Qed.
Lemma D_5637d4 : decode_any W_5637d4 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637d8 : bv 32 := 0x06f76463.
Lemma F_5637d8 : fetch_word AsanUbsan.M.loaded_segments (0x5637c4 : word) = Some W_5637d8.
Proof. vm_refl. Qed.
Lemma D_5637d8 : decode_any W_5637d8 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637dc : bv 32 := 0x00c5a623.
Lemma F_5637dc : fetch_word AsanUbsan.M.loaded_segments (0x5637c8 : word) = Some W_5637dc.
Proof. vm_refl. Qed.
Lemma D_5637dc : decode_any W_5637dc = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637e0 : bv 32 := 0x00c5a823.
Lemma F_5637e0 : fetch_word AsanUbsan.M.loaded_segments (0x5637cc : word) = Some W_5637e0.
Proof. vm_refl. Qed.
Lemma D_5637e0 : decode_any W_5637e0 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637e4 : bv 32 := 0x00c5aa23.
Lemma F_5637e4 : fetch_word AsanUbsan.M.loaded_segments (0x5637d0 : word) = Some W_5637e4.
Proof. vm_refl. Qed.
Lemma D_5637e4 : decode_any W_5637e4 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637e8 : bv 32 := 0x00c5ac23.
Lemma F_5637e8 : fetch_word AsanUbsan.M.loaded_segments (0x5637d4 : word) = Some W_5637e8.
Proof. vm_refl. Qed.
Lemma D_5637e8 : decode_any W_5637e8 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637ec : bv 32 := 0x0045f793.
Lemma F_5637ec : fetch_word AsanUbsan.M.loaded_segments (0x5637d8 : word) = Some W_5637ec.
Proof. vm_refl. Qed.
Lemma D_5637ec : decode_any W_5637ec = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637f0 : bv 32 := 0x02000813.
Lemma F_5637f0 : fetch_word AsanUbsan.M.loaded_segments (0x5637dc : word) = Some W_5637f0.
Proof. vm_refl. Qed.
Lemma D_5637f0 : decode_any W_5637f0 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637f4 : bv 32 := 0x01878793.
Lemma F_5637f4 : fetch_word AsanUbsan.M.loaded_segments (0x5637e0 : word) = Some W_5637f4.
Proof. vm_refl. Qed.
Lemma D_5637f4 : decode_any W_5637f4 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637f8 : bv 32 := 0x40f70733.
Lemma F_5637f8 : fetch_word AsanUbsan.M.loaded_segments (0x5637e4 : word) = Some W_5637f8.
Proof. vm_refl. Qed.
Lemma D_5637f8 : decode_any W_5637f8 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5637fc : bv 32 := 0xfec6a223.
Lemma F_5637fc : fetch_word AsanUbsan.M.loaded_segments (0x5637e8 : word) = Some W_5637fc.
Proof. vm_refl. Qed.
Lemma D_5637fc : decode_any W_5637fc = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563800 : bv 32 := 0xfec6a423.
Lemma F_563800 : fetch_word AsanUbsan.M.loaded_segments (0x5637ec : word) = Some W_563800.
Proof. vm_refl. Qed.
Lemma D_563800 : decode_any W_563800 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563804 : bv 32 := 0xfec6a623.
Lemma F_563804 : fetch_word AsanUbsan.M.loaded_segments (0x5637f0 : word) = Some W_563804.
Proof. vm_refl. Qed.
Lemma D_563804 : decode_any W_563804 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563808 : bv 32 := 0xfec6a823.
Lemma F_563808 : fetch_word AsanUbsan.M.loaded_segments (0x5637f4 : word) = Some W_563808.
Proof. vm_refl. Qed.
Lemma D_563808 : decode_any W_563808 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56380c : bv 32 := 0x03076a63.
Lemma F_56380c : fetch_word AsanUbsan.M.loaded_segments (0x5637f8 : word) = Some W_56380c.
Proof. vm_refl. Qed.
Lemma D_56380c : decode_any W_56380c = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563810 : bv 32 := 0x02061613.
Lemma F_563810 : fetch_word AsanUbsan.M.loaded_segments (0x5637fc : word) = Some W_563810.
Proof. vm_refl. Qed.
Lemma D_563810 : decode_any W_563810 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563814 : bv 32 := 0x00f585b3.
Lemma F_563814 : fetch_word AsanUbsan.M.loaded_segments (0x563800 : word) = Some W_563814.
Proof. vm_refl. Qed.
Lemma D_563814 : decode_any W_563814 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563818 : bv 32 := 0x02065693.
Lemma F_563818 : fetch_word AsanUbsan.M.loaded_segments (0x563804 : word) = Some W_563818.
Proof. vm_refl. Qed.
Lemma D_563818 : decode_any W_563818 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56381c : bv 32 := 0x00d66633.
Lemma F_56381c : fetch_word AsanUbsan.M.loaded_segments (0x563808 : word) = Some W_56381c.
Proof. vm_refl. Qed.
Lemma D_56381c : decode_any W_56381c = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563820 : bv 32 := 0x01f00693.
Lemma F_563820 : fetch_word AsanUbsan.M.loaded_segments (0x56380c : word) = Some W_563820.
Proof. vm_refl. Qed.
Lemma D_563820 : decode_any W_563820 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563824 : bv 32 := 0x00c5b023.
Lemma F_563824 : fetch_word AsanUbsan.M.loaded_segments (0x563810 : word) = Some W_563824.
Proof. vm_refl. Qed.
Lemma D_563824 : decode_any W_563824 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563828 : bv 32 := 0x00c5b423.
Lemma F_563828 : fetch_word AsanUbsan.M.loaded_segments (0x563814 : word) = Some W_563828.
Proof. vm_refl. Qed.
Lemma D_563828 : decode_any W_563828 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56382c : bv 32 := 0x00c5b823.
Lemma F_56382c : fetch_word AsanUbsan.M.loaded_segments (0x563818 : word) = Some W_56382c.
Proof. vm_refl. Qed.
Lemma D_56382c : decode_any W_56382c = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563830 : bv 32 := 0x00c5bc23.
Lemma F_563830 : fetch_word AsanUbsan.M.loaded_segments (0x56381c : word) = Some W_563830.
Proof. vm_refl. Qed.
Lemma D_563830 : decode_any W_563830 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563834 : bv 32 := 0xfe070713.
Lemma F_563834 : fetch_word AsanUbsan.M.loaded_segments (0x563820 : word) = Some W_563834.
Proof. vm_refl. Qed.
Lemma D_563834 : decode_any W_563834 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563838 : bv 32 := 0x02058593.
Lemma F_563838 : fetch_word AsanUbsan.M.loaded_segments (0x563824 : word) = Some W_563838.
Proof. vm_refl. Qed.
Lemma D_563838 : decode_any W_563838 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_56383c : bv 32 := 0xfee6e4e3.
Lemma F_56383c : fetch_word AsanUbsan.M.loaded_segments (0x563828 : word) = Some W_56383c.
Proof. vm_refl. Qed.
Lemma D_56383c : decode_any W_56383c = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_563840 : bv 32 := 0x00008067.
Lemma F_563840 : fetch_word AsanUbsan.M.loaded_segments (0x56382c : word) = Some W_563840.
Proof. vm_refl. Qed.
Lemma D_563840 : decode_any W_563840 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0x563738%Z.
Definition Fo_000 := F_56374c.
Definition Do_000 := D_56374c.
Definition Fo_004 := F_563750.
Definition Do_004 := D_563750.
Definition Fo_008 := F_563754.
Definition Do_008 := D_563754.
Definition Fo_00c := F_563758.
Definition Do_00c := D_563758.
Definition Fo_010 := F_56375c.
Definition Do_010 := D_56375c.
Definition Fo_014 := F_563760.
Definition Do_014 := D_563760.
Definition Fo_018 := F_563764.
Definition Do_018 := D_563764.
Definition Fo_01c := F_563768.
Definition Do_01c := D_563768.
Definition Fo_020 := F_56376c.
Definition Do_020 := D_56376c.
Definition Fo_024 := F_563770.
Definition Do_024 := D_563770.
Definition Fo_028 := F_563774.
Definition Do_028 := D_563774.
Definition Fo_02c := F_563778.
Definition Do_02c := D_563778.
Definition Fo_030 := F_56377c.
Definition Do_030 := D_56377c.
Definition Fo_034 := F_563780.
Definition Do_034 := D_563780.
Definition Fo_038 := F_563784.
Definition Do_038 := D_563784.
Definition Fo_03c := F_563788.
Definition Do_03c := D_563788.
Definition Fo_040 := F_56378c.
Definition Do_040 := D_56378c.
Definition Fo_044 := F_563790.
Definition Do_044 := D_563790.
Definition Fo_048 := F_563794.
Definition Do_048 := D_563794.
Definition Fo_04c := F_563798.
Definition Do_04c := D_563798.
Definition Fo_050 := F_56379c.
Definition Do_050 := D_56379c.
Definition Fo_054 := F_5637a0.
Definition Do_054 := D_5637a0.
Definition Fo_058 := F_5637a4.
Definition Do_058 := D_5637a4.
Definition Fo_05c := F_5637a8.
Definition Do_05c := D_5637a8.
Definition Fo_060 := F_5637ac.
Definition Do_060 := D_5637ac.
Definition Fo_064 := F_5637b0.
Definition Do_064 := D_5637b0.
Definition Fo_068 := F_5637b4.
Definition Do_068 := D_5637b4.
Definition Fo_06c := F_5637b8.
Definition Do_06c := D_5637b8.
Definition Fo_070 := F_5637bc.
Definition Do_070 := D_5637bc.
Definition Fo_074 := F_5637c0.
Definition Do_074 := D_5637c0.
Definition Fo_078 := F_5637c4.
Definition Do_078 := D_5637c4.
Definition Fo_07c := F_5637c8.
Definition Do_07c := D_5637c8.
Definition Fo_080 := F_5637cc.
Definition Do_080 := D_5637cc.
Definition Fo_084 := F_5637d0.
Definition Do_084 := D_5637d0.
Definition Fo_088 := F_5637d4.
Definition Do_088 := D_5637d4.
Definition Fo_08c := F_5637d8.
Definition Do_08c := D_5637d8.
Definition Fo_090 := F_5637dc.
Definition Do_090 := D_5637dc.
Definition Fo_094 := F_5637e0.
Definition Do_094 := D_5637e0.
Definition Fo_098 := F_5637e4.
Definition Do_098 := D_5637e4.
Definition Fo_09c := F_5637e8.
Definition Do_09c := D_5637e8.
Definition Fo_0a0 := F_5637ec.
Definition Do_0a0 := D_5637ec.
Definition Fo_0a4 := F_5637f0.
Definition Do_0a4 := D_5637f0.
Definition Fo_0a8 := F_5637f4.
Definition Do_0a8 := D_5637f4.
Definition Fo_0ac := F_5637f8.
Definition Do_0ac := D_5637f8.
Definition Fo_0b0 := F_5637fc.
Definition Do_0b0 := D_5637fc.
Definition Fo_0b4 := F_563800.
Definition Do_0b4 := D_563800.
Definition Fo_0b8 := F_563804.
Definition Do_0b8 := D_563804.
Definition Fo_0bc := F_563808.
Definition Do_0bc := D_563808.
Definition Fo_0c0 := F_56380c.
Definition Do_0c0 := D_56380c.
Definition Fo_0c4 := F_563810.
Definition Do_0c4 := D_563810.
Definition Fo_0c8 := F_563814.
Definition Do_0c8 := D_563814.
Definition Fo_0cc := F_563818.
Definition Do_0cc := D_563818.
Definition Fo_0d0 := F_56381c.
Definition Do_0d0 := D_56381c.
Definition Fo_0d4 := F_563820.
Definition Do_0d4 := D_563820.
Definition Fo_0d8 := F_563824.
Definition Do_0d8 := D_563824.
Definition Fo_0dc := F_563828.
Definition Do_0dc := D_563828.
Definition Fo_0e0 := F_56382c.
Definition Do_0e0 := D_56382c.
Definition Fo_0e4 := F_563830.
Definition Do_0e4 := D_563830.
Definition Fo_0e8 := F_563834.
Definition Do_0e8 := D_563834.
Definition Fo_0ec := F_563838.
Definition Do_0ec := D_563838.
Definition Fo_0f0 := F_56383c.
Definition Do_0f0 := D_56383c.
Definition Fo_0f4 := F_563840.
Definition Do_0f4 := D_563840.
