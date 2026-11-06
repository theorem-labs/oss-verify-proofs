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
From OSSVerify.zstd.zstd_frame_info.images Require Import AsanUbsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_92708 : bv 32 := 0x0e060a63.
Lemma F_92708 : fetch_word AsanUbsan.M.loaded_segments (0x92744 : word) = Some W_92708.
Proof. vm_refl. Qed.
Lemma D_92708 : decode_any W_92708 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9270c : bv 32 := 0x00b50023.
Lemma F_9270c : fetch_word AsanUbsan.M.loaded_segments (0x92748 : word) = Some W_9270c.
Proof. vm_refl. Qed.
Lemma D_9270c : decode_any W_9270c = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92710 : bv 32 := 0x00c506b3.
Lemma F_92710 : fetch_word AsanUbsan.M.loaded_segments (0x9274c : word) = Some W_92710.
Proof. vm_refl. Qed.
Lemma D_92710 : decode_any W_92710 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92714 : bv 32 := 0x00300713.
Lemma F_92714 : fetch_word AsanUbsan.M.loaded_segments (0x92750 : word) = Some W_92714.
Proof. vm_refl. Qed.
Lemma D_92714 : decode_any W_92714 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92718 : bv 32 := 0xfeb68fa3.
Lemma F_92718 : fetch_word AsanUbsan.M.loaded_segments (0x92754 : word) = Some W_92718.
Proof. vm_refl. Qed.
Lemma D_92718 : decode_any W_92718 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9271c : bv 32 := 0x0ee66063.
Lemma F_9271c : fetch_word AsanUbsan.M.loaded_segments (0x92758 : word) = Some W_9271c.
Proof. vm_refl. Qed.
Lemma D_9271c : decode_any W_9271c = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92720 : bv 32 := 0x00b500a3.
Lemma F_92720 : fetch_word AsanUbsan.M.loaded_segments (0x9275c : word) = Some W_92720.
Proof. vm_refl. Qed.
Lemma D_92720 : decode_any W_92720 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92724 : bv 32 := 0x00b50123.
Lemma F_92724 : fetch_word AsanUbsan.M.loaded_segments (0x92760 : word) = Some W_92724.
Proof. vm_refl. Qed.
Lemma D_92724 : decode_any W_92724 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92728 : bv 32 := 0x00700713.
Lemma F_92728 : fetch_word AsanUbsan.M.loaded_segments (0x92764 : word) = Some W_92728.
Proof. vm_refl. Qed.
Lemma D_92728 : decode_any W_92728 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9272c : bv 32 := 0xfeb68ea3.
Lemma F_9272c : fetch_word AsanUbsan.M.loaded_segments (0x92768 : word) = Some W_9272c.
Proof. vm_refl. Qed.
Lemma D_9272c : decode_any W_9272c = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92730 : bv 32 := 0xfeb68f23.
Lemma F_92730 : fetch_word AsanUbsan.M.loaded_segments (0x9276c : word) = Some W_92730.
Proof. vm_refl. Qed.
Lemma D_92730 : decode_any W_92730 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92734 : bv 32 := 0x0ce66463.
Lemma F_92734 : fetch_word AsanUbsan.M.loaded_segments (0x92770 : word) = Some W_92734.
Proof. vm_refl. Qed.
Lemma D_92734 : decode_any W_92734 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92738 : bv 32 := 0x00b501a3.
Lemma F_92738 : fetch_word AsanUbsan.M.loaded_segments (0x92774 : word) = Some W_92738.
Proof. vm_refl. Qed.
Lemma D_92738 : decode_any W_92738 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9273c : bv 32 := 0x00900793.
Lemma F_9273c : fetch_word AsanUbsan.M.loaded_segments (0x92778 : word) = Some W_9273c.
Proof. vm_refl. Qed.
Lemma D_9273c : decode_any W_9273c = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92740 : bv 32 := 0xfeb68e23.
Lemma F_92740 : fetch_word AsanUbsan.M.loaded_segments (0x9277c : word) = Some W_92740.
Proof. vm_refl. Qed.
Lemma D_92740 : decode_any W_92740 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92744 : bv 32 := 0x0af66c63.
Lemma F_92744 : fetch_word AsanUbsan.M.loaded_segments (0x92780 : word) = Some W_92744.
Proof. vm_refl. Qed.
Lemma D_92744 : decode_any W_92744 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92748 : bv 32 := 0x40a006bb.
Lemma F_92748 : fetch_word AsanUbsan.M.loaded_segments (0x92784 : word) = Some W_92748.
Proof. vm_refl. Qed.
Lemma D_92748 : decode_any W_92748 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9274c : bv 32 := 0x03859813.
Lemma F_9274c : fetch_word AsanUbsan.M.loaded_segments (0x92788 : word) = Some W_9274c.
Proof. vm_refl. Qed.
Lemma D_9274c : decode_any W_9274c = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92750 : bv 32 := 0x101015b7.
Lemma F_92750 : fetch_word AsanUbsan.M.loaded_segments (0x9278c : word) = Some W_92750.
Proof. vm_refl. Qed.
Lemma D_92750 : decode_any W_92750 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92754 : bv 32 := 0x0036f693.
Lemma F_92754 : fetch_word AsanUbsan.M.loaded_segments (0x92790 : word) = Some W_92754.
Proof. vm_refl. Qed.
Lemma D_92754 : decode_any W_92754 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92758 : bv 32 := 0x00459713.
Lemma F_92758 : fetch_word AsanUbsan.M.loaded_segments (0x92794 : word) = Some W_92758.
Proof. vm_refl. Qed.
Lemma D_92758 : decode_any W_92758 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9275c : bv 32 := 0x40d60633.
Lemma F_9275c : fetch_word AsanUbsan.M.loaded_segments (0x92798 : word) = Some W_9275c.
Proof. vm_refl. Qed.
Lemma D_9275c : decode_any W_9275c = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92760 : bv 32 := 0x00d505b3.
Lemma F_92760 : fetch_word AsanUbsan.M.loaded_segments (0x9279c : word) = Some W_92760.
Proof. vm_refl. Qed.
Lemma D_92760 : decode_any W_92760 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92764 : bv 32 := 0x10070693.
Lemma F_92764 : fetch_word AsanUbsan.M.loaded_segments (0x927a0 : word) = Some W_92764.
Proof. vm_refl. Qed.
Lemma D_92764 : decode_any W_92764 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92768 : bv 32 := 0xffc67713.
Lemma F_92768 : fetch_word AsanUbsan.M.loaded_segments (0x927a4 : word) = Some W_92768.
Proof. vm_refl. Qed.
Lemma D_92768 : decode_any W_92768 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9276c : bv 32 := 0x02d83633.
Lemma F_9276c : fetch_word AsanUbsan.M.loaded_segments (0x927a8 : word) = Some W_9276c.
Proof. vm_refl. Qed.
Lemma D_9276c : decode_any W_9276c = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92770 : bv 32 := 0x00c5a023.
Lemma F_92770 : fetch_word AsanUbsan.M.loaded_segments (0x927ac : word) = Some W_92770.
Proof. vm_refl. Qed.
Lemma D_92770 : decode_any W_92770 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92774 : bv 32 := 0x00e586b3.
Lemma F_92774 : fetch_word AsanUbsan.M.loaded_segments (0x927b0 : word) = Some W_92774.
Proof. vm_refl. Qed.
Lemma D_92774 : decode_any W_92774 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92778 : bv 32 := 0xfec6ae23.
Lemma F_92778 : fetch_word AsanUbsan.M.loaded_segments (0x927b4 : word) = Some W_92778.
Proof. vm_refl. Qed.
Lemma D_92778 : decode_any W_92778 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9277c : bv 32 := 0x08f76063.
Lemma F_9277c : fetch_word AsanUbsan.M.loaded_segments (0x927b8 : word) = Some W_9277c.
Proof. vm_refl. Qed.
Lemma D_9277c : decode_any W_9277c = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92780 : bv 32 := 0x00c5a223.
Lemma F_92780 : fetch_word AsanUbsan.M.loaded_segments (0x927bc : word) = Some W_92780.
Proof. vm_refl. Qed.
Lemma D_92780 : decode_any W_92780 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92784 : bv 32 := 0x00c5a423.
Lemma F_92784 : fetch_word AsanUbsan.M.loaded_segments (0x927c0 : word) = Some W_92784.
Proof. vm_refl. Qed.
Lemma D_92784 : decode_any W_92784 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92788 : bv 32 := 0x01900793.
Lemma F_92788 : fetch_word AsanUbsan.M.loaded_segments (0x927c4 : word) = Some W_92788.
Proof. vm_refl. Qed.
Lemma D_92788 : decode_any W_92788 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9278c : bv 32 := 0xfec6aa23.
Lemma F_9278c : fetch_word AsanUbsan.M.loaded_segments (0x927c8 : word) = Some W_9278c.
Proof. vm_refl. Qed.
Lemma D_9278c : decode_any W_9278c = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92790 : bv 32 := 0xfec6ac23.
Lemma F_92790 : fetch_word AsanUbsan.M.loaded_segments (0x927cc : word) = Some W_92790.
Proof. vm_refl. Qed.
Lemma D_92790 : decode_any W_92790 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92794 : bv 32 := 0x06f76463.
Lemma F_92794 : fetch_word AsanUbsan.M.loaded_segments (0x927d0 : word) = Some W_92794.
Proof. vm_refl. Qed.
Lemma D_92794 : decode_any W_92794 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92798 : bv 32 := 0x00c5a623.
Lemma F_92798 : fetch_word AsanUbsan.M.loaded_segments (0x927d4 : word) = Some W_92798.
Proof. vm_refl. Qed.
Lemma D_92798 : decode_any W_92798 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9279c : bv 32 := 0x00c5a823.
Lemma F_9279c : fetch_word AsanUbsan.M.loaded_segments (0x927d8 : word) = Some W_9279c.
Proof. vm_refl. Qed.
Lemma D_9279c : decode_any W_9279c = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927a0 : bv 32 := 0x00c5aa23.
Lemma F_927a0 : fetch_word AsanUbsan.M.loaded_segments (0x927dc : word) = Some W_927a0.
Proof. vm_refl. Qed.
Lemma D_927a0 : decode_any W_927a0 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927a4 : bv 32 := 0x00c5ac23.
Lemma F_927a4 : fetch_word AsanUbsan.M.loaded_segments (0x927e0 : word) = Some W_927a4.
Proof. vm_refl. Qed.
Lemma D_927a4 : decode_any W_927a4 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927a8 : bv 32 := 0x0045f793.
Lemma F_927a8 : fetch_word AsanUbsan.M.loaded_segments (0x927e4 : word) = Some W_927a8.
Proof. vm_refl. Qed.
Lemma D_927a8 : decode_any W_927a8 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927ac : bv 32 := 0x02000813.
Lemma F_927ac : fetch_word AsanUbsan.M.loaded_segments (0x927e8 : word) = Some W_927ac.
Proof. vm_refl. Qed.
Lemma D_927ac : decode_any W_927ac = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927b0 : bv 32 := 0x01878793.
Lemma F_927b0 : fetch_word AsanUbsan.M.loaded_segments (0x927ec : word) = Some W_927b0.
Proof. vm_refl. Qed.
Lemma D_927b0 : decode_any W_927b0 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927b4 : bv 32 := 0x40f70733.
Lemma F_927b4 : fetch_word AsanUbsan.M.loaded_segments (0x927f0 : word) = Some W_927b4.
Proof. vm_refl. Qed.
Lemma D_927b4 : decode_any W_927b4 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927b8 : bv 32 := 0xfec6a223.
Lemma F_927b8 : fetch_word AsanUbsan.M.loaded_segments (0x927f4 : word) = Some W_927b8.
Proof. vm_refl. Qed.
Lemma D_927b8 : decode_any W_927b8 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927bc : bv 32 := 0xfec6a423.
Lemma F_927bc : fetch_word AsanUbsan.M.loaded_segments (0x927f8 : word) = Some W_927bc.
Proof. vm_refl. Qed.
Lemma D_927bc : decode_any W_927bc = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927c0 : bv 32 := 0xfec6a623.
Lemma F_927c0 : fetch_word AsanUbsan.M.loaded_segments (0x927fc : word) = Some W_927c0.
Proof. vm_refl. Qed.
Lemma D_927c0 : decode_any W_927c0 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927c4 : bv 32 := 0xfec6a823.
Lemma F_927c4 : fetch_word AsanUbsan.M.loaded_segments (0x92800 : word) = Some W_927c4.
Proof. vm_refl. Qed.
Lemma D_927c4 : decode_any W_927c4 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927c8 : bv 32 := 0x03076a63.
Lemma F_927c8 : fetch_word AsanUbsan.M.loaded_segments (0x92804 : word) = Some W_927c8.
Proof. vm_refl. Qed.
Lemma D_927c8 : decode_any W_927c8 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927cc : bv 32 := 0x02061613.
Lemma F_927cc : fetch_word AsanUbsan.M.loaded_segments (0x92808 : word) = Some W_927cc.
Proof. vm_refl. Qed.
Lemma D_927cc : decode_any W_927cc = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927d0 : bv 32 := 0x00f585b3.
Lemma F_927d0 : fetch_word AsanUbsan.M.loaded_segments (0x9280c : word) = Some W_927d0.
Proof. vm_refl. Qed.
Lemma D_927d0 : decode_any W_927d0 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927d4 : bv 32 := 0x02065693.
Lemma F_927d4 : fetch_word AsanUbsan.M.loaded_segments (0x92810 : word) = Some W_927d4.
Proof. vm_refl. Qed.
Lemma D_927d4 : decode_any W_927d4 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927d8 : bv 32 := 0x00d66633.
Lemma F_927d8 : fetch_word AsanUbsan.M.loaded_segments (0x92814 : word) = Some W_927d8.
Proof. vm_refl. Qed.
Lemma D_927d8 : decode_any W_927d8 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927dc : bv 32 := 0x01f00693.
Lemma F_927dc : fetch_word AsanUbsan.M.loaded_segments (0x92818 : word) = Some W_927dc.
Proof. vm_refl. Qed.
Lemma D_927dc : decode_any W_927dc = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927e0 : bv 32 := 0x00c5b023.
Lemma F_927e0 : fetch_word AsanUbsan.M.loaded_segments (0x9281c : word) = Some W_927e0.
Proof. vm_refl. Qed.
Lemma D_927e0 : decode_any W_927e0 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927e4 : bv 32 := 0x00c5b423.
Lemma F_927e4 : fetch_word AsanUbsan.M.loaded_segments (0x92820 : word) = Some W_927e4.
Proof. vm_refl. Qed.
Lemma D_927e4 : decode_any W_927e4 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927e8 : bv 32 := 0x00c5b823.
Lemma F_927e8 : fetch_word AsanUbsan.M.loaded_segments (0x92824 : word) = Some W_927e8.
Proof. vm_refl. Qed.
Lemma D_927e8 : decode_any W_927e8 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927ec : bv 32 := 0x00c5bc23.
Lemma F_927ec : fetch_word AsanUbsan.M.loaded_segments (0x92828 : word) = Some W_927ec.
Proof. vm_refl. Qed.
Lemma D_927ec : decode_any W_927ec = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927f0 : bv 32 := 0xfe070713.
Lemma F_927f0 : fetch_word AsanUbsan.M.loaded_segments (0x9282c : word) = Some W_927f0.
Proof. vm_refl. Qed.
Lemma D_927f0 : decode_any W_927f0 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927f4 : bv 32 := 0x02058593.
Lemma F_927f4 : fetch_word AsanUbsan.M.loaded_segments (0x92830 : word) = Some W_927f4.
Proof. vm_refl. Qed.
Lemma D_927f4 : decode_any W_927f4 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927f8 : bv 32 := 0xfee6e4e3.
Lemma F_927f8 : fetch_word AsanUbsan.M.loaded_segments (0x92834 : word) = Some W_927f8.
Proof. vm_refl. Qed.
Lemma D_927f8 : decode_any W_927f8 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_927fc : bv 32 := 0x00008067.
Lemma F_927fc : fetch_word AsanUbsan.M.loaded_segments (0x92838 : word) = Some W_927fc.
Proof. vm_refl. Qed.
Lemma D_927fc : decode_any W_927fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0x92744%Z.
Definition Fo_000 := F_92708.
Definition Do_000 := D_92708.
Definition Fo_004 := F_9270c.
Definition Do_004 := D_9270c.
Definition Fo_008 := F_92710.
Definition Do_008 := D_92710.
Definition Fo_00c := F_92714.
Definition Do_00c := D_92714.
Definition Fo_010 := F_92718.
Definition Do_010 := D_92718.
Definition Fo_014 := F_9271c.
Definition Do_014 := D_9271c.
Definition Fo_018 := F_92720.
Definition Do_018 := D_92720.
Definition Fo_01c := F_92724.
Definition Do_01c := D_92724.
Definition Fo_020 := F_92728.
Definition Do_020 := D_92728.
Definition Fo_024 := F_9272c.
Definition Do_024 := D_9272c.
Definition Fo_028 := F_92730.
Definition Do_028 := D_92730.
Definition Fo_02c := F_92734.
Definition Do_02c := D_92734.
Definition Fo_030 := F_92738.
Definition Do_030 := D_92738.
Definition Fo_034 := F_9273c.
Definition Do_034 := D_9273c.
Definition Fo_038 := F_92740.
Definition Do_038 := D_92740.
Definition Fo_03c := F_92744.
Definition Do_03c := D_92744.
Definition Fo_040 := F_92748.
Definition Do_040 := D_92748.
Definition Fo_044 := F_9274c.
Definition Do_044 := D_9274c.
Definition Fo_048 := F_92750.
Definition Do_048 := D_92750.
Definition Fo_04c := F_92754.
Definition Do_04c := D_92754.
Definition Fo_050 := F_92758.
Definition Do_050 := D_92758.
Definition Fo_054 := F_9275c.
Definition Do_054 := D_9275c.
Definition Fo_058 := F_92760.
Definition Do_058 := D_92760.
Definition Fo_05c := F_92764.
Definition Do_05c := D_92764.
Definition Fo_060 := F_92768.
Definition Do_060 := D_92768.
Definition Fo_064 := F_9276c.
Definition Do_064 := D_9276c.
Definition Fo_068 := F_92770.
Definition Do_068 := D_92770.
Definition Fo_06c := F_92774.
Definition Do_06c := D_92774.
Definition Fo_070 := F_92778.
Definition Do_070 := D_92778.
Definition Fo_074 := F_9277c.
Definition Do_074 := D_9277c.
Definition Fo_078 := F_92780.
Definition Do_078 := D_92780.
Definition Fo_07c := F_92784.
Definition Do_07c := D_92784.
Definition Fo_080 := F_92788.
Definition Do_080 := D_92788.
Definition Fo_084 := F_9278c.
Definition Do_084 := D_9278c.
Definition Fo_088 := F_92790.
Definition Do_088 := D_92790.
Definition Fo_08c := F_92794.
Definition Do_08c := D_92794.
Definition Fo_090 := F_92798.
Definition Do_090 := D_92798.
Definition Fo_094 := F_9279c.
Definition Do_094 := D_9279c.
Definition Fo_098 := F_927a0.
Definition Do_098 := D_927a0.
Definition Fo_09c := F_927a4.
Definition Do_09c := D_927a4.
Definition Fo_0a0 := F_927a8.
Definition Do_0a0 := D_927a8.
Definition Fo_0a4 := F_927ac.
Definition Do_0a4 := D_927ac.
Definition Fo_0a8 := F_927b0.
Definition Do_0a8 := D_927b0.
Definition Fo_0ac := F_927b4.
Definition Do_0ac := D_927b4.
Definition Fo_0b0 := F_927b8.
Definition Do_0b0 := D_927b8.
Definition Fo_0b4 := F_927bc.
Definition Do_0b4 := D_927bc.
Definition Fo_0b8 := F_927c0.
Definition Do_0b8 := D_927c0.
Definition Fo_0bc := F_927c4.
Definition Do_0bc := D_927c4.
Definition Fo_0c0 := F_927c8.
Definition Do_0c0 := D_927c8.
Definition Fo_0c4 := F_927cc.
Definition Do_0c4 := D_927cc.
Definition Fo_0c8 := F_927d0.
Definition Do_0c8 := D_927d0.
Definition Fo_0cc := F_927d4.
Definition Do_0cc := D_927d4.
Definition Fo_0d0 := F_927d8.
Definition Do_0d0 := D_927d8.
Definition Fo_0d4 := F_927dc.
Definition Do_0d4 := D_927dc.
Definition Fo_0d8 := F_927e0.
Definition Do_0d8 := D_927e0.
Definition Fo_0dc := F_927e4.
Definition Do_0dc := D_927e4.
Definition Fo_0e0 := F_927e8.
Definition Do_0e0 := D_927e8.
Definition Fo_0e4 := F_927ec.
Definition Do_0e4 := D_927ec.
Definition Fo_0e8 := F_927f0.
Definition Do_0e8 := D_927f0.
Definition Fo_0ec := F_927f4.
Definition Do_0ec := D_927f4.
Definition Fo_0f0 := F_927f8.
Definition Do_0f0 := D_927f8.
Definition Fo_0f4 := F_927fc.
Definition Do_0f4 := D_927fc.
