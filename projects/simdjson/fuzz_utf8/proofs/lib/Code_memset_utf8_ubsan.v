(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_ce69c : bv 32 := 0x0e060a63.
Lemma F_ce69c : fetch_word Ubsan.M.loaded_segments (0xce854 : word) = Some W_ce69c.
Proof. vm_refl. Qed.
Lemma D_ce69c : decode_any W_ce69c = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6a0 : bv 32 := 0x00b50023.
Lemma F_ce6a0 : fetch_word Ubsan.M.loaded_segments (0xce858 : word) = Some W_ce6a0.
Proof. vm_refl. Qed.
Lemma D_ce6a0 : decode_any W_ce6a0 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6a4 : bv 32 := 0x00c506b3.
Lemma F_ce6a4 : fetch_word Ubsan.M.loaded_segments (0xce85c : word) = Some W_ce6a4.
Proof. vm_refl. Qed.
Lemma D_ce6a4 : decode_any W_ce6a4 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6a8 : bv 32 := 0x00300713.
Lemma F_ce6a8 : fetch_word Ubsan.M.loaded_segments (0xce860 : word) = Some W_ce6a8.
Proof. vm_refl. Qed.
Lemma D_ce6a8 : decode_any W_ce6a8 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6ac : bv 32 := 0xfeb68fa3.
Lemma F_ce6ac : fetch_word Ubsan.M.loaded_segments (0xce864 : word) = Some W_ce6ac.
Proof. vm_refl. Qed.
Lemma D_ce6ac : decode_any W_ce6ac = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6b0 : bv 32 := 0x0ee66063.
Lemma F_ce6b0 : fetch_word Ubsan.M.loaded_segments (0xce868 : word) = Some W_ce6b0.
Proof. vm_refl. Qed.
Lemma D_ce6b0 : decode_any W_ce6b0 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6b4 : bv 32 := 0x00b500a3.
Lemma F_ce6b4 : fetch_word Ubsan.M.loaded_segments (0xce86c : word) = Some W_ce6b4.
Proof. vm_refl. Qed.
Lemma D_ce6b4 : decode_any W_ce6b4 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6b8 : bv 32 := 0x00b50123.
Lemma F_ce6b8 : fetch_word Ubsan.M.loaded_segments (0xce870 : word) = Some W_ce6b8.
Proof. vm_refl. Qed.
Lemma D_ce6b8 : decode_any W_ce6b8 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6bc : bv 32 := 0x00700713.
Lemma F_ce6bc : fetch_word Ubsan.M.loaded_segments (0xce874 : word) = Some W_ce6bc.
Proof. vm_refl. Qed.
Lemma D_ce6bc : decode_any W_ce6bc = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6c0 : bv 32 := 0xfeb68ea3.
Lemma F_ce6c0 : fetch_word Ubsan.M.loaded_segments (0xce878 : word) = Some W_ce6c0.
Proof. vm_refl. Qed.
Lemma D_ce6c0 : decode_any W_ce6c0 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6c4 : bv 32 := 0xfeb68f23.
Lemma F_ce6c4 : fetch_word Ubsan.M.loaded_segments (0xce87c : word) = Some W_ce6c4.
Proof. vm_refl. Qed.
Lemma D_ce6c4 : decode_any W_ce6c4 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6c8 : bv 32 := 0x0ce66463.
Lemma F_ce6c8 : fetch_word Ubsan.M.loaded_segments (0xce880 : word) = Some W_ce6c8.
Proof. vm_refl. Qed.
Lemma D_ce6c8 : decode_any W_ce6c8 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6cc : bv 32 := 0x00b501a3.
Lemma F_ce6cc : fetch_word Ubsan.M.loaded_segments (0xce884 : word) = Some W_ce6cc.
Proof. vm_refl. Qed.
Lemma D_ce6cc : decode_any W_ce6cc = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6d0 : bv 32 := 0x00900793.
Lemma F_ce6d0 : fetch_word Ubsan.M.loaded_segments (0xce888 : word) = Some W_ce6d0.
Proof. vm_refl. Qed.
Lemma D_ce6d0 : decode_any W_ce6d0 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6d4 : bv 32 := 0xfeb68e23.
Lemma F_ce6d4 : fetch_word Ubsan.M.loaded_segments (0xce88c : word) = Some W_ce6d4.
Proof. vm_refl. Qed.
Lemma D_ce6d4 : decode_any W_ce6d4 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6d8 : bv 32 := 0x0af66c63.
Lemma F_ce6d8 : fetch_word Ubsan.M.loaded_segments (0xce890 : word) = Some W_ce6d8.
Proof. vm_refl. Qed.
Lemma D_ce6d8 : decode_any W_ce6d8 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6dc : bv 32 := 0x40a006bb.
Lemma F_ce6dc : fetch_word Ubsan.M.loaded_segments (0xce894 : word) = Some W_ce6dc.
Proof. vm_refl. Qed.
Lemma D_ce6dc : decode_any W_ce6dc = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6e0 : bv 32 := 0x03859813.
Lemma F_ce6e0 : fetch_word Ubsan.M.loaded_segments (0xce898 : word) = Some W_ce6e0.
Proof. vm_refl. Qed.
Lemma D_ce6e0 : decode_any W_ce6e0 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6e4 : bv 32 := 0x101015b7.
Lemma F_ce6e4 : fetch_word Ubsan.M.loaded_segments (0xce89c : word) = Some W_ce6e4.
Proof. vm_refl. Qed.
Lemma D_ce6e4 : decode_any W_ce6e4 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6e8 : bv 32 := 0x0036f693.
Lemma F_ce6e8 : fetch_word Ubsan.M.loaded_segments (0xce8a0 : word) = Some W_ce6e8.
Proof. vm_refl. Qed.
Lemma D_ce6e8 : decode_any W_ce6e8 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6ec : bv 32 := 0x00459713.
Lemma F_ce6ec : fetch_word Ubsan.M.loaded_segments (0xce8a4 : word) = Some W_ce6ec.
Proof. vm_refl. Qed.
Lemma D_ce6ec : decode_any W_ce6ec = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6f0 : bv 32 := 0x40d60633.
Lemma F_ce6f0 : fetch_word Ubsan.M.loaded_segments (0xce8a8 : word) = Some W_ce6f0.
Proof. vm_refl. Qed.
Lemma D_ce6f0 : decode_any W_ce6f0 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6f4 : bv 32 := 0x00d505b3.
Lemma F_ce6f4 : fetch_word Ubsan.M.loaded_segments (0xce8ac : word) = Some W_ce6f4.
Proof. vm_refl. Qed.
Lemma D_ce6f4 : decode_any W_ce6f4 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6f8 : bv 32 := 0x10070693.
Lemma F_ce6f8 : fetch_word Ubsan.M.loaded_segments (0xce8b0 : word) = Some W_ce6f8.
Proof. vm_refl. Qed.
Lemma D_ce6f8 : decode_any W_ce6f8 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce6fc : bv 32 := 0xffc67713.
Lemma F_ce6fc : fetch_word Ubsan.M.loaded_segments (0xce8b4 : word) = Some W_ce6fc.
Proof. vm_refl. Qed.
Lemma D_ce6fc : decode_any W_ce6fc = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce700 : bv 32 := 0x02d83633.
Lemma F_ce700 : fetch_word Ubsan.M.loaded_segments (0xce8b8 : word) = Some W_ce700.
Proof. vm_refl. Qed.
Lemma D_ce700 : decode_any W_ce700 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce704 : bv 32 := 0x00c5a023.
Lemma F_ce704 : fetch_word Ubsan.M.loaded_segments (0xce8bc : word) = Some W_ce704.
Proof. vm_refl. Qed.
Lemma D_ce704 : decode_any W_ce704 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce708 : bv 32 := 0x00e586b3.
Lemma F_ce708 : fetch_word Ubsan.M.loaded_segments (0xce8c0 : word) = Some W_ce708.
Proof. vm_refl. Qed.
Lemma D_ce708 : decode_any W_ce708 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce70c : bv 32 := 0xfec6ae23.
Lemma F_ce70c : fetch_word Ubsan.M.loaded_segments (0xce8c4 : word) = Some W_ce70c.
Proof. vm_refl. Qed.
Lemma D_ce70c : decode_any W_ce70c = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce710 : bv 32 := 0x08f76063.
Lemma F_ce710 : fetch_word Ubsan.M.loaded_segments (0xce8c8 : word) = Some W_ce710.
Proof. vm_refl. Qed.
Lemma D_ce710 : decode_any W_ce710 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce714 : bv 32 := 0x00c5a223.
Lemma F_ce714 : fetch_word Ubsan.M.loaded_segments (0xce8cc : word) = Some W_ce714.
Proof. vm_refl. Qed.
Lemma D_ce714 : decode_any W_ce714 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce718 : bv 32 := 0x00c5a423.
Lemma F_ce718 : fetch_word Ubsan.M.loaded_segments (0xce8d0 : word) = Some W_ce718.
Proof. vm_refl. Qed.
Lemma D_ce718 : decode_any W_ce718 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce71c : bv 32 := 0x01900793.
Lemma F_ce71c : fetch_word Ubsan.M.loaded_segments (0xce8d4 : word) = Some W_ce71c.
Proof. vm_refl. Qed.
Lemma D_ce71c : decode_any W_ce71c = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce720 : bv 32 := 0xfec6aa23.
Lemma F_ce720 : fetch_word Ubsan.M.loaded_segments (0xce8d8 : word) = Some W_ce720.
Proof. vm_refl. Qed.
Lemma D_ce720 : decode_any W_ce720 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce724 : bv 32 := 0xfec6ac23.
Lemma F_ce724 : fetch_word Ubsan.M.loaded_segments (0xce8dc : word) = Some W_ce724.
Proof. vm_refl. Qed.
Lemma D_ce724 : decode_any W_ce724 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce728 : bv 32 := 0x06f76463.
Lemma F_ce728 : fetch_word Ubsan.M.loaded_segments (0xce8e0 : word) = Some W_ce728.
Proof. vm_refl. Qed.
Lemma D_ce728 : decode_any W_ce728 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce72c : bv 32 := 0x00c5a623.
Lemma F_ce72c : fetch_word Ubsan.M.loaded_segments (0xce8e4 : word) = Some W_ce72c.
Proof. vm_refl. Qed.
Lemma D_ce72c : decode_any W_ce72c = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce730 : bv 32 := 0x00c5a823.
Lemma F_ce730 : fetch_word Ubsan.M.loaded_segments (0xce8e8 : word) = Some W_ce730.
Proof. vm_refl. Qed.
Lemma D_ce730 : decode_any W_ce730 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce734 : bv 32 := 0x00c5aa23.
Lemma F_ce734 : fetch_word Ubsan.M.loaded_segments (0xce8ec : word) = Some W_ce734.
Proof. vm_refl. Qed.
Lemma D_ce734 : decode_any W_ce734 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce738 : bv 32 := 0x00c5ac23.
Lemma F_ce738 : fetch_word Ubsan.M.loaded_segments (0xce8f0 : word) = Some W_ce738.
Proof. vm_refl. Qed.
Lemma D_ce738 : decode_any W_ce738 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce73c : bv 32 := 0x0045f793.
Lemma F_ce73c : fetch_word Ubsan.M.loaded_segments (0xce8f4 : word) = Some W_ce73c.
Proof. vm_refl. Qed.
Lemma D_ce73c : decode_any W_ce73c = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce740 : bv 32 := 0x02000813.
Lemma F_ce740 : fetch_word Ubsan.M.loaded_segments (0xce8f8 : word) = Some W_ce740.
Proof. vm_refl. Qed.
Lemma D_ce740 : decode_any W_ce740 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce744 : bv 32 := 0x01878793.
Lemma F_ce744 : fetch_word Ubsan.M.loaded_segments (0xce8fc : word) = Some W_ce744.
Proof. vm_refl. Qed.
Lemma D_ce744 : decode_any W_ce744 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce748 : bv 32 := 0x40f70733.
Lemma F_ce748 : fetch_word Ubsan.M.loaded_segments (0xce900 : word) = Some W_ce748.
Proof. vm_refl. Qed.
Lemma D_ce748 : decode_any W_ce748 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce74c : bv 32 := 0xfec6a223.
Lemma F_ce74c : fetch_word Ubsan.M.loaded_segments (0xce904 : word) = Some W_ce74c.
Proof. vm_refl. Qed.
Lemma D_ce74c : decode_any W_ce74c = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce750 : bv 32 := 0xfec6a423.
Lemma F_ce750 : fetch_word Ubsan.M.loaded_segments (0xce908 : word) = Some W_ce750.
Proof. vm_refl. Qed.
Lemma D_ce750 : decode_any W_ce750 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce754 : bv 32 := 0xfec6a623.
Lemma F_ce754 : fetch_word Ubsan.M.loaded_segments (0xce90c : word) = Some W_ce754.
Proof. vm_refl. Qed.
Lemma D_ce754 : decode_any W_ce754 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce758 : bv 32 := 0xfec6a823.
Lemma F_ce758 : fetch_word Ubsan.M.loaded_segments (0xce910 : word) = Some W_ce758.
Proof. vm_refl. Qed.
Lemma D_ce758 : decode_any W_ce758 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce75c : bv 32 := 0x03076a63.
Lemma F_ce75c : fetch_word Ubsan.M.loaded_segments (0xce914 : word) = Some W_ce75c.
Proof. vm_refl. Qed.
Lemma D_ce75c : decode_any W_ce75c = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce760 : bv 32 := 0x02061613.
Lemma F_ce760 : fetch_word Ubsan.M.loaded_segments (0xce918 : word) = Some W_ce760.
Proof. vm_refl. Qed.
Lemma D_ce760 : decode_any W_ce760 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce764 : bv 32 := 0x00f585b3.
Lemma F_ce764 : fetch_word Ubsan.M.loaded_segments (0xce91c : word) = Some W_ce764.
Proof. vm_refl. Qed.
Lemma D_ce764 : decode_any W_ce764 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce768 : bv 32 := 0x02065693.
Lemma F_ce768 : fetch_word Ubsan.M.loaded_segments (0xce920 : word) = Some W_ce768.
Proof. vm_refl. Qed.
Lemma D_ce768 : decode_any W_ce768 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce76c : bv 32 := 0x00d66633.
Lemma F_ce76c : fetch_word Ubsan.M.loaded_segments (0xce924 : word) = Some W_ce76c.
Proof. vm_refl. Qed.
Lemma D_ce76c : decode_any W_ce76c = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce770 : bv 32 := 0x01f00693.
Lemma F_ce770 : fetch_word Ubsan.M.loaded_segments (0xce928 : word) = Some W_ce770.
Proof. vm_refl. Qed.
Lemma D_ce770 : decode_any W_ce770 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce774 : bv 32 := 0x00c5b023.
Lemma F_ce774 : fetch_word Ubsan.M.loaded_segments (0xce92c : word) = Some W_ce774.
Proof. vm_refl. Qed.
Lemma D_ce774 : decode_any W_ce774 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce778 : bv 32 := 0x00c5b423.
Lemma F_ce778 : fetch_word Ubsan.M.loaded_segments (0xce930 : word) = Some W_ce778.
Proof. vm_refl. Qed.
Lemma D_ce778 : decode_any W_ce778 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce77c : bv 32 := 0x00c5b823.
Lemma F_ce77c : fetch_word Ubsan.M.loaded_segments (0xce934 : word) = Some W_ce77c.
Proof. vm_refl. Qed.
Lemma D_ce77c : decode_any W_ce77c = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce780 : bv 32 := 0x00c5bc23.
Lemma F_ce780 : fetch_word Ubsan.M.loaded_segments (0xce938 : word) = Some W_ce780.
Proof. vm_refl. Qed.
Lemma D_ce780 : decode_any W_ce780 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce784 : bv 32 := 0xfe070713.
Lemma F_ce784 : fetch_word Ubsan.M.loaded_segments (0xce93c : word) = Some W_ce784.
Proof. vm_refl. Qed.
Lemma D_ce784 : decode_any W_ce784 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce788 : bv 32 := 0x02058593.
Lemma F_ce788 : fetch_word Ubsan.M.loaded_segments (0xce940 : word) = Some W_ce788.
Proof. vm_refl. Qed.
Lemma D_ce788 : decode_any W_ce788 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce78c : bv 32 := 0xfee6e4e3.
Lemma F_ce78c : fetch_word Ubsan.M.loaded_segments (0xce944 : word) = Some W_ce78c.
Proof. vm_refl. Qed.
Lemma D_ce78c : decode_any W_ce78c = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ce790 : bv 32 := 0x00008067.
Lemma F_ce790 : fetch_word Ubsan.M.loaded_segments (0xce948 : word) = Some W_ce790.
Proof. vm_refl. Qed.
Lemma D_ce790 : decode_any W_ce790 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := Ubsan.M.loaded_segments.
Definition ms_base : Z := 0xce854%Z.
Definition Fo_000 := F_ce69c.
Definition Do_000 := D_ce69c.
Definition Fo_004 := F_ce6a0.
Definition Do_004 := D_ce6a0.
Definition Fo_008 := F_ce6a4.
Definition Do_008 := D_ce6a4.
Definition Fo_00c := F_ce6a8.
Definition Do_00c := D_ce6a8.
Definition Fo_010 := F_ce6ac.
Definition Do_010 := D_ce6ac.
Definition Fo_014 := F_ce6b0.
Definition Do_014 := D_ce6b0.
Definition Fo_018 := F_ce6b4.
Definition Do_018 := D_ce6b4.
Definition Fo_01c := F_ce6b8.
Definition Do_01c := D_ce6b8.
Definition Fo_020 := F_ce6bc.
Definition Do_020 := D_ce6bc.
Definition Fo_024 := F_ce6c0.
Definition Do_024 := D_ce6c0.
Definition Fo_028 := F_ce6c4.
Definition Do_028 := D_ce6c4.
Definition Fo_02c := F_ce6c8.
Definition Do_02c := D_ce6c8.
Definition Fo_030 := F_ce6cc.
Definition Do_030 := D_ce6cc.
Definition Fo_034 := F_ce6d0.
Definition Do_034 := D_ce6d0.
Definition Fo_038 := F_ce6d4.
Definition Do_038 := D_ce6d4.
Definition Fo_03c := F_ce6d8.
Definition Do_03c := D_ce6d8.
Definition Fo_040 := F_ce6dc.
Definition Do_040 := D_ce6dc.
Definition Fo_044 := F_ce6e0.
Definition Do_044 := D_ce6e0.
Definition Fo_048 := F_ce6e4.
Definition Do_048 := D_ce6e4.
Definition Fo_04c := F_ce6e8.
Definition Do_04c := D_ce6e8.
Definition Fo_050 := F_ce6ec.
Definition Do_050 := D_ce6ec.
Definition Fo_054 := F_ce6f0.
Definition Do_054 := D_ce6f0.
Definition Fo_058 := F_ce6f4.
Definition Do_058 := D_ce6f4.
Definition Fo_05c := F_ce6f8.
Definition Do_05c := D_ce6f8.
Definition Fo_060 := F_ce6fc.
Definition Do_060 := D_ce6fc.
Definition Fo_064 := F_ce700.
Definition Do_064 := D_ce700.
Definition Fo_068 := F_ce704.
Definition Do_068 := D_ce704.
Definition Fo_06c := F_ce708.
Definition Do_06c := D_ce708.
Definition Fo_070 := F_ce70c.
Definition Do_070 := D_ce70c.
Definition Fo_074 := F_ce710.
Definition Do_074 := D_ce710.
Definition Fo_078 := F_ce714.
Definition Do_078 := D_ce714.
Definition Fo_07c := F_ce718.
Definition Do_07c := D_ce718.
Definition Fo_080 := F_ce71c.
Definition Do_080 := D_ce71c.
Definition Fo_084 := F_ce720.
Definition Do_084 := D_ce720.
Definition Fo_088 := F_ce724.
Definition Do_088 := D_ce724.
Definition Fo_08c := F_ce728.
Definition Do_08c := D_ce728.
Definition Fo_090 := F_ce72c.
Definition Do_090 := D_ce72c.
Definition Fo_094 := F_ce730.
Definition Do_094 := D_ce730.
Definition Fo_098 := F_ce734.
Definition Do_098 := D_ce734.
Definition Fo_09c := F_ce738.
Definition Do_09c := D_ce738.
Definition Fo_0a0 := F_ce73c.
Definition Do_0a0 := D_ce73c.
Definition Fo_0a4 := F_ce740.
Definition Do_0a4 := D_ce740.
Definition Fo_0a8 := F_ce744.
Definition Do_0a8 := D_ce744.
Definition Fo_0ac := F_ce748.
Definition Do_0ac := D_ce748.
Definition Fo_0b0 := F_ce74c.
Definition Do_0b0 := D_ce74c.
Definition Fo_0b4 := F_ce750.
Definition Do_0b4 := D_ce750.
Definition Fo_0b8 := F_ce754.
Definition Do_0b8 := D_ce754.
Definition Fo_0bc := F_ce758.
Definition Do_0bc := D_ce758.
Definition Fo_0c0 := F_ce75c.
Definition Do_0c0 := D_ce75c.
Definition Fo_0c4 := F_ce760.
Definition Do_0c4 := D_ce760.
Definition Fo_0c8 := F_ce764.
Definition Do_0c8 := D_ce764.
Definition Fo_0cc := F_ce768.
Definition Do_0cc := D_ce768.
Definition Fo_0d0 := F_ce76c.
Definition Do_0d0 := D_ce76c.
Definition Fo_0d4 := F_ce770.
Definition Do_0d4 := D_ce770.
Definition Fo_0d8 := F_ce774.
Definition Do_0d8 := D_ce774.
Definition Fo_0dc := F_ce778.
Definition Do_0dc := D_ce778.
Definition Fo_0e0 := F_ce77c.
Definition Do_0e0 := D_ce77c.
Definition Fo_0e4 := F_ce780.
Definition Do_0e4 := D_ce780.
Definition Fo_0e8 := F_ce784.
Definition Do_0e8 := D_ce784.
Definition Fo_0ec := F_ce788.
Definition Do_0ec := D_ce788.
Definition Fo_0f0 := F_ce78c.
Definition Do_0f0 := D_ce78c.
Definition Fo_0f4 := F_ce790.
Definition Do_0f4 := D_ce790.
