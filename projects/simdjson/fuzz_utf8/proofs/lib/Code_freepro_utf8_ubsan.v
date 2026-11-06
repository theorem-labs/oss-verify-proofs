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
Definition W_bf69c : bv 32 := 0x1c050463.
Lemma F_bf69c : fetch_word Ubsan.M.loaded_segments (0xbf854 : word) = Some W_bf69c.
Proof. vm_refl. Qed.
Lemma D_bf69c : decode_any W_bf69c = Some (Branch BC_EQ 10 0 456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6a0 : bv 32 := 0xfd010113.
Lemma F_bf6a0 : fetch_word Ubsan.M.loaded_segments (0xbf858 : word) = Some W_bf6a0.
Proof. vm_refl. Qed.
Lemma D_bf6a0 : decode_any W_bf6a0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6a4 : bv 32 := 0x02113423.
Lemma F_bf6a4 : fetch_word Ubsan.M.loaded_segments (0xbf85c : word) = Some W_bf6a4.
Proof. vm_refl. Qed.
Lemma D_bf6a4 : decode_any W_bf6a4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6a8 : bv 32 := 0x02813023.
Lemma F_bf6a8 : fetch_word Ubsan.M.loaded_segments (0xbf860 : word) = Some W_bf6a8.
Proof. vm_refl. Qed.
Lemma D_bf6a8 : decode_any W_bf6a8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6ac : bv 32 := 0x00913c23.
Lemma F_bf6ac : fetch_word Ubsan.M.loaded_segments (0xbf864 : word) = Some W_bf6ac.
Proof. vm_refl. Qed.
Lemma D_bf6ac : decode_any W_bf6ac = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6b0 : bv 32 := 0x01213823.
Lemma F_bf6b0 : fetch_word Ubsan.M.loaded_segments (0xbf868 : word) = Some W_bf6b0.
Proof. vm_refl. Qed.
Lemma D_bf6b0 : decode_any W_bf6b0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6b4 : bv 32 := 0x01313423.
Lemma F_bf6b4 : fetch_word Ubsan.M.loaded_segments (0xbf86c : word) = Some W_bf6b4.
Proof. vm_refl. Qed.
Lemma D_bf6b4 : decode_any W_bf6b4 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6b8 : bv 32 := 0x00050493.
Lemma F_bf6b8 : fetch_word Ubsan.M.loaded_segments (0xbf870 : word) = Some W_bf6b8.
Proof. vm_refl. Qed.
Lemma D_bf6b8 : decode_any W_bf6b8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6bc : bv 32 := 0x1ac000ef.
Lemma F_bf6bc : fetch_word Ubsan.M.loaded_segments (0xbf874 : word) = Some W_bf6bc.
Proof. vm_refl. Qed.
Lemma D_bf6bc : decode_any W_bf6bc = Some (Jal 1 428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6c0 : bv 32 := 0x02053583.
Lemma F_bf6c0 : fetch_word Ubsan.M.loaded_segments (0xbf878 : word) = Some W_bf6c0.
Proof. vm_refl. Qed.
Lemma D_bf6c0 : decode_any W_bf6c0 = Some (Load SZ8 true 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6c4 : bv 32 := 0xffd4c683.
Lemma F_bf6c4 : fetch_word Ubsan.M.loaded_segments (0xbf87c : word) = Some W_bf6c4.
Proof. vm_refl. Qed.
Lemma D_bf6c4 : decode_any W_bf6c4 = Some (Load SZ1 false 13 9 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6c8 : bv 32 := 0x00c5d613.
Lemma F_bf6c8 : fetch_word Ubsan.M.loaded_segments (0xbf880 : word) = Some W_bf6c8.
Proof. vm_refl. Qed.
Lemma D_bf6c8 : decode_any W_bf6c8 = Some (ShiftImm ALU_SRL 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6cc : bv 32 := 0x01f6f413.
Lemma F_bf6cc : fetch_word Ubsan.M.loaded_segments (0xbf884 : word) = Some W_bf6cc.
Proof. vm_refl. Qed.
Lemma D_bf6cc : decode_any W_bf6cc = Some (OpImm ALU_AND 8 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6d0 : bv 32 := 0x00060e63.
Lemma F_bf6d0 : fetch_word Ubsan.M.loaded_segments (0xbf888 : word) = Some W_bf6d0.
Proof. vm_refl. Qed.
Lemma D_bf6d0 : decode_any W_bf6d0 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6d4 : bv 32 := 0x01f5f613.
Lemma F_bf6d4 : fetch_word Ubsan.M.loaded_segments (0xbf88c : word) = Some W_bf6d4.
Proof. vm_refl. Qed.
Lemma D_bf6d4 : decode_any W_bf6d4 = Some (OpImm ALU_AND 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6d8 : bv 32 := 0x00061a63.
Lemma F_bf6d8 : fetch_word Ubsan.M.loaded_segments (0xbf890 : word) = Some W_bf6d8.
Proof. vm_refl. Qed.
Lemma D_bf6d8 : decode_any W_bf6d8 = Some (Branch BC_NE 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6dc : bv 32 := 0xfffff637.
Lemma F_bf6dc : fetch_word Ubsan.M.loaded_segments (0xbf894 : word) = Some W_bf6dc.
Proof. vm_refl. Qed.
Lemma D_bf6dc : decode_any W_bf6dc = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6e0 : bv 32 := 0x00c5f633.
Lemma F_bf6e0 : fetch_word Ubsan.M.loaded_segments (0xbf898 : word) = Some W_bf6e0.
Proof. vm_refl. Qed.
Lemma D_bf6e0 : decode_any W_bf6e0 = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6e4 : bv 32 := 0xff060613.
Lemma F_bf6e4 : fetch_word Ubsan.M.loaded_segments (0xbf89c : word) = Some W_bf6e4.
Proof. vm_refl. Qed.
Lemma D_bf6e4 : decode_any W_bf6e4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6e8 : bv 32 := 0x0200006f.
Lemma F_bf6e8 : fetch_word Ubsan.M.loaded_segments (0xbf8a0 : word) = Some W_bf6e8.
Proof. vm_refl. Qed.
Lemma D_bf6e8 : decode_any W_bf6e8 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6ec : bv 32 := 0x0055d613.
Lemma F_bf6ec : fetch_word Ubsan.M.loaded_segments (0xbf8a4 : word) = Some W_bf6ec.
Proof. vm_refl. Qed.
Lemma D_bf6ec : decode_any W_bf6ec = Some (ShiftImm ALU_SRL 12 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6f0 : bv 32 := 0xfff62717.
Lemma F_bf6f0 : fetch_word Ubsan.M.loaded_segments (0xbf8a8 : word) = Some W_bf6f0.
Proof. vm_refl. Qed.
Lemma D_bf6f0 : decode_any W_bf6f0 = Some (Auipc 14 1048418, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6f4 : bv 32 := 0x07e67613.
Lemma F_bf6f4 : fetch_word Ubsan.M.loaded_segments (0xbf8ac : word) = Some W_bf6f4.
Proof. vm_refl. Qed.
Lemma D_bf6f4 : decode_any W_bf6f4 = Some (OpImm ALU_AND 12 12 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6f8 : bv 32 := 0xca870713.
Lemma F_bf6f8 : fetch_word Ubsan.M.loaded_segments (0xbf8b0 : word) = Some W_bf6f8.
Proof. vm_refl. Qed.
Lemma D_bf6f8 : decode_any W_bf6f8 = Some (OpImm ALU_ADD 14 14 3240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf6fc : bv 32 := 0x00c70633.
Lemma F_bf6fc : fetch_word Ubsan.M.loaded_segments (0xbf8b4 : word) = Some W_bf6fc.
Proof. vm_refl. Qed.
Lemma D_bf6fc : decode_any W_bf6fc = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf700 : bv 32 := 0x00065603.
Lemma F_bf700 : fetch_word Ubsan.M.loaded_segments (0xbf8b8 : word) = Some W_bf700.
Proof. vm_refl. Qed.
Lemma D_bf700 : decode_any W_bf700 = Some (Load SZ2 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf704 : bv 32 := 0x00461613.
Lemma F_bf704 : fetch_word Ubsan.M.loaded_segments (0xbf8bc : word) = Some W_bf704.
Proof. vm_refl. Qed.
Lemma D_bf704 : decode_any W_bf704 = Some (ShiftImm ALU_SLL 12 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf708 : bv 32 := 0x01053703.
Lemma F_bf708 : fetch_word Ubsan.M.loaded_segments (0xbf8c0 : word) = Some W_bf708.
Proof. vm_refl. Qed.
Lemma D_bf708 : decode_any W_bf708 = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf70c : bv 32 := 0x028607b3.
Lemma F_bf70c : fetch_word Ubsan.M.loaded_segments (0xbf8c4 : word) = Some W_bf70c.
Proof. vm_refl. Qed.
Lemma D_bf70c : decode_any W_bf70c = Some (Mul M_MUL 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf710 : bv 32 := 0x0a000813.
Lemma F_bf710 : fetch_word Ubsan.M.loaded_segments (0xbf8c8 : word) = Some W_bf710.
Proof. vm_refl. Qed.
Lemma D_bf710 : decode_any W_bf710 = Some (OpImm ALU_ADD 16 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf714 : bv 32 := 0x00c70633.
Lemma F_bf714 : fetch_word Ubsan.M.loaded_segments (0xbf8cc : word) = Some W_bf714.
Proof. vm_refl. Qed.
Lemma D_bf714 : decode_any W_bf714 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf718 : bv 32 := 0x00f607b3.
Lemma F_bf718 : fetch_word Ubsan.M.loaded_segments (0xbf8d0 : word) = Some W_bf718.
Proof. vm_refl. Qed.
Lemma D_bf718 : decode_any W_bf718 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf71c : bv 32 := 0x00c78613.
Lemma F_bf71c : fetch_word Ubsan.M.loaded_segments (0xbf8d4 : word) = Some W_bf71c.
Proof. vm_refl. Qed.
Lemma D_bf71c : decode_any W_bf71c = Some (OpImm ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf720 : bv 32 := 0x0056d713.
Lemma F_bf720 : fetch_word Ubsan.M.loaded_segments (0xbf8d8 : word) = Some W_bf720.
Proof. vm_refl. Qed.
Lemma D_bf720 : decode_any W_bf720 = Some (ShiftImm ALU_SRL 14 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf724 : bv 32 := 0x0306e663.
Lemma F_bf724 : fetch_word Ubsan.M.loaded_segments (0xbf8dc : word) = Some W_bf724.
Proof. vm_refl. Qed.
Lemma D_bf724 : decode_any W_bf724 = Some (Branch BC_LTU 13 16 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf728 : bv 32 := 0x00500693.
Lemma F_bf728 : fetch_word Ubsan.M.loaded_segments (0xbf8e0 : word) = Some W_bf728.
Proof. vm_refl. Qed.
Lemma D_bf728 : decode_any W_bf728 = Some (OpImm ALU_ADD 13 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf72c : bv 32 := 0x00d70463.
Lemma F_bf72c : fetch_word Ubsan.M.loaded_segments (0xbf8e4 : word) = Some W_bf72c.
Proof. vm_refl. Qed.
Lemma D_bf72c : decode_any W_bf72c = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf730 : bv 32 := 0x00000023.
Lemma F_bf730 : fetch_word Ubsan.M.loaded_segments (0xbf8e8 : word) = Some W_bf730.
Proof. vm_refl. Qed.
Lemma D_bf730 : decode_any W_bf730 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf734 : bv 32 := 0x0087e703.
Lemma F_bf734 : fetch_word Ubsan.M.loaded_segments (0xbf8ec : word) = Some W_bf734.
Proof. vm_refl. Qed.
Lemma D_bf734 : decode_any W_bf734 = Some (Load SZ4 false 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf738 : bv 32 := 0x00400693.
Lemma F_bf738 : fetch_word Ubsan.M.loaded_segments (0xbf8f0 : word) = Some W_bf738.
Proof. vm_refl. Qed.
Lemma D_bf738 : decode_any W_bf738 = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf73c : bv 32 := 0x00e6e463.
Lemma F_bf73c : fetch_word Ubsan.M.loaded_segments (0xbf8f4 : word) = Some W_bf73c.
Proof. vm_refl. Qed.
Lemma D_bf73c : decode_any W_bf73c = Some (Branch BC_LTU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf740 : bv 32 := 0x00000023.
Lemma F_bf740 : fetch_word Ubsan.M.loaded_segments (0xbf8f8 : word) = Some W_bf740.
Proof. vm_refl. Qed.
Lemma D_bf740 : decode_any W_bf740 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf744 : bv 32 := 0x0077c683.
Lemma F_bf744 : fetch_word Ubsan.M.loaded_segments (0xbf8fc : word) = Some W_bf744.
Proof. vm_refl. Qed.
Lemma D_bf744 : decode_any W_bf744 = Some (Load SZ1 false 13 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf748 : bv 32 := 0x00068463.
Lemma F_bf748 : fetch_word Ubsan.M.loaded_segments (0xbf900 : word) = Some W_bf748.
Proof. vm_refl. Qed.
Lemma D_bf748 : decode_any W_bf748 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf74c : bv 32 := 0x00000023.
Lemma F_bf74c : fetch_word Ubsan.M.loaded_segments (0xbf904 : word) = Some W_bf74c.
Proof. vm_refl. Qed.
Lemma D_bf74c : decode_any W_bf74c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf750 : bv 32 := 0x409606b3.
Lemma F_bf750 : fetch_word Ubsan.M.loaded_segments (0xbf908 : word) = Some W_bf750.
Proof. vm_refl. Qed.
Lemma D_bf750 : decode_any W_bf750 = Some (Op ALU_SUB 13 12 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf754 : bv 32 := 0x00e6f463.
Lemma F_bf754 : fetch_word Ubsan.M.loaded_segments (0xbf90c : word) = Some W_bf754.
Proof. vm_refl. Qed.
Lemma D_bf754 : decode_any W_bf754 = Some (Branch BC_GEU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf758 : bv 32 := 0x00000023.
Lemma F_bf758 : fetch_word Ubsan.M.loaded_segments (0xbf910 : word) = Some W_bf758.
Proof. vm_refl. Qed.
Lemma D_bf758 : decode_any W_bf758 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf75c : bv 32 := 0x40e606b3.
Lemma F_bf75c : fetch_word Ubsan.M.loaded_segments (0xbf914 : word) = Some W_bf75c.
Proof. vm_refl. Qed.
Lemma D_bf75c : decode_any W_bf75c = Some (Op ALU_SUB 13 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf760 : bv 32 := 0x0006c683.
Lemma F_bf760 : fetch_word Ubsan.M.loaded_segments (0xbf918 : word) = Some W_bf760.
Proof. vm_refl. Qed.
Lemma D_bf760 : decode_any W_bf760 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf764 : bv 32 := 0x00068463.
Lemma F_bf764 : fetch_word Ubsan.M.loaded_segments (0xbf91c : word) = Some W_bf764.
Proof. vm_refl. Qed.
Lemma D_bf764 : decode_any W_bf764 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf768 : bv 32 := 0x00000023.
Lemma F_bf768 : fetch_word Ubsan.M.loaded_segments (0xbf920 : word) = Some W_bf768.
Proof. vm_refl. Qed.
Lemma D_bf768 : decode_any W_bf768 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf76c : bv 32 := 0x00064603.
Lemma F_bf76c : fetch_word Ubsan.M.loaded_segments (0xbf924 : word) = Some W_bf76c.
Proof. vm_refl. Qed.
Lemma D_bf76c : decode_any W_bf76c = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf770 : bv 32 := 0x00060463.
Lemma F_bf770 : fetch_word Ubsan.M.loaded_segments (0xbf928 : word) = Some W_bf770.
Proof. vm_refl. Qed.
Lemma D_bf770 : decode_any W_bf770 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf774 : bv 32 := 0x00000023.
Lemma F_bf774 : fetch_word Ubsan.M.loaded_segments (0xbf92c : word) = Some W_bf774.
Proof. vm_refl. Qed.
Lemma D_bf774 : decode_any W_bf774 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf778 : bv 32 := 0x00100613.
Lemma F_bf778 : fetch_word Ubsan.M.loaded_segments (0xbf930 : word) = Some W_bf778.
Proof. vm_refl. Qed.
Lemma D_bf778 : decode_any W_bf778 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.
