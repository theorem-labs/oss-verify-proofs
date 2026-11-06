(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5e870 : bv 32 := 0x0e060a63.
Lemma F_5e870 : fetch_word Plain.M.loaded_segments (0x5e870 : word) = Some W_5e870.
Proof. vm_refl. Qed.
Lemma D_5e870 : decode_any W_5e870 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e874 : bv 32 := 0x00b50023.
Lemma F_5e874 : fetch_word Plain.M.loaded_segments (0x5e874 : word) = Some W_5e874.
Proof. vm_refl. Qed.
Lemma D_5e874 : decode_any W_5e874 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e878 : bv 32 := 0x00c506b3.
Lemma F_5e878 : fetch_word Plain.M.loaded_segments (0x5e878 : word) = Some W_5e878.
Proof. vm_refl. Qed.
Lemma D_5e878 : decode_any W_5e878 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e87c : bv 32 := 0x00300713.
Lemma F_5e87c : fetch_word Plain.M.loaded_segments (0x5e87c : word) = Some W_5e87c.
Proof. vm_refl. Qed.
Lemma D_5e87c : decode_any W_5e87c = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e880 : bv 32 := 0xfeb68fa3.
Lemma F_5e880 : fetch_word Plain.M.loaded_segments (0x5e880 : word) = Some W_5e880.
Proof. vm_refl. Qed.
Lemma D_5e880 : decode_any W_5e880 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e884 : bv 32 := 0x0ee66063.
Lemma F_5e884 : fetch_word Plain.M.loaded_segments (0x5e884 : word) = Some W_5e884.
Proof. vm_refl. Qed.
Lemma D_5e884 : decode_any W_5e884 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e888 : bv 32 := 0x00b500a3.
Lemma F_5e888 : fetch_word Plain.M.loaded_segments (0x5e888 : word) = Some W_5e888.
Proof. vm_refl. Qed.
Lemma D_5e888 : decode_any W_5e888 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e88c : bv 32 := 0x00b50123.
Lemma F_5e88c : fetch_word Plain.M.loaded_segments (0x5e88c : word) = Some W_5e88c.
Proof. vm_refl. Qed.
Lemma D_5e88c : decode_any W_5e88c = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e890 : bv 32 := 0x00700713.
Lemma F_5e890 : fetch_word Plain.M.loaded_segments (0x5e890 : word) = Some W_5e890.
Proof. vm_refl. Qed.
Lemma D_5e890 : decode_any W_5e890 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e894 : bv 32 := 0xfeb68ea3.
Lemma F_5e894 : fetch_word Plain.M.loaded_segments (0x5e894 : word) = Some W_5e894.
Proof. vm_refl. Qed.
Lemma D_5e894 : decode_any W_5e894 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e898 : bv 32 := 0xfeb68f23.
Lemma F_5e898 : fetch_word Plain.M.loaded_segments (0x5e898 : word) = Some W_5e898.
Proof. vm_refl. Qed.
Lemma D_5e898 : decode_any W_5e898 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e89c : bv 32 := 0x0ce66463.
Lemma F_5e89c : fetch_word Plain.M.loaded_segments (0x5e89c : word) = Some W_5e89c.
Proof. vm_refl. Qed.
Lemma D_5e89c : decode_any W_5e89c = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8a0 : bv 32 := 0x00b501a3.
Lemma F_5e8a0 : fetch_word Plain.M.loaded_segments (0x5e8a0 : word) = Some W_5e8a0.
Proof. vm_refl. Qed.
Lemma D_5e8a0 : decode_any W_5e8a0 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8a4 : bv 32 := 0x00900793.
Lemma F_5e8a4 : fetch_word Plain.M.loaded_segments (0x5e8a4 : word) = Some W_5e8a4.
Proof. vm_refl. Qed.
Lemma D_5e8a4 : decode_any W_5e8a4 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8a8 : bv 32 := 0xfeb68e23.
Lemma F_5e8a8 : fetch_word Plain.M.loaded_segments (0x5e8a8 : word) = Some W_5e8a8.
Proof. vm_refl. Qed.
Lemma D_5e8a8 : decode_any W_5e8a8 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8ac : bv 32 := 0x0af66c63.
Lemma F_5e8ac : fetch_word Plain.M.loaded_segments (0x5e8ac : word) = Some W_5e8ac.
Proof. vm_refl. Qed.
Lemma D_5e8ac : decode_any W_5e8ac = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8b0 : bv 32 := 0x40a006bb.
Lemma F_5e8b0 : fetch_word Plain.M.loaded_segments (0x5e8b0 : word) = Some W_5e8b0.
Proof. vm_refl. Qed.
Lemma D_5e8b0 : decode_any W_5e8b0 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8b4 : bv 32 := 0x03859813.
Lemma F_5e8b4 : fetch_word Plain.M.loaded_segments (0x5e8b4 : word) = Some W_5e8b4.
Proof. vm_refl. Qed.
Lemma D_5e8b4 : decode_any W_5e8b4 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8b8 : bv 32 := 0x101015b7.
Lemma F_5e8b8 : fetch_word Plain.M.loaded_segments (0x5e8b8 : word) = Some W_5e8b8.
Proof. vm_refl. Qed.
Lemma D_5e8b8 : decode_any W_5e8b8 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8bc : bv 32 := 0x0036f693.
Lemma F_5e8bc : fetch_word Plain.M.loaded_segments (0x5e8bc : word) = Some W_5e8bc.
Proof. vm_refl. Qed.
Lemma D_5e8bc : decode_any W_5e8bc = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8c0 : bv 32 := 0x00459713.
Lemma F_5e8c0 : fetch_word Plain.M.loaded_segments (0x5e8c0 : word) = Some W_5e8c0.
Proof. vm_refl. Qed.
Lemma D_5e8c0 : decode_any W_5e8c0 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8c4 : bv 32 := 0x40d60633.
Lemma F_5e8c4 : fetch_word Plain.M.loaded_segments (0x5e8c4 : word) = Some W_5e8c4.
Proof. vm_refl. Qed.
Lemma D_5e8c4 : decode_any W_5e8c4 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8c8 : bv 32 := 0x00d505b3.
Lemma F_5e8c8 : fetch_word Plain.M.loaded_segments (0x5e8c8 : word) = Some W_5e8c8.
Proof. vm_refl. Qed.
Lemma D_5e8c8 : decode_any W_5e8c8 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8cc : bv 32 := 0x10070693.
Lemma F_5e8cc : fetch_word Plain.M.loaded_segments (0x5e8cc : word) = Some W_5e8cc.
Proof. vm_refl. Qed.
Lemma D_5e8cc : decode_any W_5e8cc = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8d0 : bv 32 := 0xffc67713.
Lemma F_5e8d0 : fetch_word Plain.M.loaded_segments (0x5e8d0 : word) = Some W_5e8d0.
Proof. vm_refl. Qed.
Lemma D_5e8d0 : decode_any W_5e8d0 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8d4 : bv 32 := 0x02d83633.
Lemma F_5e8d4 : fetch_word Plain.M.loaded_segments (0x5e8d4 : word) = Some W_5e8d4.
Proof. vm_refl. Qed.
Lemma D_5e8d4 : decode_any W_5e8d4 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8d8 : bv 32 := 0x00c5a023.
Lemma F_5e8d8 : fetch_word Plain.M.loaded_segments (0x5e8d8 : word) = Some W_5e8d8.
Proof. vm_refl. Qed.
Lemma D_5e8d8 : decode_any W_5e8d8 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8dc : bv 32 := 0x00e586b3.
Lemma F_5e8dc : fetch_word Plain.M.loaded_segments (0x5e8dc : word) = Some W_5e8dc.
Proof. vm_refl. Qed.
Lemma D_5e8dc : decode_any W_5e8dc = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8e0 : bv 32 := 0xfec6ae23.
Lemma F_5e8e0 : fetch_word Plain.M.loaded_segments (0x5e8e0 : word) = Some W_5e8e0.
Proof. vm_refl. Qed.
Lemma D_5e8e0 : decode_any W_5e8e0 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8e4 : bv 32 := 0x08f76063.
Lemma F_5e8e4 : fetch_word Plain.M.loaded_segments (0x5e8e4 : word) = Some W_5e8e4.
Proof. vm_refl. Qed.
Lemma D_5e8e4 : decode_any W_5e8e4 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8e8 : bv 32 := 0x00c5a223.
Lemma F_5e8e8 : fetch_word Plain.M.loaded_segments (0x5e8e8 : word) = Some W_5e8e8.
Proof. vm_refl. Qed.
Lemma D_5e8e8 : decode_any W_5e8e8 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8ec : bv 32 := 0x00c5a423.
Lemma F_5e8ec : fetch_word Plain.M.loaded_segments (0x5e8ec : word) = Some W_5e8ec.
Proof. vm_refl. Qed.
Lemma D_5e8ec : decode_any W_5e8ec = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8f0 : bv 32 := 0x01900793.
Lemma F_5e8f0 : fetch_word Plain.M.loaded_segments (0x5e8f0 : word) = Some W_5e8f0.
Proof. vm_refl. Qed.
Lemma D_5e8f0 : decode_any W_5e8f0 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8f4 : bv 32 := 0xfec6aa23.
Lemma F_5e8f4 : fetch_word Plain.M.loaded_segments (0x5e8f4 : word) = Some W_5e8f4.
Proof. vm_refl. Qed.
Lemma D_5e8f4 : decode_any W_5e8f4 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8f8 : bv 32 := 0xfec6ac23.
Lemma F_5e8f8 : fetch_word Plain.M.loaded_segments (0x5e8f8 : word) = Some W_5e8f8.
Proof. vm_refl. Qed.
Lemma D_5e8f8 : decode_any W_5e8f8 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e8fc : bv 32 := 0x06f76463.
Lemma F_5e8fc : fetch_word Plain.M.loaded_segments (0x5e8fc : word) = Some W_5e8fc.
Proof. vm_refl. Qed.
Lemma D_5e8fc : decode_any W_5e8fc = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e900 : bv 32 := 0x00c5a623.
Lemma F_5e900 : fetch_word Plain.M.loaded_segments (0x5e900 : word) = Some W_5e900.
Proof. vm_refl. Qed.
Lemma D_5e900 : decode_any W_5e900 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e904 : bv 32 := 0x00c5a823.
Lemma F_5e904 : fetch_word Plain.M.loaded_segments (0x5e904 : word) = Some W_5e904.
Proof. vm_refl. Qed.
Lemma D_5e904 : decode_any W_5e904 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e908 : bv 32 := 0x00c5aa23.
Lemma F_5e908 : fetch_word Plain.M.loaded_segments (0x5e908 : word) = Some W_5e908.
Proof. vm_refl. Qed.
Lemma D_5e908 : decode_any W_5e908 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e90c : bv 32 := 0x00c5ac23.
Lemma F_5e90c : fetch_word Plain.M.loaded_segments (0x5e90c : word) = Some W_5e90c.
Proof. vm_refl. Qed.
Lemma D_5e90c : decode_any W_5e90c = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e910 : bv 32 := 0x0045f793.
Lemma F_5e910 : fetch_word Plain.M.loaded_segments (0x5e910 : word) = Some W_5e910.
Proof. vm_refl. Qed.
Lemma D_5e910 : decode_any W_5e910 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e914 : bv 32 := 0x02000813.
Lemma F_5e914 : fetch_word Plain.M.loaded_segments (0x5e914 : word) = Some W_5e914.
Proof. vm_refl. Qed.
Lemma D_5e914 : decode_any W_5e914 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e918 : bv 32 := 0x01878793.
Lemma F_5e918 : fetch_word Plain.M.loaded_segments (0x5e918 : word) = Some W_5e918.
Proof. vm_refl. Qed.
Lemma D_5e918 : decode_any W_5e918 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e91c : bv 32 := 0x40f70733.
Lemma F_5e91c : fetch_word Plain.M.loaded_segments (0x5e91c : word) = Some W_5e91c.
Proof. vm_refl. Qed.
Lemma D_5e91c : decode_any W_5e91c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e920 : bv 32 := 0xfec6a223.
Lemma F_5e920 : fetch_word Plain.M.loaded_segments (0x5e920 : word) = Some W_5e920.
Proof. vm_refl. Qed.
Lemma D_5e920 : decode_any W_5e920 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e924 : bv 32 := 0xfec6a423.
Lemma F_5e924 : fetch_word Plain.M.loaded_segments (0x5e924 : word) = Some W_5e924.
Proof. vm_refl. Qed.
Lemma D_5e924 : decode_any W_5e924 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e928 : bv 32 := 0xfec6a623.
Lemma F_5e928 : fetch_word Plain.M.loaded_segments (0x5e928 : word) = Some W_5e928.
Proof. vm_refl. Qed.
Lemma D_5e928 : decode_any W_5e928 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e92c : bv 32 := 0xfec6a823.
Lemma F_5e92c : fetch_word Plain.M.loaded_segments (0x5e92c : word) = Some W_5e92c.
Proof. vm_refl. Qed.
Lemma D_5e92c : decode_any W_5e92c = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e930 : bv 32 := 0x03076a63.
Lemma F_5e930 : fetch_word Plain.M.loaded_segments (0x5e930 : word) = Some W_5e930.
Proof. vm_refl. Qed.
Lemma D_5e930 : decode_any W_5e930 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e934 : bv 32 := 0x02061613.
Lemma F_5e934 : fetch_word Plain.M.loaded_segments (0x5e934 : word) = Some W_5e934.
Proof. vm_refl. Qed.
Lemma D_5e934 : decode_any W_5e934 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e938 : bv 32 := 0x00f585b3.
Lemma F_5e938 : fetch_word Plain.M.loaded_segments (0x5e938 : word) = Some W_5e938.
Proof. vm_refl. Qed.
Lemma D_5e938 : decode_any W_5e938 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e93c : bv 32 := 0x02065693.
Lemma F_5e93c : fetch_word Plain.M.loaded_segments (0x5e93c : word) = Some W_5e93c.
Proof. vm_refl. Qed.
Lemma D_5e93c : decode_any W_5e93c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e940 : bv 32 := 0x00d66633.
Lemma F_5e940 : fetch_word Plain.M.loaded_segments (0x5e940 : word) = Some W_5e940.
Proof. vm_refl. Qed.
Lemma D_5e940 : decode_any W_5e940 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e944 : bv 32 := 0x01f00693.
Lemma F_5e944 : fetch_word Plain.M.loaded_segments (0x5e944 : word) = Some W_5e944.
Proof. vm_refl. Qed.
Lemma D_5e944 : decode_any W_5e944 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e948 : bv 32 := 0x00c5b023.
Lemma F_5e948 : fetch_word Plain.M.loaded_segments (0x5e948 : word) = Some W_5e948.
Proof. vm_refl. Qed.
Lemma D_5e948 : decode_any W_5e948 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e94c : bv 32 := 0x00c5b423.
Lemma F_5e94c : fetch_word Plain.M.loaded_segments (0x5e94c : word) = Some W_5e94c.
Proof. vm_refl. Qed.
Lemma D_5e94c : decode_any W_5e94c = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e950 : bv 32 := 0x00c5b823.
Lemma F_5e950 : fetch_word Plain.M.loaded_segments (0x5e950 : word) = Some W_5e950.
Proof. vm_refl. Qed.
Lemma D_5e950 : decode_any W_5e950 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e954 : bv 32 := 0x00c5bc23.
Lemma F_5e954 : fetch_word Plain.M.loaded_segments (0x5e954 : word) = Some W_5e954.
Proof. vm_refl. Qed.
Lemma D_5e954 : decode_any W_5e954 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e958 : bv 32 := 0xfe070713.
Lemma F_5e958 : fetch_word Plain.M.loaded_segments (0x5e958 : word) = Some W_5e958.
Proof. vm_refl. Qed.
Lemma D_5e958 : decode_any W_5e958 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e95c : bv 32 := 0x02058593.
Lemma F_5e95c : fetch_word Plain.M.loaded_segments (0x5e95c : word) = Some W_5e95c.
Proof. vm_refl. Qed.
Lemma D_5e95c : decode_any W_5e95c = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e960 : bv 32 := 0xfee6e4e3.
Lemma F_5e960 : fetch_word Plain.M.loaded_segments (0x5e960 : word) = Some W_5e960.
Proof. vm_refl. Qed.
Lemma D_5e960 : decode_any W_5e960 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e964 : bv 32 := 0x00008067.
Lemma F_5e964 : fetch_word Plain.M.loaded_segments (0x5e964 : word) = Some W_5e964.
Proof. vm_refl. Qed.
Lemma D_5e964 : decode_any W_5e964 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
