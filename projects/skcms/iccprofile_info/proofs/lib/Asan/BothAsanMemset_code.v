(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_99050 : bv 32 := 0x0e060a63.
Lemma F_99050 : fetch_word AsanUbsan.M.loaded_segments (0x99050 : word) = Some W_99050.
Proof. vm_refl. Qed.
Lemma D_99050 : decode_any W_99050 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99054 : bv 32 := 0x00b50023.
Lemma F_99054 : fetch_word AsanUbsan.M.loaded_segments (0x99054 : word) = Some W_99054.
Proof. vm_refl. Qed.
Lemma D_99054 : decode_any W_99054 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99058 : bv 32 := 0x00c506b3.
Lemma F_99058 : fetch_word AsanUbsan.M.loaded_segments (0x99058 : word) = Some W_99058.
Proof. vm_refl. Qed.
Lemma D_99058 : decode_any W_99058 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9905c : bv 32 := 0x00300713.
Lemma F_9905c : fetch_word AsanUbsan.M.loaded_segments (0x9905c : word) = Some W_9905c.
Proof. vm_refl. Qed.
Lemma D_9905c : decode_any W_9905c = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99060 : bv 32 := 0xfeb68fa3.
Lemma F_99060 : fetch_word AsanUbsan.M.loaded_segments (0x99060 : word) = Some W_99060.
Proof. vm_refl. Qed.
Lemma D_99060 : decode_any W_99060 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99064 : bv 32 := 0x0ee66063.
Lemma F_99064 : fetch_word AsanUbsan.M.loaded_segments (0x99064 : word) = Some W_99064.
Proof. vm_refl. Qed.
Lemma D_99064 : decode_any W_99064 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99068 : bv 32 := 0x00b500a3.
Lemma F_99068 : fetch_word AsanUbsan.M.loaded_segments (0x99068 : word) = Some W_99068.
Proof. vm_refl. Qed.
Lemma D_99068 : decode_any W_99068 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9906c : bv 32 := 0x00b50123.
Lemma F_9906c : fetch_word AsanUbsan.M.loaded_segments (0x9906c : word) = Some W_9906c.
Proof. vm_refl. Qed.
Lemma D_9906c : decode_any W_9906c = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99070 : bv 32 := 0x00700713.
Lemma F_99070 : fetch_word AsanUbsan.M.loaded_segments (0x99070 : word) = Some W_99070.
Proof. vm_refl. Qed.
Lemma D_99070 : decode_any W_99070 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99074 : bv 32 := 0xfeb68ea3.
Lemma F_99074 : fetch_word AsanUbsan.M.loaded_segments (0x99074 : word) = Some W_99074.
Proof. vm_refl. Qed.
Lemma D_99074 : decode_any W_99074 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99078 : bv 32 := 0xfeb68f23.
Lemma F_99078 : fetch_word AsanUbsan.M.loaded_segments (0x99078 : word) = Some W_99078.
Proof. vm_refl. Qed.
Lemma D_99078 : decode_any W_99078 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9907c : bv 32 := 0x0ce66463.
Lemma F_9907c : fetch_word AsanUbsan.M.loaded_segments (0x9907c : word) = Some W_9907c.
Proof. vm_refl. Qed.
Lemma D_9907c : decode_any W_9907c = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99080 : bv 32 := 0x00b501a3.
Lemma F_99080 : fetch_word AsanUbsan.M.loaded_segments (0x99080 : word) = Some W_99080.
Proof. vm_refl. Qed.
Lemma D_99080 : decode_any W_99080 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99084 : bv 32 := 0x00900793.
Lemma F_99084 : fetch_word AsanUbsan.M.loaded_segments (0x99084 : word) = Some W_99084.
Proof. vm_refl. Qed.
Lemma D_99084 : decode_any W_99084 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99088 : bv 32 := 0xfeb68e23.
Lemma F_99088 : fetch_word AsanUbsan.M.loaded_segments (0x99088 : word) = Some W_99088.
Proof. vm_refl. Qed.
Lemma D_99088 : decode_any W_99088 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9908c : bv 32 := 0x0af66c63.
Lemma F_9908c : fetch_word AsanUbsan.M.loaded_segments (0x9908c : word) = Some W_9908c.
Proof. vm_refl. Qed.
Lemma D_9908c : decode_any W_9908c = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99090 : bv 32 := 0x40a006bb.
Lemma F_99090 : fetch_word AsanUbsan.M.loaded_segments (0x99090 : word) = Some W_99090.
Proof. vm_refl. Qed.
Lemma D_99090 : decode_any W_99090 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99094 : bv 32 := 0x03859813.
Lemma F_99094 : fetch_word AsanUbsan.M.loaded_segments (0x99094 : word) = Some W_99094.
Proof. vm_refl. Qed.
Lemma D_99094 : decode_any W_99094 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99098 : bv 32 := 0x101015b7.
Lemma F_99098 : fetch_word AsanUbsan.M.loaded_segments (0x99098 : word) = Some W_99098.
Proof. vm_refl. Qed.
Lemma D_99098 : decode_any W_99098 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9909c : bv 32 := 0x0036f693.
Lemma F_9909c : fetch_word AsanUbsan.M.loaded_segments (0x9909c : word) = Some W_9909c.
Proof. vm_refl. Qed.
Lemma D_9909c : decode_any W_9909c = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990a0 : bv 32 := 0x00459713.
Lemma F_990a0 : fetch_word AsanUbsan.M.loaded_segments (0x990a0 : word) = Some W_990a0.
Proof. vm_refl. Qed.
Lemma D_990a0 : decode_any W_990a0 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990a4 : bv 32 := 0x40d60633.
Lemma F_990a4 : fetch_word AsanUbsan.M.loaded_segments (0x990a4 : word) = Some W_990a4.
Proof. vm_refl. Qed.
Lemma D_990a4 : decode_any W_990a4 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990a8 : bv 32 := 0x00d505b3.
Lemma F_990a8 : fetch_word AsanUbsan.M.loaded_segments (0x990a8 : word) = Some W_990a8.
Proof. vm_refl. Qed.
Lemma D_990a8 : decode_any W_990a8 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990ac : bv 32 := 0x10070693.
Lemma F_990ac : fetch_word AsanUbsan.M.loaded_segments (0x990ac : word) = Some W_990ac.
Proof. vm_refl. Qed.
Lemma D_990ac : decode_any W_990ac = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990b0 : bv 32 := 0xffc67713.
Lemma F_990b0 : fetch_word AsanUbsan.M.loaded_segments (0x990b0 : word) = Some W_990b0.
Proof. vm_refl. Qed.
Lemma D_990b0 : decode_any W_990b0 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990b4 : bv 32 := 0x02d83633.
Lemma F_990b4 : fetch_word AsanUbsan.M.loaded_segments (0x990b4 : word) = Some W_990b4.
Proof. vm_refl. Qed.
Lemma D_990b4 : decode_any W_990b4 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990b8 : bv 32 := 0x00c5a023.
Lemma F_990b8 : fetch_word AsanUbsan.M.loaded_segments (0x990b8 : word) = Some W_990b8.
Proof. vm_refl. Qed.
Lemma D_990b8 : decode_any W_990b8 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990bc : bv 32 := 0x00e586b3.
Lemma F_990bc : fetch_word AsanUbsan.M.loaded_segments (0x990bc : word) = Some W_990bc.
Proof. vm_refl. Qed.
Lemma D_990bc : decode_any W_990bc = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990c0 : bv 32 := 0xfec6ae23.
Lemma F_990c0 : fetch_word AsanUbsan.M.loaded_segments (0x990c0 : word) = Some W_990c0.
Proof. vm_refl. Qed.
Lemma D_990c0 : decode_any W_990c0 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990c4 : bv 32 := 0x08f76063.
Lemma F_990c4 : fetch_word AsanUbsan.M.loaded_segments (0x990c4 : word) = Some W_990c4.
Proof. vm_refl. Qed.
Lemma D_990c4 : decode_any W_990c4 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990c8 : bv 32 := 0x00c5a223.
Lemma F_990c8 : fetch_word AsanUbsan.M.loaded_segments (0x990c8 : word) = Some W_990c8.
Proof. vm_refl. Qed.
Lemma D_990c8 : decode_any W_990c8 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990cc : bv 32 := 0x00c5a423.
Lemma F_990cc : fetch_word AsanUbsan.M.loaded_segments (0x990cc : word) = Some W_990cc.
Proof. vm_refl. Qed.
Lemma D_990cc : decode_any W_990cc = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990d0 : bv 32 := 0x01900793.
Lemma F_990d0 : fetch_word AsanUbsan.M.loaded_segments (0x990d0 : word) = Some W_990d0.
Proof. vm_refl. Qed.
Lemma D_990d0 : decode_any W_990d0 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990d4 : bv 32 := 0xfec6aa23.
Lemma F_990d4 : fetch_word AsanUbsan.M.loaded_segments (0x990d4 : word) = Some W_990d4.
Proof. vm_refl. Qed.
Lemma D_990d4 : decode_any W_990d4 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990d8 : bv 32 := 0xfec6ac23.
Lemma F_990d8 : fetch_word AsanUbsan.M.loaded_segments (0x990d8 : word) = Some W_990d8.
Proof. vm_refl. Qed.
Lemma D_990d8 : decode_any W_990d8 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990dc : bv 32 := 0x06f76463.
Lemma F_990dc : fetch_word AsanUbsan.M.loaded_segments (0x990dc : word) = Some W_990dc.
Proof. vm_refl. Qed.
Lemma D_990dc : decode_any W_990dc = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990e0 : bv 32 := 0x00c5a623.
Lemma F_990e0 : fetch_word AsanUbsan.M.loaded_segments (0x990e0 : word) = Some W_990e0.
Proof. vm_refl. Qed.
Lemma D_990e0 : decode_any W_990e0 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990e4 : bv 32 := 0x00c5a823.
Lemma F_990e4 : fetch_word AsanUbsan.M.loaded_segments (0x990e4 : word) = Some W_990e4.
Proof. vm_refl. Qed.
Lemma D_990e4 : decode_any W_990e4 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990e8 : bv 32 := 0x00c5aa23.
Lemma F_990e8 : fetch_word AsanUbsan.M.loaded_segments (0x990e8 : word) = Some W_990e8.
Proof. vm_refl. Qed.
Lemma D_990e8 : decode_any W_990e8 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990ec : bv 32 := 0x00c5ac23.
Lemma F_990ec : fetch_word AsanUbsan.M.loaded_segments (0x990ec : word) = Some W_990ec.
Proof. vm_refl. Qed.
Lemma D_990ec : decode_any W_990ec = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990f0 : bv 32 := 0x0045f793.
Lemma F_990f0 : fetch_word AsanUbsan.M.loaded_segments (0x990f0 : word) = Some W_990f0.
Proof. vm_refl. Qed.
Lemma D_990f0 : decode_any W_990f0 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990f4 : bv 32 := 0x02000813.
Lemma F_990f4 : fetch_word AsanUbsan.M.loaded_segments (0x990f4 : word) = Some W_990f4.
Proof. vm_refl. Qed.
Lemma D_990f4 : decode_any W_990f4 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990f8 : bv 32 := 0x01878793.
Lemma F_990f8 : fetch_word AsanUbsan.M.loaded_segments (0x990f8 : word) = Some W_990f8.
Proof. vm_refl. Qed.
Lemma D_990f8 : decode_any W_990f8 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_990fc : bv 32 := 0x40f70733.
Lemma F_990fc : fetch_word AsanUbsan.M.loaded_segments (0x990fc : word) = Some W_990fc.
Proof. vm_refl. Qed.
Lemma D_990fc : decode_any W_990fc = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99100 : bv 32 := 0xfec6a223.
Lemma F_99100 : fetch_word AsanUbsan.M.loaded_segments (0x99100 : word) = Some W_99100.
Proof. vm_refl. Qed.
Lemma D_99100 : decode_any W_99100 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99104 : bv 32 := 0xfec6a423.
Lemma F_99104 : fetch_word AsanUbsan.M.loaded_segments (0x99104 : word) = Some W_99104.
Proof. vm_refl. Qed.
Lemma D_99104 : decode_any W_99104 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99108 : bv 32 := 0xfec6a623.
Lemma F_99108 : fetch_word AsanUbsan.M.loaded_segments (0x99108 : word) = Some W_99108.
Proof. vm_refl. Qed.
Lemma D_99108 : decode_any W_99108 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9910c : bv 32 := 0xfec6a823.
Lemma F_9910c : fetch_word AsanUbsan.M.loaded_segments (0x9910c : word) = Some W_9910c.
Proof. vm_refl. Qed.
Lemma D_9910c : decode_any W_9910c = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99110 : bv 32 := 0x03076a63.
Lemma F_99110 : fetch_word AsanUbsan.M.loaded_segments (0x99110 : word) = Some W_99110.
Proof. vm_refl. Qed.
Lemma D_99110 : decode_any W_99110 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99114 : bv 32 := 0x02061613.
Lemma F_99114 : fetch_word AsanUbsan.M.loaded_segments (0x99114 : word) = Some W_99114.
Proof. vm_refl. Qed.
Lemma D_99114 : decode_any W_99114 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99118 : bv 32 := 0x00f585b3.
Lemma F_99118 : fetch_word AsanUbsan.M.loaded_segments (0x99118 : word) = Some W_99118.
Proof. vm_refl. Qed.
Lemma D_99118 : decode_any W_99118 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9911c : bv 32 := 0x02065693.
Lemma F_9911c : fetch_word AsanUbsan.M.loaded_segments (0x9911c : word) = Some W_9911c.
Proof. vm_refl. Qed.
Lemma D_9911c : decode_any W_9911c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99120 : bv 32 := 0x00d66633.
Lemma F_99120 : fetch_word AsanUbsan.M.loaded_segments (0x99120 : word) = Some W_99120.
Proof. vm_refl. Qed.
Lemma D_99120 : decode_any W_99120 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99124 : bv 32 := 0x01f00693.
Lemma F_99124 : fetch_word AsanUbsan.M.loaded_segments (0x99124 : word) = Some W_99124.
Proof. vm_refl. Qed.
Lemma D_99124 : decode_any W_99124 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99128 : bv 32 := 0x00c5b023.
Lemma F_99128 : fetch_word AsanUbsan.M.loaded_segments (0x99128 : word) = Some W_99128.
Proof. vm_refl. Qed.
Lemma D_99128 : decode_any W_99128 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9912c : bv 32 := 0x00c5b423.
Lemma F_9912c : fetch_word AsanUbsan.M.loaded_segments (0x9912c : word) = Some W_9912c.
Proof. vm_refl. Qed.
Lemma D_9912c : decode_any W_9912c = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99130 : bv 32 := 0x00c5b823.
Lemma F_99130 : fetch_word AsanUbsan.M.loaded_segments (0x99130 : word) = Some W_99130.
Proof. vm_refl. Qed.
Lemma D_99130 : decode_any W_99130 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99134 : bv 32 := 0x00c5bc23.
Lemma F_99134 : fetch_word AsanUbsan.M.loaded_segments (0x99134 : word) = Some W_99134.
Proof. vm_refl. Qed.
Lemma D_99134 : decode_any W_99134 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99138 : bv 32 := 0xfe070713.
Lemma F_99138 : fetch_word AsanUbsan.M.loaded_segments (0x99138 : word) = Some W_99138.
Proof. vm_refl. Qed.
Lemma D_99138 : decode_any W_99138 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9913c : bv 32 := 0x02058593.
Lemma F_9913c : fetch_word AsanUbsan.M.loaded_segments (0x9913c : word) = Some W_9913c.
Proof. vm_refl. Qed.
Lemma D_9913c : decode_any W_9913c = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99140 : bv 32 := 0xfee6e4e3.
Lemma F_99140 : fetch_word AsanUbsan.M.loaded_segments (0x99140 : word) = Some W_99140.
Proof. vm_refl. Qed.
Lemma D_99140 : decode_any W_99140 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99144 : bv 32 := 0x00008067.
Lemma F_99144 : fetch_word AsanUbsan.M.loaded_segments (0x99144 : word) = Some W_99144.
Proof. vm_refl. Qed.
Lemma D_99144 : decode_any W_99144 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0x99050%Z.
Definition Fo_000 := F_99050.
Definition Do_000 := D_99050.
Definition Fo_004 := F_99054.
Definition Do_004 := D_99054.
Definition Fo_008 := F_99058.
Definition Do_008 := D_99058.
Definition Fo_00c := F_9905c.
Definition Do_00c := D_9905c.
Definition Fo_010 := F_99060.
Definition Do_010 := D_99060.
Definition Fo_014 := F_99064.
Definition Do_014 := D_99064.
Definition Fo_018 := F_99068.
Definition Do_018 := D_99068.
Definition Fo_01c := F_9906c.
Definition Do_01c := D_9906c.
Definition Fo_020 := F_99070.
Definition Do_020 := D_99070.
Definition Fo_024 := F_99074.
Definition Do_024 := D_99074.
Definition Fo_028 := F_99078.
Definition Do_028 := D_99078.
Definition Fo_02c := F_9907c.
Definition Do_02c := D_9907c.
Definition Fo_030 := F_99080.
Definition Do_030 := D_99080.
Definition Fo_034 := F_99084.
Definition Do_034 := D_99084.
Definition Fo_038 := F_99088.
Definition Do_038 := D_99088.
Definition Fo_03c := F_9908c.
Definition Do_03c := D_9908c.
Definition Fo_040 := F_99090.
Definition Do_040 := D_99090.
Definition Fo_044 := F_99094.
Definition Do_044 := D_99094.
Definition Fo_048 := F_99098.
Definition Do_048 := D_99098.
Definition Fo_04c := F_9909c.
Definition Do_04c := D_9909c.
Definition Fo_050 := F_990a0.
Definition Do_050 := D_990a0.
Definition Fo_054 := F_990a4.
Definition Do_054 := D_990a4.
Definition Fo_058 := F_990a8.
Definition Do_058 := D_990a8.
Definition Fo_05c := F_990ac.
Definition Do_05c := D_990ac.
Definition Fo_060 := F_990b0.
Definition Do_060 := D_990b0.
Definition Fo_064 := F_990b4.
Definition Do_064 := D_990b4.
Definition Fo_068 := F_990b8.
Definition Do_068 := D_990b8.
Definition Fo_06c := F_990bc.
Definition Do_06c := D_990bc.
Definition Fo_070 := F_990c0.
Definition Do_070 := D_990c0.
Definition Fo_074 := F_990c4.
Definition Do_074 := D_990c4.
Definition Fo_078 := F_990c8.
Definition Do_078 := D_990c8.
Definition Fo_07c := F_990cc.
Definition Do_07c := D_990cc.
Definition Fo_080 := F_990d0.
Definition Do_080 := D_990d0.
Definition Fo_084 := F_990d4.
Definition Do_084 := D_990d4.
Definition Fo_088 := F_990d8.
Definition Do_088 := D_990d8.
Definition Fo_08c := F_990dc.
Definition Do_08c := D_990dc.
Definition Fo_090 := F_990e0.
Definition Do_090 := D_990e0.
Definition Fo_094 := F_990e4.
Definition Do_094 := D_990e4.
Definition Fo_098 := F_990e8.
Definition Do_098 := D_990e8.
Definition Fo_09c := F_990ec.
Definition Do_09c := D_990ec.
Definition Fo_0a0 := F_990f0.
Definition Do_0a0 := D_990f0.
Definition Fo_0a4 := F_990f4.
Definition Do_0a4 := D_990f4.
Definition Fo_0a8 := F_990f8.
Definition Do_0a8 := D_990f8.
Definition Fo_0ac := F_990fc.
Definition Do_0ac := D_990fc.
Definition Fo_0b0 := F_99100.
Definition Do_0b0 := D_99100.
Definition Fo_0b4 := F_99104.
Definition Do_0b4 := D_99104.
Definition Fo_0b8 := F_99108.
Definition Do_0b8 := D_99108.
Definition Fo_0bc := F_9910c.
Definition Do_0bc := D_9910c.
Definition Fo_0c0 := F_99110.
Definition Do_0c0 := D_99110.
Definition Fo_0c4 := F_99114.
Definition Do_0c4 := D_99114.
Definition Fo_0c8 := F_99118.
Definition Do_0c8 := D_99118.
Definition Fo_0cc := F_9911c.
Definition Do_0cc := D_9911c.
Definition Fo_0d0 := F_99120.
Definition Do_0d0 := D_99120.
Definition Fo_0d4 := F_99124.
Definition Do_0d4 := D_99124.
Definition Fo_0d8 := F_99128.
Definition Do_0d8 := D_99128.
Definition Fo_0dc := F_9912c.
Definition Do_0dc := D_9912c.
Definition Fo_0e0 := F_99130.
Definition Do_0e0 := D_99130.
Definition Fo_0e4 := F_99134.
Definition Do_0e4 := D_99134.
Definition Fo_0e8 := F_99138.
Definition Do_0e8 := D_99138.
Definition Fo_0ec := F_9913c.
Definition Do_0ec := D_9913c.
Definition Fo_0f0 := F_99140.
Definition Do_0f0 := D_99140.
Definition Fo_0f4 := F_99144.
Definition Do_0f4 := D_99144.
