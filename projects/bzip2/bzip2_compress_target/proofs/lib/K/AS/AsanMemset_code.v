(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Asan.
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
Definition W_b9004 : bv 32 := 0x0e060a63.
Lemma F_b9004 : fetch_word Asan.M.loaded_segments (0xb9188 : word) = Some W_b9004.
Proof. vm_refl. Qed.
Lemma D_b9004 : decode_any W_b9004 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9008 : bv 32 := 0x00b50023.
Lemma F_b9008 : fetch_word Asan.M.loaded_segments (0xb918c : word) = Some W_b9008.
Proof. vm_refl. Qed.
Lemma D_b9008 : decode_any W_b9008 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b900c : bv 32 := 0x00c506b3.
Lemma F_b900c : fetch_word Asan.M.loaded_segments (0xb9190 : word) = Some W_b900c.
Proof. vm_refl. Qed.
Lemma D_b900c : decode_any W_b900c = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9010 : bv 32 := 0x00300713.
Lemma F_b9010 : fetch_word Asan.M.loaded_segments (0xb9194 : word) = Some W_b9010.
Proof. vm_refl. Qed.
Lemma D_b9010 : decode_any W_b9010 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9014 : bv 32 := 0xfeb68fa3.
Lemma F_b9014 : fetch_word Asan.M.loaded_segments (0xb9198 : word) = Some W_b9014.
Proof. vm_refl. Qed.
Lemma D_b9014 : decode_any W_b9014 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9018 : bv 32 := 0x0ee66063.
Lemma F_b9018 : fetch_word Asan.M.loaded_segments (0xb919c : word) = Some W_b9018.
Proof. vm_refl. Qed.
Lemma D_b9018 : decode_any W_b9018 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b901c : bv 32 := 0x00b500a3.
Lemma F_b901c : fetch_word Asan.M.loaded_segments (0xb91a0 : word) = Some W_b901c.
Proof. vm_refl. Qed.
Lemma D_b901c : decode_any W_b901c = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9020 : bv 32 := 0x00b50123.
Lemma F_b9020 : fetch_word Asan.M.loaded_segments (0xb91a4 : word) = Some W_b9020.
Proof. vm_refl. Qed.
Lemma D_b9020 : decode_any W_b9020 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9024 : bv 32 := 0x00700713.
Lemma F_b9024 : fetch_word Asan.M.loaded_segments (0xb91a8 : word) = Some W_b9024.
Proof. vm_refl. Qed.
Lemma D_b9024 : decode_any W_b9024 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9028 : bv 32 := 0xfeb68ea3.
Lemma F_b9028 : fetch_word Asan.M.loaded_segments (0xb91ac : word) = Some W_b9028.
Proof. vm_refl. Qed.
Lemma D_b9028 : decode_any W_b9028 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b902c : bv 32 := 0xfeb68f23.
Lemma F_b902c : fetch_word Asan.M.loaded_segments (0xb91b0 : word) = Some W_b902c.
Proof. vm_refl. Qed.
Lemma D_b902c : decode_any W_b902c = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9030 : bv 32 := 0x0ce66463.
Lemma F_b9030 : fetch_word Asan.M.loaded_segments (0xb91b4 : word) = Some W_b9030.
Proof. vm_refl. Qed.
Lemma D_b9030 : decode_any W_b9030 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9034 : bv 32 := 0x00b501a3.
Lemma F_b9034 : fetch_word Asan.M.loaded_segments (0xb91b8 : word) = Some W_b9034.
Proof. vm_refl. Qed.
Lemma D_b9034 : decode_any W_b9034 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9038 : bv 32 := 0x00900793.
Lemma F_b9038 : fetch_word Asan.M.loaded_segments (0xb91bc : word) = Some W_b9038.
Proof. vm_refl. Qed.
Lemma D_b9038 : decode_any W_b9038 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b903c : bv 32 := 0xfeb68e23.
Lemma F_b903c : fetch_word Asan.M.loaded_segments (0xb91c0 : word) = Some W_b903c.
Proof. vm_refl. Qed.
Lemma D_b903c : decode_any W_b903c = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9040 : bv 32 := 0x0af66c63.
Lemma F_b9040 : fetch_word Asan.M.loaded_segments (0xb91c4 : word) = Some W_b9040.
Proof. vm_refl. Qed.
Lemma D_b9040 : decode_any W_b9040 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9044 : bv 32 := 0x40a006bb.
Lemma F_b9044 : fetch_word Asan.M.loaded_segments (0xb91c8 : word) = Some W_b9044.
Proof. vm_refl. Qed.
Lemma D_b9044 : decode_any W_b9044 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9048 : bv 32 := 0x03859813.
Lemma F_b9048 : fetch_word Asan.M.loaded_segments (0xb91cc : word) = Some W_b9048.
Proof. vm_refl. Qed.
Lemma D_b9048 : decode_any W_b9048 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b904c : bv 32 := 0x101015b7.
Lemma F_b904c : fetch_word Asan.M.loaded_segments (0xb91d0 : word) = Some W_b904c.
Proof. vm_refl. Qed.
Lemma D_b904c : decode_any W_b904c = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9050 : bv 32 := 0x0036f693.
Lemma F_b9050 : fetch_word Asan.M.loaded_segments (0xb91d4 : word) = Some W_b9050.
Proof. vm_refl. Qed.
Lemma D_b9050 : decode_any W_b9050 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9054 : bv 32 := 0x00459713.
Lemma F_b9054 : fetch_word Asan.M.loaded_segments (0xb91d8 : word) = Some W_b9054.
Proof. vm_refl. Qed.
Lemma D_b9054 : decode_any W_b9054 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9058 : bv 32 := 0x40d60633.
Lemma F_b9058 : fetch_word Asan.M.loaded_segments (0xb91dc : word) = Some W_b9058.
Proof. vm_refl. Qed.
Lemma D_b9058 : decode_any W_b9058 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b905c : bv 32 := 0x00d505b3.
Lemma F_b905c : fetch_word Asan.M.loaded_segments (0xb91e0 : word) = Some W_b905c.
Proof. vm_refl. Qed.
Lemma D_b905c : decode_any W_b905c = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9060 : bv 32 := 0x10070693.
Lemma F_b9060 : fetch_word Asan.M.loaded_segments (0xb91e4 : word) = Some W_b9060.
Proof. vm_refl. Qed.
Lemma D_b9060 : decode_any W_b9060 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9064 : bv 32 := 0xffc67713.
Lemma F_b9064 : fetch_word Asan.M.loaded_segments (0xb91e8 : word) = Some W_b9064.
Proof. vm_refl. Qed.
Lemma D_b9064 : decode_any W_b9064 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9068 : bv 32 := 0x02d83633.
Lemma F_b9068 : fetch_word Asan.M.loaded_segments (0xb91ec : word) = Some W_b9068.
Proof. vm_refl. Qed.
Lemma D_b9068 : decode_any W_b9068 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b906c : bv 32 := 0x00c5a023.
Lemma F_b906c : fetch_word Asan.M.loaded_segments (0xb91f0 : word) = Some W_b906c.
Proof. vm_refl. Qed.
Lemma D_b906c : decode_any W_b906c = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9070 : bv 32 := 0x00e586b3.
Lemma F_b9070 : fetch_word Asan.M.loaded_segments (0xb91f4 : word) = Some W_b9070.
Proof. vm_refl. Qed.
Lemma D_b9070 : decode_any W_b9070 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9074 : bv 32 := 0xfec6ae23.
Lemma F_b9074 : fetch_word Asan.M.loaded_segments (0xb91f8 : word) = Some W_b9074.
Proof. vm_refl. Qed.
Lemma D_b9074 : decode_any W_b9074 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9078 : bv 32 := 0x08f76063.
Lemma F_b9078 : fetch_word Asan.M.loaded_segments (0xb91fc : word) = Some W_b9078.
Proof. vm_refl. Qed.
Lemma D_b9078 : decode_any W_b9078 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b907c : bv 32 := 0x00c5a223.
Lemma F_b907c : fetch_word Asan.M.loaded_segments (0xb9200 : word) = Some W_b907c.
Proof. vm_refl. Qed.
Lemma D_b907c : decode_any W_b907c = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9080 : bv 32 := 0x00c5a423.
Lemma F_b9080 : fetch_word Asan.M.loaded_segments (0xb9204 : word) = Some W_b9080.
Proof. vm_refl. Qed.
Lemma D_b9080 : decode_any W_b9080 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9084 : bv 32 := 0x01900793.
Lemma F_b9084 : fetch_word Asan.M.loaded_segments (0xb9208 : word) = Some W_b9084.
Proof. vm_refl. Qed.
Lemma D_b9084 : decode_any W_b9084 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9088 : bv 32 := 0xfec6aa23.
Lemma F_b9088 : fetch_word Asan.M.loaded_segments (0xb920c : word) = Some W_b9088.
Proof. vm_refl. Qed.
Lemma D_b9088 : decode_any W_b9088 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b908c : bv 32 := 0xfec6ac23.
Lemma F_b908c : fetch_word Asan.M.loaded_segments (0xb9210 : word) = Some W_b908c.
Proof. vm_refl. Qed.
Lemma D_b908c : decode_any W_b908c = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9090 : bv 32 := 0x06f76463.
Lemma F_b9090 : fetch_word Asan.M.loaded_segments (0xb9214 : word) = Some W_b9090.
Proof. vm_refl. Qed.
Lemma D_b9090 : decode_any W_b9090 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9094 : bv 32 := 0x00c5a623.
Lemma F_b9094 : fetch_word Asan.M.loaded_segments (0xb9218 : word) = Some W_b9094.
Proof. vm_refl. Qed.
Lemma D_b9094 : decode_any W_b9094 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b9098 : bv 32 := 0x00c5a823.
Lemma F_b9098 : fetch_word Asan.M.loaded_segments (0xb921c : word) = Some W_b9098.
Proof. vm_refl. Qed.
Lemma D_b9098 : decode_any W_b9098 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b909c : bv 32 := 0x00c5aa23.
Lemma F_b909c : fetch_word Asan.M.loaded_segments (0xb9220 : word) = Some W_b909c.
Proof. vm_refl. Qed.
Lemma D_b909c : decode_any W_b909c = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90a0 : bv 32 := 0x00c5ac23.
Lemma F_b90a0 : fetch_word Asan.M.loaded_segments (0xb9224 : word) = Some W_b90a0.
Proof. vm_refl. Qed.
Lemma D_b90a0 : decode_any W_b90a0 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90a4 : bv 32 := 0x0045f793.
Lemma F_b90a4 : fetch_word Asan.M.loaded_segments (0xb9228 : word) = Some W_b90a4.
Proof. vm_refl. Qed.
Lemma D_b90a4 : decode_any W_b90a4 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90a8 : bv 32 := 0x02000813.
Lemma F_b90a8 : fetch_word Asan.M.loaded_segments (0xb922c : word) = Some W_b90a8.
Proof. vm_refl. Qed.
Lemma D_b90a8 : decode_any W_b90a8 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90ac : bv 32 := 0x01878793.
Lemma F_b90ac : fetch_word Asan.M.loaded_segments (0xb9230 : word) = Some W_b90ac.
Proof. vm_refl. Qed.
Lemma D_b90ac : decode_any W_b90ac = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90b0 : bv 32 := 0x40f70733.
Lemma F_b90b0 : fetch_word Asan.M.loaded_segments (0xb9234 : word) = Some W_b90b0.
Proof. vm_refl. Qed.
Lemma D_b90b0 : decode_any W_b90b0 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90b4 : bv 32 := 0xfec6a223.
Lemma F_b90b4 : fetch_word Asan.M.loaded_segments (0xb9238 : word) = Some W_b90b4.
Proof. vm_refl. Qed.
Lemma D_b90b4 : decode_any W_b90b4 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90b8 : bv 32 := 0xfec6a423.
Lemma F_b90b8 : fetch_word Asan.M.loaded_segments (0xb923c : word) = Some W_b90b8.
Proof. vm_refl. Qed.
Lemma D_b90b8 : decode_any W_b90b8 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90bc : bv 32 := 0xfec6a623.
Lemma F_b90bc : fetch_word Asan.M.loaded_segments (0xb9240 : word) = Some W_b90bc.
Proof. vm_refl. Qed.
Lemma D_b90bc : decode_any W_b90bc = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90c0 : bv 32 := 0xfec6a823.
Lemma F_b90c0 : fetch_word Asan.M.loaded_segments (0xb9244 : word) = Some W_b90c0.
Proof. vm_refl. Qed.
Lemma D_b90c0 : decode_any W_b90c0 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90c4 : bv 32 := 0x03076a63.
Lemma F_b90c4 : fetch_word Asan.M.loaded_segments (0xb9248 : word) = Some W_b90c4.
Proof. vm_refl. Qed.
Lemma D_b90c4 : decode_any W_b90c4 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90c8 : bv 32 := 0x02061613.
Lemma F_b90c8 : fetch_word Asan.M.loaded_segments (0xb924c : word) = Some W_b90c8.
Proof. vm_refl. Qed.
Lemma D_b90c8 : decode_any W_b90c8 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90cc : bv 32 := 0x00f585b3.
Lemma F_b90cc : fetch_word Asan.M.loaded_segments (0xb9250 : word) = Some W_b90cc.
Proof. vm_refl. Qed.
Lemma D_b90cc : decode_any W_b90cc = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90d0 : bv 32 := 0x02065693.
Lemma F_b90d0 : fetch_word Asan.M.loaded_segments (0xb9254 : word) = Some W_b90d0.
Proof. vm_refl. Qed.
Lemma D_b90d0 : decode_any W_b90d0 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90d4 : bv 32 := 0x00d66633.
Lemma F_b90d4 : fetch_word Asan.M.loaded_segments (0xb9258 : word) = Some W_b90d4.
Proof. vm_refl. Qed.
Lemma D_b90d4 : decode_any W_b90d4 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90d8 : bv 32 := 0x01f00693.
Lemma F_b90d8 : fetch_word Asan.M.loaded_segments (0xb925c : word) = Some W_b90d8.
Proof. vm_refl. Qed.
Lemma D_b90d8 : decode_any W_b90d8 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90dc : bv 32 := 0x00c5b023.
Lemma F_b90dc : fetch_word Asan.M.loaded_segments (0xb9260 : word) = Some W_b90dc.
Proof. vm_refl. Qed.
Lemma D_b90dc : decode_any W_b90dc = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90e0 : bv 32 := 0x00c5b423.
Lemma F_b90e0 : fetch_word Asan.M.loaded_segments (0xb9264 : word) = Some W_b90e0.
Proof. vm_refl. Qed.
Lemma D_b90e0 : decode_any W_b90e0 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90e4 : bv 32 := 0x00c5b823.
Lemma F_b90e4 : fetch_word Asan.M.loaded_segments (0xb9268 : word) = Some W_b90e4.
Proof. vm_refl. Qed.
Lemma D_b90e4 : decode_any W_b90e4 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90e8 : bv 32 := 0x00c5bc23.
Lemma F_b90e8 : fetch_word Asan.M.loaded_segments (0xb926c : word) = Some W_b90e8.
Proof. vm_refl. Qed.
Lemma D_b90e8 : decode_any W_b90e8 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90ec : bv 32 := 0xfe070713.
Lemma F_b90ec : fetch_word Asan.M.loaded_segments (0xb9270 : word) = Some W_b90ec.
Proof. vm_refl. Qed.
Lemma D_b90ec : decode_any W_b90ec = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90f0 : bv 32 := 0x02058593.
Lemma F_b90f0 : fetch_word Asan.M.loaded_segments (0xb9274 : word) = Some W_b90f0.
Proof. vm_refl. Qed.
Lemma D_b90f0 : decode_any W_b90f0 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90f4 : bv 32 := 0xfee6e4e3.
Lemma F_b90f4 : fetch_word Asan.M.loaded_segments (0xb9278 : word) = Some W_b90f4.
Proof. vm_refl. Qed.
Lemma D_b90f4 : decode_any W_b90f4 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b90f8 : bv 32 := 0x00008067.
Lemma F_b90f8 : fetch_word Asan.M.loaded_segments (0xb927c : word) = Some W_b90f8.
Proof. vm_refl. Qed.
Lemma D_b90f8 : decode_any W_b90f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0xb9188%Z.
Definition Fo_000 := F_b9004.
Definition Do_000 := D_b9004.
Definition Fo_004 := F_b9008.
Definition Do_004 := D_b9008.
Definition Fo_008 := F_b900c.
Definition Do_008 := D_b900c.
Definition Fo_00c := F_b9010.
Definition Do_00c := D_b9010.
Definition Fo_010 := F_b9014.
Definition Do_010 := D_b9014.
Definition Fo_014 := F_b9018.
Definition Do_014 := D_b9018.
Definition Fo_018 := F_b901c.
Definition Do_018 := D_b901c.
Definition Fo_01c := F_b9020.
Definition Do_01c := D_b9020.
Definition Fo_020 := F_b9024.
Definition Do_020 := D_b9024.
Definition Fo_024 := F_b9028.
Definition Do_024 := D_b9028.
Definition Fo_028 := F_b902c.
Definition Do_028 := D_b902c.
Definition Fo_02c := F_b9030.
Definition Do_02c := D_b9030.
Definition Fo_030 := F_b9034.
Definition Do_030 := D_b9034.
Definition Fo_034 := F_b9038.
Definition Do_034 := D_b9038.
Definition Fo_038 := F_b903c.
Definition Do_038 := D_b903c.
Definition Fo_03c := F_b9040.
Definition Do_03c := D_b9040.
Definition Fo_040 := F_b9044.
Definition Do_040 := D_b9044.
Definition Fo_044 := F_b9048.
Definition Do_044 := D_b9048.
Definition Fo_048 := F_b904c.
Definition Do_048 := D_b904c.
Definition Fo_04c := F_b9050.
Definition Do_04c := D_b9050.
Definition Fo_050 := F_b9054.
Definition Do_050 := D_b9054.
Definition Fo_054 := F_b9058.
Definition Do_054 := D_b9058.
Definition Fo_058 := F_b905c.
Definition Do_058 := D_b905c.
Definition Fo_05c := F_b9060.
Definition Do_05c := D_b9060.
Definition Fo_060 := F_b9064.
Definition Do_060 := D_b9064.
Definition Fo_064 := F_b9068.
Definition Do_064 := D_b9068.
Definition Fo_068 := F_b906c.
Definition Do_068 := D_b906c.
Definition Fo_06c := F_b9070.
Definition Do_06c := D_b9070.
Definition Fo_070 := F_b9074.
Definition Do_070 := D_b9074.
Definition Fo_074 := F_b9078.
Definition Do_074 := D_b9078.
Definition Fo_078 := F_b907c.
Definition Do_078 := D_b907c.
Definition Fo_07c := F_b9080.
Definition Do_07c := D_b9080.
Definition Fo_080 := F_b9084.
Definition Do_080 := D_b9084.
Definition Fo_084 := F_b9088.
Definition Do_084 := D_b9088.
Definition Fo_088 := F_b908c.
Definition Do_088 := D_b908c.
Definition Fo_08c := F_b9090.
Definition Do_08c := D_b9090.
Definition Fo_090 := F_b9094.
Definition Do_090 := D_b9094.
Definition Fo_094 := F_b9098.
Definition Do_094 := D_b9098.
Definition Fo_098 := F_b909c.
Definition Do_098 := D_b909c.
Definition Fo_09c := F_b90a0.
Definition Do_09c := D_b90a0.
Definition Fo_0a0 := F_b90a4.
Definition Do_0a0 := D_b90a4.
Definition Fo_0a4 := F_b90a8.
Definition Do_0a4 := D_b90a8.
Definition Fo_0a8 := F_b90ac.
Definition Do_0a8 := D_b90ac.
Definition Fo_0ac := F_b90b0.
Definition Do_0ac := D_b90b0.
Definition Fo_0b0 := F_b90b4.
Definition Do_0b0 := D_b90b4.
Definition Fo_0b4 := F_b90b8.
Definition Do_0b4 := D_b90b8.
Definition Fo_0b8 := F_b90bc.
Definition Do_0b8 := D_b90bc.
Definition Fo_0bc := F_b90c0.
Definition Do_0bc := D_b90c0.
Definition Fo_0c0 := F_b90c4.
Definition Do_0c0 := D_b90c4.
Definition Fo_0c4 := F_b90c8.
Definition Do_0c4 := D_b90c8.
Definition Fo_0c8 := F_b90cc.
Definition Do_0c8 := D_b90cc.
Definition Fo_0cc := F_b90d0.
Definition Do_0cc := D_b90d0.
Definition Fo_0d0 := F_b90d4.
Definition Do_0d0 := D_b90d4.
Definition Fo_0d4 := F_b90d8.
Definition Do_0d4 := D_b90d8.
Definition Fo_0d8 := F_b90dc.
Definition Do_0d8 := D_b90dc.
Definition Fo_0dc := F_b90e0.
Definition Do_0dc := D_b90e0.
Definition Fo_0e0 := F_b90e4.
Definition Do_0e0 := D_b90e4.
Definition Fo_0e4 := F_b90e8.
Definition Do_0e4 := D_b90e8.
Definition Fo_0e8 := F_b90ec.
Definition Do_0e8 := D_b90ec.
Definition Fo_0ec := F_b90f0.
Definition Do_0ec := D_b90f0.
Definition Fo_0f0 := F_b90f4.
Definition Do_0f0 := D_b90f4.
Definition Fo_0f4 := F_b90f8.
Definition Do_0f4 := D_b90f8.
