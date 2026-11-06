(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)


(* [comment removed for export] *)
Definition W_657d4 : bv 32 := 0x06060663.
Lemma F_657d4 : fetch_word Asan.M.loaded_segments (0x65848 : word) = Some W_657d4.
Proof. vm_refl. Qed.
Lemma D_657d4 : decode_any W_657d4 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_657d8 : bv 32 := 0x00000693.
Lemma F_657d8 : fetch_word Asan.M.loaded_segments (0x6584c : word) = Some W_657d8.
Proof. vm_refl. Qed.
Lemma D_657d8 : decode_any W_657d8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_657dc : bv 32 := 0x00d58733.
Lemma F_657dc : fetch_word Asan.M.loaded_segments (0x65850 : word) = Some W_657dc.
Proof. vm_refl. Qed.
Lemma D_657dc : decode_any W_657dc = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_657e0 : bv 32 := 0x00074703.
Lemma F_657e0 : fetch_word Asan.M.loaded_segments (0x65854 : word) = Some W_657e0.
Proof. vm_refl. Qed.
Lemma D_657e0 : decode_any W_657e0 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_657e4 : bv 32 := 0x00070c63.
Lemma F_657e4 : fetch_word Asan.M.loaded_segments (0x65858 : word) = Some W_657e4.
Proof. vm_refl. Qed.
Lemma D_657e4 : decode_any W_657e4 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_657e8 : bv 32 := 0x00d507b3.
Lemma F_657e8 : fetch_word Asan.M.loaded_segments (0x6585c : word) = Some W_657e8.
Proof. vm_refl. Qed.
Lemma D_657e8 : decode_any W_657e8 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_657ec : bv 32 := 0x00168693.
Lemma F_657ec : fetch_word Asan.M.loaded_segments (0x65860 : word) = Some W_657ec.
Proof. vm_refl. Qed.
Lemma D_657ec : decode_any W_657ec = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_657f0 : bv 32 := 0x00e78023.
Lemma F_657f0 : fetch_word Asan.M.loaded_segments (0x65864 : word) = Some W_657f0.
Proof. vm_refl. Qed.
Lemma D_657f0 : decode_any W_657f0 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_657f4 : bv 32 := 0xfed614e3.
Lemma F_657f4 : fetch_word Asan.M.loaded_segments (0x65868 : word) = Some W_657f4.
Proof. vm_refl. Qed.
Lemma D_657f4 : decode_any W_657f4 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_657f8 : bv 32 := 0x00060693.
Lemma F_657f8 : fetch_word Asan.M.loaded_segments (0x6586c : word) = Some W_657f8.
Proof. vm_refl. Qed.
Lemma D_657f8 : decode_any W_657f8 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_657fc : bv 32 := 0x00d505b3.
Lemma F_657fc : fetch_word Asan.M.loaded_segments (0x65870 : word) = Some W_657fc.
Proof. vm_refl. Qed.
Lemma D_657fc : decode_any W_657fc = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65800 : bv 32 := 0x40d6073b.
Lemma F_65800 : fetch_word Asan.M.loaded_segments (0x65874 : word) = Some W_65800.
Proof. vm_refl. Qed.
Lemma D_65800 : decode_any W_65800 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65804 : bv 32 := 0x00b76733.
Lemma F_65804 : fetch_word Asan.M.loaded_segments (0x65878 : word) = Some W_65804.
Proof. vm_refl. Qed.
Lemma D_65804 : decode_any W_65804 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65808 : bv 32 := 0x00f77713.
Lemma F_65808 : fetch_word Asan.M.loaded_segments (0x6587c : word) = Some W_65808.
Proof. vm_refl. Qed.
Lemma D_65808 : decode_any W_65808 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6580c : bv 32 := 0x00070e63.
Lemma F_6580c : fetch_word Asan.M.loaded_segments (0x65880 : word) = Some W_6580c.
Proof. vm_refl. Qed.
Lemma D_6580c : decode_any W_6580c = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65810 : bv 32 := 0x02d60863.
Lemma F_65810 : fetch_word Asan.M.loaded_segments (0x65884 : word) = Some W_65810.
Proof. vm_refl. Qed.
Lemma D_65810 : decode_any W_65810 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65814 : bv 32 := 0x00c50633.
Lemma F_65814 : fetch_word Asan.M.loaded_segments (0x65888 : word) = Some W_65814.
Proof. vm_refl. Qed.
Lemma D_65814 : decode_any W_65814 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65818 : bv 32 := 0x00058023.
Lemma F_65818 : fetch_word Asan.M.loaded_segments (0x6588c : word) = Some W_65818.
Proof. vm_refl. Qed.
Lemma D_65818 : decode_any W_65818 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6581c : bv 32 := 0x00158593.
Lemma F_6581c : fetch_word Asan.M.loaded_segments (0x65890 : word) = Some W_6581c.
Proof. vm_refl. Qed.
Lemma D_6581c : decode_any W_6581c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65820 : bv 32 := 0xfec59ce3.
Lemma F_65820 : fetch_word Asan.M.loaded_segments (0x65894 : word) = Some W_65820.
Proof. vm_refl. Qed.
Lemma D_65820 : decode_any W_65820 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65824 : bv 32 := 0x01c0006f.
Lemma F_65824 : fetch_word Asan.M.loaded_segments (0x65898 : word) = Some W_65824.
Proof. vm_refl. Qed.
Lemma D_65824 : decode_any W_65824 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65828 : bv 32 := 0x00d60c63.
Lemma F_65828 : fetch_word Asan.M.loaded_segments (0x6589c : word) = Some W_65828.
Proof. vm_refl. Qed.
Lemma D_65828 : decode_any W_65828 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6582c : bv 32 := 0x00c50633.
Lemma F_6582c : fetch_word Asan.M.loaded_segments (0x658a0 : word) = Some W_6582c.
Proof. vm_refl. Qed.
Lemma D_6582c : decode_any W_6582c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65830 : bv 32 := 0x0005b023.
Lemma F_65830 : fetch_word Asan.M.loaded_segments (0x658a4 : word) = Some W_65830.
Proof. vm_refl. Qed.
Lemma D_65830 : decode_any W_65830 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65834 : bv 32 := 0x0005b423.
Lemma F_65834 : fetch_word Asan.M.loaded_segments (0x658a8 : word) = Some W_65834.
Proof. vm_refl. Qed.
Lemma D_65834 : decode_any W_65834 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65838 : bv 32 := 0x01058593.
Lemma F_65838 : fetch_word Asan.M.loaded_segments (0x658ac : word) = Some W_65838.
Proof. vm_refl. Qed.
Lemma D_65838 : decode_any W_65838 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6583c : bv 32 := 0xfec5eae3.
Lemma F_6583c : fetch_word Asan.M.loaded_segments (0x658b0 : word) = Some W_6583c.
Proof. vm_refl. Qed.
Lemma D_6583c : decode_any W_6583c = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65840 : bv 32 := 0x00008067.
Lemma F_65840 : fetch_word Asan.M.loaded_segments (0x658b4 : word) = Some W_65840.
Proof. vm_refl. Qed.
Lemma D_65840 : decode_any W_65840 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition W_526b0 : bv 32 := 0x00200613.
Lemma F_526b0 : fetch_word Asan.M.loaded_segments (0x52724 : word) = Some W_526b0.
Proof. vm_refl. Qed.
Lemma D_526b0 : decode_any W_526b0 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526b4 : bv 32 := 0x14c5ea63.
Lemma F_526b4 : fetch_word Asan.M.loaded_segments (0x52728 : word) = Some W_526b4.
Proof. vm_refl. Qed.
Lemma D_526b4 : decode_any W_526b4 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526b8 : bv 32 := 0x00100613.
Lemma F_526b8 : fetch_word Asan.M.loaded_segments (0x5272c : word) = Some W_526b8.
Proof. vm_refl. Qed.
Lemma D_526b8 : decode_any W_526b8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526bc : bv 32 := 0x00100693.
Lemma F_526bc : fetch_word Asan.M.loaded_segments (0x52730 : word) = Some W_526bc.
Proof. vm_refl. Qed.
Lemma D_526bc : decode_any W_526bc = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526c0 : bv 32 := 0x00c0006f.
Lemma F_526c0 : fetch_word Asan.M.loaded_segments (0x52734 : word) = Some W_526c0.
Proof. vm_refl. Qed.
Lemma D_526c0 : decode_any W_526c0 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526c4 : bv 32 := 0x00160613.
Lemma F_526c4 : fetch_word Asan.M.loaded_segments (0x52738 : word) = Some W_526c4.
Proof. vm_refl. Qed.
Lemma D_526c4 : decode_any W_526c4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526c8 : bv 32 := 0x12b60c63.
Lemma F_526c8 : fetch_word Asan.M.loaded_segments (0x5273c : word) = Some W_526c8.
Proof. vm_refl. Qed.
Lemma D_526c8 : decode_any W_526c8 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526cc : bv 32 := 0x00461713.
Lemma F_526cc : fetch_word Asan.M.loaded_segments (0x52740 : word) = Some W_526cc.
Proof. vm_refl. Qed.
Lemma D_526cc : decode_any W_526cc = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526d0 : bv 32 := 0x00e50733.
Lemma F_526d0 : fetch_word Asan.M.loaded_segments (0x52744 : word) = Some W_526d0.
Proof. vm_refl. Qed.
Lemma D_526d0 : decode_any W_526d0 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526d4 : bv 32 := 0x00072703.
Lemma F_526d4 : fetch_word Asan.M.loaded_segments (0x52748 : word) = Some W_526d4.
Proof. vm_refl. Qed.
Lemma D_526d4 : decode_any W_526d4 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526d8 : bv 32 := 0x00060893.
Lemma F_526d8 : fetch_word Asan.M.loaded_segments (0x5274c : word) = Some W_526d8.
Proof. vm_refl. Qed.
Lemma D_526d8 : decode_any W_526d8 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526dc : bv 32 := 0xfff88793.
Lemma F_526dc : fetch_word Asan.M.loaded_segments (0x52750 : word) = Some W_526dc.
Proof. vm_refl. Qed.
Lemma D_526dc : decode_any W_526dc = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526e0 : bv 32 := 0x0017d813.
Lemma F_526e0 : fetch_word Asan.M.loaded_segments (0x52754 : word) = Some W_526e0.
Proof. vm_refl. Qed.
Lemma D_526e0 : decode_any W_526e0 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526e4 : bv 32 := 0x00481293.
Lemma F_526e4 : fetch_word Asan.M.loaded_segments (0x52758 : word) = Some W_526e4.
Proof. vm_refl. Qed.
Lemma D_526e4 : decode_any W_526e4 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526e8 : bv 32 := 0x005502b3.
Lemma F_526e8 : fetch_word Asan.M.loaded_segments (0x5275c : word) = Some W_526e8.
Proof. vm_refl. Qed.
Lemma D_526e8 : decode_any W_526e8 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526ec : bv 32 := 0x0002a303.
Lemma F_526ec : fetch_word Asan.M.loaded_segments (0x52760 : word) = Some W_526ec.
Proof. vm_refl. Qed.
Lemma D_526ec : decode_any W_526ec = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526f0 : bv 32 := 0xfce37ae3.
Lemma F_526f0 : fetch_word Asan.M.loaded_segments (0x52764 : word) = Some W_526f0.
Proof. vm_refl. Qed.
Lemma D_526f0 : decode_any W_526f0 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526f4 : bv 32 := 0x0002b303.
Lemma F_526f4 : fetch_word Asan.M.loaded_segments (0x52768 : word) = Some W_526f4.
Proof. vm_refl. Qed.
Lemma D_526f4 : decode_any W_526f4 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526f8 : bv 32 := 0x00489893.
Lemma F_526f8 : fetch_word Asan.M.loaded_segments (0x5276c : word) = Some W_526f8.
Proof. vm_refl. Qed.
Lemma D_526f8 : decode_any W_526f8 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526fc : bv 32 := 0x011508b3.
Lemma F_526fc : fetch_word Asan.M.loaded_segments (0x52770 : word) = Some W_526fc.
Proof. vm_refl. Qed.
Lemma D_526fc : decode_any W_526fc = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52700 : bv 32 := 0x0048a383.
Lemma F_52700 : fetch_word Asan.M.loaded_segments (0x52774 : word) = Some W_52700.
Proof. vm_refl. Qed.
Lemma D_52700 : decode_any W_52700 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52704 : bv 32 := 0x0068b023.
Lemma F_52704 : fetch_word Asan.M.loaded_segments (0x52778 : word) = Some W_52704.
Proof. vm_refl. Qed.
Lemma D_52704 : decode_any W_52704 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52708 : bv 32 := 0x0082b303.
Lemma F_52708 : fetch_word Asan.M.loaded_segments (0x5277c : word) = Some W_52708.
Proof. vm_refl. Qed.
Lemma D_52708 : decode_any W_52708 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5270c : bv 32 := 0x0088be03.
Lemma F_5270c : fetch_word Asan.M.loaded_segments (0x52780 : word) = Some W_5270c.
Proof. vm_refl. Qed.
Lemma D_5270c : decode_any W_5270c = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52710 : bv 32 := 0x0068b423.
Lemma F_52710 : fetch_word Asan.M.loaded_segments (0x52784 : word) = Some W_52710.
Proof. vm_refl. Qed.
Lemma D_52710 : decode_any W_52710 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52714 : bv 32 := 0x00e2a023.
Lemma F_52714 : fetch_word Asan.M.loaded_segments (0x52788 : word) = Some W_52714.
Proof. vm_refl. Qed.
Lemma D_52714 : decode_any W_52714 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52718 : bv 32 := 0x0072a223.
Lemma F_52718 : fetch_word Asan.M.loaded_segments (0x5278c : word) = Some W_52718.
Proof. vm_refl. Qed.
Lemma D_52718 : decode_any W_52718 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5271c : bv 32 := 0x01c2b423.
Lemma F_5271c : fetch_word Asan.M.loaded_segments (0x52790 : word) = Some W_5271c.
Proof. vm_refl. Qed.
Lemma D_5271c : decode_any W_5271c = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52720 : bv 32 := 0x00080893.
Lemma F_52720 : fetch_word Asan.M.loaded_segments (0x52794 : word) = Some W_52720.
Proof. vm_refl. Qed.
Lemma D_52720 : decode_any W_52720 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52724 : bv 32 := 0xfaf6ece3.
Lemma F_52724 : fetch_word Asan.M.loaded_segments (0x52798 : word) = Some W_52724.
Proof. vm_refl. Qed.
Lemma D_52724 : decode_any W_52724 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52728 : bv 32 := 0xf9dff06f.
Lemma F_52728 : fetch_word Asan.M.loaded_segments (0x5279c : word) = Some W_52728.
Proof. vm_refl. Qed.
Lemma D_52728 : decode_any W_52728 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5272c : bv 32 := 0x00000613.
Lemma F_5272c : fetch_word Asan.M.loaded_segments (0x527a0 : word) = Some W_5272c.
Proof. vm_refl. Qed.
Lemma D_5272c : decode_any W_5272c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52730 : bv 32 := 0x00459693.
Lemma F_52730 : fetch_word Asan.M.loaded_segments (0x527a4 : word) = Some W_52730.
Proof. vm_refl. Qed.
Lemma D_52730 : decode_any W_52730 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52734 : bv 32 := 0x00d506b3.
Lemma F_52734 : fetch_word Asan.M.loaded_segments (0x527a8 : word) = Some W_52734.
Proof. vm_refl. Qed.
Lemma D_52734 : decode_any W_52734 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52738 : bv 32 := 0x0006b703.
Lemma F_52738 : fetch_word Asan.M.loaded_segments (0x527ac : word) = Some W_52738.
Proof. vm_refl. Qed.
Lemma D_52738 : decode_any W_52738 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5273c : bv 32 := 0x0086b783.
Lemma F_5273c : fetch_word Asan.M.loaded_segments (0x527b0 : word) = Some W_5273c.
Proof. vm_refl. Qed.
Lemma D_5273c : decode_any W_5273c = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52740 : bv 32 := 0x00053803.
Lemma F_52740 : fetch_word Asan.M.loaded_segments (0x527b4 : word) = Some W_52740.
Proof. vm_refl. Qed.
Lemma D_52740 : decode_any W_52740 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52744 : bv 32 := 0x00853883.
Lemma F_52744 : fetch_word Asan.M.loaded_segments (0x527b8 : word) = Some W_52744.
Proof. vm_refl. Qed.
Lemma D_52744 : decode_any W_52744 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52748 : bv 32 := 0x00e53023.
Lemma F_52748 : fetch_word Asan.M.loaded_segments (0x527bc : word) = Some W_52748.
Proof. vm_refl. Qed.
Lemma D_52748 : decode_any W_52748 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5274c : bv 32 := 0x00f53423.
Lemma F_5274c : fetch_word Asan.M.loaded_segments (0x527c0 : word) = Some W_5274c.
Proof. vm_refl. Qed.
Lemma D_5274c : decode_any W_5274c = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52750 : bv 32 := 0x0106b023.
Lemma F_52750 : fetch_word Asan.M.loaded_segments (0x527c4 : word) = Some W_52750.
Proof. vm_refl. Qed.
Lemma D_52750 : decode_any W_52750 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52754 : bv 32 := 0x0116b423.
Lemma F_52754 : fetch_word Asan.M.loaded_segments (0x527c8 : word) = Some W_52754.
Proof. vm_refl. Qed.
Lemma D_52754 : decode_any W_52754 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52758 : bv 32 := 0x00000693.
Lemma F_52758 : fetch_word Asan.M.loaded_segments (0x527cc : word) = Some W_52758.
Proof. vm_refl. Qed.
Lemma D_52758 : decode_any W_52758 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5275c : bv 32 := 0x00161793.
Lemma F_5275c : fetch_word Asan.M.loaded_segments (0x527d0 : word) = Some W_5275c.
Proof. vm_refl. Qed.
Lemma D_5275c : decode_any W_5275c = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52760 : bv 32 := 0x00178813.
Lemma F_52760 : fetch_word Asan.M.loaded_segments (0x527d4 : word) = Some W_52760.
Proof. vm_refl. Qed.
Lemma D_52760 : decode_any W_52760 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52764 : bv 32 := 0x00461713.
Lemma F_52764 : fetch_word Asan.M.loaded_segments (0x527d8 : word) = Some W_52764.
Proof. vm_refl. Qed.
Lemma D_52764 : decode_any W_52764 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52768 : bv 32 := 0x00b86a63.
Lemma F_52768 : fetch_word Asan.M.loaded_segments (0x527dc : word) = Some W_52768.
Proof. vm_refl. Qed.
Lemma D_52768 : decode_any W_52768 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5276c : bv 32 := 0x00278793.
Lemma F_5276c : fetch_word Asan.M.loaded_segments (0x527e0 : word) = Some W_5276c.
Proof. vm_refl. Qed.
Lemma D_5276c : decode_any W_5276c = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52770 : bv 32 := 0x02b7ea63.
Lemma F_52770 : fetch_word Asan.M.loaded_segments (0x527e4 : word) = Some W_52770.
Proof. vm_refl. Qed.
Lemma D_52770 : decode_any W_52770 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52774 : bv 32 := 0x04c69c63.
Lemma F_52774 : fetch_word Asan.M.loaded_segments (0x527e8 : word) = Some W_52774.
Proof. vm_refl. Qed.
Lemma D_52774 : decode_any W_52774 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52778 : bv 32 := 0x0880006f.
Lemma F_52778 : fetch_word Asan.M.loaded_segments (0x527ec : word) = Some W_52778.
Proof. vm_refl. Qed.
Lemma D_52778 : decode_any W_52778 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5277c : bv 32 := 0x00e506b3.
Lemma F_5277c : fetch_word Asan.M.loaded_segments (0x527f0 : word) = Some W_5277c.
Proof. vm_refl. Qed.
Lemma D_5277c : decode_any W_5277c = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52780 : bv 32 := 0x00481893.
Lemma F_52780 : fetch_word Asan.M.loaded_segments (0x527f4 : word) = Some W_52780.
Proof. vm_refl. Qed.
Lemma D_52780 : decode_any W_52780 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52784 : bv 32 := 0x011508b3.
Lemma F_52784 : fetch_word Asan.M.loaded_segments (0x527f8 : word) = Some W_52784.
Proof. vm_refl. Qed.
Lemma D_52784 : decode_any W_52784 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52788 : bv 32 := 0x0006a683.
Lemma F_52788 : fetch_word Asan.M.loaded_segments (0x527fc : word) = Some W_52788.
Proof. vm_refl. Qed.
Lemma D_52788 : decode_any W_52788 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5278c : bv 32 := 0x0008a883.
Lemma F_5278c : fetch_word Asan.M.loaded_segments (0x52800 : word) = Some W_5278c.
Proof. vm_refl. Qed.
Lemma D_5278c : decode_any W_5278c = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52790 : bv 32 := 0x0116e463.
Lemma F_52790 : fetch_word Asan.M.loaded_segments (0x52804 : word) = Some W_52790.
Proof. vm_refl. Qed.
Lemma D_52790 : decode_any W_52790 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52794 : bv 32 := 0x00060813.
Lemma F_52794 : fetch_word Asan.M.loaded_segments (0x52808 : word) = Some W_52794.
Proof. vm_refl. Qed.
Lemma D_52794 : decode_any W_52794 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52798 : bv 32 := 0x00080693.
Lemma F_52798 : fetch_word Asan.M.loaded_segments (0x5280c : word) = Some W_52798.
Proof. vm_refl. Qed.
Lemma D_52798 : decode_any W_52798 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5279c : bv 32 := 0x00278793.
Lemma F_5279c : fetch_word Asan.M.loaded_segments (0x52810 : word) = Some W_5279c.
Proof. vm_refl. Qed.
Lemma D_5279c : decode_any W_5279c = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527a0 : bv 32 := 0xfcb7fae3.
Lemma F_527a0 : fetch_word Asan.M.loaded_segments (0x52814 : word) = Some W_527a0.
Proof. vm_refl. Qed.
Lemma D_527a0 : decode_any W_527a0 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527a4 : bv 32 := 0x00469813.
Lemma F_527a4 : fetch_word Asan.M.loaded_segments (0x52818 : word) = Some W_527a4.
Proof. vm_refl. Qed.
Lemma D_527a4 : decode_any W_527a4 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527a8 : bv 32 := 0x00479893.
Lemma F_527a8 : fetch_word Asan.M.loaded_segments (0x5281c : word) = Some W_527a8.
Proof. vm_refl. Qed.
Lemma D_527a8 : decode_any W_527a8 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527ac : bv 32 := 0x01050833.
Lemma F_527ac : fetch_word Asan.M.loaded_segments (0x52820 : word) = Some W_527ac.
Proof. vm_refl. Qed.
Lemma D_527ac : decode_any W_527ac = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527b0 : bv 32 := 0x011508b3.
Lemma F_527b0 : fetch_word Asan.M.loaded_segments (0x52824 : word) = Some W_527b0.
Proof. vm_refl. Qed.
Lemma D_527b0 : decode_any W_527b0 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527b4 : bv 32 := 0x00082803.
Lemma F_527b4 : fetch_word Asan.M.loaded_segments (0x52828 : word) = Some W_527b4.
Proof. vm_refl. Qed.
Lemma D_527b4 : decode_any W_527b4 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527b8 : bv 32 := 0x0008a883.
Lemma F_527b8 : fetch_word Asan.M.loaded_segments (0x5282c : word) = Some W_527b8.
Proof. vm_refl. Qed.
Lemma D_527b8 : decode_any W_527b8 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527bc : bv 32 := 0x01186463.
Lemma F_527bc : fetch_word Asan.M.loaded_segments (0x52830 : word) = Some W_527bc.
Proof. vm_refl. Qed.
Lemma D_527bc : decode_any W_527bc = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527c0 : bv 32 := 0x00068793.
Lemma F_527c0 : fetch_word Asan.M.loaded_segments (0x52834 : word) = Some W_527c0.
Proof. vm_refl. Qed.
Lemma D_527c0 : decode_any W_527c0 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527c4 : bv 32 := 0x00078693.
Lemma F_527c4 : fetch_word Asan.M.loaded_segments (0x52838 : word) = Some W_527c4.
Proof. vm_refl. Qed.
Lemma D_527c4 : decode_any W_527c4 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527c8 : bv 32 := 0x02c78c63.
Lemma F_527c8 : fetch_word Asan.M.loaded_segments (0x5283c : word) = Some W_527c8.
Proof. vm_refl. Qed.
Lemma D_527c8 : decode_any W_527c8 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527cc : bv 32 := 0x00469613.
Lemma F_527cc : fetch_word Asan.M.loaded_segments (0x52840 : word) = Some W_527cc.
Proof. vm_refl. Qed.
Lemma D_527cc : decode_any W_527cc = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527d0 : bv 32 := 0x00c50633.
Lemma F_527d0 : fetch_word Asan.M.loaded_segments (0x52844 : word) = Some W_527d0.
Proof. vm_refl. Qed.
Lemma D_527d0 : decode_any W_527d0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527d4 : bv 32 := 0x00063783.
Lemma F_527d4 : fetch_word Asan.M.loaded_segments (0x52848 : word) = Some W_527d4.
Proof. vm_refl. Qed.
Lemma D_527d4 : decode_any W_527d4 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527d8 : bv 32 := 0x00e50733.
Lemma F_527d8 : fetch_word Asan.M.loaded_segments (0x5284c : word) = Some W_527d8.
Proof. vm_refl. Qed.
Lemma D_527d8 : decode_any W_527d8 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527dc : bv 32 := 0x00073803.
Lemma F_527dc : fetch_word Asan.M.loaded_segments (0x52850 : word) = Some W_527dc.
Proof. vm_refl. Qed.
Lemma D_527dc : decode_any W_527dc = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527e0 : bv 32 := 0x00873883.
Lemma F_527e0 : fetch_word Asan.M.loaded_segments (0x52854 : word) = Some W_527e0.
Proof. vm_refl. Qed.
Lemma D_527e0 : decode_any W_527e0 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527e4 : bv 32 := 0x00f73023.
Lemma F_527e4 : fetch_word Asan.M.loaded_segments (0x52858 : word) = Some W_527e4.
Proof. vm_refl. Qed.
Lemma D_527e4 : decode_any W_527e4 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527e8 : bv 32 := 0x00863783.
Lemma F_527e8 : fetch_word Asan.M.loaded_segments (0x5285c : word) = Some W_527e8.
Proof. vm_refl. Qed.
Lemma D_527e8 : decode_any W_527e8 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527ec : bv 32 := 0x00f73423.
Lemma F_527ec : fetch_word Asan.M.loaded_segments (0x52860 : word) = Some W_527ec.
Proof. vm_refl. Qed.
Lemma D_527ec : decode_any W_527ec = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527f0 : bv 32 := 0x01063023.
Lemma F_527f0 : fetch_word Asan.M.loaded_segments (0x52864 : word) = Some W_527f0.
Proof. vm_refl. Qed.
Lemma D_527f0 : decode_any W_527f0 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527f4 : bv 32 := 0x01163423.
Lemma F_527f4 : fetch_word Asan.M.loaded_segments (0x52868 : word) = Some W_527f4.
Proof. vm_refl. Qed.
Lemma D_527f4 : decode_any W_527f4 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527f8 : bv 32 := 0x00068613.
Lemma F_527f8 : fetch_word Asan.M.loaded_segments (0x5286c : word) = Some W_527f8.
Proof. vm_refl. Qed.
Lemma D_527f8 : decode_any W_527f8 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527fc : bv 32 := 0xf6b6e0e3.
Lemma F_527fc : fetch_word Asan.M.loaded_segments (0x52870 : word) = Some W_527fc.
Proof. vm_refl. Qed.
Lemma D_527fc : decode_any W_527fc = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52800 : bv 32 := 0xfff58593.
Lemma F_52800 : fetch_word Asan.M.loaded_segments (0x52874 : word) = Some W_52800.
Proof. vm_refl. Qed.
Lemma D_52800 : decode_any W_52800 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52804 : bv 32 := 0xf20594e3.
Lemma F_52804 : fetch_word Asan.M.loaded_segments (0x52878 : word) = Some W_52804.
Proof. vm_refl. Qed.
Lemma D_52804 : decode_any W_52804 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52808 : bv 32 := 0x00008067.
Lemma F_52808 : fetch_word Asan.M.loaded_segments (0x5287c : word) = Some W_52808.
Proof. vm_refl. Qed.
Lemma D_52808 : decode_any W_52808 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

