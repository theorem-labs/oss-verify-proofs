(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_65800 : bv 32 := 0x06060663.
Lemma F_65800 : fetch_word AsanUbsan.M.loaded_segments (0x65654 : word) = Some W_65800.
Proof. vm_refl. Qed.
Lemma D_65800 : decode_any W_65800 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65804 : bv 32 := 0x00000693.
Lemma F_65804 : fetch_word AsanUbsan.M.loaded_segments (0x65658 : word) = Some W_65804.
Proof. vm_refl. Qed.
Lemma D_65804 : decode_any W_65804 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65808 : bv 32 := 0x00d58733.
Lemma F_65808 : fetch_word AsanUbsan.M.loaded_segments (0x6565c : word) = Some W_65808.
Proof. vm_refl. Qed.
Lemma D_65808 : decode_any W_65808 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6580c : bv 32 := 0x00074703.
Lemma F_6580c : fetch_word AsanUbsan.M.loaded_segments (0x65660 : word) = Some W_6580c.
Proof. vm_refl. Qed.
Lemma D_6580c : decode_any W_6580c = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65810 : bv 32 := 0x00070c63.
Lemma F_65810 : fetch_word AsanUbsan.M.loaded_segments (0x65664 : word) = Some W_65810.
Proof. vm_refl. Qed.
Lemma D_65810 : decode_any W_65810 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65814 : bv 32 := 0x00d507b3.
Lemma F_65814 : fetch_word AsanUbsan.M.loaded_segments (0x65668 : word) = Some W_65814.
Proof. vm_refl. Qed.
Lemma D_65814 : decode_any W_65814 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65818 : bv 32 := 0x00168693.
Lemma F_65818 : fetch_word AsanUbsan.M.loaded_segments (0x6566c : word) = Some W_65818.
Proof. vm_refl. Qed.
Lemma D_65818 : decode_any W_65818 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6581c : bv 32 := 0x00e78023.
Lemma F_6581c : fetch_word AsanUbsan.M.loaded_segments (0x65670 : word) = Some W_6581c.
Proof. vm_refl. Qed.
Lemma D_6581c : decode_any W_6581c = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65820 : bv 32 := 0xfed614e3.
Lemma F_65820 : fetch_word AsanUbsan.M.loaded_segments (0x65674 : word) = Some W_65820.
Proof. vm_refl. Qed.
Lemma D_65820 : decode_any W_65820 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65824 : bv 32 := 0x00060693.
Lemma F_65824 : fetch_word AsanUbsan.M.loaded_segments (0x65678 : word) = Some W_65824.
Proof. vm_refl. Qed.
Lemma D_65824 : decode_any W_65824 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65828 : bv 32 := 0x00d505b3.
Lemma F_65828 : fetch_word AsanUbsan.M.loaded_segments (0x6567c : word) = Some W_65828.
Proof. vm_refl. Qed.
Lemma D_65828 : decode_any W_65828 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6582c : bv 32 := 0x40d6073b.
Lemma F_6582c : fetch_word AsanUbsan.M.loaded_segments (0x65680 : word) = Some W_6582c.
Proof. vm_refl. Qed.
Lemma D_6582c : decode_any W_6582c = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65830 : bv 32 := 0x00b76733.
Lemma F_65830 : fetch_word AsanUbsan.M.loaded_segments (0x65684 : word) = Some W_65830.
Proof. vm_refl. Qed.
Lemma D_65830 : decode_any W_65830 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65834 : bv 32 := 0x00f77713.
Lemma F_65834 : fetch_word AsanUbsan.M.loaded_segments (0x65688 : word) = Some W_65834.
Proof. vm_refl. Qed.
Lemma D_65834 : decode_any W_65834 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65838 : bv 32 := 0x00070e63.
Lemma F_65838 : fetch_word AsanUbsan.M.loaded_segments (0x6568c : word) = Some W_65838.
Proof. vm_refl. Qed.
Lemma D_65838 : decode_any W_65838 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6583c : bv 32 := 0x02d60863.
Lemma F_6583c : fetch_word AsanUbsan.M.loaded_segments (0x65690 : word) = Some W_6583c.
Proof. vm_refl. Qed.
Lemma D_6583c : decode_any W_6583c = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65840 : bv 32 := 0x00c50633.
Lemma F_65840 : fetch_word AsanUbsan.M.loaded_segments (0x65694 : word) = Some W_65840.
Proof. vm_refl. Qed.
Lemma D_65840 : decode_any W_65840 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65844 : bv 32 := 0x00058023.
Lemma F_65844 : fetch_word AsanUbsan.M.loaded_segments (0x65698 : word) = Some W_65844.
Proof. vm_refl. Qed.
Lemma D_65844 : decode_any W_65844 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65848 : bv 32 := 0x00158593.
Lemma F_65848 : fetch_word AsanUbsan.M.loaded_segments (0x6569c : word) = Some W_65848.
Proof. vm_refl. Qed.
Lemma D_65848 : decode_any W_65848 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6584c : bv 32 := 0xfec59ce3.
Lemma F_6584c : fetch_word AsanUbsan.M.loaded_segments (0x656a0 : word) = Some W_6584c.
Proof. vm_refl. Qed.
Lemma D_6584c : decode_any W_6584c = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65850 : bv 32 := 0x01c0006f.
Lemma F_65850 : fetch_word AsanUbsan.M.loaded_segments (0x656a4 : word) = Some W_65850.
Proof. vm_refl. Qed.
Lemma D_65850 : decode_any W_65850 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65854 : bv 32 := 0x00d60c63.
Lemma F_65854 : fetch_word AsanUbsan.M.loaded_segments (0x656a8 : word) = Some W_65854.
Proof. vm_refl. Qed.
Lemma D_65854 : decode_any W_65854 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65858 : bv 32 := 0x00c50633.
Lemma F_65858 : fetch_word AsanUbsan.M.loaded_segments (0x656ac : word) = Some W_65858.
Proof. vm_refl. Qed.
Lemma D_65858 : decode_any W_65858 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6585c : bv 32 := 0x0005b023.
Lemma F_6585c : fetch_word AsanUbsan.M.loaded_segments (0x656b0 : word) = Some W_6585c.
Proof. vm_refl. Qed.
Lemma D_6585c : decode_any W_6585c = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65860 : bv 32 := 0x0005b423.
Lemma F_65860 : fetch_word AsanUbsan.M.loaded_segments (0x656b4 : word) = Some W_65860.
Proof. vm_refl. Qed.
Lemma D_65860 : decode_any W_65860 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65864 : bv 32 := 0x01058593.
Lemma F_65864 : fetch_word AsanUbsan.M.loaded_segments (0x656b8 : word) = Some W_65864.
Proof. vm_refl. Qed.
Lemma D_65864 : decode_any W_65864 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65868 : bv 32 := 0xfec5eae3.
Lemma F_65868 : fetch_word AsanUbsan.M.loaded_segments (0x656bc : word) = Some W_65868.
Proof. vm_refl. Qed.
Lemma D_65868 : decode_any W_65868 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6586c : bv 32 := 0x00008067.
Lemma F_6586c : fetch_word AsanUbsan.M.loaded_segments (0x656c0 : word) = Some W_6586c.
Proof. vm_refl. Qed.
Lemma D_6586c : decode_any W_6586c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_526dc : bv 32 := 0x00200613.
Lemma F_526dc : fetch_word AsanUbsan.M.loaded_segments (0x52530 : word) = Some W_526dc.
Proof. vm_refl. Qed.
Lemma D_526dc : decode_any W_526dc = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526e0 : bv 32 := 0x14c5ea63.
Lemma F_526e0 : fetch_word AsanUbsan.M.loaded_segments (0x52534 : word) = Some W_526e0.
Proof. vm_refl. Qed.
Lemma D_526e0 : decode_any W_526e0 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526e4 : bv 32 := 0x00100613.
Lemma F_526e4 : fetch_word AsanUbsan.M.loaded_segments (0x52538 : word) = Some W_526e4.
Proof. vm_refl. Qed.
Lemma D_526e4 : decode_any W_526e4 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526e8 : bv 32 := 0x00100693.
Lemma F_526e8 : fetch_word AsanUbsan.M.loaded_segments (0x5253c : word) = Some W_526e8.
Proof. vm_refl. Qed.
Lemma D_526e8 : decode_any W_526e8 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526ec : bv 32 := 0x00c0006f.
Lemma F_526ec : fetch_word AsanUbsan.M.loaded_segments (0x52540 : word) = Some W_526ec.
Proof. vm_refl. Qed.
Lemma D_526ec : decode_any W_526ec = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526f0 : bv 32 := 0x00160613.
Lemma F_526f0 : fetch_word AsanUbsan.M.loaded_segments (0x52544 : word) = Some W_526f0.
Proof. vm_refl. Qed.
Lemma D_526f0 : decode_any W_526f0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526f4 : bv 32 := 0x12b60c63.
Lemma F_526f4 : fetch_word AsanUbsan.M.loaded_segments (0x52548 : word) = Some W_526f4.
Proof. vm_refl. Qed.
Lemma D_526f4 : decode_any W_526f4 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526f8 : bv 32 := 0x00461713.
Lemma F_526f8 : fetch_word AsanUbsan.M.loaded_segments (0x5254c : word) = Some W_526f8.
Proof. vm_refl. Qed.
Lemma D_526f8 : decode_any W_526f8 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_526fc : bv 32 := 0x00e50733.
Lemma F_526fc : fetch_word AsanUbsan.M.loaded_segments (0x52550 : word) = Some W_526fc.
Proof. vm_refl. Qed.
Lemma D_526fc : decode_any W_526fc = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52700 : bv 32 := 0x00072703.
Lemma F_52700 : fetch_word AsanUbsan.M.loaded_segments (0x52554 : word) = Some W_52700.
Proof. vm_refl. Qed.
Lemma D_52700 : decode_any W_52700 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52704 : bv 32 := 0x00060893.
Lemma F_52704 : fetch_word AsanUbsan.M.loaded_segments (0x52558 : word) = Some W_52704.
Proof. vm_refl. Qed.
Lemma D_52704 : decode_any W_52704 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52708 : bv 32 := 0xfff88793.
Lemma F_52708 : fetch_word AsanUbsan.M.loaded_segments (0x5255c : word) = Some W_52708.
Proof. vm_refl. Qed.
Lemma D_52708 : decode_any W_52708 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5270c : bv 32 := 0x0017d813.
Lemma F_5270c : fetch_word AsanUbsan.M.loaded_segments (0x52560 : word) = Some W_5270c.
Proof. vm_refl. Qed.
Lemma D_5270c : decode_any W_5270c = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52710 : bv 32 := 0x00481293.
Lemma F_52710 : fetch_word AsanUbsan.M.loaded_segments (0x52564 : word) = Some W_52710.
Proof. vm_refl. Qed.
Lemma D_52710 : decode_any W_52710 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52714 : bv 32 := 0x005502b3.
Lemma F_52714 : fetch_word AsanUbsan.M.loaded_segments (0x52568 : word) = Some W_52714.
Proof. vm_refl. Qed.
Lemma D_52714 : decode_any W_52714 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52718 : bv 32 := 0x0002a303.
Lemma F_52718 : fetch_word AsanUbsan.M.loaded_segments (0x5256c : word) = Some W_52718.
Proof. vm_refl. Qed.
Lemma D_52718 : decode_any W_52718 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5271c : bv 32 := 0xfce37ae3.
Lemma F_5271c : fetch_word AsanUbsan.M.loaded_segments (0x52570 : word) = Some W_5271c.
Proof. vm_refl. Qed.
Lemma D_5271c : decode_any W_5271c = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52720 : bv 32 := 0x0002b303.
Lemma F_52720 : fetch_word AsanUbsan.M.loaded_segments (0x52574 : word) = Some W_52720.
Proof. vm_refl. Qed.
Lemma D_52720 : decode_any W_52720 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52724 : bv 32 := 0x00489893.
Lemma F_52724 : fetch_word AsanUbsan.M.loaded_segments (0x52578 : word) = Some W_52724.
Proof. vm_refl. Qed.
Lemma D_52724 : decode_any W_52724 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52728 : bv 32 := 0x011508b3.
Lemma F_52728 : fetch_word AsanUbsan.M.loaded_segments (0x5257c : word) = Some W_52728.
Proof. vm_refl. Qed.
Lemma D_52728 : decode_any W_52728 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5272c : bv 32 := 0x0048a383.
Lemma F_5272c : fetch_word AsanUbsan.M.loaded_segments (0x52580 : word) = Some W_5272c.
Proof. vm_refl. Qed.
Lemma D_5272c : decode_any W_5272c = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52730 : bv 32 := 0x0068b023.
Lemma F_52730 : fetch_word AsanUbsan.M.loaded_segments (0x52584 : word) = Some W_52730.
Proof. vm_refl. Qed.
Lemma D_52730 : decode_any W_52730 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52734 : bv 32 := 0x0082b303.
Lemma F_52734 : fetch_word AsanUbsan.M.loaded_segments (0x52588 : word) = Some W_52734.
Proof. vm_refl. Qed.
Lemma D_52734 : decode_any W_52734 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52738 : bv 32 := 0x0088be03.
Lemma F_52738 : fetch_word AsanUbsan.M.loaded_segments (0x5258c : word) = Some W_52738.
Proof. vm_refl. Qed.
Lemma D_52738 : decode_any W_52738 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5273c : bv 32 := 0x0068b423.
Lemma F_5273c : fetch_word AsanUbsan.M.loaded_segments (0x52590 : word) = Some W_5273c.
Proof. vm_refl. Qed.
Lemma D_5273c : decode_any W_5273c = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52740 : bv 32 := 0x00e2a023.
Lemma F_52740 : fetch_word AsanUbsan.M.loaded_segments (0x52594 : word) = Some W_52740.
Proof. vm_refl. Qed.
Lemma D_52740 : decode_any W_52740 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52744 : bv 32 := 0x0072a223.
Lemma F_52744 : fetch_word AsanUbsan.M.loaded_segments (0x52598 : word) = Some W_52744.
Proof. vm_refl. Qed.
Lemma D_52744 : decode_any W_52744 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52748 : bv 32 := 0x01c2b423.
Lemma F_52748 : fetch_word AsanUbsan.M.loaded_segments (0x5259c : word) = Some W_52748.
Proof. vm_refl. Qed.
Lemma D_52748 : decode_any W_52748 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5274c : bv 32 := 0x00080893.
Lemma F_5274c : fetch_word AsanUbsan.M.loaded_segments (0x525a0 : word) = Some W_5274c.
Proof. vm_refl. Qed.
Lemma D_5274c : decode_any W_5274c = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52750 : bv 32 := 0xfaf6ece3.
Lemma F_52750 : fetch_word AsanUbsan.M.loaded_segments (0x525a4 : word) = Some W_52750.
Proof. vm_refl. Qed.
Lemma D_52750 : decode_any W_52750 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52754 : bv 32 := 0xf9dff06f.
Lemma F_52754 : fetch_word AsanUbsan.M.loaded_segments (0x525a8 : word) = Some W_52754.
Proof. vm_refl. Qed.
Lemma D_52754 : decode_any W_52754 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52758 : bv 32 := 0x00000613.
Lemma F_52758 : fetch_word AsanUbsan.M.loaded_segments (0x525ac : word) = Some W_52758.
Proof. vm_refl. Qed.
Lemma D_52758 : decode_any W_52758 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5275c : bv 32 := 0x00459693.
Lemma F_5275c : fetch_word AsanUbsan.M.loaded_segments (0x525b0 : word) = Some W_5275c.
Proof. vm_refl. Qed.
Lemma D_5275c : decode_any W_5275c = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52760 : bv 32 := 0x00d506b3.
Lemma F_52760 : fetch_word AsanUbsan.M.loaded_segments (0x525b4 : word) = Some W_52760.
Proof. vm_refl. Qed.
Lemma D_52760 : decode_any W_52760 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52764 : bv 32 := 0x0006b703.
Lemma F_52764 : fetch_word AsanUbsan.M.loaded_segments (0x525b8 : word) = Some W_52764.
Proof. vm_refl. Qed.
Lemma D_52764 : decode_any W_52764 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52768 : bv 32 := 0x0086b783.
Lemma F_52768 : fetch_word AsanUbsan.M.loaded_segments (0x525bc : word) = Some W_52768.
Proof. vm_refl. Qed.
Lemma D_52768 : decode_any W_52768 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5276c : bv 32 := 0x00053803.
Lemma F_5276c : fetch_word AsanUbsan.M.loaded_segments (0x525c0 : word) = Some W_5276c.
Proof. vm_refl. Qed.
Lemma D_5276c : decode_any W_5276c = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52770 : bv 32 := 0x00853883.
Lemma F_52770 : fetch_word AsanUbsan.M.loaded_segments (0x525c4 : word) = Some W_52770.
Proof. vm_refl. Qed.
Lemma D_52770 : decode_any W_52770 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52774 : bv 32 := 0x00e53023.
Lemma F_52774 : fetch_word AsanUbsan.M.loaded_segments (0x525c8 : word) = Some W_52774.
Proof. vm_refl. Qed.
Lemma D_52774 : decode_any W_52774 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52778 : bv 32 := 0x00f53423.
Lemma F_52778 : fetch_word AsanUbsan.M.loaded_segments (0x525cc : word) = Some W_52778.
Proof. vm_refl. Qed.
Lemma D_52778 : decode_any W_52778 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5277c : bv 32 := 0x0106b023.
Lemma F_5277c : fetch_word AsanUbsan.M.loaded_segments (0x525d0 : word) = Some W_5277c.
Proof. vm_refl. Qed.
Lemma D_5277c : decode_any W_5277c = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52780 : bv 32 := 0x0116b423.
Lemma F_52780 : fetch_word AsanUbsan.M.loaded_segments (0x525d4 : word) = Some W_52780.
Proof. vm_refl. Qed.
Lemma D_52780 : decode_any W_52780 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52784 : bv 32 := 0x00000693.
Lemma F_52784 : fetch_word AsanUbsan.M.loaded_segments (0x525d8 : word) = Some W_52784.
Proof. vm_refl. Qed.
Lemma D_52784 : decode_any W_52784 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52788 : bv 32 := 0x00161793.
Lemma F_52788 : fetch_word AsanUbsan.M.loaded_segments (0x525dc : word) = Some W_52788.
Proof. vm_refl. Qed.
Lemma D_52788 : decode_any W_52788 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5278c : bv 32 := 0x00178813.
Lemma F_5278c : fetch_word AsanUbsan.M.loaded_segments (0x525e0 : word) = Some W_5278c.
Proof. vm_refl. Qed.
Lemma D_5278c : decode_any W_5278c = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52790 : bv 32 := 0x00461713.
Lemma F_52790 : fetch_word AsanUbsan.M.loaded_segments (0x525e4 : word) = Some W_52790.
Proof. vm_refl. Qed.
Lemma D_52790 : decode_any W_52790 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52794 : bv 32 := 0x00b86a63.
Lemma F_52794 : fetch_word AsanUbsan.M.loaded_segments (0x525e8 : word) = Some W_52794.
Proof. vm_refl. Qed.
Lemma D_52794 : decode_any W_52794 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52798 : bv 32 := 0x00278793.
Lemma F_52798 : fetch_word AsanUbsan.M.loaded_segments (0x525ec : word) = Some W_52798.
Proof. vm_refl. Qed.
Lemma D_52798 : decode_any W_52798 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5279c : bv 32 := 0x02b7ea63.
Lemma F_5279c : fetch_word AsanUbsan.M.loaded_segments (0x525f0 : word) = Some W_5279c.
Proof. vm_refl. Qed.
Lemma D_5279c : decode_any W_5279c = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527a0 : bv 32 := 0x04c69c63.
Lemma F_527a0 : fetch_word AsanUbsan.M.loaded_segments (0x525f4 : word) = Some W_527a0.
Proof. vm_refl. Qed.
Lemma D_527a0 : decode_any W_527a0 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527a4 : bv 32 := 0x0880006f.
Lemma F_527a4 : fetch_word AsanUbsan.M.loaded_segments (0x525f8 : word) = Some W_527a4.
Proof. vm_refl. Qed.
Lemma D_527a4 : decode_any W_527a4 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527a8 : bv 32 := 0x00e506b3.
Lemma F_527a8 : fetch_word AsanUbsan.M.loaded_segments (0x525fc : word) = Some W_527a8.
Proof. vm_refl. Qed.
Lemma D_527a8 : decode_any W_527a8 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527ac : bv 32 := 0x00481893.
Lemma F_527ac : fetch_word AsanUbsan.M.loaded_segments (0x52600 : word) = Some W_527ac.
Proof. vm_refl. Qed.
Lemma D_527ac : decode_any W_527ac = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527b0 : bv 32 := 0x011508b3.
Lemma F_527b0 : fetch_word AsanUbsan.M.loaded_segments (0x52604 : word) = Some W_527b0.
Proof. vm_refl. Qed.
Lemma D_527b0 : decode_any W_527b0 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527b4 : bv 32 := 0x0006a683.
Lemma F_527b4 : fetch_word AsanUbsan.M.loaded_segments (0x52608 : word) = Some W_527b4.
Proof. vm_refl. Qed.
Lemma D_527b4 : decode_any W_527b4 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527b8 : bv 32 := 0x0008a883.
Lemma F_527b8 : fetch_word AsanUbsan.M.loaded_segments (0x5260c : word) = Some W_527b8.
Proof. vm_refl. Qed.
Lemma D_527b8 : decode_any W_527b8 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527bc : bv 32 := 0x0116e463.
Lemma F_527bc : fetch_word AsanUbsan.M.loaded_segments (0x52610 : word) = Some W_527bc.
Proof. vm_refl. Qed.
Lemma D_527bc : decode_any W_527bc = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527c0 : bv 32 := 0x00060813.
Lemma F_527c0 : fetch_word AsanUbsan.M.loaded_segments (0x52614 : word) = Some W_527c0.
Proof. vm_refl. Qed.
Lemma D_527c0 : decode_any W_527c0 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527c4 : bv 32 := 0x00080693.
Lemma F_527c4 : fetch_word AsanUbsan.M.loaded_segments (0x52618 : word) = Some W_527c4.
Proof. vm_refl. Qed.
Lemma D_527c4 : decode_any W_527c4 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527c8 : bv 32 := 0x00278793.
Lemma F_527c8 : fetch_word AsanUbsan.M.loaded_segments (0x5261c : word) = Some W_527c8.
Proof. vm_refl. Qed.
Lemma D_527c8 : decode_any W_527c8 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527cc : bv 32 := 0xfcb7fae3.
Lemma F_527cc : fetch_word AsanUbsan.M.loaded_segments (0x52620 : word) = Some W_527cc.
Proof. vm_refl. Qed.
Lemma D_527cc : decode_any W_527cc = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527d0 : bv 32 := 0x00469813.
Lemma F_527d0 : fetch_word AsanUbsan.M.loaded_segments (0x52624 : word) = Some W_527d0.
Proof. vm_refl. Qed.
Lemma D_527d0 : decode_any W_527d0 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527d4 : bv 32 := 0x00479893.
Lemma F_527d4 : fetch_word AsanUbsan.M.loaded_segments (0x52628 : word) = Some W_527d4.
Proof. vm_refl. Qed.
Lemma D_527d4 : decode_any W_527d4 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527d8 : bv 32 := 0x01050833.
Lemma F_527d8 : fetch_word AsanUbsan.M.loaded_segments (0x5262c : word) = Some W_527d8.
Proof. vm_refl. Qed.
Lemma D_527d8 : decode_any W_527d8 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527dc : bv 32 := 0x011508b3.
Lemma F_527dc : fetch_word AsanUbsan.M.loaded_segments (0x52630 : word) = Some W_527dc.
Proof. vm_refl. Qed.
Lemma D_527dc : decode_any W_527dc = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527e0 : bv 32 := 0x00082803.
Lemma F_527e0 : fetch_word AsanUbsan.M.loaded_segments (0x52634 : word) = Some W_527e0.
Proof. vm_refl. Qed.
Lemma D_527e0 : decode_any W_527e0 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527e4 : bv 32 := 0x0008a883.
Lemma F_527e4 : fetch_word AsanUbsan.M.loaded_segments (0x52638 : word) = Some W_527e4.
Proof. vm_refl. Qed.
Lemma D_527e4 : decode_any W_527e4 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527e8 : bv 32 := 0x01186463.
Lemma F_527e8 : fetch_word AsanUbsan.M.loaded_segments (0x5263c : word) = Some W_527e8.
Proof. vm_refl. Qed.
Lemma D_527e8 : decode_any W_527e8 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527ec : bv 32 := 0x00068793.
Lemma F_527ec : fetch_word AsanUbsan.M.loaded_segments (0x52640 : word) = Some W_527ec.
Proof. vm_refl. Qed.
Lemma D_527ec : decode_any W_527ec = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527f0 : bv 32 := 0x00078693.
Lemma F_527f0 : fetch_word AsanUbsan.M.loaded_segments (0x52644 : word) = Some W_527f0.
Proof. vm_refl. Qed.
Lemma D_527f0 : decode_any W_527f0 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527f4 : bv 32 := 0x02c78c63.
Lemma F_527f4 : fetch_word AsanUbsan.M.loaded_segments (0x52648 : word) = Some W_527f4.
Proof. vm_refl. Qed.
Lemma D_527f4 : decode_any W_527f4 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527f8 : bv 32 := 0x00469613.
Lemma F_527f8 : fetch_word AsanUbsan.M.loaded_segments (0x5264c : word) = Some W_527f8.
Proof. vm_refl. Qed.
Lemma D_527f8 : decode_any W_527f8 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_527fc : bv 32 := 0x00c50633.
Lemma F_527fc : fetch_word AsanUbsan.M.loaded_segments (0x52650 : word) = Some W_527fc.
Proof. vm_refl. Qed.
Lemma D_527fc : decode_any W_527fc = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52800 : bv 32 := 0x00063783.
Lemma F_52800 : fetch_word AsanUbsan.M.loaded_segments (0x52654 : word) = Some W_52800.
Proof. vm_refl. Qed.
Lemma D_52800 : decode_any W_52800 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52804 : bv 32 := 0x00e50733.
Lemma F_52804 : fetch_word AsanUbsan.M.loaded_segments (0x52658 : word) = Some W_52804.
Proof. vm_refl. Qed.
Lemma D_52804 : decode_any W_52804 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52808 : bv 32 := 0x00073803.
Lemma F_52808 : fetch_word AsanUbsan.M.loaded_segments (0x5265c : word) = Some W_52808.
Proof. vm_refl. Qed.
Lemma D_52808 : decode_any W_52808 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5280c : bv 32 := 0x00873883.
Lemma F_5280c : fetch_word AsanUbsan.M.loaded_segments (0x52660 : word) = Some W_5280c.
Proof. vm_refl. Qed.
Lemma D_5280c : decode_any W_5280c = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52810 : bv 32 := 0x00f73023.
Lemma F_52810 : fetch_word AsanUbsan.M.loaded_segments (0x52664 : word) = Some W_52810.
Proof. vm_refl. Qed.
Lemma D_52810 : decode_any W_52810 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52814 : bv 32 := 0x00863783.
Lemma F_52814 : fetch_word AsanUbsan.M.loaded_segments (0x52668 : word) = Some W_52814.
Proof. vm_refl. Qed.
Lemma D_52814 : decode_any W_52814 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52818 : bv 32 := 0x00f73423.
Lemma F_52818 : fetch_word AsanUbsan.M.loaded_segments (0x5266c : word) = Some W_52818.
Proof. vm_refl. Qed.
Lemma D_52818 : decode_any W_52818 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5281c : bv 32 := 0x01063023.
Lemma F_5281c : fetch_word AsanUbsan.M.loaded_segments (0x52670 : word) = Some W_5281c.
Proof. vm_refl. Qed.
Lemma D_5281c : decode_any W_5281c = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52820 : bv 32 := 0x01163423.
Lemma F_52820 : fetch_word AsanUbsan.M.loaded_segments (0x52674 : word) = Some W_52820.
Proof. vm_refl. Qed.
Lemma D_52820 : decode_any W_52820 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52824 : bv 32 := 0x00068613.
Lemma F_52824 : fetch_word AsanUbsan.M.loaded_segments (0x52678 : word) = Some W_52824.
Proof. vm_refl. Qed.
Lemma D_52824 : decode_any W_52824 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52828 : bv 32 := 0xf6b6e0e3.
Lemma F_52828 : fetch_word AsanUbsan.M.loaded_segments (0x5267c : word) = Some W_52828.
Proof. vm_refl. Qed.
Lemma D_52828 : decode_any W_52828 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5282c : bv 32 := 0xfff58593.
Lemma F_5282c : fetch_word AsanUbsan.M.loaded_segments (0x52680 : word) = Some W_5282c.
Proof. vm_refl. Qed.
Lemma D_5282c : decode_any W_5282c = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52830 : bv 32 := 0xf20594e3.
Lemma F_52830 : fetch_word AsanUbsan.M.loaded_segments (0x52684 : word) = Some W_52830.
Proof. vm_refl. Qed.
Lemma D_52830 : decode_any W_52830 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52834 : bv 32 := 0x00008067.
Lemma F_52834 : fetch_word AsanUbsan.M.loaded_segments (0x52688 : word) = Some W_52834.
Proof. vm_refl. Qed.
Lemma D_52834 : decode_any W_52834 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
