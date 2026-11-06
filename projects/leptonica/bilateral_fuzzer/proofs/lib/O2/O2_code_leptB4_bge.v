(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_2e670 : bv 32 := 0x02812783.
Lemma F_2e670 : fetch_word Plain.M.loaded_segments (0x2e6c8 : word) = Some W_2e670.
Proof. vm_refl. Qed.
Lemma D_2e670 : decode_any W_2e670 = Some (Load SZ4 true 15 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e674 : bv 32 := 0x28f05a63.
Lemma F_2e674 : fetch_word Plain.M.loaded_segments (0x2e6cc : word) = Some W_2e674.
Proof. vm_refl. Qed.
Lemma D_2e674 : decode_any W_2e674 = Some (Branch BC_GE 0 15 660, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e678 : bv 32 := 0x000a8593.
Lemma F_2e678 : fetch_word Plain.M.loaded_segments (0x2e6d0 : word) = Some W_2e678.
Proof. vm_refl. Qed.
Lemma D_2e678 : decode_any W_2e678 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e67c : bv 32 := 0x00000613.
Lemma F_2e67c : fetch_word Plain.M.loaded_segments (0x2e6d4 : word) = Some W_2e67c.
Proof. vm_refl. Qed.
Lemma D_2e67c : decode_any W_2e67c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e680 : bv 32 := 0x02c12283.
Lemma F_2e680 : fetch_word Plain.M.loaded_segments (0x2e6d8 : word) = Some W_2e680.
Proof. vm_refl. Qed.
Lemma D_2e680 : decode_any W_2e680 = Some (Load SZ4 true 5 2 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e684 : bv 32 := 0x00291693.
Lemma F_2e684 : fetch_word Plain.M.loaded_segments (0x2e6dc : word) = Some W_2e684.
Proof. vm_refl. Qed.
Lemma D_2e684 : decode_any W_2e684 = Some (ShiftImm ALU_SLL 13 18 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e688 : bv 32 := 0xf00007d3.
Lemma F_2e688 : fetch_word Plain.M.loaded_segments (0x2e6e0 : word) = Some W_2e688.
Proof. vm_refl. Qed.
Lemma D_2e688 : decode_any W_2e688 = Some (Fmv FMV_F_X FMT_S 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e68c : bv 32 := 0x00040713.
Lemma F_2e68c : fetch_word Plain.M.loaded_segments (0x2e6e4 : word) = Some W_2e68c.
Proof. vm_refl. Qed.
Lemma D_2e68c : decode_any W_2e68c = Some (OpImm ALU_ADD 14 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e690 : bv 32 := 0x1180006f.
Lemma F_2e690 : fetch_word Plain.M.loaded_segments (0x2e6e8 : word) = Some W_2e690.
Proof. vm_refl. Qed.
Lemma D_2e690 : decode_any W_2e690 = Some (Jal 0 280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e798 : bv 32 := 0x02812783.
Lemma F_2e798 : fetch_word Plain.M.loaded_segments (0x2e7f0 : word) = Some W_2e798.
Proof. vm_refl. Qed.
Lemma D_2e798 : decode_any W_2e798 = Some (Load SZ4 true 15 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e79c : bv 32 := 0x00160613.
Lemma F_2e79c : fetch_word Plain.M.loaded_segments (0x2e7f4 : word) = Some W_2e79c.
Proof. vm_refl. Qed.
Lemma D_2e79c : decode_any W_2e79c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7a0 : bv 32 := 0x00d70733.
Lemma F_2e7a0 : fetch_word Plain.M.loaded_segments (0x2e7f8 : word) = Some W_2e7a0.
Proof. vm_refl. Qed.
Lemma D_2e7a0 : decode_any W_2e7a0 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7a4 : bv 32 := 0x16f65263.
Lemma F_2e7a4 : fetch_word Plain.M.loaded_segments (0x2e7fc : word) = Some W_2e7a4.
Proof. vm_refl. Qed.
Lemma D_2e7a4 : decode_any W_2e7a4 = Some (Branch BC_GE 12 15 356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7a8 : bv 32 := 0xfe505ae3.
Lemma F_2e7a8 : fetch_word Plain.M.loaded_segments (0x2e800 : word) = Some W_2e7a8.
Proof. vm_refl. Qed.
Lemma D_2e7a8 : decode_any W_2e7a8 = Some (Branch BC_GE 0 5 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7ac : bv 32 := 0x00000793.
Lemma F_2e7ac : fetch_word Plain.M.loaded_segments (0x2e804 : word) = Some W_2e7ac.
Proof. vm_refl. Qed.
Lemma D_2e7ac : decode_any W_2e7ac = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7b0 : bv 32 := 0x02a60833.
Lemma F_2e7b0 : fetch_word Plain.M.loaded_segments (0x2e808 : word) = Some W_2e7b0.
Proof. vm_refl. Qed.
Lemma D_2e7b0 : decode_any W_2e7b0 = Some (Mul M_MUL 16 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7b4 : bv 32 := 0x00281813.
Lemma F_2e7b4 : fetch_word Plain.M.loaded_segments (0x2e80c : word) = Some W_2e7b4.
Proof. vm_refl. Qed.
Lemma D_2e7b4 : decode_any W_2e7b4 = Some (ShiftImm ALU_SLL 16 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7b8 : bv 32 := 0x01048833.
Lemma F_2e7b8 : fetch_word Plain.M.loaded_segments (0x2e810 : word) = Some W_2e7b8.
Proof. vm_refl. Qed.
Lemma D_2e7b8 : decode_any W_2e7b8 = Some (Op ALU_ADD 16 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7bc : bv 32 := 0x00070893.
Lemma F_2e7bc : fetch_word Plain.M.loaded_segments (0x2e814 : word) = Some W_2e7bc.
Proof. vm_refl. Qed.
Lemma D_2e7bc : decode_any W_2e7bc = Some (OpImm ALU_ADD 17 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7c0 : bv 32 := 0x0380006f.
Lemma F_2e7c0 : fetch_word Plain.M.loaded_segments (0x2e818 : word) = Some W_2e7c0.
Proof. vm_refl. Qed.
Lemma D_2e7c0 : decode_any W_2e7c0 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7c4 : bv 32 := 0xfffe4297.
Lemma F_2e7c4 : fetch_word Plain.M.loaded_segments (0x2e81c : word) = Some W_2e7c4.
Proof. vm_refl. Qed.
Lemma D_2e7c4 : decode_any W_2e7c4 = Some (Auipc 5 1048548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7c8 : bv 32 := 0xd6c2b607.
Lemma F_2e7c8 : fetch_word Plain.M.loaded_segments (0x2e820 : word) = Some W_2e7c8.
Proof. vm_refl. Qed.
Lemma D_2e7c8 : decode_any W_2e7c8 = Some (FLoad FMT_D 12 5 3436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7cc : bv 32 := 0x18e6f753.
Lemma F_2e7cc : fetch_word Plain.M.loaded_segments (0x2e824 : word) = Some W_2e7cc.
Proof. vm_refl. Qed.
Lemma D_2e7cc : decode_any W_2e7cc = Some (Fari F_DIV FMT_S 14 13 14 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7d0 : bv 32 := 0x42070753.
Lemma F_2e7d0 : fetch_word Plain.M.loaded_segments (0x2e828 : word) = Some W_2e7d0.
Proof. vm_refl. Qed.
Lemma D_2e7d0 : decode_any W_2e7d0 = Some (Fcvt FC_D FC_S 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7d4 : bv 32 := 0x02c77753.
Lemma F_2e7d4 : fetch_word Plain.M.loaded_segments (0x2e82c : word) = Some W_2e7d4.
Proof. vm_refl. Qed.
Lemma D_2e7d4 : decode_any W_2e7d4 = Some (Fari F_ADD FMT_D 14 14 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7d8 : bv 32 := 0xc2071353.
Lemma F_2e7d8 : fetch_word Plain.M.loaded_segments (0x2e830 : word) = Some W_2e7d8.
Proof. vm_refl. Qed.
Lemma D_2e7d8 : decode_any W_2e7d8 = Some (Fcvt FC_W FC_D 6 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7dc : bv 32 := 0x00f802b3.
Lemma F_2e7dc : fetch_word Plain.M.loaded_segments (0x2e834 : word) = Some W_2e7dc.
Proof. vm_refl. Qed.
Lemma D_2e7dc : decode_any W_2e7dc = Some (Op ALU_ADD 5 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7e0 : bv 32 := 0x0032c293.
Lemma F_2e7e0 : fetch_word Plain.M.loaded_segments (0x2e838 : word) = Some W_2e7e0.
Proof. vm_refl. Qed.
Lemma D_2e7e0 : decode_any W_2e7e0 = Some (OpImm ALU_XOR 5 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7e4 : bv 32 := 0x00628023.
Lemma F_2e7e4 : fetch_word Plain.M.loaded_segments (0x2e83c : word) = Some W_2e7e4.
Proof. vm_refl. Qed.
Lemma D_2e7e4 : decode_any W_2e7e4 = Some (Store SZ1 5 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7e8 : bv 32 := 0x02c12283.
Lemma F_2e7e8 : fetch_word Plain.M.loaded_segments (0x2e840 : word) = Some W_2e7e8.
Proof. vm_refl. Qed.
Lemma D_2e7e8 : decode_any W_2e7e8 = Some (Load SZ4 true 5 2 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7ec : bv 32 := 0x00178793.
Lemma F_2e7ec : fetch_word Plain.M.loaded_segments (0x2e844 : word) = Some W_2e7ec.
Proof. vm_refl. Qed.
Lemma D_2e7ec : decode_any W_2e7ec = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7f0 : bv 32 := 0x00188893.
Lemma F_2e7f0 : fetch_word Plain.M.loaded_segments (0x2e848 : word) = Some W_2e7f0.
Proof. vm_refl. Qed.
Lemma D_2e7f0 : decode_any W_2e7f0 = Some (OpImm ALU_ADD 17 17 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7f4 : bv 32 := 0xfa57d2e3.
Lemma F_2e7f4 : fetch_word Plain.M.loaded_segments (0x2e84c : word) = Some W_2e7f4.
Proof. vm_refl. Qed.
Lemma D_2e7f4 : decode_any W_2e7f4 = Some (Branch BC_GE 15 5 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7f8 : bv 32 := 0x01c12283.
Lemma F_2e7f8 : fetch_word Plain.M.loaded_segments (0x2e850 : word) = Some W_2e7f8.
Proof. vm_refl. Qed.
Lemma D_2e7f8 : decode_any W_2e7f8 = Some (Load SZ4 true 5 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e7fc : bv 32 := 0xfe5050e3.
Lemma F_2e7fc : fetch_word Plain.M.loaded_segments (0x2e854 : word) = Some W_2e7fc.
Proof. vm_refl. Qed.
Lemma D_2e7fc : decode_any W_2e7fc = Some (Branch BC_GE 0 5 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e800 : bv 32 := 0x00000313.
Lemma F_2e800 : fetch_word Plain.M.loaded_segments (0x2e858 : word) = Some W_2e800.
Proof. vm_refl. Qed.
Lemma D_2e800 : decode_any W_2e800 = Some (OpImm ALU_ADD 6 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e804 : bv 32 := 0x01412383.
Lemma F_2e804 : fetch_word Plain.M.loaded_segments (0x2e85c : word) = Some W_2e804.
Proof. vm_refl. Qed.
Lemma D_2e804 : decode_any W_2e804 = Some (Load SZ4 true 7 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e808 : bv 32 := 0x01812e03.
Lemma F_2e808 : fetch_word Plain.M.loaded_segments (0x2e860 : word) = Some W_2e808.
Proof. vm_refl. Qed.
Lemma D_2e808 : decode_any W_2e808 = Some (Load SZ4 true 28 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e80c : bv 32 := 0x02016f03.
Lemma F_2e80c : fetch_word Plain.M.loaded_segments (0x2e864 : word) = Some W_2e80c.
Proof. vm_refl. Qed.
Lemma D_2e80c : decode_any W_2e80c = Some (Load SZ4 false 30 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e810 : bv 32 := 0x00c383b3.
Lemma F_2e810 : fetch_word Plain.M.loaded_segments (0x2e868 : word) = Some W_2e810.
Proof. vm_refl. Qed.
Lemma D_2e810 : decode_any W_2e810 = Some (Op ALU_ADD 7 7 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e814 : bv 32 := 0x00fe0e33.
Lemma F_2e814 : fetch_word Plain.M.loaded_segments (0x2e86c : word) = Some W_2e814.
Proof. vm_refl. Qed.
Lemma D_2e814 : decode_any W_2e814 = Some (Op ALU_ADD 28 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e818 : bv 32 := 0x032383bb.
Lemma F_2e818 : fetch_word Plain.M.loaded_segments (0x2e870 : word) = Some W_2e818.
Proof. vm_refl. Qed.
Lemma D_2e818 : decode_any W_2e818 = Some (Mul32 M_MUL 7 7 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e81c : bv 32 := 0x01c40e33.
Lemma F_2e81c : fetch_word Plain.M.loaded_segments (0x2e874 : word) = Some W_2e81c.
Proof. vm_refl. Qed.
Lemma D_2e81c : decode_any W_2e81c = Some (Op ALU_ADD 28 8 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e820 : bv 32 := 0x00239393.
Lemma F_2e820 : fetch_word Plain.M.loaded_segments (0x2e878 : word) = Some W_2e820.
Proof. vm_refl. Qed.
Lemma D_2e820 : decode_any W_2e820 = Some (ShiftImm ALU_SLL 7 7 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e824 : bv 32 := 0x007e03b3.
Lemma F_2e824 : fetch_word Plain.M.loaded_segments (0x2e87c : word) = Some W_2e824.
Proof. vm_refl. Qed.
Lemma D_2e824 : decode_any W_2e824 = Some (Op ALU_ADD 7 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e828 : bv 32 := 0x0033c393.
Lemma F_2e828 : fetch_word Plain.M.loaded_segments (0x2e880 : word) = Some W_2e828.
Proof. vm_refl. Qed.
Lemma D_2e828 : decode_any W_2e828 = Some (OpImm ALU_XOR 7 7 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e82c : bv 32 := 0x0003c383.
Lemma F_2e82c : fetch_word Plain.M.loaded_segments (0x2e884 : word) = Some W_2e82c.
Proof. vm_refl. Qed.
Lemma D_2e82c : decode_any W_2e82c = Some (Load SZ1 false 7 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e830 : bv 32 := 0x00813e03.
Lemma F_2e830 : fetch_word Plain.M.loaded_segments (0x2e888 : word) = Some W_2e830.
Proof. vm_refl. Qed.
Lemma D_2e830 : decode_any W_2e830 = Some (Load SZ8 true 28 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e834 : bv 32 := 0x000f0e9b.
Lemma F_2e834 : fetch_word Plain.M.loaded_segments (0x2e88c : word) = Some W_2e834.
Proof. vm_refl. Qed.
Lemma D_2e834 : decode_any W_2e834 = Some (OpImm32 29 30 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e838 : bv 32 := 0x01e88f33.
Lemma F_2e838 : fetch_word Plain.M.loaded_segments (0x2e890 : word) = Some W_2e838.
Proof. vm_refl. Qed.
Lemma D_2e838 : decode_any W_2e838 = Some (Op ALU_ADD 30 17 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e83c : bv 32 := 0x00088f93.
Lemma F_2e83c : fetch_word Plain.M.loaded_segments (0x2e894 : word) = Some W_2e83c.
Proof. vm_refl. Qed.
Lemma D_2e83c : decode_any W_2e83c = Some (OpImm ALU_ADD 31 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e840 : bv 32 := 0x20f78753.
Lemma F_2e840 : fetch_word Plain.M.loaded_segments (0x2e898 : word) = Some W_2e840.
Proof. vm_refl. Qed.
Lemma D_2e840 : decode_any W_2e840 = Some (Fsgnj F_SGNJ FMT_S 14 15 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e844 : bv 32 := 0x20f786d3.
Lemma F_2e844 : fetch_word Plain.M.loaded_segments (0x2e89c : word) = Some W_2e844.
Proof. vm_refl. Qed.
Lemma D_2e844 : decode_any W_2e844 = Some (Fsgnj F_SGNJ FMT_S 13 15 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e848 : bv 32 := 0x0100006f.
Lemma F_2e848 : fetch_word Plain.M.loaded_segments (0x2e8a0 : word) = Some W_2e848.
Proof. vm_refl. Qed.
Lemma D_2e848 : decode_any W_2e848 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e84c : bv 32 := 0x00130313.
Lemma F_2e84c : fetch_word Plain.M.loaded_segments (0x2e8a4 : word) = Some W_2e84c.
Proof. vm_refl. Qed.
Lemma D_2e84c : decode_any W_2e84c = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e850 : bv 32 := 0x00df8fb3.
Lemma F_2e850 : fetch_word Plain.M.loaded_segments (0x2e8a8 : word) = Some W_2e850.
Proof. vm_refl. Qed.
Lemma D_2e850 : decode_any W_2e850 = Some (Op ALU_ADD 31 31 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e854 : bv 32 := 0xf65308e3.
Lemma F_2e854 : fetch_word Plain.M.loaded_segments (0x2e8ac : word) = Some W_2e854.
Proof. vm_refl. Qed.
Lemma D_2e854 : decode_any W_2e854 = Some (Branch BC_EQ 6 5 8048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e858 : bv 32 := 0xffd05ae3.
Lemma F_2e858 : fetch_word Plain.M.loaded_segments (0x2e8b0 : word) = Some W_2e858.
Proof. vm_refl. Qed.
Lemma D_2e858 : decode_any W_2e858 = Some (Branch BC_GE 0 29 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e85c : bv 32 := 0x010e3983.
Lemma F_2e85c : fetch_word Plain.M.loaded_segments (0x2e8b4 : word) = Some W_2e85c.
Proof. vm_refl. Qed.
Lemma D_2e85c : decode_any W_2e85c = Some (Load SZ8 true 19 28 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e860 : bv 32 := 0x0105ba83.
Lemma F_2e860 : fetch_word Plain.M.loaded_segments (0x2e8b8 : word) = Some W_2e860.
Proof. vm_refl. Qed.
Lemma D_2e860 : decode_any W_2e860 = Some (Load SZ8 true 21 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e864 : bv 32 := 0x00331b13.
Lemma F_2e864 : fetch_word Plain.M.loaded_segments (0x2e8bc : word) = Some W_2e864.
Proof. vm_refl. Qed.
Lemma D_2e864 : decode_any W_2e864 = Some (ShiftImm ALU_SLL 22 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e868 : bv 32 := 0x016989b3.
Lemma F_2e868 : fetch_word Plain.M.loaded_segments (0x2e8c0 : word) = Some W_2e868.
Proof. vm_refl. Qed.
Lemma D_2e868 : decode_any W_2e868 = Some (Op ALU_ADD 19 19 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e86c : bv 32 := 0x0009b983.
Lemma F_2e86c : fetch_word Plain.M.loaded_segments (0x2e8c4 : word) = Some W_2e86c.
Proof. vm_refl. Qed.
Lemma D_2e86c : decode_any W_2e86c = Some (Load SZ8 true 19 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e870 : bv 32 := 0x000aba83.
Lemma F_2e870 : fetch_word Plain.M.loaded_segments (0x2e8c8 : word) = Some W_2e870.
Proof. vm_refl. Qed.
Lemma D_2e870 : decode_any W_2e870 = Some (Load SZ8 true 21 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e874 : bv 32 := 0x02668b33.
Lemma F_2e874 : fetch_word Plain.M.loaded_segments (0x2e8cc : word) = Some W_2e874.
Proof. vm_refl. Qed.
Lemma D_2e874 : decode_any W_2e874 = Some (Mul M_MUL 22 13 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e878 : bv 32 := 0x016f0b33.
Lemma F_2e878 : fetch_word Plain.M.loaded_segments (0x2e8d0 : word) = Some W_2e878.
Proof. vm_refl. Qed.
Lemma D_2e878 : decode_any W_2e878 = Some (Op ALU_ADD 22 30 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e87c : bv 32 := 0x000f8b93.
Lemma F_2e87c : fetch_word Plain.M.loaded_segments (0x2e8d4 : word) = Some W_2e87c.
Proof. vm_refl. Qed.
Lemma D_2e87c : decode_any W_2e87c = Some (OpImm ALU_ADD 23 31 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e880 : bv 32 := 0x003bcc13.
Lemma F_2e880 : fetch_word Plain.M.loaded_segments (0x2e8d8 : word) = Some W_2e880.
Proof. vm_refl. Qed.
Lemma D_2e880 : decode_any W_2e880 = Some (OpImm ALU_XOR 24 23 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e884 : bv 32 := 0x000c4c03.
Lemma F_2e884 : fetch_word Plain.M.loaded_segments (0x2e8dc : word) = Some W_2e884.
Proof. vm_refl. Qed.
Lemma D_2e884 : decode_any W_2e884 = Some (Load SZ1 false 24 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e888 : bv 32 := 0x0009a607.
Lemma F_2e888 : fetch_word Plain.M.loaded_segments (0x2e8e0 : word) = Some W_2e888.
Proof. vm_refl. Qed.
Lemma D_2e888 : decode_any W_2e888 = Some (FLoad FMT_S 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e88c : bv 32 := 0x41838cb3.
Lemma F_2e88c : fetch_word Plain.M.loaded_segments (0x2e8e4 : word) = Some W_2e88c.
Proof. vm_refl. Qed.
Lemma D_2e88c : decode_any W_2e88c = Some (Op ALU_SUB 25 7 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e890 : bv 32 := 0x43fcdd13.
Lemma F_2e890 : fetch_word Plain.M.loaded_segments (0x2e8e8 : word) = Some W_2e890.
Proof. vm_refl. Qed.
Lemma D_2e890 : decode_any W_2e890 = Some (ShiftImm ALU_SRA 26 25 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e894 : bv 32 := 0x01acccb3.
Lemma F_2e894 : fetch_word Plain.M.loaded_segments (0x2e8ec : word) = Some W_2e894.
Proof. vm_refl. Qed.
Lemma D_2e894 : decode_any W_2e894 = Some (Op ALU_XOR 25 25 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e898 : bv 32 := 0x41ac8cb3.
Lemma F_2e898 : fetch_word Plain.M.loaded_segments (0x2e8f0 : word) = Some W_2e898.
Proof. vm_refl. Qed.
Lemma D_2e898 : decode_any W_2e898 = Some (Op ALU_SUB 25 25 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e89c : bv 32 := 0x002c9c93.
Lemma F_2e89c : fetch_word Plain.M.loaded_segments (0x2e8f4 : word) = Some W_2e89c.
Proof. vm_refl. Qed.
Lemma D_2e89c : decode_any W_2e89c = Some (ShiftImm ALU_SLL 25 25 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e8a0 : bv 32 := 0x019a8cb3.
Lemma F_2e8a0 : fetch_word Plain.M.loaded_segments (0x2e8f8 : word) = Some W_2e8a0.
Proof. vm_refl. Qed.
Lemma D_2e8a0 : decode_any W_2e8a0 = Some (Op ALU_ADD 25 21 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e8a4 : bv 32 := 0x000ca587.
Lemma F_2e8a4 : fetch_word Plain.M.loaded_segments (0x2e8fc : word) = Some W_2e8a4.
Proof. vm_refl. Qed.
Lemma D_2e8a4 : decode_any W_2e8a4 = Some (FLoad FMT_S 11 25 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e8a8 : bv 32 := 0x001b8b93.
Lemma F_2e8a8 : fetch_word Plain.M.loaded_segments (0x2e900 : word) = Some W_2e8a8.
Proof. vm_refl. Qed.
Lemma D_2e8a8 : decode_any W_2e8a8 = Some (OpImm ALU_ADD 23 23 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e8ac : bv 32 := 0x10b67653.
Lemma F_2e8ac : fetch_word Plain.M.loaded_segments (0x2e904 : word) = Some W_2e8ac.
Proof. vm_refl. Qed.
Lemma D_2e8ac : decode_any W_2e8ac = Some (Fari F_MUL FMT_S 12 12 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e8b0 : bv 32 := 0xd01c75d3.
Lemma F_2e8b0 : fetch_word Plain.M.loaded_segments (0x2e908 : word) = Some W_2e8b0.
Proof. vm_refl. Qed.
Lemma D_2e8b0 : decode_any W_2e8b0 = Some (Fcvt FC_S FC_WU 11 24 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e8b4 : bv 32 := 0x00c77753.
Lemma F_2e8b4 : fetch_word Plain.M.loaded_segments (0x2e90c : word) = Some W_2e8b4.
Proof. vm_refl. Qed.
Lemma D_2e8b4 : decode_any W_2e8b4 = Some (Fari F_ADD FMT_S 14 14 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e8b8 : bv 32 := 0x68c5f6c3.
Lemma F_2e8b8 : fetch_word Plain.M.loaded_segments (0x2e910 : word) = Some W_2e8b8.
Proof. vm_refl. Qed.
Lemma D_2e8b8 : decode_any W_2e8b8 = Some (Fma F_MADD FMT_S 13 11 12 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e8bc : bv 32 := 0x00498993.
Lemma F_2e8bc : fetch_word Plain.M.loaded_segments (0x2e914 : word) = Some W_2e8bc.
Proof. vm_refl. Qed.
Lemma D_2e8bc : decode_any W_2e8bc = Some (OpImm ALU_ADD 19 19 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e8c0 : bv 32 := 0xfd6b90e3.
Lemma F_2e8c0 : fetch_word Plain.M.loaded_segments (0x2e918 : word) = Some W_2e8c0.
Proof. vm_refl. Qed.
Lemma D_2e8c0 : decode_any W_2e8c0 = Some (Branch BC_NE 23 22 8128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e8c4 : bv 32 := 0xf89ff06f.
Lemma F_2e8c4 : fetch_word Plain.M.loaded_segments (0x2e91c : word) = Some W_2e8c4.
Proof. vm_refl. Qed.
Lemma D_2e8c4 : decode_any W_2e8c4 = Some (Jal 0 2097032, 4%Z).
Proof. vm_refl. Qed.

