(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_ca5f8 : bv 32 := 0x06060663.
Lemma D_ca5f8 : decode_any W_ca5f8 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca5fc : bv 32 := 0x00000693.
Lemma D_ca5fc : decode_any W_ca5fc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca600 : bv 32 := 0x00d58733.
Lemma D_ca600 : decode_any W_ca600 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca604 : bv 32 := 0x00074703.
Lemma D_ca604 : decode_any W_ca604 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca608 : bv 32 := 0x00070c63.
Lemma D_ca608 : decode_any W_ca608 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca60c : bv 32 := 0x00d507b3.
Lemma D_ca60c : decode_any W_ca60c = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca610 : bv 32 := 0x00168693.
Lemma D_ca610 : decode_any W_ca610 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca614 : bv 32 := 0x00e78023.
Lemma D_ca614 : decode_any W_ca614 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca618 : bv 32 := 0xfed614e3.
Lemma D_ca618 : decode_any W_ca618 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca61c : bv 32 := 0x00060693.
Lemma D_ca61c : decode_any W_ca61c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca620 : bv 32 := 0x00d505b3.
Lemma D_ca620 : decode_any W_ca620 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca624 : bv 32 := 0x40d6073b.
Lemma D_ca624 : decode_any W_ca624 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca628 : bv 32 := 0x00b76733.
Lemma D_ca628 : decode_any W_ca628 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca62c : bv 32 := 0x00f77713.
Lemma D_ca62c : decode_any W_ca62c = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca630 : bv 32 := 0x00070e63.
Lemma D_ca630 : decode_any W_ca630 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca634 : bv 32 := 0x02d60863.
Lemma D_ca634 : decode_any W_ca634 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca638 : bv 32 := 0x00c50633.
Lemma D_ca638 : decode_any W_ca638 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca63c : bv 32 := 0x00058023.
Lemma D_ca63c : decode_any W_ca63c = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca640 : bv 32 := 0x00158593.
Lemma D_ca640 : decode_any W_ca640 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca644 : bv 32 := 0xfec59ce3.
Lemma D_ca644 : decode_any W_ca644 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca648 : bv 32 := 0x01c0006f.
Lemma D_ca648 : decode_any W_ca648 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca64c : bv 32 := 0x00d60c63.
Lemma D_ca64c : decode_any W_ca64c = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca650 : bv 32 := 0x00c50633.
Lemma D_ca650 : decode_any W_ca650 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca654 : bv 32 := 0x0005b023.
Lemma D_ca654 : decode_any W_ca654 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca658 : bv 32 := 0x0005b423.
Lemma D_ca658 : decode_any W_ca658 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca65c : bv 32 := 0x01058593.
Lemma D_ca65c : decode_any W_ca65c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca660 : bv 32 := 0xfec5eae3.
Lemma D_ca660 : decode_any W_ca660 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca664 : bv 32 := 0x00008067.
Lemma D_ca664 : decode_any W_ca664 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.



(* [comment removed for export] *)
Definition W_b6838 : bv 32 := 0x00200613.
Lemma D_b6838 : decode_any W_b6838 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b683c : bv 32 := 0x14c5ea63.
Lemma D_b683c : decode_any W_b683c = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6840 : bv 32 := 0x00100613.
Lemma D_b6840 : decode_any W_b6840 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6844 : bv 32 := 0x00100693.
Lemma D_b6844 : decode_any W_b6844 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6848 : bv 32 := 0x00c0006f.
Lemma D_b6848 : decode_any W_b6848 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b684c : bv 32 := 0x00160613.
Lemma D_b684c : decode_any W_b684c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6850 : bv 32 := 0x12b60c63.
Lemma D_b6850 : decode_any W_b6850 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6854 : bv 32 := 0x00461713.
Lemma D_b6854 : decode_any W_b6854 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6858 : bv 32 := 0x00e50733.
Lemma D_b6858 : decode_any W_b6858 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b685c : bv 32 := 0x00072703.
Lemma D_b685c : decode_any W_b685c = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6860 : bv 32 := 0x00060893.
Lemma D_b6860 : decode_any W_b6860 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6864 : bv 32 := 0xfff88793.
Lemma D_b6864 : decode_any W_b6864 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6868 : bv 32 := 0x0017d813.
Lemma D_b6868 : decode_any W_b6868 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b686c : bv 32 := 0x00481293.
Lemma D_b686c : decode_any W_b686c = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6870 : bv 32 := 0x005502b3.
Lemma D_b6870 : decode_any W_b6870 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6874 : bv 32 := 0x0002a303.
Lemma D_b6874 : decode_any W_b6874 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6878 : bv 32 := 0xfce37ae3.
Lemma D_b6878 : decode_any W_b6878 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b687c : bv 32 := 0x0002b303.
Lemma D_b687c : decode_any W_b687c = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6880 : bv 32 := 0x00489893.
Lemma D_b6880 : decode_any W_b6880 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6884 : bv 32 := 0x011508b3.
Lemma D_b6884 : decode_any W_b6884 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6888 : bv 32 := 0x0048a383.
Lemma D_b6888 : decode_any W_b6888 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b688c : bv 32 := 0x0068b023.
Lemma D_b688c : decode_any W_b688c = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6890 : bv 32 := 0x0082b303.
Lemma D_b6890 : decode_any W_b6890 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6894 : bv 32 := 0x0088be03.
Lemma D_b6894 : decode_any W_b6894 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6898 : bv 32 := 0x0068b423.
Lemma D_b6898 : decode_any W_b6898 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b689c : bv 32 := 0x00e2a023.
Lemma D_b689c : decode_any W_b689c = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68a0 : bv 32 := 0x0072a223.
Lemma D_b68a0 : decode_any W_b68a0 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68a4 : bv 32 := 0x01c2b423.
Lemma D_b68a4 : decode_any W_b68a4 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68a8 : bv 32 := 0x00080893.
Lemma D_b68a8 : decode_any W_b68a8 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68ac : bv 32 := 0xfaf6ece3.
Lemma D_b68ac : decode_any W_b68ac = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68b0 : bv 32 := 0xf9dff06f.
Lemma D_b68b0 : decode_any W_b68b0 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68b4 : bv 32 := 0x00000613.
Lemma D_b68b4 : decode_any W_b68b4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68b8 : bv 32 := 0x00459693.
Lemma D_b68b8 : decode_any W_b68b8 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68bc : bv 32 := 0x00d506b3.
Lemma D_b68bc : decode_any W_b68bc = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68c0 : bv 32 := 0x0006b703.
Lemma D_b68c0 : decode_any W_b68c0 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68c4 : bv 32 := 0x0086b783.
Lemma D_b68c4 : decode_any W_b68c4 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68c8 : bv 32 := 0x00053803.
Lemma D_b68c8 : decode_any W_b68c8 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68cc : bv 32 := 0x00853883.
Lemma D_b68cc : decode_any W_b68cc = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68d0 : bv 32 := 0x00e53023.
Lemma D_b68d0 : decode_any W_b68d0 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68d4 : bv 32 := 0x00f53423.
Lemma D_b68d4 : decode_any W_b68d4 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68d8 : bv 32 := 0x0106b023.
Lemma D_b68d8 : decode_any W_b68d8 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68dc : bv 32 := 0x0116b423.
Lemma D_b68dc : decode_any W_b68dc = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68e0 : bv 32 := 0x00000693.
Lemma D_b68e0 : decode_any W_b68e0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68e4 : bv 32 := 0x00161793.
Lemma D_b68e4 : decode_any W_b68e4 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68e8 : bv 32 := 0x00178813.
Lemma D_b68e8 : decode_any W_b68e8 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68ec : bv 32 := 0x00461713.
Lemma D_b68ec : decode_any W_b68ec = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68f0 : bv 32 := 0x00b86a63.
Lemma D_b68f0 : decode_any W_b68f0 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68f4 : bv 32 := 0x00278793.
Lemma D_b68f4 : decode_any W_b68f4 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68f8 : bv 32 := 0x02b7ea63.
Lemma D_b68f8 : decode_any W_b68f8 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b68fc : bv 32 := 0x04c69c63.
Lemma D_b68fc : decode_any W_b68fc = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6900 : bv 32 := 0x0880006f.
Lemma D_b6900 : decode_any W_b6900 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6904 : bv 32 := 0x00e506b3.
Lemma D_b6904 : decode_any W_b6904 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6908 : bv 32 := 0x00481893.
Lemma D_b6908 : decode_any W_b6908 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b690c : bv 32 := 0x011508b3.
Lemma D_b690c : decode_any W_b690c = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6910 : bv 32 := 0x0006a683.
Lemma D_b6910 : decode_any W_b6910 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6914 : bv 32 := 0x0008a883.
Lemma D_b6914 : decode_any W_b6914 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6918 : bv 32 := 0x0116e463.
Lemma D_b6918 : decode_any W_b6918 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b691c : bv 32 := 0x00060813.
Lemma D_b691c : decode_any W_b691c = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6920 : bv 32 := 0x00080693.
Lemma D_b6920 : decode_any W_b6920 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6924 : bv 32 := 0x00278793.
Lemma D_b6924 : decode_any W_b6924 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6928 : bv 32 := 0xfcb7fae3.
Lemma D_b6928 : decode_any W_b6928 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b692c : bv 32 := 0x00469813.
Lemma D_b692c : decode_any W_b692c = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6930 : bv 32 := 0x00479893.
Lemma D_b6930 : decode_any W_b6930 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6934 : bv 32 := 0x01050833.
Lemma D_b6934 : decode_any W_b6934 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6938 : bv 32 := 0x011508b3.
Lemma D_b6938 : decode_any W_b6938 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b693c : bv 32 := 0x00082803.
Lemma D_b693c : decode_any W_b693c = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6940 : bv 32 := 0x0008a883.
Lemma D_b6940 : decode_any W_b6940 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6944 : bv 32 := 0x01186463.
Lemma D_b6944 : decode_any W_b6944 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6948 : bv 32 := 0x00068793.
Lemma D_b6948 : decode_any W_b6948 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b694c : bv 32 := 0x00078693.
Lemma D_b694c : decode_any W_b694c = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6950 : bv 32 := 0x02c78c63.
Lemma D_b6950 : decode_any W_b6950 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6954 : bv 32 := 0x00469613.
Lemma D_b6954 : decode_any W_b6954 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6958 : bv 32 := 0x00c50633.
Lemma D_b6958 : decode_any W_b6958 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b695c : bv 32 := 0x00063783.
Lemma D_b695c : decode_any W_b695c = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6960 : bv 32 := 0x00e50733.
Lemma D_b6960 : decode_any W_b6960 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6964 : bv 32 := 0x00073803.
Lemma D_b6964 : decode_any W_b6964 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6968 : bv 32 := 0x00873883.
Lemma D_b6968 : decode_any W_b6968 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b696c : bv 32 := 0x00f73023.
Lemma D_b696c : decode_any W_b696c = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6970 : bv 32 := 0x00863783.
Lemma D_b6970 : decode_any W_b6970 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6974 : bv 32 := 0x00f73423.
Lemma D_b6974 : decode_any W_b6974 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6978 : bv 32 := 0x01063023.
Lemma D_b6978 : decode_any W_b6978 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b697c : bv 32 := 0x01163423.
Lemma D_b697c : decode_any W_b697c = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6980 : bv 32 := 0x00068613.
Lemma D_b6980 : decode_any W_b6980 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6984 : bv 32 := 0xf6b6e0e3.
Lemma D_b6984 : decode_any W_b6984 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6988 : bv 32 := 0xfff58593.
Lemma D_b6988 : decode_any W_b6988 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b698c : bv 32 := 0xf20594e3.
Lemma D_b698c : decode_any W_b698c = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b6990 : bv 32 := 0x00008067.
Lemma D_b6990 : decode_any W_b6990 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
