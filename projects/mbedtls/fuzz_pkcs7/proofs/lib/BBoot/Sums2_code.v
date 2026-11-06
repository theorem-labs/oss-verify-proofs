(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_7a920 : bv 32 := 0x06060663.
Lemma D_7a920 : decode_any W_7a920 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a924 : bv 32 := 0x00000693.
Lemma D_7a924 : decode_any W_7a924 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a928 : bv 32 := 0x00d58733.
Lemma D_7a928 : decode_any W_7a928 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a92c : bv 32 := 0x00074703.
Lemma D_7a92c : decode_any W_7a92c = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a930 : bv 32 := 0x00070c63.
Lemma D_7a930 : decode_any W_7a930 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a934 : bv 32 := 0x00d507b3.
Lemma D_7a934 : decode_any W_7a934 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a938 : bv 32 := 0x00168693.
Lemma D_7a938 : decode_any W_7a938 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a93c : bv 32 := 0x00e78023.
Lemma D_7a93c : decode_any W_7a93c = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a940 : bv 32 := 0xfed614e3.
Lemma D_7a940 : decode_any W_7a940 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a944 : bv 32 := 0x00060693.
Lemma D_7a944 : decode_any W_7a944 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a948 : bv 32 := 0x00d505b3.
Lemma D_7a948 : decode_any W_7a948 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a94c : bv 32 := 0x40d6073b.
Lemma D_7a94c : decode_any W_7a94c = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a950 : bv 32 := 0x00b76733.
Lemma D_7a950 : decode_any W_7a950 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a954 : bv 32 := 0x00f77713.
Lemma D_7a954 : decode_any W_7a954 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a958 : bv 32 := 0x00070e63.
Lemma D_7a958 : decode_any W_7a958 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a95c : bv 32 := 0x02d60863.
Lemma D_7a95c : decode_any W_7a95c = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a960 : bv 32 := 0x00c50633.
Lemma D_7a960 : decode_any W_7a960 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a964 : bv 32 := 0x00058023.
Lemma D_7a964 : decode_any W_7a964 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a968 : bv 32 := 0x00158593.
Lemma D_7a968 : decode_any W_7a968 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a96c : bv 32 := 0xfec59ce3.
Lemma D_7a96c : decode_any W_7a96c = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a970 : bv 32 := 0x01c0006f.
Lemma D_7a970 : decode_any W_7a970 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a974 : bv 32 := 0x00d60c63.
Lemma D_7a974 : decode_any W_7a974 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a978 : bv 32 := 0x00c50633.
Lemma D_7a978 : decode_any W_7a978 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a97c : bv 32 := 0x0005b023.
Lemma D_7a97c : decode_any W_7a97c = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a980 : bv 32 := 0x0005b423.
Lemma D_7a980 : decode_any W_7a980 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a984 : bv 32 := 0x01058593.
Lemma D_7a984 : decode_any W_7a984 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a988 : bv 32 := 0xfec5eae3.
Lemma D_7a988 : decode_any W_7a988 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7a98c : bv 32 := 0x00008067.
Lemma D_7a98c : decode_any W_7a98c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.



(* [comment removed for export] *)
Definition W_676f4 : bv 32 := 0x00200613.
Lemma D_676f4 : decode_any W_676f4 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676f8 : bv 32 := 0x14c5ea63.
Lemma D_676f8 : decode_any W_676f8 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_676fc : bv 32 := 0x00100613.
Lemma D_676fc : decode_any W_676fc = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67700 : bv 32 := 0x00100693.
Lemma D_67700 : decode_any W_67700 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67704 : bv 32 := 0x00c0006f.
Lemma D_67704 : decode_any W_67704 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67708 : bv 32 := 0x00160613.
Lemma D_67708 : decode_any W_67708 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6770c : bv 32 := 0x12b60c63.
Lemma D_6770c : decode_any W_6770c = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67710 : bv 32 := 0x00461713.
Lemma D_67710 : decode_any W_67710 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67714 : bv 32 := 0x00e50733.
Lemma D_67714 : decode_any W_67714 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67718 : bv 32 := 0x00072703.
Lemma D_67718 : decode_any W_67718 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6771c : bv 32 := 0x00060893.
Lemma D_6771c : decode_any W_6771c = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67720 : bv 32 := 0xfff88793.
Lemma D_67720 : decode_any W_67720 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67724 : bv 32 := 0x0017d813.
Lemma D_67724 : decode_any W_67724 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67728 : bv 32 := 0x00481293.
Lemma D_67728 : decode_any W_67728 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6772c : bv 32 := 0x005502b3.
Lemma D_6772c : decode_any W_6772c = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67730 : bv 32 := 0x0002a303.
Lemma D_67730 : decode_any W_67730 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67734 : bv 32 := 0xfce37ae3.
Lemma D_67734 : decode_any W_67734 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67738 : bv 32 := 0x0002b303.
Lemma D_67738 : decode_any W_67738 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6773c : bv 32 := 0x00489893.
Lemma D_6773c : decode_any W_6773c = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67740 : bv 32 := 0x011508b3.
Lemma D_67740 : decode_any W_67740 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67744 : bv 32 := 0x0048a383.
Lemma D_67744 : decode_any W_67744 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67748 : bv 32 := 0x0068b023.
Lemma D_67748 : decode_any W_67748 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6774c : bv 32 := 0x0082b303.
Lemma D_6774c : decode_any W_6774c = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67750 : bv 32 := 0x0088be03.
Lemma D_67750 : decode_any W_67750 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67754 : bv 32 := 0x0068b423.
Lemma D_67754 : decode_any W_67754 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67758 : bv 32 := 0x00e2a023.
Lemma D_67758 : decode_any W_67758 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6775c : bv 32 := 0x0072a223.
Lemma D_6775c : decode_any W_6775c = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67760 : bv 32 := 0x01c2b423.
Lemma D_67760 : decode_any W_67760 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67764 : bv 32 := 0x00080893.
Lemma D_67764 : decode_any W_67764 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67768 : bv 32 := 0xfaf6ece3.
Lemma D_67768 : decode_any W_67768 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6776c : bv 32 := 0xf9dff06f.
Lemma D_6776c : decode_any W_6776c = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67770 : bv 32 := 0x00000613.
Lemma D_67770 : decode_any W_67770 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67774 : bv 32 := 0x00459693.
Lemma D_67774 : decode_any W_67774 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67778 : bv 32 := 0x00d506b3.
Lemma D_67778 : decode_any W_67778 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6777c : bv 32 := 0x0006b703.
Lemma D_6777c : decode_any W_6777c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67780 : bv 32 := 0x0086b783.
Lemma D_67780 : decode_any W_67780 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67784 : bv 32 := 0x00053803.
Lemma D_67784 : decode_any W_67784 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67788 : bv 32 := 0x00853883.
Lemma D_67788 : decode_any W_67788 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6778c : bv 32 := 0x00e53023.
Lemma D_6778c : decode_any W_6778c = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67790 : bv 32 := 0x00f53423.
Lemma D_67790 : decode_any W_67790 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67794 : bv 32 := 0x0106b023.
Lemma D_67794 : decode_any W_67794 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67798 : bv 32 := 0x0116b423.
Lemma D_67798 : decode_any W_67798 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6779c : bv 32 := 0x00000693.
Lemma D_6779c : decode_any W_6779c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677a0 : bv 32 := 0x00161793.
Lemma D_677a0 : decode_any W_677a0 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677a4 : bv 32 := 0x00178813.
Lemma D_677a4 : decode_any W_677a4 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677a8 : bv 32 := 0x00461713.
Lemma D_677a8 : decode_any W_677a8 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677ac : bv 32 := 0x00b86a63.
Lemma D_677ac : decode_any W_677ac = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677b0 : bv 32 := 0x00278793.
Lemma D_677b0 : decode_any W_677b0 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677b4 : bv 32 := 0x02b7ea63.
Lemma D_677b4 : decode_any W_677b4 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677b8 : bv 32 := 0x04c69c63.
Lemma D_677b8 : decode_any W_677b8 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677bc : bv 32 := 0x0880006f.
Lemma D_677bc : decode_any W_677bc = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677c0 : bv 32 := 0x00e506b3.
Lemma D_677c0 : decode_any W_677c0 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677c4 : bv 32 := 0x00481893.
Lemma D_677c4 : decode_any W_677c4 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677c8 : bv 32 := 0x011508b3.
Lemma D_677c8 : decode_any W_677c8 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677cc : bv 32 := 0x0006a683.
Lemma D_677cc : decode_any W_677cc = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677d0 : bv 32 := 0x0008a883.
Lemma D_677d0 : decode_any W_677d0 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677d4 : bv 32 := 0x0116e463.
Lemma D_677d4 : decode_any W_677d4 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677d8 : bv 32 := 0x00060813.
Lemma D_677d8 : decode_any W_677d8 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677dc : bv 32 := 0x00080693.
Lemma D_677dc : decode_any W_677dc = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677e0 : bv 32 := 0x00278793.
Lemma D_677e0 : decode_any W_677e0 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677e4 : bv 32 := 0xfcb7fae3.
Lemma D_677e4 : decode_any W_677e4 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677e8 : bv 32 := 0x00469813.
Lemma D_677e8 : decode_any W_677e8 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677ec : bv 32 := 0x00479893.
Lemma D_677ec : decode_any W_677ec = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677f0 : bv 32 := 0x01050833.
Lemma D_677f0 : decode_any W_677f0 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677f4 : bv 32 := 0x011508b3.
Lemma D_677f4 : decode_any W_677f4 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677f8 : bv 32 := 0x00082803.
Lemma D_677f8 : decode_any W_677f8 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_677fc : bv 32 := 0x0008a883.
Lemma D_677fc : decode_any W_677fc = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67800 : bv 32 := 0x01186463.
Lemma D_67800 : decode_any W_67800 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67804 : bv 32 := 0x00068793.
Lemma D_67804 : decode_any W_67804 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67808 : bv 32 := 0x00078693.
Lemma D_67808 : decode_any W_67808 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6780c : bv 32 := 0x02c78c63.
Lemma D_6780c : decode_any W_6780c = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67810 : bv 32 := 0x00469613.
Lemma D_67810 : decode_any W_67810 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67814 : bv 32 := 0x00c50633.
Lemma D_67814 : decode_any W_67814 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67818 : bv 32 := 0x00063783.
Lemma D_67818 : decode_any W_67818 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6781c : bv 32 := 0x00e50733.
Lemma D_6781c : decode_any W_6781c = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67820 : bv 32 := 0x00073803.
Lemma D_67820 : decode_any W_67820 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67824 : bv 32 := 0x00873883.
Lemma D_67824 : decode_any W_67824 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67828 : bv 32 := 0x00f73023.
Lemma D_67828 : decode_any W_67828 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6782c : bv 32 := 0x00863783.
Lemma D_6782c : decode_any W_6782c = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67830 : bv 32 := 0x00f73423.
Lemma D_67830 : decode_any W_67830 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67834 : bv 32 := 0x01063023.
Lemma D_67834 : decode_any W_67834 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67838 : bv 32 := 0x01163423.
Lemma D_67838 : decode_any W_67838 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6783c : bv 32 := 0x00068613.
Lemma D_6783c : decode_any W_6783c = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67840 : bv 32 := 0xf6b6e0e3.
Lemma D_67840 : decode_any W_67840 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67844 : bv 32 := 0xfff58593.
Lemma D_67844 : decode_any W_67844 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67848 : bv 32 := 0xf20594e3.
Lemma D_67848 : decode_any W_67848 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6784c : bv 32 := 0x00008067.
Lemma D_6784c : decode_any W_6784c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
