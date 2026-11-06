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
Definition W_740b4 : bv 32 := 0x06060663.
Lemma D_740b4 : decode_any W_740b4 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_740b8 : bv 32 := 0x00000693.
Lemma D_740b8 : decode_any W_740b8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_740bc : bv 32 := 0x00d58733.
Lemma D_740bc : decode_any W_740bc = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_740c0 : bv 32 := 0x00074703.
Lemma D_740c0 : decode_any W_740c0 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_740c4 : bv 32 := 0x00070c63.
Lemma D_740c4 : decode_any W_740c4 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_740c8 : bv 32 := 0x00d507b3.
Lemma D_740c8 : decode_any W_740c8 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_740cc : bv 32 := 0x00168693.
Lemma D_740cc : decode_any W_740cc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_740d0 : bv 32 := 0x00e78023.
Lemma D_740d0 : decode_any W_740d0 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_740d4 : bv 32 := 0xfed614e3.
Lemma D_740d4 : decode_any W_740d4 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_740d8 : bv 32 := 0x00060693.
Lemma D_740d8 : decode_any W_740d8 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_740dc : bv 32 := 0x00d505b3.
Lemma D_740dc : decode_any W_740dc = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_740e0 : bv 32 := 0x40d6073b.
Lemma D_740e0 : decode_any W_740e0 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_740e4 : bv 32 := 0x00b76733.
Lemma D_740e4 : decode_any W_740e4 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_740e8 : bv 32 := 0x00f77713.
Lemma D_740e8 : decode_any W_740e8 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_740ec : bv 32 := 0x00070e63.
Lemma D_740ec : decode_any W_740ec = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_740f0 : bv 32 := 0x02d60863.
Lemma D_740f0 : decode_any W_740f0 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_740f4 : bv 32 := 0x00c50633.
Lemma D_740f4 : decode_any W_740f4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_740f8 : bv 32 := 0x00058023.
Lemma D_740f8 : decode_any W_740f8 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_740fc : bv 32 := 0x00158593.
Lemma D_740fc : decode_any W_740fc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74100 : bv 32 := 0xfec59ce3.
Lemma D_74100 : decode_any W_74100 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74104 : bv 32 := 0x01c0006f.
Lemma D_74104 : decode_any W_74104 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74108 : bv 32 := 0x00d60c63.
Lemma D_74108 : decode_any W_74108 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7410c : bv 32 := 0x00c50633.
Lemma D_7410c : decode_any W_7410c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74110 : bv 32 := 0x0005b023.
Lemma D_74110 : decode_any W_74110 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74114 : bv 32 := 0x0005b423.
Lemma D_74114 : decode_any W_74114 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74118 : bv 32 := 0x01058593.
Lemma D_74118 : decode_any W_74118 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7411c : bv 32 := 0xfec5eae3.
Lemma D_7411c : decode_any W_7411c = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74120 : bv 32 := 0x00008067.
Lemma D_74120 : decode_any W_74120 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.



(* [comment removed for export] *)
Definition W_60664 : bv 32 := 0x00200613.
Lemma D_60664 : decode_any W_60664 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60668 : bv 32 := 0x14c5ea63.
Lemma D_60668 : decode_any W_60668 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6066c : bv 32 := 0x00100613.
Lemma D_6066c : decode_any W_6066c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60670 : bv 32 := 0x00100693.
Lemma D_60670 : decode_any W_60670 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60674 : bv 32 := 0x00c0006f.
Lemma D_60674 : decode_any W_60674 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60678 : bv 32 := 0x00160613.
Lemma D_60678 : decode_any W_60678 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6067c : bv 32 := 0x12b60c63.
Lemma D_6067c : decode_any W_6067c = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60680 : bv 32 := 0x00461713.
Lemma D_60680 : decode_any W_60680 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60684 : bv 32 := 0x00e50733.
Lemma D_60684 : decode_any W_60684 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60688 : bv 32 := 0x00072703.
Lemma D_60688 : decode_any W_60688 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6068c : bv 32 := 0x00060893.
Lemma D_6068c : decode_any W_6068c = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60690 : bv 32 := 0xfff88793.
Lemma D_60690 : decode_any W_60690 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60694 : bv 32 := 0x0017d813.
Lemma D_60694 : decode_any W_60694 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60698 : bv 32 := 0x00481293.
Lemma D_60698 : decode_any W_60698 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6069c : bv 32 := 0x005502b3.
Lemma D_6069c : decode_any W_6069c = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606a0 : bv 32 := 0x0002a303.
Lemma D_606a0 : decode_any W_606a0 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606a4 : bv 32 := 0xfce37ae3.
Lemma D_606a4 : decode_any W_606a4 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606a8 : bv 32 := 0x0002b303.
Lemma D_606a8 : decode_any W_606a8 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606ac : bv 32 := 0x00489893.
Lemma D_606ac : decode_any W_606ac = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606b0 : bv 32 := 0x011508b3.
Lemma D_606b0 : decode_any W_606b0 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606b4 : bv 32 := 0x0048a383.
Lemma D_606b4 : decode_any W_606b4 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606b8 : bv 32 := 0x0068b023.
Lemma D_606b8 : decode_any W_606b8 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606bc : bv 32 := 0x0082b303.
Lemma D_606bc : decode_any W_606bc = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606c0 : bv 32 := 0x0088be03.
Lemma D_606c0 : decode_any W_606c0 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606c4 : bv 32 := 0x0068b423.
Lemma D_606c4 : decode_any W_606c4 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606c8 : bv 32 := 0x00e2a023.
Lemma D_606c8 : decode_any W_606c8 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606cc : bv 32 := 0x0072a223.
Lemma D_606cc : decode_any W_606cc = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606d0 : bv 32 := 0x01c2b423.
Lemma D_606d0 : decode_any W_606d0 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606d4 : bv 32 := 0x00080893.
Lemma D_606d4 : decode_any W_606d4 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606d8 : bv 32 := 0xfaf6ece3.
Lemma D_606d8 : decode_any W_606d8 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606dc : bv 32 := 0xf9dff06f.
Lemma D_606dc : decode_any W_606dc = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606e0 : bv 32 := 0x00000613.
Lemma D_606e0 : decode_any W_606e0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606e4 : bv 32 := 0x00459693.
Lemma D_606e4 : decode_any W_606e4 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606e8 : bv 32 := 0x00d506b3.
Lemma D_606e8 : decode_any W_606e8 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606ec : bv 32 := 0x0006b703.
Lemma D_606ec : decode_any W_606ec = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606f0 : bv 32 := 0x0086b783.
Lemma D_606f0 : decode_any W_606f0 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606f4 : bv 32 := 0x00053803.
Lemma D_606f4 : decode_any W_606f4 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606f8 : bv 32 := 0x00853883.
Lemma D_606f8 : decode_any W_606f8 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_606fc : bv 32 := 0x00e53023.
Lemma D_606fc : decode_any W_606fc = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60700 : bv 32 := 0x00f53423.
Lemma D_60700 : decode_any W_60700 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60704 : bv 32 := 0x0106b023.
Lemma D_60704 : decode_any W_60704 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60708 : bv 32 := 0x0116b423.
Lemma D_60708 : decode_any W_60708 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6070c : bv 32 := 0x00000693.
Lemma D_6070c : decode_any W_6070c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60710 : bv 32 := 0x00161793.
Lemma D_60710 : decode_any W_60710 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60714 : bv 32 := 0x00178813.
Lemma D_60714 : decode_any W_60714 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60718 : bv 32 := 0x00461713.
Lemma D_60718 : decode_any W_60718 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6071c : bv 32 := 0x00b86a63.
Lemma D_6071c : decode_any W_6071c = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60720 : bv 32 := 0x00278793.
Lemma D_60720 : decode_any W_60720 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60724 : bv 32 := 0x02b7ea63.
Lemma D_60724 : decode_any W_60724 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60728 : bv 32 := 0x04c69c63.
Lemma D_60728 : decode_any W_60728 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6072c : bv 32 := 0x0880006f.
Lemma D_6072c : decode_any W_6072c = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60730 : bv 32 := 0x00e506b3.
Lemma D_60730 : decode_any W_60730 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60734 : bv 32 := 0x00481893.
Lemma D_60734 : decode_any W_60734 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60738 : bv 32 := 0x011508b3.
Lemma D_60738 : decode_any W_60738 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6073c : bv 32 := 0x0006a683.
Lemma D_6073c : decode_any W_6073c = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60740 : bv 32 := 0x0008a883.
Lemma D_60740 : decode_any W_60740 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60744 : bv 32 := 0x0116e463.
Lemma D_60744 : decode_any W_60744 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60748 : bv 32 := 0x00060813.
Lemma D_60748 : decode_any W_60748 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6074c : bv 32 := 0x00080693.
Lemma D_6074c : decode_any W_6074c = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60750 : bv 32 := 0x00278793.
Lemma D_60750 : decode_any W_60750 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60754 : bv 32 := 0xfcb7fae3.
Lemma D_60754 : decode_any W_60754 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60758 : bv 32 := 0x00469813.
Lemma D_60758 : decode_any W_60758 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6075c : bv 32 := 0x00479893.
Lemma D_6075c : decode_any W_6075c = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60760 : bv 32 := 0x01050833.
Lemma D_60760 : decode_any W_60760 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60764 : bv 32 := 0x011508b3.
Lemma D_60764 : decode_any W_60764 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60768 : bv 32 := 0x00082803.
Lemma D_60768 : decode_any W_60768 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6076c : bv 32 := 0x0008a883.
Lemma D_6076c : decode_any W_6076c = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60770 : bv 32 := 0x01186463.
Lemma D_60770 : decode_any W_60770 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60774 : bv 32 := 0x00068793.
Lemma D_60774 : decode_any W_60774 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60778 : bv 32 := 0x00078693.
Lemma D_60778 : decode_any W_60778 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6077c : bv 32 := 0x02c78c63.
Lemma D_6077c : decode_any W_6077c = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60780 : bv 32 := 0x00469613.
Lemma D_60780 : decode_any W_60780 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60784 : bv 32 := 0x00c50633.
Lemma D_60784 : decode_any W_60784 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60788 : bv 32 := 0x00063783.
Lemma D_60788 : decode_any W_60788 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6078c : bv 32 := 0x00e50733.
Lemma D_6078c : decode_any W_6078c = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60790 : bv 32 := 0x00073803.
Lemma D_60790 : decode_any W_60790 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60794 : bv 32 := 0x00873883.
Lemma D_60794 : decode_any W_60794 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_60798 : bv 32 := 0x00f73023.
Lemma D_60798 : decode_any W_60798 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6079c : bv 32 := 0x00863783.
Lemma D_6079c : decode_any W_6079c = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_607a0 : bv 32 := 0x00f73423.
Lemma D_607a0 : decode_any W_607a0 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_607a4 : bv 32 := 0x01063023.
Lemma D_607a4 : decode_any W_607a4 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_607a8 : bv 32 := 0x01163423.
Lemma D_607a8 : decode_any W_607a8 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_607ac : bv 32 := 0x00068613.
Lemma D_607ac : decode_any W_607ac = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_607b0 : bv 32 := 0xf6b6e0e3.
Lemma D_607b0 : decode_any W_607b0 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_607b4 : bv 32 := 0xfff58593.
Lemma D_607b4 : decode_any W_607b4 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_607b8 : bv 32 := 0xf20594e3.
Lemma D_607b8 : decode_any W_607b8 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_607bc : bv 32 := 0x00008067.
Lemma D_607bc : decode_any W_607bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
