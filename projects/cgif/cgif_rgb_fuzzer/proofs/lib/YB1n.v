(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_e29c0 : bv 32 := 0x06060663.
Lemma D_e29c0 : decode_any W_e29c0 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.
Definition W_e29c4 : bv 32 := 0x00000693.
Lemma D_e29c4 : decode_any W_e29c4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_e29c8 : bv 32 := 0x00d58733.
Lemma D_e29c8 : decode_any W_e29c8 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_e29cc : bv 32 := 0x00074703.
Lemma D_e29cc : decode_any W_e29cc = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_e29d0 : bv 32 := 0x00070c63.
Lemma D_e29d0 : decode_any W_e29d0 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_e29d4 : bv 32 := 0x00d507b3.
Lemma D_e29d4 : decode_any W_e29d4 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_e29d8 : bv 32 := 0x00168693.
Lemma D_e29d8 : decode_any W_e29d8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_e29dc : bv 32 := 0x00e78023.
Lemma D_e29dc : decode_any W_e29dc = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_e29e0 : bv 32 := 0xfed614e3.
Lemma D_e29e0 : decode_any W_e29e0 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.
Definition W_e29e4 : bv 32 := 0x00060693.

Definition W_e29e8 : bv 32 := 0x00d505b3.
Lemma D_e29e8 : decode_any W_e29e8 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_e29ec : bv 32 := 0x40d6073b.
Lemma D_e29ec : decode_any W_e29ec = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_e29f0 : bv 32 := 0x00b76733.
Lemma D_e29f0 : decode_any W_e29f0 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_e29f4 : bv 32 := 0x00f77713.
Lemma D_e29f4 : decode_any W_e29f4 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_e29f8 : bv 32 := 0x00070e63.
Lemma D_e29f8 : decode_any W_e29f8 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.
Definition W_e29fc : bv 32 := 0x02d60863.
Lemma D_e29fc : decode_any W_e29fc = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2a00 : bv 32 := 0x00c50633.
Lemma D_e2a00 : decode_any W_e2a00 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2a04 : bv 32 := 0x00058023.
Lemma D_e2a04 : decode_any W_e2a04 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2a08 : bv 32 := 0x00158593.
Lemma D_e2a08 : decode_any W_e2a08 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2a0c : bv 32 := 0xfec59ce3.
Lemma D_e2a0c : decode_any W_e2a0c = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2a10 : bv 32 := 0x01c0006f.
Lemma D_e2a10 : decode_any W_e2a10 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2a14 : bv 32 := 0x00d60c63.

Definition W_e2a18 : bv 32 := 0x00c50633.

Definition W_e2a1c : bv 32 := 0x0005b023.

Definition W_e2a20 : bv 32 := 0x0005b423.

Definition W_e2a24 : bv 32 := 0x01058593.

Definition W_e2a28 : bv 32 := 0xfec5eae3.

Definition W_e2a2c : bv 32 := 0x00008067.
Lemma D_e2a2c : decode_any W_e2a2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c96ec : bv 32 := 0x00200613.

Definition W_c96f0 : bv 32 := 0x14c5ea63.

Definition W_c96f4 : bv 32 := 0x00100613.

Definition W_c96f8 : bv 32 := 0x00100693.

Definition W_c96fc : bv 32 := 0x00c0006f.

Definition W_c9700 : bv 32 := 0x00160613.

Definition W_c9704 : bv 32 := 0x12b60c63.

Definition W_c9708 : bv 32 := 0x00461713.

Definition W_c970c : bv 32 := 0x00e50733.

Definition W_c9710 : bv 32 := 0x00072703.

Definition W_c9714 : bv 32 := 0x00060893.

Definition W_c9718 : bv 32 := 0xfff88793.

Definition W_c971c : bv 32 := 0x0017d813.

Definition W_c9720 : bv 32 := 0x00481293.

Definition W_c9724 : bv 32 := 0x005502b3.

Definition W_c9728 : bv 32 := 0x0002a303.

Definition W_c972c : bv 32 := 0xfce37ae3.

Definition W_c9730 : bv 32 := 0x0002b303.

Definition W_c9734 : bv 32 := 0x00489893.

Definition W_c9738 : bv 32 := 0x011508b3.

Definition W_c973c : bv 32 := 0x0048a383.

Definition W_c9740 : bv 32 := 0x0068b023.

Definition W_c9744 : bv 32 := 0x0082b303.

Definition W_c9748 : bv 32 := 0x0088be03.

Definition W_c974c : bv 32 := 0x0068b423.

Definition W_c9750 : bv 32 := 0x00e2a023.

Definition W_c9754 : bv 32 := 0x0072a223.

Definition W_c9758 : bv 32 := 0x01c2b423.

Definition W_c975c : bv 32 := 0x00080893.

Definition W_c9760 : bv 32 := 0xfaf6ece3.

Definition W_c9764 : bv 32 := 0xf9dff06f.

Definition W_c9768 : bv 32 := 0x00000613.

Definition W_c976c : bv 32 := 0x00459693.

Definition W_c9770 : bv 32 := 0x00d506b3.

Definition W_c9774 : bv 32 := 0x0006b703.

Definition W_c9778 : bv 32 := 0x0086b783.

Definition W_c977c : bv 32 := 0x00053803.

Definition W_c9780 : bv 32 := 0x00853883.

Definition W_c9784 : bv 32 := 0x00e53023.

Definition W_c9788 : bv 32 := 0x00f53423.

Definition W_c978c : bv 32 := 0x0106b023.

Definition W_c9790 : bv 32 := 0x0116b423.

Definition W_c9794 : bv 32 := 0x00000693.

Definition W_c9798 : bv 32 := 0x00161793.

Definition W_c979c : bv 32 := 0x00178813.

Definition W_c97a0 : bv 32 := 0x00461713.

Definition W_c97a4 : bv 32 := 0x00b86a63.

Definition W_c97a8 : bv 32 := 0x00278793.

Definition W_c97ac : bv 32 := 0x02b7ea63.

Definition W_c97b0 : bv 32 := 0x04c69c63.

Definition W_c97b4 : bv 32 := 0x0880006f.

Definition W_c97b8 : bv 32 := 0x00e506b3.

Definition W_c97bc : bv 32 := 0x00481893.

Definition W_c97c0 : bv 32 := 0x011508b3.

Definition W_c97c4 : bv 32 := 0x0006a683.

Definition W_c97c8 : bv 32 := 0x0008a883.

Definition W_c97cc : bv 32 := 0x0116e463.

Definition W_c97d0 : bv 32 := 0x00060813.

Definition W_c97d4 : bv 32 := 0x00080693.

Definition W_c97d8 : bv 32 := 0x00278793.

Definition W_c97dc : bv 32 := 0xfcb7fae3.

Definition W_c97e0 : bv 32 := 0x00469813.

Definition W_c97e4 : bv 32 := 0x00479893.

Definition W_c97e8 : bv 32 := 0x01050833.

Definition W_c97ec : bv 32 := 0x011508b3.

Definition W_c97f0 : bv 32 := 0x00082803.

Definition W_c97f4 : bv 32 := 0x0008a883.

Definition W_c97f8 : bv 32 := 0x01186463.

Definition W_c97fc : bv 32 := 0x00068793.

Definition W_c9800 : bv 32 := 0x00078693.

Definition W_c9804 : bv 32 := 0x02c78c63.

Definition W_c9808 : bv 32 := 0x00469613.

Definition W_c980c : bv 32 := 0x00c50633.

Definition W_c9810 : bv 32 := 0x00063783.

Definition W_c9814 : bv 32 := 0x00e50733.

Definition W_c9818 : bv 32 := 0x00073803.

Definition W_c981c : bv 32 := 0x00873883.

Definition W_c9820 : bv 32 := 0x00f73023.

Definition W_c9824 : bv 32 := 0x00863783.

Definition W_c9828 : bv 32 := 0x00f73423.

Definition W_c982c : bv 32 := 0x01063023.

Definition W_c9830 : bv 32 := 0x01163423.

Definition W_c9834 : bv 32 := 0x00068613.

Definition W_c9838 : bv 32 := 0xf6b6e0e3.

Definition W_c983c : bv 32 := 0xfff58593.

Definition W_c9840 : bv 32 := 0xf20594e3.

Definition W_c9844 : bv 32 := 0x00008067.

