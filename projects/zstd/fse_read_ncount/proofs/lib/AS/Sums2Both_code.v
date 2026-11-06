(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_64794 : bv 32 := 0x06060663.
Lemma D_64794 : decode_any W_64794 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.
Definition W_64798 : bv 32 := 0x00000693.
Lemma D_64798 : decode_any W_64798 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_6479c : bv 32 := 0x00d58733.
Lemma D_6479c : decode_any W_6479c = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_647a0 : bv 32 := 0x00074703.
Lemma D_647a0 : decode_any W_647a0 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_647a4 : bv 32 := 0x00070c63.
Lemma D_647a4 : decode_any W_647a4 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_647a8 : bv 32 := 0x00d507b3.
Lemma D_647a8 : decode_any W_647a8 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_647ac : bv 32 := 0x00168693.
Lemma D_647ac : decode_any W_647ac = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_647b0 : bv 32 := 0x00e78023.
Lemma D_647b0 : decode_any W_647b0 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_647b4 : bv 32 := 0xfed614e3.
Lemma D_647b4 : decode_any W_647b4 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.
Definition W_647b8 : bv 32 := 0x00060693.
Definition W_647bc : bv 32 := 0x00d505b3.
Lemma D_647bc : decode_any W_647bc = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_647c0 : bv 32 := 0x40d6073b.
Lemma D_647c0 : decode_any W_647c0 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_647c4 : bv 32 := 0x00b76733.
Lemma D_647c4 : decode_any W_647c4 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_647c8 : bv 32 := 0x00f77713.
Lemma D_647c8 : decode_any W_647c8 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_647cc : bv 32 := 0x00070e63.
Lemma D_647cc : decode_any W_647cc = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.
Definition W_647d0 : bv 32 := 0x02d60863.
Lemma D_647d0 : decode_any W_647d0 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.
Definition W_647d4 : bv 32 := 0x00c50633.
Lemma D_647d4 : decode_any W_647d4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_647d8 : bv 32 := 0x00058023.
Lemma D_647d8 : decode_any W_647d8 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_647dc : bv 32 := 0x00158593.
Lemma D_647dc : decode_any W_647dc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_647e0 : bv 32 := 0xfec59ce3.
Lemma D_647e0 : decode_any W_647e0 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.
Definition W_647e4 : bv 32 := 0x01c0006f.
Lemma D_647e4 : decode_any W_647e4 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.
Definition W_647e8 : bv 32 := 0x00d60c63.
Definition W_647ec : bv 32 := 0x00c50633.
Definition W_647f0 : bv 32 := 0x0005b023.
Definition W_647f4 : bv 32 := 0x0005b423.
Definition W_647f8 : bv 32 := 0x01058593.
Definition W_647fc : bv 32 := 0xfec5eae3.
Definition W_64800 : bv 32 := 0x00008067.
Lemma D_64800 : decode_any W_64800 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
