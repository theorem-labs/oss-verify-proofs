(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
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
Definition W_94730 : bv 32 := 0x06060663.
Lemma D_94730 : decode_any W_94730 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94734 : bv 32 := 0x00000693.
Lemma D_94734 : decode_any W_94734 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94738 : bv 32 := 0x00d58733.
Lemma D_94738 : decode_any W_94738 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9473c : bv 32 := 0x00074703.
Lemma D_9473c : decode_any W_9473c = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94740 : bv 32 := 0x00070c63.
Lemma D_94740 : decode_any W_94740 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94744 : bv 32 := 0x00d507b3.
Lemma D_94744 : decode_any W_94744 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94748 : bv 32 := 0x00168693.
Lemma D_94748 : decode_any W_94748 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9474c : bv 32 := 0x00e78023.
Lemma D_9474c : decode_any W_9474c = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94750 : bv 32 := 0xfed614e3.
Lemma D_94750 : decode_any W_94750 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94754 : bv 32 := 0x00060693.
Lemma D_94754 : decode_any W_94754 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94758 : bv 32 := 0x00d505b3.
Lemma D_94758 : decode_any W_94758 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9475c : bv 32 := 0x40d6073b.
Lemma D_9475c : decode_any W_9475c = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94760 : bv 32 := 0x00b76733.
Lemma D_94760 : decode_any W_94760 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94764 : bv 32 := 0x00f77713.
Lemma D_94764 : decode_any W_94764 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94768 : bv 32 := 0x00070e63.
Lemma D_94768 : decode_any W_94768 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9476c : bv 32 := 0x02d60863.
Lemma D_9476c : decode_any W_9476c = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94770 : bv 32 := 0x00c50633.
Lemma D_94770 : decode_any W_94770 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94774 : bv 32 := 0x00058023.
Lemma D_94774 : decode_any W_94774 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94778 : bv 32 := 0x00158593.
Lemma D_94778 : decode_any W_94778 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9477c : bv 32 := 0xfec59ce3.
Lemma D_9477c : decode_any W_9477c = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94780 : bv 32 := 0x01c0006f.
Lemma D_94780 : decode_any W_94780 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94784 : bv 32 := 0x00d60c63.
Lemma D_94784 : decode_any W_94784 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94788 : bv 32 := 0x00c50633.
Lemma D_94788 : decode_any W_94788 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9478c : bv 32 := 0x0005b023.
Lemma D_9478c : decode_any W_9478c = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94790 : bv 32 := 0x0005b423.
Lemma D_94790 : decode_any W_94790 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94794 : bv 32 := 0x01058593.
Lemma D_94794 : decode_any W_94794 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94798 : bv 32 := 0xfec5eae3.
Lemma D_94798 : decode_any W_94798 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9479c : bv 32 := 0x00008067.
Lemma D_9479c : decode_any W_9479c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.



(* [comment removed for export] *)
Definition W_80510 : bv 32 := 0x00200613.
Lemma D_80510 : decode_any W_80510 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80514 : bv 32 := 0x14c5ea63.
Lemma D_80514 : decode_any W_80514 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80518 : bv 32 := 0x00100613.
Lemma D_80518 : decode_any W_80518 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8051c : bv 32 := 0x00100693.
Lemma D_8051c : decode_any W_8051c = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80520 : bv 32 := 0x00c0006f.
Lemma D_80520 : decode_any W_80520 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80524 : bv 32 := 0x00160613.
Lemma D_80524 : decode_any W_80524 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80528 : bv 32 := 0x12b60c63.
Lemma D_80528 : decode_any W_80528 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8052c : bv 32 := 0x00461713.
Lemma D_8052c : decode_any W_8052c = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80530 : bv 32 := 0x00e50733.
Lemma D_80530 : decode_any W_80530 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80534 : bv 32 := 0x00072703.
Lemma D_80534 : decode_any W_80534 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80538 : bv 32 := 0x00060893.
Lemma D_80538 : decode_any W_80538 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8053c : bv 32 := 0xfff88793.
Lemma D_8053c : decode_any W_8053c = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80540 : bv 32 := 0x0017d813.
Lemma D_80540 : decode_any W_80540 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80544 : bv 32 := 0x00481293.
Lemma D_80544 : decode_any W_80544 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80548 : bv 32 := 0x005502b3.
Lemma D_80548 : decode_any W_80548 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8054c : bv 32 := 0x0002a303.
Lemma D_8054c : decode_any W_8054c = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80550 : bv 32 := 0xfce37ae3.
Lemma D_80550 : decode_any W_80550 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80554 : bv 32 := 0x0002b303.
Lemma D_80554 : decode_any W_80554 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80558 : bv 32 := 0x00489893.
Lemma D_80558 : decode_any W_80558 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8055c : bv 32 := 0x011508b3.
Lemma D_8055c : decode_any W_8055c = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80560 : bv 32 := 0x0048a383.
Lemma D_80560 : decode_any W_80560 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80564 : bv 32 := 0x0068b023.
Lemma D_80564 : decode_any W_80564 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80568 : bv 32 := 0x0082b303.
Lemma D_80568 : decode_any W_80568 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8056c : bv 32 := 0x0088be03.
Lemma D_8056c : decode_any W_8056c = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80570 : bv 32 := 0x0068b423.
Lemma D_80570 : decode_any W_80570 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80574 : bv 32 := 0x00e2a023.
Lemma D_80574 : decode_any W_80574 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80578 : bv 32 := 0x0072a223.
Lemma D_80578 : decode_any W_80578 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8057c : bv 32 := 0x01c2b423.
Lemma D_8057c : decode_any W_8057c = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80580 : bv 32 := 0x00080893.
Lemma D_80580 : decode_any W_80580 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80584 : bv 32 := 0xfaf6ece3.
Lemma D_80584 : decode_any W_80584 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80588 : bv 32 := 0xf9dff06f.
Lemma D_80588 : decode_any W_80588 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8058c : bv 32 := 0x00000613.
Lemma D_8058c : decode_any W_8058c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80590 : bv 32 := 0x00459693.
Lemma D_80590 : decode_any W_80590 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80594 : bv 32 := 0x00d506b3.
Lemma D_80594 : decode_any W_80594 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80598 : bv 32 := 0x0006b703.
Lemma D_80598 : decode_any W_80598 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8059c : bv 32 := 0x0086b783.
Lemma D_8059c : decode_any W_8059c = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805a0 : bv 32 := 0x00053803.
Lemma D_805a0 : decode_any W_805a0 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805a4 : bv 32 := 0x00853883.
Lemma D_805a4 : decode_any W_805a4 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805a8 : bv 32 := 0x00e53023.
Lemma D_805a8 : decode_any W_805a8 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805ac : bv 32 := 0x00f53423.
Lemma D_805ac : decode_any W_805ac = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805b0 : bv 32 := 0x0106b023.
Lemma D_805b0 : decode_any W_805b0 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805b4 : bv 32 := 0x0116b423.
Lemma D_805b4 : decode_any W_805b4 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805b8 : bv 32 := 0x00000693.
Lemma D_805b8 : decode_any W_805b8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805bc : bv 32 := 0x00161793.
Lemma D_805bc : decode_any W_805bc = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805c0 : bv 32 := 0x00178813.
Lemma D_805c0 : decode_any W_805c0 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805c4 : bv 32 := 0x00461713.
Lemma D_805c4 : decode_any W_805c4 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805c8 : bv 32 := 0x00b86a63.
Lemma D_805c8 : decode_any W_805c8 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805cc : bv 32 := 0x00278793.
Lemma D_805cc : decode_any W_805cc = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805d0 : bv 32 := 0x02b7ea63.
Lemma D_805d0 : decode_any W_805d0 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805d4 : bv 32 := 0x04c69c63.
Lemma D_805d4 : decode_any W_805d4 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805d8 : bv 32 := 0x0880006f.
Lemma D_805d8 : decode_any W_805d8 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805dc : bv 32 := 0x00e506b3.
Lemma D_805dc : decode_any W_805dc = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805e0 : bv 32 := 0x00481893.
Lemma D_805e0 : decode_any W_805e0 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805e4 : bv 32 := 0x011508b3.
Lemma D_805e4 : decode_any W_805e4 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805e8 : bv 32 := 0x0006a683.
Lemma D_805e8 : decode_any W_805e8 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805ec : bv 32 := 0x0008a883.
Lemma D_805ec : decode_any W_805ec = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805f0 : bv 32 := 0x0116e463.
Lemma D_805f0 : decode_any W_805f0 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805f4 : bv 32 := 0x00060813.
Lemma D_805f4 : decode_any W_805f4 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805f8 : bv 32 := 0x00080693.
Lemma D_805f8 : decode_any W_805f8 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_805fc : bv 32 := 0x00278793.
Lemma D_805fc : decode_any W_805fc = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80600 : bv 32 := 0xfcb7fae3.
Lemma D_80600 : decode_any W_80600 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80604 : bv 32 := 0x00469813.
Lemma D_80604 : decode_any W_80604 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80608 : bv 32 := 0x00479893.
Lemma D_80608 : decode_any W_80608 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8060c : bv 32 := 0x01050833.
Lemma D_8060c : decode_any W_8060c = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80610 : bv 32 := 0x011508b3.
Lemma D_80610 : decode_any W_80610 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80614 : bv 32 := 0x00082803.
Lemma D_80614 : decode_any W_80614 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80618 : bv 32 := 0x0008a883.
Lemma D_80618 : decode_any W_80618 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8061c : bv 32 := 0x01186463.
Lemma D_8061c : decode_any W_8061c = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80620 : bv 32 := 0x00068793.
Lemma D_80620 : decode_any W_80620 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80624 : bv 32 := 0x00078693.
Lemma D_80624 : decode_any W_80624 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80628 : bv 32 := 0x02c78c63.
Lemma D_80628 : decode_any W_80628 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8062c : bv 32 := 0x00469613.
Lemma D_8062c : decode_any W_8062c = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80630 : bv 32 := 0x00c50633.
Lemma D_80630 : decode_any W_80630 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80634 : bv 32 := 0x00063783.
Lemma D_80634 : decode_any W_80634 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80638 : bv 32 := 0x00e50733.
Lemma D_80638 : decode_any W_80638 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8063c : bv 32 := 0x00073803.
Lemma D_8063c : decode_any W_8063c = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80640 : bv 32 := 0x00873883.
Lemma D_80640 : decode_any W_80640 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80644 : bv 32 := 0x00f73023.
Lemma D_80644 : decode_any W_80644 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80648 : bv 32 := 0x00863783.
Lemma D_80648 : decode_any W_80648 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8064c : bv 32 := 0x00f73423.
Lemma D_8064c : decode_any W_8064c = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80650 : bv 32 := 0x01063023.
Lemma D_80650 : decode_any W_80650 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80654 : bv 32 := 0x01163423.
Lemma D_80654 : decode_any W_80654 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80658 : bv 32 := 0x00068613.
Lemma D_80658 : decode_any W_80658 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8065c : bv 32 := 0xf6b6e0e3.
Lemma D_8065c : decode_any W_8065c = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80660 : bv 32 := 0xfff58593.
Lemma D_80660 : decode_any W_80660 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80664 : bv 32 := 0xf20594e3.
Lemma D_80664 : decode_any W_80664 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_80668 : bv 32 := 0x00008067.
Lemma D_80668 : decode_any W_80668 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
