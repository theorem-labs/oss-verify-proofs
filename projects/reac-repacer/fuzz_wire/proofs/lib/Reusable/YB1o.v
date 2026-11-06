(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YB1o.v (release 2026.10.0), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_grant/lib/Reusable/YB1o.v at 4f87de75d677 (donor image sha256 c2c7559b29bd), with its module paths changed. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
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
Lemma D_e29e4 : decode_any W_e29e4 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.
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
Lemma D_e2a14 : decode_any W_e2a14 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2a18 : bv 32 := 0x00c50633.
Lemma D_e2a18 : decode_any W_e2a18 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2a1c : bv 32 := 0x0005b023.
Lemma D_e2a1c : decode_any W_e2a1c = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2a20 : bv 32 := 0x0005b423.
Lemma D_e2a20 : decode_any W_e2a20 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2a24 : bv 32 := 0x01058593.
Lemma D_e2a24 : decode_any W_e2a24 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2a28 : bv 32 := 0xfec5eae3.
Lemma D_e2a28 : decode_any W_e2a28 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.
Definition W_e2a2c : bv 32 := 0x00008067.
Lemma D_e2a2c : decode_any W_e2a2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c96ec : bv 32 := 0x00200613.
Lemma D_c96ec : decode_any W_c96ec = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_c96f0 : bv 32 := 0x14c5ea63.
Lemma D_c96f0 : decode_any W_c96f0 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.
Definition W_c96f4 : bv 32 := 0x00100613.
Lemma D_c96f4 : decode_any W_c96f4 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_c96f8 : bv 32 := 0x00100693.
Lemma D_c96f8 : decode_any W_c96f8 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_c96fc : bv 32 := 0x00c0006f.
Lemma D_c96fc : decode_any W_c96fc = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9700 : bv 32 := 0x00160613.
Lemma D_c9700 : decode_any W_c9700 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9704 : bv 32 := 0x12b60c63.
Lemma D_c9704 : decode_any W_c9704 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9708 : bv 32 := 0x00461713.
Lemma D_c9708 : decode_any W_c9708 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_c970c : bv 32 := 0x00e50733.
Lemma D_c970c : decode_any W_c970c = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9710 : bv 32 := 0x00072703.
Lemma D_c9710 : decode_any W_c9710 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9714 : bv 32 := 0x00060893.
Lemma D_c9714 : decode_any W_c9714 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9718 : bv 32 := 0xfff88793.
Lemma D_c9718 : decode_any W_c9718 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.
Definition W_c971c : bv 32 := 0x0017d813.
Lemma D_c971c : decode_any W_c971c = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9720 : bv 32 := 0x00481293.
Lemma D_c9720 : decode_any W_c9720 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9724 : bv 32 := 0x005502b3.
Lemma D_c9724 : decode_any W_c9724 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9728 : bv 32 := 0x0002a303.
Lemma D_c9728 : decode_any W_c9728 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c972c : bv 32 := 0xfce37ae3.
Lemma D_c972c : decode_any W_c972c = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9730 : bv 32 := 0x0002b303.
Lemma D_c9730 : decode_any W_c9730 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9734 : bv 32 := 0x00489893.
Lemma D_c9734 : decode_any W_c9734 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9738 : bv 32 := 0x011508b3.
Lemma D_c9738 : decode_any W_c9738 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.
Definition W_c973c : bv 32 := 0x0048a383.
Lemma D_c973c : decode_any W_c973c = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9740 : bv 32 := 0x0068b023.
Lemma D_c9740 : decode_any W_c9740 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9744 : bv 32 := 0x0082b303.
Lemma D_c9744 : decode_any W_c9744 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9748 : bv 32 := 0x0088be03.
Lemma D_c9748 : decode_any W_c9748 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_c974c : bv 32 := 0x0068b423.
Lemma D_c974c : decode_any W_c974c = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9750 : bv 32 := 0x00e2a023.
Lemma D_c9750 : decode_any W_c9750 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9754 : bv 32 := 0x0072a223.
Lemma D_c9754 : decode_any W_c9754 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9758 : bv 32 := 0x01c2b423.
Lemma D_c9758 : decode_any W_c9758 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_c975c : bv 32 := 0x00080893.
Lemma D_c975c : decode_any W_c975c = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9760 : bv 32 := 0xfaf6ece3.
Lemma D_c9760 : decode_any W_c9760 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9764 : bv 32 := 0xf9dff06f.
Lemma D_c9764 : decode_any W_c9764 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9768 : bv 32 := 0x00000613.
Lemma D_c9768 : decode_any W_c9768 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c976c : bv 32 := 0x00459693.
Lemma D_c976c : decode_any W_c976c = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9770 : bv 32 := 0x00d506b3.
Lemma D_c9770 : decode_any W_c9770 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9774 : bv 32 := 0x0006b703.
Lemma D_c9774 : decode_any W_c9774 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9778 : bv 32 := 0x0086b783.
Lemma D_c9778 : decode_any W_c9778 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_c977c : bv 32 := 0x00053803.
Lemma D_c977c : decode_any W_c977c = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9780 : bv 32 := 0x00853883.
Lemma D_c9780 : decode_any W_c9780 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9784 : bv 32 := 0x00e53023.
Lemma D_c9784 : decode_any W_c9784 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9788 : bv 32 := 0x00f53423.
Lemma D_c9788 : decode_any W_c9788 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_c978c : bv 32 := 0x0106b023.
Lemma D_c978c : decode_any W_c978c = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9790 : bv 32 := 0x0116b423.
Lemma D_c9790 : decode_any W_c9790 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9794 : bv 32 := 0x00000693.
Lemma D_c9794 : decode_any W_c9794 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9798 : bv 32 := 0x00161793.
Lemma D_c9798 : decode_any W_c9798 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_c979c : bv 32 := 0x00178813.
Lemma D_c979c : decode_any W_c979c = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97a0 : bv 32 := 0x00461713.
Lemma D_c97a0 : decode_any W_c97a0 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97a4 : bv 32 := 0x00b86a63.
Lemma D_c97a4 : decode_any W_c97a4 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97a8 : bv 32 := 0x00278793.
Lemma D_c97a8 : decode_any W_c97a8 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97ac : bv 32 := 0x02b7ea63.
Lemma D_c97ac : decode_any W_c97ac = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97b0 : bv 32 := 0x04c69c63.
Lemma D_c97b0 : decode_any W_c97b0 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97b4 : bv 32 := 0x0880006f.
Lemma D_c97b4 : decode_any W_c97b4 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97b8 : bv 32 := 0x00e506b3.
Lemma D_c97b8 : decode_any W_c97b8 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97bc : bv 32 := 0x00481893.
Lemma D_c97bc : decode_any W_c97bc = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97c0 : bv 32 := 0x011508b3.
Lemma D_c97c0 : decode_any W_c97c0 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97c4 : bv 32 := 0x0006a683.
Lemma D_c97c4 : decode_any W_c97c4 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97c8 : bv 32 := 0x0008a883.
Lemma D_c97c8 : decode_any W_c97c8 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97cc : bv 32 := 0x0116e463.
Lemma D_c97cc : decode_any W_c97cc = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97d0 : bv 32 := 0x00060813.
Lemma D_c97d0 : decode_any W_c97d0 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97d4 : bv 32 := 0x00080693.
Lemma D_c97d4 : decode_any W_c97d4 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97d8 : bv 32 := 0x00278793.
Lemma D_c97d8 : decode_any W_c97d8 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97dc : bv 32 := 0xfcb7fae3.
Lemma D_c97dc : decode_any W_c97dc = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97e0 : bv 32 := 0x00469813.
Lemma D_c97e0 : decode_any W_c97e0 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97e4 : bv 32 := 0x00479893.
Lemma D_c97e4 : decode_any W_c97e4 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97e8 : bv 32 := 0x01050833.
Lemma D_c97e8 : decode_any W_c97e8 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97ec : bv 32 := 0x011508b3.
Lemma D_c97ec : decode_any W_c97ec = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97f0 : bv 32 := 0x00082803.
Lemma D_c97f0 : decode_any W_c97f0 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97f4 : bv 32 := 0x0008a883.
Lemma D_c97f4 : decode_any W_c97f4 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97f8 : bv 32 := 0x01186463.
Lemma D_c97f8 : decode_any W_c97f8 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_c97fc : bv 32 := 0x00068793.
Lemma D_c97fc : decode_any W_c97fc = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9800 : bv 32 := 0x00078693.
Lemma D_c9800 : decode_any W_c9800 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9804 : bv 32 := 0x02c78c63.
Lemma D_c9804 : decode_any W_c9804 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9808 : bv 32 := 0x00469613.
Lemma D_c9808 : decode_any W_c9808 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_c980c : bv 32 := 0x00c50633.
Lemma D_c980c : decode_any W_c980c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9810 : bv 32 := 0x00063783.
Lemma D_c9810 : decode_any W_c9810 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9814 : bv 32 := 0x00e50733.
Lemma D_c9814 : decode_any W_c9814 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9818 : bv 32 := 0x00073803.
Lemma D_c9818 : decode_any W_c9818 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c981c : bv 32 := 0x00873883.
Lemma D_c981c : decode_any W_c981c = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9820 : bv 32 := 0x00f73023.
Lemma D_c9820 : decode_any W_c9820 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9824 : bv 32 := 0x00863783.
Lemma D_c9824 : decode_any W_c9824 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9828 : bv 32 := 0x00f73423.
Lemma D_c9828 : decode_any W_c9828 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_c982c : bv 32 := 0x01063023.
Lemma D_c982c : decode_any W_c982c = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9830 : bv 32 := 0x01163423.
Lemma D_c9830 : decode_any W_c9830 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9834 : bv 32 := 0x00068613.
Lemma D_c9834 : decode_any W_c9834 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9838 : bv 32 := 0xf6b6e0e3.
Lemma D_c9838 : decode_any W_c9838 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.
Definition W_c983c : bv 32 := 0xfff58593.
Lemma D_c983c : decode_any W_c983c = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9840 : bv 32 := 0xf20594e3.
Lemma D_c9840 : decode_any W_c9840 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.
Definition W_c9844 : bv 32 := 0x00008067.
Lemma D_c9844 : decode_any W_c9844 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
