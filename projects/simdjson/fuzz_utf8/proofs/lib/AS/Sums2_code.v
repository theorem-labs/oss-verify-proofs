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
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_93608 : bv 32 := 0x06060663.
Lemma D_93608 : decode_any W_93608 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9360c : bv 32 := 0x00000693.
Lemma D_9360c : decode_any W_9360c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93610 : bv 32 := 0x00d58733.
Lemma D_93610 : decode_any W_93610 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93614 : bv 32 := 0x00074703.
Lemma D_93614 : decode_any W_93614 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93618 : bv 32 := 0x00070c63.
Lemma D_93618 : decode_any W_93618 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9361c : bv 32 := 0x00d507b3.
Lemma D_9361c : decode_any W_9361c = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93620 : bv 32 := 0x00168693.
Lemma D_93620 : decode_any W_93620 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93624 : bv 32 := 0x00e78023.
Lemma D_93624 : decode_any W_93624 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93628 : bv 32 := 0xfed614e3.
Lemma D_93628 : decode_any W_93628 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9362c : bv 32 := 0x00060693.
Lemma D_9362c : decode_any W_9362c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93630 : bv 32 := 0x00d505b3.
Lemma D_93630 : decode_any W_93630 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93634 : bv 32 := 0x40d6073b.
Lemma D_93634 : decode_any W_93634 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93638 : bv 32 := 0x00b76733.
Lemma D_93638 : decode_any W_93638 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9363c : bv 32 := 0x00f77713.
Lemma D_9363c : decode_any W_9363c = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93640 : bv 32 := 0x00070e63.
Lemma D_93640 : decode_any W_93640 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93644 : bv 32 := 0x02d60863.
Lemma D_93644 : decode_any W_93644 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93648 : bv 32 := 0x00c50633.
Lemma D_93648 : decode_any W_93648 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9364c : bv 32 := 0x00058023.
Lemma D_9364c : decode_any W_9364c = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93650 : bv 32 := 0x00158593.
Lemma D_93650 : decode_any W_93650 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93654 : bv 32 := 0xfec59ce3.
Lemma D_93654 : decode_any W_93654 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93658 : bv 32 := 0x01c0006f.
Lemma D_93658 : decode_any W_93658 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9365c : bv 32 := 0x00d60c63.
Lemma D_9365c : decode_any W_9365c = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93660 : bv 32 := 0x00c50633.
Lemma D_93660 : decode_any W_93660 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93664 : bv 32 := 0x0005b023.
Lemma D_93664 : decode_any W_93664 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93668 : bv 32 := 0x0005b423.
Lemma D_93668 : decode_any W_93668 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9366c : bv 32 := 0x01058593.
Lemma D_9366c : decode_any W_9366c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93670 : bv 32 := 0xfec5eae3.
Lemma D_93670 : decode_any W_93670 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93674 : bv 32 := 0x00008067.
Lemma D_93674 : decode_any W_93674 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.



(* [comment removed for export] *)
Definition W_7f3e8 : bv 32 := 0x00200613.
Lemma D_7f3e8 : decode_any W_7f3e8 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f3ec : bv 32 := 0x14c5ea63.
Lemma D_7f3ec : decode_any W_7f3ec = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f3f0 : bv 32 := 0x00100613.
Lemma D_7f3f0 : decode_any W_7f3f0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f3f4 : bv 32 := 0x00100693.
Lemma D_7f3f4 : decode_any W_7f3f4 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f3f8 : bv 32 := 0x00c0006f.
Lemma D_7f3f8 : decode_any W_7f3f8 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f3fc : bv 32 := 0x00160613.
Lemma D_7f3fc : decode_any W_7f3fc = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f400 : bv 32 := 0x12b60c63.
Lemma D_7f400 : decode_any W_7f400 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f404 : bv 32 := 0x00461713.
Lemma D_7f404 : decode_any W_7f404 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f408 : bv 32 := 0x00e50733.
Lemma D_7f408 : decode_any W_7f408 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f40c : bv 32 := 0x00072703.
Lemma D_7f40c : decode_any W_7f40c = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f410 : bv 32 := 0x00060893.
Lemma D_7f410 : decode_any W_7f410 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f414 : bv 32 := 0xfff88793.
Lemma D_7f414 : decode_any W_7f414 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f418 : bv 32 := 0x0017d813.
Lemma D_7f418 : decode_any W_7f418 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f41c : bv 32 := 0x00481293.
Lemma D_7f41c : decode_any W_7f41c = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f420 : bv 32 := 0x005502b3.
Lemma D_7f420 : decode_any W_7f420 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f424 : bv 32 := 0x0002a303.
Lemma D_7f424 : decode_any W_7f424 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f428 : bv 32 := 0xfce37ae3.
Lemma D_7f428 : decode_any W_7f428 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f42c : bv 32 := 0x0002b303.
Lemma D_7f42c : decode_any W_7f42c = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f430 : bv 32 := 0x00489893.
Lemma D_7f430 : decode_any W_7f430 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f434 : bv 32 := 0x011508b3.
Lemma D_7f434 : decode_any W_7f434 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f438 : bv 32 := 0x0048a383.
Lemma D_7f438 : decode_any W_7f438 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f43c : bv 32 := 0x0068b023.
Lemma D_7f43c : decode_any W_7f43c = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f440 : bv 32 := 0x0082b303.
Lemma D_7f440 : decode_any W_7f440 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f444 : bv 32 := 0x0088be03.
Lemma D_7f444 : decode_any W_7f444 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f448 : bv 32 := 0x0068b423.
Lemma D_7f448 : decode_any W_7f448 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f44c : bv 32 := 0x00e2a023.
Lemma D_7f44c : decode_any W_7f44c = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f450 : bv 32 := 0x0072a223.
Lemma D_7f450 : decode_any W_7f450 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f454 : bv 32 := 0x01c2b423.
Lemma D_7f454 : decode_any W_7f454 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f458 : bv 32 := 0x00080893.
Lemma D_7f458 : decode_any W_7f458 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f45c : bv 32 := 0xfaf6ece3.
Lemma D_7f45c : decode_any W_7f45c = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f460 : bv 32 := 0xf9dff06f.
Lemma D_7f460 : decode_any W_7f460 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f464 : bv 32 := 0x00000613.
Lemma D_7f464 : decode_any W_7f464 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f468 : bv 32 := 0x00459693.
Lemma D_7f468 : decode_any W_7f468 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f46c : bv 32 := 0x00d506b3.
Lemma D_7f46c : decode_any W_7f46c = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f470 : bv 32 := 0x0006b703.
Lemma D_7f470 : decode_any W_7f470 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f474 : bv 32 := 0x0086b783.
Lemma D_7f474 : decode_any W_7f474 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f478 : bv 32 := 0x00053803.
Lemma D_7f478 : decode_any W_7f478 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f47c : bv 32 := 0x00853883.
Lemma D_7f47c : decode_any W_7f47c = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f480 : bv 32 := 0x00e53023.
Lemma D_7f480 : decode_any W_7f480 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f484 : bv 32 := 0x00f53423.
Lemma D_7f484 : decode_any W_7f484 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f488 : bv 32 := 0x0106b023.
Lemma D_7f488 : decode_any W_7f488 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f48c : bv 32 := 0x0116b423.
Lemma D_7f48c : decode_any W_7f48c = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f490 : bv 32 := 0x00000693.
Lemma D_7f490 : decode_any W_7f490 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f494 : bv 32 := 0x00161793.
Lemma D_7f494 : decode_any W_7f494 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f498 : bv 32 := 0x00178813.
Lemma D_7f498 : decode_any W_7f498 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f49c : bv 32 := 0x00461713.
Lemma D_7f49c : decode_any W_7f49c = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4a0 : bv 32 := 0x00b86a63.
Lemma D_7f4a0 : decode_any W_7f4a0 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4a4 : bv 32 := 0x00278793.
Lemma D_7f4a4 : decode_any W_7f4a4 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4a8 : bv 32 := 0x02b7ea63.
Lemma D_7f4a8 : decode_any W_7f4a8 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4ac : bv 32 := 0x04c69c63.
Lemma D_7f4ac : decode_any W_7f4ac = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4b0 : bv 32 := 0x0880006f.
Lemma D_7f4b0 : decode_any W_7f4b0 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4b4 : bv 32 := 0x00e506b3.
Lemma D_7f4b4 : decode_any W_7f4b4 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4b8 : bv 32 := 0x00481893.
Lemma D_7f4b8 : decode_any W_7f4b8 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4bc : bv 32 := 0x011508b3.
Lemma D_7f4bc : decode_any W_7f4bc = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4c0 : bv 32 := 0x0006a683.
Lemma D_7f4c0 : decode_any W_7f4c0 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4c4 : bv 32 := 0x0008a883.
Lemma D_7f4c4 : decode_any W_7f4c4 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4c8 : bv 32 := 0x0116e463.
Lemma D_7f4c8 : decode_any W_7f4c8 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4cc : bv 32 := 0x00060813.
Lemma D_7f4cc : decode_any W_7f4cc = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4d0 : bv 32 := 0x00080693.
Lemma D_7f4d0 : decode_any W_7f4d0 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4d4 : bv 32 := 0x00278793.
Lemma D_7f4d4 : decode_any W_7f4d4 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4d8 : bv 32 := 0xfcb7fae3.
Lemma D_7f4d8 : decode_any W_7f4d8 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4dc : bv 32 := 0x00469813.
Lemma D_7f4dc : decode_any W_7f4dc = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4e0 : bv 32 := 0x00479893.
Lemma D_7f4e0 : decode_any W_7f4e0 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4e4 : bv 32 := 0x01050833.
Lemma D_7f4e4 : decode_any W_7f4e4 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4e8 : bv 32 := 0x011508b3.
Lemma D_7f4e8 : decode_any W_7f4e8 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4ec : bv 32 := 0x00082803.
Lemma D_7f4ec : decode_any W_7f4ec = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4f0 : bv 32 := 0x0008a883.
Lemma D_7f4f0 : decode_any W_7f4f0 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4f4 : bv 32 := 0x01186463.
Lemma D_7f4f4 : decode_any W_7f4f4 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4f8 : bv 32 := 0x00068793.
Lemma D_7f4f8 : decode_any W_7f4f8 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f4fc : bv 32 := 0x00078693.
Lemma D_7f4fc : decode_any W_7f4fc = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f500 : bv 32 := 0x02c78c63.
Lemma D_7f500 : decode_any W_7f500 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f504 : bv 32 := 0x00469613.
Lemma D_7f504 : decode_any W_7f504 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f508 : bv 32 := 0x00c50633.
Lemma D_7f508 : decode_any W_7f508 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f50c : bv 32 := 0x00063783.
Lemma D_7f50c : decode_any W_7f50c = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f510 : bv 32 := 0x00e50733.
Lemma D_7f510 : decode_any W_7f510 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f514 : bv 32 := 0x00073803.
Lemma D_7f514 : decode_any W_7f514 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f518 : bv 32 := 0x00873883.
Lemma D_7f518 : decode_any W_7f518 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f51c : bv 32 := 0x00f73023.
Lemma D_7f51c : decode_any W_7f51c = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f520 : bv 32 := 0x00863783.
Lemma D_7f520 : decode_any W_7f520 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f524 : bv 32 := 0x00f73423.
Lemma D_7f524 : decode_any W_7f524 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f528 : bv 32 := 0x01063023.
Lemma D_7f528 : decode_any W_7f528 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f52c : bv 32 := 0x01163423.
Lemma D_7f52c : decode_any W_7f52c = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f530 : bv 32 := 0x00068613.
Lemma D_7f530 : decode_any W_7f530 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f534 : bv 32 := 0xf6b6e0e3.
Lemma D_7f534 : decode_any W_7f534 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f538 : bv 32 := 0xfff58593.
Lemma D_7f538 : decode_any W_7f538 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f53c : bv 32 := 0xf20594e3.
Lemma D_7f53c : decode_any W_7f53c = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7f540 : bv 32 := 0x00008067.
Lemma D_7f540 : decode_any W_7f540 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
