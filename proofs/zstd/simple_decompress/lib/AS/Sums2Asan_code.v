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
Definition W_665c0 : bv 32 := 0x06060663.
Lemma D_665c0 : decode_any W_665c0 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665c4 : bv 32 := 0x00000693.
Lemma D_665c4 : decode_any W_665c4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665c8 : bv 32 := 0x00d58733.
Lemma D_665c8 : decode_any W_665c8 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665cc : bv 32 := 0x00074703.
Lemma D_665cc : decode_any W_665cc = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665d0 : bv 32 := 0x00070c63.
Lemma D_665d0 : decode_any W_665d0 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665d4 : bv 32 := 0x00d507b3.
Lemma D_665d4 : decode_any W_665d4 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665d8 : bv 32 := 0x00168693.
Lemma D_665d8 : decode_any W_665d8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665dc : bv 32 := 0x00e78023.
Lemma D_665dc : decode_any W_665dc = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665e0 : bv 32 := 0xfed614e3.
Lemma D_665e0 : decode_any W_665e0 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665e4 : bv 32 := 0x00060693.
Lemma D_665e4 : decode_any W_665e4 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665e8 : bv 32 := 0x00d505b3.
Lemma D_665e8 : decode_any W_665e8 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665ec : bv 32 := 0x40d6073b.
Lemma D_665ec : decode_any W_665ec = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665f0 : bv 32 := 0x00b76733.
Lemma D_665f0 : decode_any W_665f0 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665f4 : bv 32 := 0x00f77713.
Lemma D_665f4 : decode_any W_665f4 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665f8 : bv 32 := 0x00070e63.
Lemma D_665f8 : decode_any W_665f8 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665fc : bv 32 := 0x02d60863.
Lemma D_665fc : decode_any W_665fc = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66600 : bv 32 := 0x00c50633.
Lemma D_66600 : decode_any W_66600 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66604 : bv 32 := 0x00058023.
Lemma D_66604 : decode_any W_66604 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66608 : bv 32 := 0x00158593.
Lemma D_66608 : decode_any W_66608 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6660c : bv 32 := 0xfec59ce3.
Lemma D_6660c : decode_any W_6660c = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66610 : bv 32 := 0x01c0006f.
Lemma D_66610 : decode_any W_66610 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66614 : bv 32 := 0x00d60c63.
Lemma D_66614 : decode_any W_66614 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66618 : bv 32 := 0x00c50633.
Lemma D_66618 : decode_any W_66618 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6661c : bv 32 := 0x0005b023.
Lemma D_6661c : decode_any W_6661c = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66620 : bv 32 := 0x0005b423.
Lemma D_66620 : decode_any W_66620 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66624 : bv 32 := 0x01058593.
Lemma D_66624 : decode_any W_66624 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66628 : bv 32 := 0xfec5eae3.
Lemma D_66628 : decode_any W_66628 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6662c : bv 32 := 0x00008067.
Lemma D_6662c : decode_any W_6662c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.



(* [comment removed for export] *)
Definition W_53934 : bv 32 := 0x00200613.
Lemma D_53934 : decode_any W_53934 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53938 : bv 32 := 0x14c5ea63.
Lemma D_53938 : decode_any W_53938 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5393c : bv 32 := 0x00100613.
Lemma D_5393c : decode_any W_5393c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53940 : bv 32 := 0x00100693.
Lemma D_53940 : decode_any W_53940 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53944 : bv 32 := 0x00c0006f.
Lemma D_53944 : decode_any W_53944 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53948 : bv 32 := 0x00160613.
Lemma D_53948 : decode_any W_53948 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5394c : bv 32 := 0x12b60c63.
Lemma D_5394c : decode_any W_5394c = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53950 : bv 32 := 0x00461713.
Lemma D_53950 : decode_any W_53950 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53954 : bv 32 := 0x00e50733.
Lemma D_53954 : decode_any W_53954 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53958 : bv 32 := 0x00072703.
Lemma D_53958 : decode_any W_53958 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5395c : bv 32 := 0x00060893.
Lemma D_5395c : decode_any W_5395c = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53960 : bv 32 := 0xfff88793.
Lemma D_53960 : decode_any W_53960 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53964 : bv 32 := 0x0017d813.
Lemma D_53964 : decode_any W_53964 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53968 : bv 32 := 0x00481293.
Lemma D_53968 : decode_any W_53968 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5396c : bv 32 := 0x005502b3.
Lemma D_5396c : decode_any W_5396c = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53970 : bv 32 := 0x0002a303.
Lemma D_53970 : decode_any W_53970 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53974 : bv 32 := 0xfce37ae3.
Lemma D_53974 : decode_any W_53974 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53978 : bv 32 := 0x0002b303.
Lemma D_53978 : decode_any W_53978 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5397c : bv 32 := 0x00489893.
Lemma D_5397c : decode_any W_5397c = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53980 : bv 32 := 0x011508b3.
Lemma D_53980 : decode_any W_53980 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53984 : bv 32 := 0x0048a383.
Lemma D_53984 : decode_any W_53984 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53988 : bv 32 := 0x0068b023.
Lemma D_53988 : decode_any W_53988 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5398c : bv 32 := 0x0082b303.
Lemma D_5398c : decode_any W_5398c = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53990 : bv 32 := 0x0088be03.
Lemma D_53990 : decode_any W_53990 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53994 : bv 32 := 0x0068b423.
Lemma D_53994 : decode_any W_53994 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53998 : bv 32 := 0x00e2a023.
Lemma D_53998 : decode_any W_53998 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5399c : bv 32 := 0x0072a223.
Lemma D_5399c : decode_any W_5399c = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539a0 : bv 32 := 0x01c2b423.
Lemma D_539a0 : decode_any W_539a0 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539a4 : bv 32 := 0x00080893.
Lemma D_539a4 : decode_any W_539a4 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539a8 : bv 32 := 0xfaf6ece3.
Lemma D_539a8 : decode_any W_539a8 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539ac : bv 32 := 0xf9dff06f.
Lemma D_539ac : decode_any W_539ac = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539b0 : bv 32 := 0x00000613.
Lemma D_539b0 : decode_any W_539b0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539b4 : bv 32 := 0x00459693.
Lemma D_539b4 : decode_any W_539b4 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539b8 : bv 32 := 0x00d506b3.
Lemma D_539b8 : decode_any W_539b8 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539bc : bv 32 := 0x0006b703.
Lemma D_539bc : decode_any W_539bc = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539c0 : bv 32 := 0x0086b783.
Lemma D_539c0 : decode_any W_539c0 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539c4 : bv 32 := 0x00053803.
Lemma D_539c4 : decode_any W_539c4 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539c8 : bv 32 := 0x00853883.
Lemma D_539c8 : decode_any W_539c8 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539cc : bv 32 := 0x00e53023.
Lemma D_539cc : decode_any W_539cc = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539d0 : bv 32 := 0x00f53423.
Lemma D_539d0 : decode_any W_539d0 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539d4 : bv 32 := 0x0106b023.
Lemma D_539d4 : decode_any W_539d4 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539d8 : bv 32 := 0x0116b423.
Lemma D_539d8 : decode_any W_539d8 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539dc : bv 32 := 0x00000693.
Lemma D_539dc : decode_any W_539dc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539e0 : bv 32 := 0x00161793.
Lemma D_539e0 : decode_any W_539e0 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539e4 : bv 32 := 0x00178813.
Lemma D_539e4 : decode_any W_539e4 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539e8 : bv 32 := 0x00461713.
Lemma D_539e8 : decode_any W_539e8 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539ec : bv 32 := 0x00b86a63.
Lemma D_539ec : decode_any W_539ec = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539f0 : bv 32 := 0x00278793.
Lemma D_539f0 : decode_any W_539f0 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539f4 : bv 32 := 0x02b7ea63.
Lemma D_539f4 : decode_any W_539f4 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539f8 : bv 32 := 0x04c69c63.
Lemma D_539f8 : decode_any W_539f8 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_539fc : bv 32 := 0x0880006f.
Lemma D_539fc : decode_any W_539fc = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a00 : bv 32 := 0x00e506b3.
Lemma D_53a00 : decode_any W_53a00 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a04 : bv 32 := 0x00481893.
Lemma D_53a04 : decode_any W_53a04 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a08 : bv 32 := 0x011508b3.
Lemma D_53a08 : decode_any W_53a08 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a0c : bv 32 := 0x0006a683.
Lemma D_53a0c : decode_any W_53a0c = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a10 : bv 32 := 0x0008a883.
Lemma D_53a10 : decode_any W_53a10 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a14 : bv 32 := 0x0116e463.
Lemma D_53a14 : decode_any W_53a14 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a18 : bv 32 := 0x00060813.
Lemma D_53a18 : decode_any W_53a18 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a1c : bv 32 := 0x00080693.
Lemma D_53a1c : decode_any W_53a1c = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a20 : bv 32 := 0x00278793.
Lemma D_53a20 : decode_any W_53a20 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a24 : bv 32 := 0xfcb7fae3.
Lemma D_53a24 : decode_any W_53a24 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a28 : bv 32 := 0x00469813.
Lemma D_53a28 : decode_any W_53a28 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a2c : bv 32 := 0x00479893.
Lemma D_53a2c : decode_any W_53a2c = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a30 : bv 32 := 0x01050833.
Lemma D_53a30 : decode_any W_53a30 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a34 : bv 32 := 0x011508b3.
Lemma D_53a34 : decode_any W_53a34 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a38 : bv 32 := 0x00082803.
Lemma D_53a38 : decode_any W_53a38 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a3c : bv 32 := 0x0008a883.
Lemma D_53a3c : decode_any W_53a3c = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a40 : bv 32 := 0x01186463.
Lemma D_53a40 : decode_any W_53a40 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a44 : bv 32 := 0x00068793.
Lemma D_53a44 : decode_any W_53a44 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a48 : bv 32 := 0x00078693.
Lemma D_53a48 : decode_any W_53a48 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a4c : bv 32 := 0x02c78c63.
Lemma D_53a4c : decode_any W_53a4c = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a50 : bv 32 := 0x00469613.
Lemma D_53a50 : decode_any W_53a50 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a54 : bv 32 := 0x00c50633.
Lemma D_53a54 : decode_any W_53a54 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a58 : bv 32 := 0x00063783.
Lemma D_53a58 : decode_any W_53a58 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a5c : bv 32 := 0x00e50733.
Lemma D_53a5c : decode_any W_53a5c = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a60 : bv 32 := 0x00073803.
Lemma D_53a60 : decode_any W_53a60 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a64 : bv 32 := 0x00873883.
Lemma D_53a64 : decode_any W_53a64 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a68 : bv 32 := 0x00f73023.
Lemma D_53a68 : decode_any W_53a68 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a6c : bv 32 := 0x00863783.
Lemma D_53a6c : decode_any W_53a6c = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a70 : bv 32 := 0x00f73423.
Lemma D_53a70 : decode_any W_53a70 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a74 : bv 32 := 0x01063023.
Lemma D_53a74 : decode_any W_53a74 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a78 : bv 32 := 0x01163423.
Lemma D_53a78 : decode_any W_53a78 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a7c : bv 32 := 0x00068613.
Lemma D_53a7c : decode_any W_53a7c = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a80 : bv 32 := 0xf6b6e0e3.
Lemma D_53a80 : decode_any W_53a80 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a84 : bv 32 := 0xfff58593.
Lemma D_53a84 : decode_any W_53a84 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a88 : bv 32 := 0xf20594e3.
Lemma D_53a88 : decode_any W_53a88 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_53a8c : bv 32 := 0x00008067.
Lemma D_53a8c : decode_any W_53a8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
