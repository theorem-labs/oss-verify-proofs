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

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_ca150 : bv 32 := 0x02060063.
Lemma D_ca150 : decode_any W_ca150 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca154 : bv 32 := 0x00c50633.
Lemma D_ca154 : decode_any W_ca154 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca158 : bv 32 := 0x00050693.
Lemma D_ca158 : decode_any W_ca158 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca15c : bv 32 := 0x0005c703.
Lemma D_ca15c : decode_any W_ca15c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca160 : bv 32 := 0x00e68023.
Lemma D_ca160 : decode_any W_ca160 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca164 : bv 32 := 0x00168693.
Lemma D_ca164 : decode_any W_ca164 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca168 : bv 32 := 0x00158593.
Lemma D_ca168 : decode_any W_ca168 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca16c : bv 32 := 0xfec698e3.
Lemma D_ca16c : decode_any W_ca16c = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca170 : bv 32 := 0x00008067.
Lemma D_ca170 : decode_any W_ca170 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca1cc : bv 32 := 0x00a666b3.
Lemma D_ca1cc : decode_any W_ca1cc = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca1d0 : bv 32 := 0x00f6f693.
Lemma D_ca1d0 : decode_any W_ca1d0 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca1d4 : bv 32 := 0x02068063.
Lemma D_ca1d4 : decode_any W_ca1d4 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca1d8 : bv 32 := 0x04060863.
Lemma D_ca1d8 : decode_any W_ca1d8 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca1dc : bv 32 := 0x00c50633.
Lemma D_ca1dc : decode_any W_ca1dc = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca1e0 : bv 32 := 0x00050693.
Lemma D_ca1e0 : decode_any W_ca1e0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca1e4 : bv 32 := 0x00b68023.
Lemma D_ca1e4 : decode_any W_ca1e4 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca1e8 : bv 32 := 0x00168693.
Lemma D_ca1e8 : decode_any W_ca1e8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca1ec : bv 32 := 0xfec69ce3.
Lemma D_ca1ec : decode_any W_ca1ec = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca1f0 : bv 32 := 0x0380006f.
Lemma D_ca1f0 : decode_any W_ca1f0 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca1f4 : bv 32 := 0x02060a63.
Lemma D_ca1f4 : decode_any W_ca1f4 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca1f8 : bv 32 := 0x00c50633.
Lemma D_ca1f8 : decode_any W_ca1f8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca1fc : bv 32 := 0x00859693.
Lemma D_ca1fc : decode_any W_ca1fc = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca200 : bv 32 := 0x00b6e5b3.
Lemma D_ca200 : decode_any W_ca200 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca204 : bv 32 := 0x01059693.
Lemma D_ca204 : decode_any W_ca204 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca208 : bv 32 := 0x00b6e5b3.
Lemma D_ca208 : decode_any W_ca208 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca20c : bv 32 := 0x02059693.
Lemma D_ca20c : decode_any W_ca20c = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca210 : bv 32 := 0x00b6e5b3.
Lemma D_ca210 : decode_any W_ca210 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca214 : bv 32 := 0x00050693.
Lemma D_ca214 : decode_any W_ca214 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca218 : bv 32 := 0x00b6b023.
Lemma D_ca218 : decode_any W_ca218 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca21c : bv 32 := 0x00b6b423.
Lemma D_ca21c : decode_any W_ca21c = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca220 : bv 32 := 0x01068693.
Lemma D_ca220 : decode_any W_ca220 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca224 : bv 32 := 0xfec6eae3.
Lemma D_ca224 : decode_any W_ca224 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca228 : bv 32 := 0x00008067.
Lemma D_ca228 : decode_any W_ca228 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca6fc : bv 32 := 0xff010113.
Lemma D_ca6fc : decode_any W_ca6fc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca700 : bv 32 := 0x00113423.
Lemma D_ca700 : decode_any W_ca700 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca704 : bv 32 := 0x00058693.
Lemma D_ca704 : decode_any W_ca704 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca708 : bv 32 := 0x00100713.
Lemma D_ca708 : decode_any W_ca708 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca70c : bv 32 := 0x02871713.
Lemma D_ca70c : decode_any W_ca70c = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca710 : bv 32 := 0x00170593.
Lemma D_ca710 : decode_any W_ca710 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca714 : bv 32 := 0x08b6f263.
Lemma D_ca714 : decode_any W_ca714 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca718 : bv 32 := 0x00000593.
Lemma D_ca718 : decode_any W_ca718 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca71c : bv 32 := 0x00d50733.
Lemma D_ca71c : decode_any W_ca71c = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca720 : bv 32 := 0x00750793.
Lemma D_ca720 : decode_any W_ca720 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca724 : bv 32 := 0xff87f793.
Lemma D_ca724 : decode_any W_ca724 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca728 : bv 32 := 0xff877613.
Lemma D_ca728 : decode_any W_ca728 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca72c : bv 32 := 0x02f57463.
Lemma D_ca72c : decode_any W_ca72c = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca730 : bv 32 := 0x02068263.
Lemma D_ca730 : decode_any W_ca730 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca734 : bv 32 := 0x00000593.
Lemma D_ca734 : decode_any W_ca734 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca738 : bv 32 := 0x00150693.
Lemma D_ca738 : decode_any W_ca738 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca73c : bv 32 := 0x00068813.
Lemma D_ca73c : decode_any W_ca73c = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca740 : bv 32 := 0xfff6c683.
Lemma D_ca740 : decode_any W_ca740 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca744 : bv 32 := 0x00d5e5b3.
Lemma D_ca744 : decode_any W_ca744 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca748 : bv 32 := 0x00f87663.
Lemma D_ca748 : decode_any W_ca748 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca74c : bv 32 := 0x00180693.
Lemma D_ca74c : decode_any W_ca74c = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca750 : bv 32 := 0xfee866e3.
Lemma D_ca750 : decode_any W_ca750 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca754 : bv 32 := 0x00c7fa63.
Lemma D_ca754 : decode_any W_ca754 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca758 : bv 32 := 0x0007b683.
Lemma D_ca758 : decode_any W_ca758 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca75c : bv 32 := 0x00878793.
Lemma D_ca75c : decode_any W_ca75c = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca760 : bv 32 := 0x00b6e5b3.
Lemma D_ca760 : decode_any W_ca760 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca764 : bv 32 := 0xfec7eae3.
Lemma D_ca764 : decode_any W_ca764 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca768 : bv 32 := 0x02a66063.
Lemma D_ca768 : decode_any W_ca768 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca76c : bv 32 := 0x00e67e63.
Lemma D_ca76c : decode_any W_ca76c = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca770 : bv 32 := 0x40c70733.
Lemma D_ca770 : decode_any W_ca770 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca774 : bv 32 := 0x00064503.
Lemma D_ca774 : decode_any W_ca774 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca778 : bv 32 := 0xfff70713.
Lemma D_ca778 : decode_any W_ca778 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca77c : bv 32 := 0x00a5e5b3.
Lemma D_ca77c : decode_any W_ca77c = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca780 : bv 32 := 0x00160613.
Lemma D_ca780 : decode_any W_ca780 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca784 : bv 32 := 0xfe0718e3.
Lemma D_ca784 : decode_any W_ca784 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca788 : bv 32 := 0x0015b513.
Lemma D_ca788 : decode_any W_ca788 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca78c : bv 32 := 0x00813083.
Lemma D_ca78c : decode_any W_ca78c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca790 : bv 32 := 0x01010113.
Lemma D_ca790 : decode_any W_ca790 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ca794 : bv 32 := 0x00008067.
Lemma D_ca794 : decode_any W_ca794 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
