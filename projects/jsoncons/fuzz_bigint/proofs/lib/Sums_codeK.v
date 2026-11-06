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
Definition W_10375c : bv 32 := 0x02060063.
Lemma D_10375c : decode_any W_10375c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103760 : bv 32 := 0x00c50633.
Lemma D_103760 : decode_any W_103760 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103764 : bv 32 := 0x00050693.
Lemma D_103764 : decode_any W_103764 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103768 : bv 32 := 0x0005c703.
Lemma D_103768 : decode_any W_103768 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10376c : bv 32 := 0x00e68023.
Lemma D_10376c : decode_any W_10376c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103770 : bv 32 := 0x00168693.
Lemma D_103770 : decode_any W_103770 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103774 : bv 32 := 0x00158593.
Lemma D_103774 : decode_any W_103774 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103778 : bv 32 := 0xfec698e3.
Lemma D_103778 : decode_any W_103778 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10377c : bv 32 := 0x00008067.
Lemma D_10377c : decode_any W_10377c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1037d8 : bv 32 := 0x00a666b3.
Lemma D_1037d8 : decode_any W_1037d8 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1037dc : bv 32 := 0x00f6f693.
Lemma D_1037dc : decode_any W_1037dc = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1037e0 : bv 32 := 0x02068063.
Lemma D_1037e0 : decode_any W_1037e0 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1037e4 : bv 32 := 0x04060863.
Lemma D_1037e4 : decode_any W_1037e4 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1037e8 : bv 32 := 0x00c50633.
Lemma D_1037e8 : decode_any W_1037e8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1037ec : bv 32 := 0x00050693.
Lemma D_1037ec : decode_any W_1037ec = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1037f0 : bv 32 := 0x00b68023.
Lemma D_1037f0 : decode_any W_1037f0 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1037f4 : bv 32 := 0x00168693.
Lemma D_1037f4 : decode_any W_1037f4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1037f8 : bv 32 := 0xfec69ce3.
Lemma D_1037f8 : decode_any W_1037f8 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1037fc : bv 32 := 0x0380006f.
Lemma D_1037fc : decode_any W_1037fc = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103800 : bv 32 := 0x02060a63.
Lemma D_103800 : decode_any W_103800 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103804 : bv 32 := 0x00c50633.
Lemma D_103804 : decode_any W_103804 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103808 : bv 32 := 0x00859693.
Lemma D_103808 : decode_any W_103808 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10380c : bv 32 := 0x00b6e5b3.
Lemma D_10380c : decode_any W_10380c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103810 : bv 32 := 0x01059693.
Lemma D_103810 : decode_any W_103810 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103814 : bv 32 := 0x00b6e5b3.
Lemma D_103814 : decode_any W_103814 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103818 : bv 32 := 0x02059693.
Lemma D_103818 : decode_any W_103818 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10381c : bv 32 := 0x00b6e5b3.
Lemma D_10381c : decode_any W_10381c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103820 : bv 32 := 0x00050693.
Lemma D_103820 : decode_any W_103820 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103824 : bv 32 := 0x00b6b023.
Lemma D_103824 : decode_any W_103824 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103828 : bv 32 := 0x00b6b423.
Lemma D_103828 : decode_any W_103828 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10382c : bv 32 := 0x01068693.
Lemma D_10382c : decode_any W_10382c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103830 : bv 32 := 0xfec6eae3.
Lemma D_103830 : decode_any W_103830 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103834 : bv 32 := 0x00008067.
Lemma D_103834 : decode_any W_103834 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e3c : bv 32 := 0xff010113.
Lemma D_103e3c : decode_any W_103e3c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e40 : bv 32 := 0x00113423.
Lemma D_103e40 : decode_any W_103e40 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e44 : bv 32 := 0x00058693.
Lemma D_103e44 : decode_any W_103e44 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e48 : bv 32 := 0x00100713.
Lemma D_103e48 : decode_any W_103e48 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e4c : bv 32 := 0x02871713.
Lemma D_103e4c : decode_any W_103e4c = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e50 : bv 32 := 0x00170593.
Lemma D_103e50 : decode_any W_103e50 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e54 : bv 32 := 0x08b6f263.
Lemma D_103e54 : decode_any W_103e54 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e58 : bv 32 := 0x00000593.
Lemma D_103e58 : decode_any W_103e58 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e5c : bv 32 := 0x00d50733.
Lemma D_103e5c : decode_any W_103e5c = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e60 : bv 32 := 0x00750793.
Lemma D_103e60 : decode_any W_103e60 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e64 : bv 32 := 0xff87f793.
Lemma D_103e64 : decode_any W_103e64 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e68 : bv 32 := 0xff877613.
Lemma D_103e68 : decode_any W_103e68 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e6c : bv 32 := 0x02f57463.
Lemma D_103e6c : decode_any W_103e6c = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e70 : bv 32 := 0x02068263.
Lemma D_103e70 : decode_any W_103e70 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e74 : bv 32 := 0x00000593.
Lemma D_103e74 : decode_any W_103e74 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e78 : bv 32 := 0x00150693.
Lemma D_103e78 : decode_any W_103e78 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e7c : bv 32 := 0x00068813.
Lemma D_103e7c : decode_any W_103e7c = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e80 : bv 32 := 0xfff6c683.
Lemma D_103e80 : decode_any W_103e80 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e84 : bv 32 := 0x00d5e5b3.
Lemma D_103e84 : decode_any W_103e84 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e88 : bv 32 := 0x00f87663.
Lemma D_103e88 : decode_any W_103e88 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e8c : bv 32 := 0x00180693.
Lemma D_103e8c : decode_any W_103e8c = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e90 : bv 32 := 0xfee866e3.
Lemma D_103e90 : decode_any W_103e90 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e94 : bv 32 := 0x00c7fa63.
Lemma D_103e94 : decode_any W_103e94 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e98 : bv 32 := 0x0007b683.
Lemma D_103e98 : decode_any W_103e98 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103e9c : bv 32 := 0x00878793.
Lemma D_103e9c : decode_any W_103e9c = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103ea0 : bv 32 := 0x00b6e5b3.
Lemma D_103ea0 : decode_any W_103ea0 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103ea4 : bv 32 := 0xfec7eae3.
Lemma D_103ea4 : decode_any W_103ea4 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103ea8 : bv 32 := 0x02a66063.
Lemma D_103ea8 : decode_any W_103ea8 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103eac : bv 32 := 0x00e67e63.
Lemma D_103eac : decode_any W_103eac = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103eb0 : bv 32 := 0x40c70733.
Lemma D_103eb0 : decode_any W_103eb0 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103eb4 : bv 32 := 0x00064503.
Lemma D_103eb4 : decode_any W_103eb4 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103eb8 : bv 32 := 0xfff70713.
Lemma D_103eb8 : decode_any W_103eb8 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103ebc : bv 32 := 0x00a5e5b3.
Lemma D_103ebc : decode_any W_103ebc = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103ec0 : bv 32 := 0x00160613.
Lemma D_103ec0 : decode_any W_103ec0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103ec4 : bv 32 := 0xfe0718e3.
Lemma D_103ec4 : decode_any W_103ec4 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103ec8 : bv 32 := 0x0015b513.
Lemma D_103ec8 : decode_any W_103ec8 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103ecc : bv 32 := 0x00813083.
Lemma D_103ecc : decode_any W_103ecc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103ed0 : bv 32 := 0x01010113.
Lemma D_103ed0 : decode_any W_103ed0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_103ed4 : bv 32 := 0x00008067.
Lemma D_103ed4 : decode_any W_103ed4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
