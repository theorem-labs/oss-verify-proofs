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

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_741bc : bv 32 := 0x02060063.
Lemma D_741bc : decode_any W_741bc = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741c0 : bv 32 := 0x00c50633.
Lemma D_741c0 : decode_any W_741c0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741c4 : bv 32 := 0x00050693.
Lemma D_741c4 : decode_any W_741c4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741c8 : bv 32 := 0x0005c703.
Lemma D_741c8 : decode_any W_741c8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741cc : bv 32 := 0x00e68023.
Lemma D_741cc : decode_any W_741cc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741d0 : bv 32 := 0x00168693.
Lemma D_741d0 : decode_any W_741d0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741d4 : bv 32 := 0x00158593.
Lemma D_741d4 : decode_any W_741d4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741d8 : bv 32 := 0xfec698e3.
Lemma D_741d8 : decode_any W_741d8 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_741dc : bv 32 := 0x00008067.
Lemma D_741dc : decode_any W_741dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74238 : bv 32 := 0x00a666b3.
Lemma D_74238 : decode_any W_74238 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7423c : bv 32 := 0x00f6f693.
Lemma D_7423c : decode_any W_7423c = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74240 : bv 32 := 0x02068063.
Lemma D_74240 : decode_any W_74240 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74244 : bv 32 := 0x04060863.
Lemma D_74244 : decode_any W_74244 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74248 : bv 32 := 0x00c50633.
Lemma D_74248 : decode_any W_74248 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7424c : bv 32 := 0x00050693.
Lemma D_7424c : decode_any W_7424c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74250 : bv 32 := 0x00b68023.
Lemma D_74250 : decode_any W_74250 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74254 : bv 32 := 0x00168693.
Lemma D_74254 : decode_any W_74254 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74258 : bv 32 := 0xfec69ce3.
Lemma D_74258 : decode_any W_74258 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7425c : bv 32 := 0x0380006f.
Lemma D_7425c : decode_any W_7425c = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74260 : bv 32 := 0x02060a63.
Lemma D_74260 : decode_any W_74260 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74264 : bv 32 := 0x00c50633.
Lemma D_74264 : decode_any W_74264 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74268 : bv 32 := 0x00859693.
Lemma D_74268 : decode_any W_74268 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7426c : bv 32 := 0x00b6e5b3.
Lemma D_7426c : decode_any W_7426c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74270 : bv 32 := 0x01059693.
Lemma D_74270 : decode_any W_74270 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74274 : bv 32 := 0x00b6e5b3.
Lemma D_74274 : decode_any W_74274 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74278 : bv 32 := 0x02059693.
Lemma D_74278 : decode_any W_74278 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7427c : bv 32 := 0x00b6e5b3.
Lemma D_7427c : decode_any W_7427c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74280 : bv 32 := 0x00050693.
Lemma D_74280 : decode_any W_74280 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74284 : bv 32 := 0x00b6b023.
Lemma D_74284 : decode_any W_74284 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74288 : bv 32 := 0x00b6b423.
Lemma D_74288 : decode_any W_74288 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7428c : bv 32 := 0x01068693.
Lemma D_7428c : decode_any W_7428c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74290 : bv 32 := 0xfec6eae3.
Lemma D_74290 : decode_any W_74290 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74294 : bv 32 := 0x00008067.
Lemma D_74294 : decode_any W_74294 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74768 : bv 32 := 0xff010113.
Lemma D_74768 : decode_any W_74768 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7476c : bv 32 := 0x00113423.
Lemma D_7476c : decode_any W_7476c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74770 : bv 32 := 0x00058693.
Lemma D_74770 : decode_any W_74770 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74774 : bv 32 := 0x00100713.
Lemma D_74774 : decode_any W_74774 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74778 : bv 32 := 0x02871713.
Lemma D_74778 : decode_any W_74778 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7477c : bv 32 := 0x00170593.
Lemma D_7477c : decode_any W_7477c = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74780 : bv 32 := 0x08b6f263.
Lemma D_74780 : decode_any W_74780 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74784 : bv 32 := 0x00000593.
Lemma D_74784 : decode_any W_74784 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74788 : bv 32 := 0x00d50733.
Lemma D_74788 : decode_any W_74788 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7478c : bv 32 := 0x00750793.
Lemma D_7478c : decode_any W_7478c = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74790 : bv 32 := 0xff87f793.
Lemma D_74790 : decode_any W_74790 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74794 : bv 32 := 0xff877613.
Lemma D_74794 : decode_any W_74794 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74798 : bv 32 := 0x02f57463.
Lemma D_74798 : decode_any W_74798 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7479c : bv 32 := 0x02068263.
Lemma D_7479c : decode_any W_7479c = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747a0 : bv 32 := 0x00000593.
Lemma D_747a0 : decode_any W_747a0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747a4 : bv 32 := 0x00150693.
Lemma D_747a4 : decode_any W_747a4 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747a8 : bv 32 := 0x00068813.
Lemma D_747a8 : decode_any W_747a8 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747ac : bv 32 := 0xfff6c683.
Lemma D_747ac : decode_any W_747ac = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747b0 : bv 32 := 0x00d5e5b3.
Lemma D_747b0 : decode_any W_747b0 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747b4 : bv 32 := 0x00f87663.
Lemma D_747b4 : decode_any W_747b4 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747b8 : bv 32 := 0x00180693.
Lemma D_747b8 : decode_any W_747b8 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747bc : bv 32 := 0xfee866e3.
Lemma D_747bc : decode_any W_747bc = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747c0 : bv 32 := 0x00c7fa63.
Lemma D_747c0 : decode_any W_747c0 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747c4 : bv 32 := 0x0007b683.
Lemma D_747c4 : decode_any W_747c4 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747c8 : bv 32 := 0x00878793.
Lemma D_747c8 : decode_any W_747c8 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747cc : bv 32 := 0x00b6e5b3.
Lemma D_747cc : decode_any W_747cc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747d0 : bv 32 := 0xfec7eae3.
Lemma D_747d0 : decode_any W_747d0 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747d4 : bv 32 := 0x02a66063.
Lemma D_747d4 : decode_any W_747d4 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747d8 : bv 32 := 0x00e67e63.
Lemma D_747d8 : decode_any W_747d8 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747dc : bv 32 := 0x40c70733.
Lemma D_747dc : decode_any W_747dc = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747e0 : bv 32 := 0x00064503.
Lemma D_747e0 : decode_any W_747e0 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747e4 : bv 32 := 0xfff70713.
Lemma D_747e4 : decode_any W_747e4 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747e8 : bv 32 := 0x00a5e5b3.
Lemma D_747e8 : decode_any W_747e8 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747ec : bv 32 := 0x00160613.
Lemma D_747ec : decode_any W_747ec = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747f0 : bv 32 := 0xfe0718e3.
Lemma D_747f0 : decode_any W_747f0 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747f4 : bv 32 := 0x0015b513.
Lemma D_747f4 : decode_any W_747f4 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747f8 : bv 32 := 0x00813083.
Lemma D_747f8 : decode_any W_747f8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_747fc : bv 32 := 0x01010113.
Lemma D_747fc : decode_any W_747fc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74800 : bv 32 := 0x00008067.
Lemma D_74800 : decode_any W_74800 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
