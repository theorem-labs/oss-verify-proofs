(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
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
Definition W_736dc : bv 32 := 0x02060063.
Lemma D_736dc : decode_any W_736dc = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_736e0 : bv 32 := 0x00c50633.
Lemma D_736e0 : decode_any W_736e0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_736e4 : bv 32 := 0x00050693.
Lemma D_736e4 : decode_any W_736e4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_736e8 : bv 32 := 0x0005c703.
Lemma D_736e8 : decode_any W_736e8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_736ec : bv 32 := 0x00e68023.
Lemma D_736ec : decode_any W_736ec = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_736f0 : bv 32 := 0x00168693.
Lemma D_736f0 : decode_any W_736f0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_736f4 : bv 32 := 0x00158593.
Lemma D_736f4 : decode_any W_736f4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_736f8 : bv 32 := 0xfec698e3.
Lemma D_736f8 : decode_any W_736f8 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_736fc : bv 32 := 0x00008067.
Lemma D_736fc : decode_any W_736fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73758 : bv 32 := 0x00a666b3.
Lemma D_73758 : decode_any W_73758 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7375c : bv 32 := 0x00f6f693.
Lemma D_7375c : decode_any W_7375c = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73760 : bv 32 := 0x02068063.
Lemma D_73760 : decode_any W_73760 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73764 : bv 32 := 0x04060863.
Lemma D_73764 : decode_any W_73764 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73768 : bv 32 := 0x00c50633.
Lemma D_73768 : decode_any W_73768 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7376c : bv 32 := 0x00050693.
Lemma D_7376c : decode_any W_7376c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73770 : bv 32 := 0x00b68023.
Lemma D_73770 : decode_any W_73770 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73774 : bv 32 := 0x00168693.
Lemma D_73774 : decode_any W_73774 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73778 : bv 32 := 0xfec69ce3.
Lemma D_73778 : decode_any W_73778 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7377c : bv 32 := 0x0380006f.
Lemma D_7377c : decode_any W_7377c = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73780 : bv 32 := 0x02060a63.
Lemma D_73780 : decode_any W_73780 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73784 : bv 32 := 0x00c50633.
Lemma D_73784 : decode_any W_73784 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73788 : bv 32 := 0x00859693.
Lemma D_73788 : decode_any W_73788 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7378c : bv 32 := 0x00b6e5b3.
Lemma D_7378c : decode_any W_7378c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73790 : bv 32 := 0x01059693.
Lemma D_73790 : decode_any W_73790 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73794 : bv 32 := 0x00b6e5b3.
Lemma D_73794 : decode_any W_73794 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73798 : bv 32 := 0x02059693.
Lemma D_73798 : decode_any W_73798 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7379c : bv 32 := 0x00b6e5b3.
Lemma D_7379c : decode_any W_7379c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_737a0 : bv 32 := 0x00050693.
Lemma D_737a0 : decode_any W_737a0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_737a4 : bv 32 := 0x00b6b023.
Lemma D_737a4 : decode_any W_737a4 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_737a8 : bv 32 := 0x00b6b423.
Lemma D_737a8 : decode_any W_737a8 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_737ac : bv 32 := 0x01068693.
Lemma D_737ac : decode_any W_737ac = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_737b0 : bv 32 := 0xfec6eae3.
Lemma D_737b0 : decode_any W_737b0 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_737b4 : bv 32 := 0x00008067.
Lemma D_737b4 : decode_any W_737b4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73c88 : bv 32 := 0xff010113.
Lemma D_73c88 : decode_any W_73c88 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73c8c : bv 32 := 0x00113423.
Lemma D_73c8c : decode_any W_73c8c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73c90 : bv 32 := 0x00058693.
Lemma D_73c90 : decode_any W_73c90 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73c94 : bv 32 := 0x00100713.
Lemma D_73c94 : decode_any W_73c94 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73c98 : bv 32 := 0x02871713.
Lemma D_73c98 : decode_any W_73c98 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73c9c : bv 32 := 0x00170593.
Lemma D_73c9c : decode_any W_73c9c = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ca0 : bv 32 := 0x08b6f263.
Lemma D_73ca0 : decode_any W_73ca0 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ca4 : bv 32 := 0x00000593.
Lemma D_73ca4 : decode_any W_73ca4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ca8 : bv 32 := 0x00d50733.
Lemma D_73ca8 : decode_any W_73ca8 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cac : bv 32 := 0x00750793.
Lemma D_73cac : decode_any W_73cac = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cb0 : bv 32 := 0xff87f793.
Lemma D_73cb0 : decode_any W_73cb0 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cb4 : bv 32 := 0xff877613.
Lemma D_73cb4 : decode_any W_73cb4 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cb8 : bv 32 := 0x02f57463.
Lemma D_73cb8 : decode_any W_73cb8 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cbc : bv 32 := 0x02068263.
Lemma D_73cbc : decode_any W_73cbc = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cc0 : bv 32 := 0x00000593.
Lemma D_73cc0 : decode_any W_73cc0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cc4 : bv 32 := 0x00150693.
Lemma D_73cc4 : decode_any W_73cc4 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cc8 : bv 32 := 0x00068813.
Lemma D_73cc8 : decode_any W_73cc8 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ccc : bv 32 := 0xfff6c683.
Lemma D_73ccc : decode_any W_73ccc = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cd0 : bv 32 := 0x00d5e5b3.
Lemma D_73cd0 : decode_any W_73cd0 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cd4 : bv 32 := 0x00f87663.
Lemma D_73cd4 : decode_any W_73cd4 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cd8 : bv 32 := 0x00180693.
Lemma D_73cd8 : decode_any W_73cd8 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cdc : bv 32 := 0xfee866e3.
Lemma D_73cdc : decode_any W_73cdc = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ce0 : bv 32 := 0x00c7fa63.
Lemma D_73ce0 : decode_any W_73ce0 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ce4 : bv 32 := 0x0007b683.
Lemma D_73ce4 : decode_any W_73ce4 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73ce8 : bv 32 := 0x00878793.
Lemma D_73ce8 : decode_any W_73ce8 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cec : bv 32 := 0x00b6e5b3.
Lemma D_73cec : decode_any W_73cec = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cf0 : bv 32 := 0xfec7eae3.
Lemma D_73cf0 : decode_any W_73cf0 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cf4 : bv 32 := 0x02a66063.
Lemma D_73cf4 : decode_any W_73cf4 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cf8 : bv 32 := 0x00e67e63.
Lemma D_73cf8 : decode_any W_73cf8 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73cfc : bv 32 := 0x40c70733.
Lemma D_73cfc : decode_any W_73cfc = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d00 : bv 32 := 0x00064503.
Lemma D_73d00 : decode_any W_73d00 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d04 : bv 32 := 0xfff70713.
Lemma D_73d04 : decode_any W_73d04 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d08 : bv 32 := 0x00a5e5b3.
Lemma D_73d08 : decode_any W_73d08 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d0c : bv 32 := 0x00160613.
Lemma D_73d0c : decode_any W_73d0c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d10 : bv 32 := 0xfe0718e3.
Lemma D_73d10 : decode_any W_73d10 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d14 : bv 32 := 0x0015b513.
Lemma D_73d14 : decode_any W_73d14 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d18 : bv 32 := 0x00813083.
Lemma D_73d18 : decode_any W_73d18 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d1c : bv 32 := 0x01010113.
Lemma D_73d1c : decode_any W_73d1c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_73d20 : bv 32 := 0x00008067.
Lemma D_73d20 : decode_any W_73d20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
