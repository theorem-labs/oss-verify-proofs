(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
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
Definition W_657c4 : bv 32 := 0x02060063.
Lemma D_657c4 : decode_any W_657c4 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_657c8 : bv 32 := 0x00c50633.
Lemma D_657c8 : decode_any W_657c8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_657cc : bv 32 := 0x00050693.
Lemma D_657cc : decode_any W_657cc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_657d0 : bv 32 := 0x0005c703.
Lemma D_657d0 : decode_any W_657d0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_657d4 : bv 32 := 0x00e68023.
Lemma D_657d4 : decode_any W_657d4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_657d8 : bv 32 := 0x00168693.
Lemma D_657d8 : decode_any W_657d8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_657dc : bv 32 := 0x00158593.
Lemma D_657dc : decode_any W_657dc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_657e0 : bv 32 := 0xfec698e3.
Lemma D_657e0 : decode_any W_657e0 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_657e4 : bv 32 := 0x00008067.
Lemma D_657e4 : decode_any W_657e4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65840 : bv 32 := 0x00a666b3.
Lemma D_65840 : decode_any W_65840 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65844 : bv 32 := 0x00f6f693.
Lemma D_65844 : decode_any W_65844 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65848 : bv 32 := 0x02068063.
Lemma D_65848 : decode_any W_65848 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6584c : bv 32 := 0x04060863.
Lemma D_6584c : decode_any W_6584c = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65850 : bv 32 := 0x00c50633.
Lemma D_65850 : decode_any W_65850 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65854 : bv 32 := 0x00050693.
Lemma D_65854 : decode_any W_65854 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65858 : bv 32 := 0x00b68023.
Lemma D_65858 : decode_any W_65858 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6585c : bv 32 := 0x00168693.
Lemma D_6585c : decode_any W_6585c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65860 : bv 32 := 0xfec69ce3.
Lemma D_65860 : decode_any W_65860 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65864 : bv 32 := 0x0380006f.
Lemma D_65864 : decode_any W_65864 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65868 : bv 32 := 0x02060a63.
Lemma D_65868 : decode_any W_65868 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6586c : bv 32 := 0x00c50633.
Lemma D_6586c : decode_any W_6586c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65870 : bv 32 := 0x00859693.
Lemma D_65870 : decode_any W_65870 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65874 : bv 32 := 0x00b6e5b3.
Lemma D_65874 : decode_any W_65874 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65878 : bv 32 := 0x01059693.
Lemma D_65878 : decode_any W_65878 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6587c : bv 32 := 0x00b6e5b3.
Lemma D_6587c : decode_any W_6587c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65880 : bv 32 := 0x02059693.
Lemma D_65880 : decode_any W_65880 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65884 : bv 32 := 0x00b6e5b3.
Lemma D_65884 : decode_any W_65884 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65888 : bv 32 := 0x00050693.
Lemma D_65888 : decode_any W_65888 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6588c : bv 32 := 0x00b6b023.
Lemma D_6588c : decode_any W_6588c = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65890 : bv 32 := 0x00b6b423.
Lemma D_65890 : decode_any W_65890 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65894 : bv 32 := 0x01068693.
Lemma D_65894 : decode_any W_65894 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65898 : bv 32 := 0xfec6eae3.
Lemma D_65898 : decode_any W_65898 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6589c : bv 32 := 0x00008067.
Lemma D_6589c : decode_any W_6589c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65d8c : bv 32 := 0xff010113.
Lemma D_65d8c : decode_any W_65d8c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65d90 : bv 32 := 0x00113423.
Lemma D_65d90 : decode_any W_65d90 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65d94 : bv 32 := 0x00058693.
Lemma D_65d94 : decode_any W_65d94 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65d98 : bv 32 := 0x00100713.
Lemma D_65d98 : decode_any W_65d98 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65d9c : bv 32 := 0x02871713.
Lemma D_65d9c : decode_any W_65d9c = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65da0 : bv 32 := 0x00170593.
Lemma D_65da0 : decode_any W_65da0 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65da4 : bv 32 := 0x08b6f263.
Lemma D_65da4 : decode_any W_65da4 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65da8 : bv 32 := 0x00000593.
Lemma D_65da8 : decode_any W_65da8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65dac : bv 32 := 0x00d50733.
Lemma D_65dac : decode_any W_65dac = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65db0 : bv 32 := 0x00750793.
Lemma D_65db0 : decode_any W_65db0 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65db4 : bv 32 := 0xff87f793.
Lemma D_65db4 : decode_any W_65db4 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65db8 : bv 32 := 0xff877613.
Lemma D_65db8 : decode_any W_65db8 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65dbc : bv 32 := 0x02f57463.
Lemma D_65dbc : decode_any W_65dbc = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65dc0 : bv 32 := 0x02068263.
Lemma D_65dc0 : decode_any W_65dc0 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65dc4 : bv 32 := 0x00000593.
Lemma D_65dc4 : decode_any W_65dc4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65dc8 : bv 32 := 0x00150693.
Lemma D_65dc8 : decode_any W_65dc8 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65dcc : bv 32 := 0x00068813.
Lemma D_65dcc : decode_any W_65dcc = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65dd0 : bv 32 := 0xfff6c683.
Lemma D_65dd0 : decode_any W_65dd0 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65dd4 : bv 32 := 0x00d5e5b3.
Lemma D_65dd4 : decode_any W_65dd4 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65dd8 : bv 32 := 0x00f87663.
Lemma D_65dd8 : decode_any W_65dd8 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65ddc : bv 32 := 0x00180693.
Lemma D_65ddc : decode_any W_65ddc = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65de0 : bv 32 := 0xfee866e3.
Lemma D_65de0 : decode_any W_65de0 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65de4 : bv 32 := 0x00c7fa63.
Lemma D_65de4 : decode_any W_65de4 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65de8 : bv 32 := 0x0007b683.
Lemma D_65de8 : decode_any W_65de8 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65dec : bv 32 := 0x00878793.
Lemma D_65dec : decode_any W_65dec = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65df0 : bv 32 := 0x00b6e5b3.
Lemma D_65df0 : decode_any W_65df0 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65df4 : bv 32 := 0xfec7eae3.
Lemma D_65df4 : decode_any W_65df4 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65df8 : bv 32 := 0x02a66063.
Lemma D_65df8 : decode_any W_65df8 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65dfc : bv 32 := 0x00e67e63.
Lemma D_65dfc : decode_any W_65dfc = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e00 : bv 32 := 0x40c70733.
Lemma D_65e00 : decode_any W_65e00 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e04 : bv 32 := 0x00064503.
Lemma D_65e04 : decode_any W_65e04 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e08 : bv 32 := 0xfff70713.
Lemma D_65e08 : decode_any W_65e08 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e0c : bv 32 := 0x00a5e5b3.
Lemma D_65e0c : decode_any W_65e0c = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e10 : bv 32 := 0x00160613.
Lemma D_65e10 : decode_any W_65e10 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e14 : bv 32 := 0xfe0718e3.
Lemma D_65e14 : decode_any W_65e14 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e18 : bv 32 := 0x0015b513.
Lemma D_65e18 : decode_any W_65e18 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e1c : bv 32 := 0x00813083.
Lemma D_65e1c : decode_any W_65e1c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e20 : bv 32 := 0x01010113.
Lemma D_65e20 : decode_any W_65e20 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65e24 : bv 32 := 0x00008067.
Lemma D_65e24 : decode_any W_65e24 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
