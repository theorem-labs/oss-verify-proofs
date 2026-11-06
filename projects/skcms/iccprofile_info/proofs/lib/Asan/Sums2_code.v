(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_50ed0 : bv 32 := 0x00200613.
Lemma D_50ed0 : decode_any W_50ed0 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ed4 : bv 32 := 0x14c5ea63.
Lemma D_50ed4 : decode_any W_50ed4 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ed8 : bv 32 := 0x00100613.
Lemma D_50ed8 : decode_any W_50ed8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50edc : bv 32 := 0x00100693.
Lemma D_50edc : decode_any W_50edc = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ee0 : bv 32 := 0x00c0006f.
Lemma D_50ee0 : decode_any W_50ee0 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ee4 : bv 32 := 0x00160613.
Lemma D_50ee4 : decode_any W_50ee4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ee8 : bv 32 := 0x12b60c63.
Lemma D_50ee8 : decode_any W_50ee8 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50eec : bv 32 := 0x00461713.
Lemma D_50eec : decode_any W_50eec = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ef0 : bv 32 := 0x00e50733.
Lemma D_50ef0 : decode_any W_50ef0 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ef4 : bv 32 := 0x00072703.
Lemma D_50ef4 : decode_any W_50ef4 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ef8 : bv 32 := 0x00060893.
Lemma D_50ef8 : decode_any W_50ef8 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50efc : bv 32 := 0xfff88793.
Lemma D_50efc : decode_any W_50efc = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f00 : bv 32 := 0x0017d813.
Lemma D_50f00 : decode_any W_50f00 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f04 : bv 32 := 0x00481293.
Lemma D_50f04 : decode_any W_50f04 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f08 : bv 32 := 0x005502b3.
Lemma D_50f08 : decode_any W_50f08 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f0c : bv 32 := 0x0002a303.
Lemma D_50f0c : decode_any W_50f0c = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f10 : bv 32 := 0xfce37ae3.
Lemma D_50f10 : decode_any W_50f10 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f14 : bv 32 := 0x0002b303.
Lemma D_50f14 : decode_any W_50f14 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f18 : bv 32 := 0x00489893.
Lemma D_50f18 : decode_any W_50f18 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f1c : bv 32 := 0x011508b3.
Lemma D_50f1c : decode_any W_50f1c = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f20 : bv 32 := 0x0048a383.
Lemma D_50f20 : decode_any W_50f20 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f24 : bv 32 := 0x0068b023.
Lemma D_50f24 : decode_any W_50f24 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f28 : bv 32 := 0x0082b303.
Lemma D_50f28 : decode_any W_50f28 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f2c : bv 32 := 0x0088be03.
Lemma D_50f2c : decode_any W_50f2c = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f30 : bv 32 := 0x0068b423.
Lemma D_50f30 : decode_any W_50f30 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f34 : bv 32 := 0x00e2a023.
Lemma D_50f34 : decode_any W_50f34 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f38 : bv 32 := 0x0072a223.
Lemma D_50f38 : decode_any W_50f38 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f3c : bv 32 := 0x01c2b423.
Lemma D_50f3c : decode_any W_50f3c = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f40 : bv 32 := 0x00080893.
Lemma D_50f40 : decode_any W_50f40 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f44 : bv 32 := 0xfaf6ece3.
Lemma D_50f44 : decode_any W_50f44 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f48 : bv 32 := 0xf9dff06f.
Lemma D_50f48 : decode_any W_50f48 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f4c : bv 32 := 0x00000613.
Lemma D_50f4c : decode_any W_50f4c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f50 : bv 32 := 0x00459693.
Lemma D_50f50 : decode_any W_50f50 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f54 : bv 32 := 0x00d506b3.
Lemma D_50f54 : decode_any W_50f54 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f58 : bv 32 := 0x0006b703.
Lemma D_50f58 : decode_any W_50f58 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f5c : bv 32 := 0x0086b783.
Lemma D_50f5c : decode_any W_50f5c = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f60 : bv 32 := 0x00053803.
Lemma D_50f60 : decode_any W_50f60 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f64 : bv 32 := 0x00853883.
Lemma D_50f64 : decode_any W_50f64 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f68 : bv 32 := 0x00e53023.
Lemma D_50f68 : decode_any W_50f68 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f6c : bv 32 := 0x00f53423.
Lemma D_50f6c : decode_any W_50f6c = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f70 : bv 32 := 0x0106b023.
Lemma D_50f70 : decode_any W_50f70 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f74 : bv 32 := 0x0116b423.
Lemma D_50f74 : decode_any W_50f74 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f78 : bv 32 := 0x00000693.
Lemma D_50f78 : decode_any W_50f78 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f7c : bv 32 := 0x00161793.
Lemma D_50f7c : decode_any W_50f7c = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f80 : bv 32 := 0x00178813.
Lemma D_50f80 : decode_any W_50f80 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f84 : bv 32 := 0x00461713.
Lemma D_50f84 : decode_any W_50f84 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f88 : bv 32 := 0x00b86a63.
Lemma D_50f88 : decode_any W_50f88 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f8c : bv 32 := 0x00278793.
Lemma D_50f8c : decode_any W_50f8c = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f90 : bv 32 := 0x02b7ea63.
Lemma D_50f90 : decode_any W_50f90 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f94 : bv 32 := 0x04c69c63.
Lemma D_50f94 : decode_any W_50f94 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f98 : bv 32 := 0x0880006f.
Lemma D_50f98 : decode_any W_50f98 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f9c : bv 32 := 0x00e506b3.
Lemma D_50f9c : decode_any W_50f9c = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fa0 : bv 32 := 0x00481893.
Lemma D_50fa0 : decode_any W_50fa0 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fa4 : bv 32 := 0x011508b3.
Lemma D_50fa4 : decode_any W_50fa4 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fa8 : bv 32 := 0x0006a683.
Lemma D_50fa8 : decode_any W_50fa8 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fac : bv 32 := 0x0008a883.
Lemma D_50fac : decode_any W_50fac = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fb0 : bv 32 := 0x0116e463.
Lemma D_50fb0 : decode_any W_50fb0 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fb4 : bv 32 := 0x00060813.
Lemma D_50fb4 : decode_any W_50fb4 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fb8 : bv 32 := 0x00080693.
Lemma D_50fb8 : decode_any W_50fb8 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fbc : bv 32 := 0x00278793.
Lemma D_50fbc : decode_any W_50fbc = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fc0 : bv 32 := 0xfcb7fae3.
Lemma D_50fc0 : decode_any W_50fc0 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fc4 : bv 32 := 0x00469813.
Lemma D_50fc4 : decode_any W_50fc4 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fc8 : bv 32 := 0x00479893.
Lemma D_50fc8 : decode_any W_50fc8 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fcc : bv 32 := 0x01050833.
Lemma D_50fcc : decode_any W_50fcc = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fd0 : bv 32 := 0x011508b3.
Lemma D_50fd0 : decode_any W_50fd0 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fd4 : bv 32 := 0x00082803.
Lemma D_50fd4 : decode_any W_50fd4 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fd8 : bv 32 := 0x0008a883.
Lemma D_50fd8 : decode_any W_50fd8 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fdc : bv 32 := 0x01186463.
Lemma D_50fdc : decode_any W_50fdc = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fe0 : bv 32 := 0x00068793.
Lemma D_50fe0 : decode_any W_50fe0 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fe4 : bv 32 := 0x00078693.
Lemma D_50fe4 : decode_any W_50fe4 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fe8 : bv 32 := 0x02c78c63.
Lemma D_50fe8 : decode_any W_50fe8 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fec : bv 32 := 0x00469613.
Lemma D_50fec : decode_any W_50fec = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ff0 : bv 32 := 0x00c50633.
Lemma D_50ff0 : decode_any W_50ff0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ff4 : bv 32 := 0x00063783.
Lemma D_50ff4 : decode_any W_50ff4 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ff8 : bv 32 := 0x00e50733.
Lemma D_50ff8 : decode_any W_50ff8 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ffc : bv 32 := 0x00073803.
Lemma D_50ffc : decode_any W_50ffc = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51000 : bv 32 := 0x00873883.
Lemma D_51000 : decode_any W_51000 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51004 : bv 32 := 0x00f73023.
Lemma D_51004 : decode_any W_51004 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51008 : bv 32 := 0x00863783.
Lemma D_51008 : decode_any W_51008 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5100c : bv 32 := 0x00f73423.
Lemma D_5100c : decode_any W_5100c = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51010 : bv 32 := 0x01063023.
Lemma D_51010 : decode_any W_51010 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51014 : bv 32 := 0x01163423.
Lemma D_51014 : decode_any W_51014 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51018 : bv 32 := 0x00068613.
Lemma D_51018 : decode_any W_51018 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5101c : bv 32 := 0xf6b6e0e3.
Lemma D_5101c : decode_any W_5101c = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51020 : bv 32 := 0xfff58593.
Lemma D_51020 : decode_any W_51020 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51024 : bv 32 := 0xf20594e3.
Lemma D_51024 : decode_any W_51024 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51028 : bv 32 := 0x00008067.
Lemma D_51028 : decode_any W_51028 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_637ec : bv 32 := 0x06060663.
Lemma D_637ec : decode_any W_637ec = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_637f0 : bv 32 := 0x00000693.
Lemma D_637f0 : decode_any W_637f0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_637f4 : bv 32 := 0x00d58733.
Lemma D_637f4 : decode_any W_637f4 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_637f8 : bv 32 := 0x00074703.
Lemma D_637f8 : decode_any W_637f8 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_637fc : bv 32 := 0x00070c63.
Lemma D_637fc : decode_any W_637fc = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63800 : bv 32 := 0x00d507b3.
Lemma D_63800 : decode_any W_63800 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63804 : bv 32 := 0x00168693.
Lemma D_63804 : decode_any W_63804 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63808 : bv 32 := 0x00e78023.
Lemma D_63808 : decode_any W_63808 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6380c : bv 32 := 0xfed614e3.
Lemma D_6380c : decode_any W_6380c = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63810 : bv 32 := 0x00060693.
Lemma D_63810 : decode_any W_63810 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63814 : bv 32 := 0x00d505b3.
Lemma D_63814 : decode_any W_63814 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63818 : bv 32 := 0x40d6073b.
Lemma D_63818 : decode_any W_63818 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6381c : bv 32 := 0x00b76733.
Lemma D_6381c : decode_any W_6381c = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63820 : bv 32 := 0x00f77713.
Lemma D_63820 : decode_any W_63820 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63824 : bv 32 := 0x00070e63.
Lemma D_63824 : decode_any W_63824 = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63828 : bv 32 := 0x02d60863.
Lemma D_63828 : decode_any W_63828 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6382c : bv 32 := 0x00c50633.
Lemma D_6382c : decode_any W_6382c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63830 : bv 32 := 0x00058023.
Lemma D_63830 : decode_any W_63830 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63834 : bv 32 := 0x00158593.
Lemma D_63834 : decode_any W_63834 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63838 : bv 32 := 0xfec59ce3.
Lemma D_63838 : decode_any W_63838 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6383c : bv 32 := 0x01c0006f.
Lemma D_6383c : decode_any W_6383c = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63840 : bv 32 := 0x00d60c63.
Lemma D_63840 : decode_any W_63840 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63844 : bv 32 := 0x00c50633.
Lemma D_63844 : decode_any W_63844 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63848 : bv 32 := 0x0005b023.
Lemma D_63848 : decode_any W_63848 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6384c : bv 32 := 0x0005b423.
Lemma D_6384c : decode_any W_6384c = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63850 : bv 32 := 0x01058593.
Lemma D_63850 : decode_any W_63850 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63854 : bv 32 := 0xfec5eae3.
Lemma D_63854 : decode_any W_63854 = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_63858 : bv 32 := 0x00008067.
Lemma D_63858 : decode_any W_63858 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
