(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_a9f34 : bv 32 := 0x06060663.
Lemma D_a9f34 : decode_any W_a9f34 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f38 : bv 32 := 0x00000693.
Lemma D_a9f38 : decode_any W_a9f38 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f3c : bv 32 := 0x00d58733.
Lemma D_a9f3c : decode_any W_a9f3c = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f40 : bv 32 := 0x00074703.
Lemma D_a9f40 : decode_any W_a9f40 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f44 : bv 32 := 0x00070c63.
Lemma D_a9f44 : decode_any W_a9f44 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f48 : bv 32 := 0x00d507b3.
Lemma D_a9f48 : decode_any W_a9f48 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f4c : bv 32 := 0x00168693.
Lemma D_a9f4c : decode_any W_a9f4c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f50 : bv 32 := 0x00e78023.
Lemma D_a9f50 : decode_any W_a9f50 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f54 : bv 32 := 0xfed614e3.
Lemma D_a9f54 : decode_any W_a9f54 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f58 : bv 32 := 0x00060693.
Lemma D_a9f58 : decode_any W_a9f58 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f5c : bv 32 := 0x00d505b3.
Lemma D_a9f5c : decode_any W_a9f5c = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f60 : bv 32 := 0x40d6073b.
Lemma D_a9f60 : decode_any W_a9f60 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f64 : bv 32 := 0x00b76733.
Lemma D_a9f64 : decode_any W_a9f64 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f68 : bv 32 := 0x00f77713.
Lemma D_a9f68 : decode_any W_a9f68 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f6c : bv 32 := 0x00070e63.
Lemma D_a9f6c : decode_any W_a9f6c = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f70 : bv 32 := 0x02d60863.
Lemma D_a9f70 : decode_any W_a9f70 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f74 : bv 32 := 0x00c50633.
Lemma D_a9f74 : decode_any W_a9f74 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f78 : bv 32 := 0x00058023.
Lemma D_a9f78 : decode_any W_a9f78 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f7c : bv 32 := 0x00158593.
Lemma D_a9f7c : decode_any W_a9f7c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f80 : bv 32 := 0xfec59ce3.
Lemma D_a9f80 : decode_any W_a9f80 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f84 : bv 32 := 0x01c0006f.
Lemma D_a9f84 : decode_any W_a9f84 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f88 : bv 32 := 0x00d60c63.
Lemma D_a9f88 : decode_any W_a9f88 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f8c : bv 32 := 0x00c50633.
Lemma D_a9f8c : decode_any W_a9f8c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f90 : bv 32 := 0x0005b023.
Lemma D_a9f90 : decode_any W_a9f90 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f94 : bv 32 := 0x0005b423.
Lemma D_a9f94 : decode_any W_a9f94 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f98 : bv 32 := 0x01058593.
Lemma D_a9f98 : decode_any W_a9f98 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9f9c : bv 32 := 0xfec5eae3.
Lemma D_a9f9c : decode_any W_a9f9c = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a9fa0 : bv 32 := 0x00008067.
Lemma D_a9fa0 : decode_any W_a9fa0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.



(* [comment removed for export] *)
Definition W_95d14 : bv 32 := 0x00200613.
Lemma D_95d14 : decode_any W_95d14 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d18 : bv 32 := 0x14c5ea63.
Lemma D_95d18 : decode_any W_95d18 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d1c : bv 32 := 0x00100613.
Lemma D_95d1c : decode_any W_95d1c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d20 : bv 32 := 0x00100693.
Lemma D_95d20 : decode_any W_95d20 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d24 : bv 32 := 0x00c0006f.
Lemma D_95d24 : decode_any W_95d24 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d28 : bv 32 := 0x00160613.
Lemma D_95d28 : decode_any W_95d28 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d2c : bv 32 := 0x12b60c63.
Lemma D_95d2c : decode_any W_95d2c = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d30 : bv 32 := 0x00461713.
Lemma D_95d30 : decode_any W_95d30 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d34 : bv 32 := 0x00e50733.
Lemma D_95d34 : decode_any W_95d34 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d38 : bv 32 := 0x00072703.
Lemma D_95d38 : decode_any W_95d38 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d3c : bv 32 := 0x00060893.
Lemma D_95d3c : decode_any W_95d3c = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d40 : bv 32 := 0xfff88793.
Lemma D_95d40 : decode_any W_95d40 = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d44 : bv 32 := 0x0017d813.
Lemma D_95d44 : decode_any W_95d44 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d48 : bv 32 := 0x00481293.
Lemma D_95d48 : decode_any W_95d48 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d4c : bv 32 := 0x005502b3.
Lemma D_95d4c : decode_any W_95d4c = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d50 : bv 32 := 0x0002a303.
Lemma D_95d50 : decode_any W_95d50 = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d54 : bv 32 := 0xfce37ae3.
Lemma D_95d54 : decode_any W_95d54 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d58 : bv 32 := 0x0002b303.
Lemma D_95d58 : decode_any W_95d58 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d5c : bv 32 := 0x00489893.
Lemma D_95d5c : decode_any W_95d5c = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d60 : bv 32 := 0x011508b3.
Lemma D_95d60 : decode_any W_95d60 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d64 : bv 32 := 0x0048a383.
Lemma D_95d64 : decode_any W_95d64 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d68 : bv 32 := 0x0068b023.
Lemma D_95d68 : decode_any W_95d68 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d6c : bv 32 := 0x0082b303.
Lemma D_95d6c : decode_any W_95d6c = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d70 : bv 32 := 0x0088be03.
Lemma D_95d70 : decode_any W_95d70 = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d74 : bv 32 := 0x0068b423.
Lemma D_95d74 : decode_any W_95d74 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d78 : bv 32 := 0x00e2a023.
Lemma D_95d78 : decode_any W_95d78 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d7c : bv 32 := 0x0072a223.
Lemma D_95d7c : decode_any W_95d7c = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d80 : bv 32 := 0x01c2b423.
Lemma D_95d80 : decode_any W_95d80 = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d84 : bv 32 := 0x00080893.
Lemma D_95d84 : decode_any W_95d84 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d88 : bv 32 := 0xfaf6ece3.
Lemma D_95d88 : decode_any W_95d88 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d8c : bv 32 := 0xf9dff06f.
Lemma D_95d8c : decode_any W_95d8c = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d90 : bv 32 := 0x00000613.
Lemma D_95d90 : decode_any W_95d90 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d94 : bv 32 := 0x00459693.
Lemma D_95d94 : decode_any W_95d94 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d98 : bv 32 := 0x00d506b3.
Lemma D_95d98 : decode_any W_95d98 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95d9c : bv 32 := 0x0006b703.
Lemma D_95d9c : decode_any W_95d9c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95da0 : bv 32 := 0x0086b783.
Lemma D_95da0 : decode_any W_95da0 = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95da4 : bv 32 := 0x00053803.
Lemma D_95da4 : decode_any W_95da4 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95da8 : bv 32 := 0x00853883.
Lemma D_95da8 : decode_any W_95da8 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95dac : bv 32 := 0x00e53023.
Lemma D_95dac : decode_any W_95dac = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95db0 : bv 32 := 0x00f53423.
Lemma D_95db0 : decode_any W_95db0 = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95db4 : bv 32 := 0x0106b023.
Lemma D_95db4 : decode_any W_95db4 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95db8 : bv 32 := 0x0116b423.
Lemma D_95db8 : decode_any W_95db8 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95dbc : bv 32 := 0x00000693.
Lemma D_95dbc : decode_any W_95dbc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95dc0 : bv 32 := 0x00161793.
Lemma D_95dc0 : decode_any W_95dc0 = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95dc4 : bv 32 := 0x00178813.
Lemma D_95dc4 : decode_any W_95dc4 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95dc8 : bv 32 := 0x00461713.
Lemma D_95dc8 : decode_any W_95dc8 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95dcc : bv 32 := 0x00b86a63.
Lemma D_95dcc : decode_any W_95dcc = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95dd0 : bv 32 := 0x00278793.
Lemma D_95dd0 : decode_any W_95dd0 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95dd4 : bv 32 := 0x02b7ea63.
Lemma D_95dd4 : decode_any W_95dd4 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95dd8 : bv 32 := 0x04c69c63.
Lemma D_95dd8 : decode_any W_95dd8 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95ddc : bv 32 := 0x0880006f.
Lemma D_95ddc : decode_any W_95ddc = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95de0 : bv 32 := 0x00e506b3.
Lemma D_95de0 : decode_any W_95de0 = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95de4 : bv 32 := 0x00481893.
Lemma D_95de4 : decode_any W_95de4 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95de8 : bv 32 := 0x011508b3.
Lemma D_95de8 : decode_any W_95de8 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95dec : bv 32 := 0x0006a683.
Lemma D_95dec : decode_any W_95dec = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95df0 : bv 32 := 0x0008a883.
Lemma D_95df0 : decode_any W_95df0 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95df4 : bv 32 := 0x0116e463.
Lemma D_95df4 : decode_any W_95df4 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95df8 : bv 32 := 0x00060813.
Lemma D_95df8 : decode_any W_95df8 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95dfc : bv 32 := 0x00080693.
Lemma D_95dfc : decode_any W_95dfc = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e00 : bv 32 := 0x00278793.
Lemma D_95e00 : decode_any W_95e00 = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e04 : bv 32 := 0xfcb7fae3.
Lemma D_95e04 : decode_any W_95e04 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e08 : bv 32 := 0x00469813.
Lemma D_95e08 : decode_any W_95e08 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e0c : bv 32 := 0x00479893.
Lemma D_95e0c : decode_any W_95e0c = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e10 : bv 32 := 0x01050833.
Lemma D_95e10 : decode_any W_95e10 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e14 : bv 32 := 0x011508b3.
Lemma D_95e14 : decode_any W_95e14 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e18 : bv 32 := 0x00082803.
Lemma D_95e18 : decode_any W_95e18 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e1c : bv 32 := 0x0008a883.
Lemma D_95e1c : decode_any W_95e1c = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e20 : bv 32 := 0x01186463.
Lemma D_95e20 : decode_any W_95e20 = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e24 : bv 32 := 0x00068793.
Lemma D_95e24 : decode_any W_95e24 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e28 : bv 32 := 0x00078693.
Lemma D_95e28 : decode_any W_95e28 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e2c : bv 32 := 0x02c78c63.
Lemma D_95e2c : decode_any W_95e2c = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e30 : bv 32 := 0x00469613.
Lemma D_95e30 : decode_any W_95e30 = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e34 : bv 32 := 0x00c50633.
Lemma D_95e34 : decode_any W_95e34 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e38 : bv 32 := 0x00063783.
Lemma D_95e38 : decode_any W_95e38 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e3c : bv 32 := 0x00e50733.
Lemma D_95e3c : decode_any W_95e3c = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e40 : bv 32 := 0x00073803.
Lemma D_95e40 : decode_any W_95e40 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e44 : bv 32 := 0x00873883.
Lemma D_95e44 : decode_any W_95e44 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e48 : bv 32 := 0x00f73023.
Lemma D_95e48 : decode_any W_95e48 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e4c : bv 32 := 0x00863783.
Lemma D_95e4c : decode_any W_95e4c = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e50 : bv 32 := 0x00f73423.
Lemma D_95e50 : decode_any W_95e50 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e54 : bv 32 := 0x01063023.
Lemma D_95e54 : decode_any W_95e54 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e58 : bv 32 := 0x01163423.
Lemma D_95e58 : decode_any W_95e58 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e5c : bv 32 := 0x00068613.
Lemma D_95e5c : decode_any W_95e5c = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e60 : bv 32 := 0xf6b6e0e3.
Lemma D_95e60 : decode_any W_95e60 = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e64 : bv 32 := 0xfff58593.
Lemma D_95e64 : decode_any W_95e64 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e68 : bv 32 := 0xf20594e3.
Lemma D_95e68 : decode_any W_95e68 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_95e6c : bv 32 := 0x00008067.
Lemma D_95e6c : decode_any W_95e6c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
