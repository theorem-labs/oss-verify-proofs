(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require BvKH.   (* [comment removed for export] *)
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
Definition W_749a0 : bv 32 := 0x00200613.
Lemma D_749a0 : decode_any W_749a0 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749a4 : bv 32 := 0x14c5ea63.
Lemma D_749a4 : decode_any W_749a4 = Some (Branch BC_LTU 11 12 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749a8 : bv 32 := 0x00100613.
Lemma D_749a8 : decode_any W_749a8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749ac : bv 32 := 0x00100693.
Lemma D_749ac : decode_any W_749ac = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749b0 : bv 32 := 0x00c0006f.
Lemma D_749b0 : decode_any W_749b0 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749b4 : bv 32 := 0x00160613.
Lemma D_749b4 : decode_any W_749b4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749b8 : bv 32 := 0x12b60c63.
Lemma D_749b8 : decode_any W_749b8 = Some (Branch BC_EQ 12 11 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749bc : bv 32 := 0x00461713.
Lemma D_749bc : decode_any W_749bc = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749c0 : bv 32 := 0x00e50733.
Lemma D_749c0 : decode_any W_749c0 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749c4 : bv 32 := 0x00072703.
Lemma D_749c4 : decode_any W_749c4 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749c8 : bv 32 := 0x00060893.
Lemma D_749c8 : decode_any W_749c8 = Some (OpImm ALU_ADD 17 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749cc : bv 32 := 0xfff88793.
Lemma D_749cc : decode_any W_749cc = Some (OpImm ALU_ADD 15 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749d0 : bv 32 := 0x0017d813.
Lemma D_749d0 : decode_any W_749d0 = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749d4 : bv 32 := 0x00481293.
Lemma D_749d4 : decode_any W_749d4 = Some (ShiftImm ALU_SLL 5 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749d8 : bv 32 := 0x005502b3.
Lemma D_749d8 : decode_any W_749d8 = Some (Op ALU_ADD 5 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749dc : bv 32 := 0x0002a303.
Lemma D_749dc : decode_any W_749dc = Some (Load SZ4 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749e0 : bv 32 := 0xfce37ae3.
Lemma D_749e0 : decode_any W_749e0 = Some (Branch BC_GEU 6 14 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749e4 : bv 32 := 0x0002b303.
Lemma D_749e4 : decode_any W_749e4 = Some (Load SZ8 true 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749e8 : bv 32 := 0x00489893.
Lemma D_749e8 : decode_any W_749e8 = Some (ShiftImm ALU_SLL 17 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749ec : bv 32 := 0x011508b3.
Lemma D_749ec : decode_any W_749ec = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749f0 : bv 32 := 0x0048a383.
Lemma D_749f0 : decode_any W_749f0 = Some (Load SZ4 true 7 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749f4 : bv 32 := 0x0068b023.
Lemma D_749f4 : decode_any W_749f4 = Some (Store SZ8 17 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749f8 : bv 32 := 0x0082b303.
Lemma D_749f8 : decode_any W_749f8 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_749fc : bv 32 := 0x0088be03.
Lemma D_749fc : decode_any W_749fc = Some (Load SZ8 true 28 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a00 : bv 32 := 0x0068b423.
Lemma D_74a00 : decode_any W_74a00 = Some (Store SZ8 17 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a04 : bv 32 := 0x00e2a023.
Lemma D_74a04 : decode_any W_74a04 = Some (Store SZ4 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a08 : bv 32 := 0x0072a223.
Lemma D_74a08 : decode_any W_74a08 = Some (Store SZ4 5 7 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a0c : bv 32 := 0x01c2b423.
Lemma D_74a0c : decode_any W_74a0c = Some (Store SZ8 5 28 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a10 : bv 32 := 0x00080893.
Lemma D_74a10 : decode_any W_74a10 = Some (OpImm ALU_ADD 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a14 : bv 32 := 0xfaf6ece3.
Lemma D_74a14 : decode_any W_74a14 = Some (Branch BC_LTU 13 15 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a18 : bv 32 := 0xf9dff06f.
Lemma D_74a18 : decode_any W_74a18 = Some (Jal 0 2097052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a1c : bv 32 := 0x00000613.
Lemma D_74a1c : decode_any W_74a1c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a20 : bv 32 := 0x00459693.
Lemma D_74a20 : decode_any W_74a20 = Some (ShiftImm ALU_SLL 13 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a24 : bv 32 := 0x00d506b3.
Lemma D_74a24 : decode_any W_74a24 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a28 : bv 32 := 0x0006b703.
Lemma D_74a28 : decode_any W_74a28 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a2c : bv 32 := 0x0086b783.
Lemma D_74a2c : decode_any W_74a2c = Some (Load SZ8 true 15 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a30 : bv 32 := 0x00053803.
Lemma D_74a30 : decode_any W_74a30 = Some (Load SZ8 true 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a34 : bv 32 := 0x00853883.
Lemma D_74a34 : decode_any W_74a34 = Some (Load SZ8 true 17 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a38 : bv 32 := 0x00e53023.
Lemma D_74a38 : decode_any W_74a38 = Some (Store SZ8 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a3c : bv 32 := 0x00f53423.
Lemma D_74a3c : decode_any W_74a3c = Some (Store SZ8 10 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a40 : bv 32 := 0x0106b023.
Lemma D_74a40 : decode_any W_74a40 = Some (Store SZ8 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a44 : bv 32 := 0x0116b423.
Lemma D_74a44 : decode_any W_74a44 = Some (Store SZ8 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a48 : bv 32 := 0x00000693.
Lemma D_74a48 : decode_any W_74a48 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a4c : bv 32 := 0x00161793.
Lemma D_74a4c : decode_any W_74a4c = Some (ShiftImm ALU_SLL 15 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a50 : bv 32 := 0x00178813.
Lemma D_74a50 : decode_any W_74a50 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a54 : bv 32 := 0x00461713.
Lemma D_74a54 : decode_any W_74a54 = Some (ShiftImm ALU_SLL 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a58 : bv 32 := 0x00b86a63.
Lemma D_74a58 : decode_any W_74a58 = Some (Branch BC_LTU 16 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a5c : bv 32 := 0x00278793.
Lemma D_74a5c : decode_any W_74a5c = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a60 : bv 32 := 0x02b7ea63.
Lemma D_74a60 : decode_any W_74a60 = Some (Branch BC_LTU 15 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a64 : bv 32 := 0x04c69c63.
Lemma D_74a64 : decode_any W_74a64 = Some (Branch BC_NE 13 12 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a68 : bv 32 := 0x0880006f.
Lemma D_74a68 : decode_any W_74a68 = Some (Jal 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a6c : bv 32 := 0x00e506b3.
Lemma D_74a6c : decode_any W_74a6c = Some (Op ALU_ADD 13 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a70 : bv 32 := 0x00481893.
Lemma D_74a70 : decode_any W_74a70 = Some (ShiftImm ALU_SLL 17 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a74 : bv 32 := 0x011508b3.
Lemma D_74a74 : decode_any W_74a74 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a78 : bv 32 := 0x0006a683.
Lemma D_74a78 : decode_any W_74a78 = Some (Load SZ4 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a7c : bv 32 := 0x0008a883.
Lemma D_74a7c : decode_any W_74a7c = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a80 : bv 32 := 0x0116e463.
Lemma D_74a80 : decode_any W_74a80 = Some (Branch BC_LTU 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a84 : bv 32 := 0x00060813.
Lemma D_74a84 : decode_any W_74a84 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a88 : bv 32 := 0x00080693.
Lemma D_74a88 : decode_any W_74a88 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a8c : bv 32 := 0x00278793.
Lemma D_74a8c : decode_any W_74a8c = Some (OpImm ALU_ADD 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a90 : bv 32 := 0xfcb7fae3.
Lemma D_74a90 : decode_any W_74a90 = Some (Branch BC_GEU 15 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a94 : bv 32 := 0x00469813.
Lemma D_74a94 : decode_any W_74a94 = Some (ShiftImm ALU_SLL 16 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a98 : bv 32 := 0x00479893.
Lemma D_74a98 : decode_any W_74a98 = Some (ShiftImm ALU_SLL 17 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74a9c : bv 32 := 0x01050833.
Lemma D_74a9c : decode_any W_74a9c = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74aa0 : bv 32 := 0x011508b3.
Lemma D_74aa0 : decode_any W_74aa0 = Some (Op ALU_ADD 17 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74aa4 : bv 32 := 0x00082803.
Lemma D_74aa4 : decode_any W_74aa4 = Some (Load SZ4 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74aa8 : bv 32 := 0x0008a883.
Lemma D_74aa8 : decode_any W_74aa8 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74aac : bv 32 := 0x01186463.
Lemma D_74aac : decode_any W_74aac = Some (Branch BC_LTU 16 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ab0 : bv 32 := 0x00068793.
Lemma D_74ab0 : decode_any W_74ab0 = Some (OpImm ALU_ADD 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ab4 : bv 32 := 0x00078693.
Lemma D_74ab4 : decode_any W_74ab4 = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ab8 : bv 32 := 0x02c78c63.
Lemma D_74ab8 : decode_any W_74ab8 = Some (Branch BC_EQ 15 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74abc : bv 32 := 0x00469613.
Lemma D_74abc : decode_any W_74abc = Some (ShiftImm ALU_SLL 12 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ac0 : bv 32 := 0x00c50633.
Lemma D_74ac0 : decode_any W_74ac0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ac4 : bv 32 := 0x00063783.
Lemma D_74ac4 : decode_any W_74ac4 = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ac8 : bv 32 := 0x00e50733.
Lemma D_74ac8 : decode_any W_74ac8 = Some (Op ALU_ADD 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74acc : bv 32 := 0x00073803.
Lemma D_74acc : decode_any W_74acc = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ad0 : bv 32 := 0x00873883.
Lemma D_74ad0 : decode_any W_74ad0 = Some (Load SZ8 true 17 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ad4 : bv 32 := 0x00f73023.
Lemma D_74ad4 : decode_any W_74ad4 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ad8 : bv 32 := 0x00863783.
Lemma D_74ad8 : decode_any W_74ad8 = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74adc : bv 32 := 0x00f73423.
Lemma D_74adc : decode_any W_74adc = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ae0 : bv 32 := 0x01063023.
Lemma D_74ae0 : decode_any W_74ae0 = Some (Store SZ8 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ae4 : bv 32 := 0x01163423.
Lemma D_74ae4 : decode_any W_74ae4 = Some (Store SZ8 12 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74ae8 : bv 32 := 0x00068613.
Lemma D_74ae8 : decode_any W_74ae8 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74aec : bv 32 := 0xf6b6e0e3.
Lemma D_74aec : decode_any W_74aec = Some (Branch BC_LTU 13 11 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74af0 : bv 32 := 0xfff58593.
Lemma D_74af0 : decode_any W_74af0 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74af4 : bv 32 := 0xf20594e3.
Lemma D_74af4 : decode_any W_74af4 = Some (Branch BC_NE 11 0 7976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_74af8 : bv 32 := 0x00008067.
Lemma D_74af8 : decode_any W_74af8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e74 : bv 32 := 0x06060663.
Lemma D_87e74 : decode_any W_87e74 = Some (Branch BC_EQ 12 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e78 : bv 32 := 0x00000693.
Lemma D_87e78 : decode_any W_87e78 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e7c : bv 32 := 0x00d58733.
Lemma D_87e7c : decode_any W_87e7c = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e80 : bv 32 := 0x00074703.
Lemma D_87e80 : decode_any W_87e80 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e84 : bv 32 := 0x00070c63.
Lemma D_87e84 : decode_any W_87e84 = Some (Branch BC_EQ 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e88 : bv 32 := 0x00d507b3.
Lemma D_87e88 : decode_any W_87e88 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e8c : bv 32 := 0x00168693.
Lemma D_87e8c : decode_any W_87e8c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e90 : bv 32 := 0x00e78023.
Lemma D_87e90 : decode_any W_87e90 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e94 : bv 32 := 0xfed614e3.
Lemma D_87e94 : decode_any W_87e94 = Some (Branch BC_NE 12 13 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e98 : bv 32 := 0x00060693.
Lemma D_87e98 : decode_any W_87e98 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87e9c : bv 32 := 0x00d505b3.
Lemma D_87e9c : decode_any W_87e9c = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ea0 : bv 32 := 0x40d6073b.
Lemma D_87ea0 : decode_any W_87ea0 = Some (Op32 ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ea4 : bv 32 := 0x00b76733.
Lemma D_87ea4 : decode_any W_87ea4 = Some (Op ALU_OR 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ea8 : bv 32 := 0x00f77713.
Lemma D_87ea8 : decode_any W_87ea8 = Some (OpImm ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87eac : bv 32 := 0x00070e63.
Lemma D_87eac : decode_any W_87eac = Some (Branch BC_EQ 14 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87eb0 : bv 32 := 0x02d60863.
Lemma D_87eb0 : decode_any W_87eb0 = Some (Branch BC_EQ 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87eb4 : bv 32 := 0x00c50633.
Lemma D_87eb4 : decode_any W_87eb4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87eb8 : bv 32 := 0x00058023.
Lemma D_87eb8 : decode_any W_87eb8 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ebc : bv 32 := 0x00158593.
Lemma D_87ebc : decode_any W_87ebc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ec0 : bv 32 := 0xfec59ce3.
Lemma D_87ec0 : decode_any W_87ec0 = Some (Branch BC_NE 11 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ec4 : bv 32 := 0x01c0006f.
Lemma D_87ec4 : decode_any W_87ec4 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ec8 : bv 32 := 0x00d60c63.
Lemma D_87ec8 : decode_any W_87ec8 = Some (Branch BC_EQ 12 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ecc : bv 32 := 0x00c50633.
Lemma D_87ecc : decode_any W_87ecc = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ed0 : bv 32 := 0x0005b023.
Lemma D_87ed0 : decode_any W_87ed0 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ed4 : bv 32 := 0x0005b423.
Lemma D_87ed4 : decode_any W_87ed4 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ed8 : bv 32 := 0x01058593.
Lemma D_87ed8 : decode_any W_87ed8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87edc : bv 32 := 0xfec5eae3.
Lemma D_87edc : decode_any W_87edc = Some (Branch BC_LTU 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87ee0 : bv 32 := 0x00008067.
Lemma D_87ee0 : decode_any W_87ee0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
