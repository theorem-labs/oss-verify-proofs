(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_2d99c : bv 32 := 0x07c12583.
Lemma F_2d99c : fetch_word Plain.M.loaded_segments (0x2d9f4 : word) = Some W_2d99c.
Proof. vm_refl. Qed.
Lemma D_2d99c : decode_any W_2d99c = Some (Load SZ4 true 11 2 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9a0 : bv 32 := 0x07812603.
Lemma F_2d9a0 : fetch_word Plain.M.loaded_segments (0x2d9f8 : word) = Some W_2d9a0.
Proof. vm_refl. Qed.
Lemma D_2d9a0 : decode_any W_2d9a0 = Some (Load SZ4 true 12 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9a4 : bv 32 := 0x04b64c63.
Lemma F_2d9a4 : fetch_word Plain.M.loaded_segments (0x2d9fc : word) = Some W_2d9a4.
Proof. vm_refl. Qed.
Lemma D_2d9a4 : decode_any W_2d9a4 = Some (Branch BC_LT 12 11 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9a8 : bv 32 := 0x00000713.
Lemma F_2d9a8 : fetch_word Plain.M.loaded_segments (0x2da00 : word) = Some W_2d9a8.
Proof. vm_refl. Qed.
Lemma D_2d9a8 : decode_any W_2d9a8 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9ac : bv 32 := 0x00170693.
Lemma F_2d9ac : fetch_word Plain.M.loaded_segments (0x2da04 : word) = Some W_2d9ac.
Proof. vm_refl. Qed.
Lemma D_2d9ac : decode_any W_2d9ac = Some (OpImm ALU_ADD 13 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9b0 : bv 32 := 0x00269793.
Lemma F_2d9b0 : fetch_word Plain.M.loaded_segments (0x2da08 : word) = Some W_2d9b0.
Proof. vm_refl. Qed.
Lemma D_2d9b0 : decode_any W_2d9b0 = Some (ShiftImm ALU_SLL 15 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9b4 : bv 32 := 0x00fd07b3.
Lemma F_2d9b4 : fetch_word Plain.M.loaded_segments (0x2da0c : word) = Some W_2d9b4.
Proof. vm_refl. Qed.
Lemma D_2d9b4 : decode_any W_2d9b4 = Some (Op ALU_ADD 15 26 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9b8 : bv 32 := 0x0007a783.
Lemma F_2d9b8 : fetch_word Plain.M.loaded_segments (0x2da10 : word) = Some W_2d9b8.
Proof. vm_refl. Qed.
Lemma D_2d9b8 : decode_any W_2d9b8 = Some (Load SZ4 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9bc : bv 32 := 0xd007f7d3.
Lemma F_2d9bc : fetch_word Plain.M.loaded_segments (0x2da14 : word) = Some W_2d9bc.
Proof. vm_refl. Qed.
Lemma D_2d9bc : decode_any W_2d9bc = Some (Fcvt FC_S FC_W 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9c0 : bv 32 := 0xd005f753.
Lemma F_2d9c0 : fetch_word Plain.M.loaded_segments (0x2da18 : word) = Some W_2d9c0.
Proof. vm_refl. Qed.
Lemma D_2d9c0 : decode_any W_2d9c0 = Some (Fcvt FC_S FC_W 14 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9c4 : bv 32 := 0xa0f717d3.
Lemma F_2d9c4 : fetch_word Plain.M.loaded_segments (0x2da1c : word) = Some W_2d9c4.
Proof. vm_refl. Qed.
Lemma D_2d9c4 : decode_any W_2d9c4 = Some (Fcmp F_LT FMT_S 15 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9c8 : bv 32 := 0x02078463.
Lemma F_2d9c8 : fetch_word Plain.M.loaded_segments (0x2da20 : word) = Some W_2d9c8.
Proof. vm_refl. Qed.
Lemma D_2d9c8 : decode_any W_2d9c8 = Some (Branch BC_EQ 15 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9cc : bv 32 := 0x00259613.
Lemma F_2d9cc : fetch_word Plain.M.loaded_segments (0x2da24 : word) = Some W_2d9cc.
Proof. vm_refl. Qed.
Lemma D_2d9cc : decode_any W_2d9cc = Some (ShiftImm ALU_SLL 12 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9d0 : bv 32 := 0x00c50633.
Lemma F_2d9d0 : fetch_word Plain.M.loaded_segments (0x2da28 : word) = Some W_2d9d0.
Proof. vm_refl. Qed.
Lemma D_2d9d0 : decode_any W_2d9d0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9d4 : bv 32 := 0x00e62023.
Lemma F_2d9d4 : fetch_word Plain.M.loaded_segments (0x2da2c : word) = Some W_2d9d4.
Proof. vm_refl. Qed.
Lemma D_2d9d4 : decode_any W_2d9d4 = Some (Store SZ4 12 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9d8 : bv 32 := 0x0015859b.
Lemma F_2d9d8 : fetch_word Plain.M.loaded_segments (0x2da30 : word) = Some W_2d9d8.
Proof. vm_refl. Qed.
Lemma D_2d9d8 : decode_any W_2d9d8 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9dc : bv 32 := 0xd005f753.
Lemma F_2d9dc : fetch_word Plain.M.loaded_segments (0x2da34 : word) = Some W_2d9dc.
Proof. vm_refl. Qed.
Lemma D_2d9dc : decode_any W_2d9dc = Some (Fcvt FC_S FC_W 14 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9e0 : bv 32 := 0xa0f717d3.
Lemma F_2d9e0 : fetch_word Plain.M.loaded_segments (0x2da38 : word) = Some W_2d9e0.
Proof. vm_refl. Qed.
Lemma D_2d9e0 : decode_any W_2d9e0 = Some (Fcmp F_LT FMT_S 15 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9e4 : bv 32 := 0x00460613.
Lemma F_2d9e4 : fetch_word Plain.M.loaded_segments (0x2da3c : word) = Some W_2d9e4.
Proof. vm_refl. Qed.
Lemma D_2d9e4 : decode_any W_2d9e4 = Some (OpImm ALU_ADD 12 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9e8 : bv 32 := 0xfe0796e3.
Lemma F_2d9e8 : fetch_word Plain.M.loaded_segments (0x2da40 : word) = Some W_2d9e8.
Proof. vm_refl. Qed.
Lemma D_2d9e8 : decode_any W_2d9e8 = Some (Branch BC_NE 15 0 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9ec : bv 32 := 0x07812603.
Lemma F_2d9ec : fetch_word Plain.M.loaded_segments (0x2da44 : word) = Some W_2d9ec.
Proof. vm_refl. Qed.
Lemma D_2d9ec : decode_any W_2d9ec = Some (Load SZ4 true 12 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9f0 : bv 32 := 0x00b64663.
Lemma F_2d9f0 : fetch_word Plain.M.loaded_segments (0x2da48 : word) = Some W_2d9f0.
Proof. vm_refl. Qed.
Lemma D_2d9f0 : decode_any W_2d9f0 = Some (Branch BC_LT 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9f4 : bv 32 := 0x00068713.
Lemma F_2d9f4 : fetch_word Plain.M.loaded_segments (0x2da4c : word) = Some W_2d9f4.
Proof. vm_refl. Qed.
Lemma D_2d9f4 : decode_any W_2d9f4 = Some (OpImm ALU_ADD 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9f8 : bv 32 := 0xfa86eae3.
Lemma F_2d9f8 : fetch_word Plain.M.loaded_segments (0x2da50 : word) = Some W_2d9f8.
Proof. vm_refl. Qed.
Lemma D_2d9f8 : decode_any W_2d9f8 = Some (Branch BC_LTU 13 8 8116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d9fc : bv 32 := 0x03813583.
Lemma F_2d9fc : fetch_word Plain.M.loaded_segments (0x2da54 : word) = Some W_2d9fc.
Proof. vm_refl. Qed.
Lemma D_2d9fc : decode_any W_2d9fc = Some (Load SZ8 true 11 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da00 : bv 32 := 0xffe58593.
Lemma F_2da00 : fetch_word Plain.M.loaded_segments (0x2da58 : word) = Some W_2da00.
Proof. vm_refl. Qed.
Lemma D_2da00 : decode_any W_2da00 = Some (OpImm ALU_ADD 11 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da04 : bv 32 := 0x00261613.
Lemma F_2da04 : fetch_word Plain.M.loaded_segments (0x2da5c : word) = Some W_2da04.
Proof. vm_refl. Qed.
Lemma D_2da04 : decode_any W_2da04 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da08 : bv 32 := 0x00c50633.
Lemma F_2da08 : fetch_word Plain.M.loaded_segments (0x2da60 : word) = Some W_2da08.
Proof. vm_refl. Qed.
Lemma D_2da08 : decode_any W_2da08 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da0c : bv 32 := 0x00b62023.
Lemma F_2da0c : fetch_word Plain.M.loaded_segments (0x2da64 : word) = Some W_2da0c.
Proof. vm_refl. Qed.
Lemma D_2da0c : decode_any W_2da0c = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da20 : bv 32 := 0x07c12603.
Lemma F_2da20 : fetch_word Plain.M.loaded_segments (0x2da78 : word) = Some W_2da20.
Proof. vm_refl. Qed.
Lemma D_2da20 : decode_any W_2da20 = Some (Load SZ4 true 12 2 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da24 : bv 32 := 0x07812583.
Lemma F_2da24 : fetch_word Plain.M.loaded_segments (0x2da7c : word) = Some W_2da24.
Proof. vm_refl. Qed.
Lemma D_2da24 : decode_any W_2da24 = Some (Load SZ4 true 11 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da28 : bv 32 := 0x05813883.
Lemma F_2da28 : fetch_word Plain.M.loaded_segments (0x2da80 : word) = Some W_2da28.
Proof. vm_refl. Qed.
Lemma D_2da28 : decode_any W_2da28 = Some (Load SZ8 true 17 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da2c : bv 32 := 0x06c5c463.
Lemma F_2da2c : fetch_word Plain.M.loaded_segments (0x2da84 : word) = Some W_2da2c.
Proof. vm_refl. Qed.
Lemma D_2da2c : decode_any W_2da2c = Some (Branch BC_LT 11 12 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da30 : bv 32 := 0x000d2783.
Lemma F_2da30 : fetch_word Plain.M.loaded_segments (0x2da88 : word) = Some W_2da30.
Proof. vm_refl. Qed.
Lemma D_2da30 : decode_any W_2da30 = Some (Load SZ4 true 15 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da34 : bv 32 := 0x00000693.
Lemma F_2da34 : fetch_word Plain.M.loaded_segments (0x2da8c : word) = Some W_2da34.
Proof. vm_refl. Qed.
Lemma D_2da34 : decode_any W_2da34 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da38 : bv 32 := 0x00168693.
Lemma F_2da38 : fetch_word Plain.M.loaded_segments (0x2da90 : word) = Some W_2da38.
Proof. vm_refl. Qed.
Lemma D_2da38 : decode_any W_2da38 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da3c : bv 32 := 0x00269713.
Lemma F_2da3c : fetch_word Plain.M.loaded_segments (0x2da94 : word) = Some W_2da3c.
Proof. vm_refl. Qed.
Lemma D_2da3c : decode_any W_2da3c = Some (ShiftImm ALU_SLL 14 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da40 : bv 32 := 0x00ed0733.
Lemma F_2da40 : fetch_word Plain.M.loaded_segments (0x2da98 : word) = Some W_2da40.
Proof. vm_refl. Qed.
Lemma D_2da40 : decode_any W_2da40 = Some (Op ALU_ADD 14 26 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da44 : bv 32 := 0x00072703.
Lemma F_2da44 : fetch_word Plain.M.loaded_segments (0x2da9c : word) = Some W_2da44.
Proof. vm_refl. Qed.
Lemma D_2da44 : decode_any W_2da44 = Some (Load SZ4 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da48 : bv 32 := 0xd00777d3.
Lemma F_2da48 : fetch_word Plain.M.loaded_segments (0x2daa0 : word) = Some W_2da48.
Proof. vm_refl. Qed.
Lemma D_2da48 : decode_any W_2da48 = Some (Fcvt FC_S FC_W 15 14 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da4c : bv 32 := 0xd00676d3.
Lemma F_2da4c : fetch_word Plain.M.loaded_segments (0x2daa4 : word) = Some W_2da4c.
Proof. vm_refl. Qed.
Lemma D_2da4c : decode_any W_2da4c = Some (Fcvt FC_S FC_W 13 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da50 : bv 32 := 0xa0f69853.
Lemma F_2da50 : fetch_word Plain.M.loaded_segments (0x2daa8 : word) = Some W_2da50.
Proof. vm_refl. Qed.
Lemma D_2da50 : decode_any W_2da50 = Some (Fcmp F_LT FMT_S 16 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da54 : bv 32 := 0x02080a63.
Lemma F_2da54 : fetch_word Plain.M.loaded_segments (0x2daac : word) = Some W_2da54.
Proof. vm_refl. Qed.
Lemma D_2da54 : decode_any W_2da54 = Some (Branch BC_EQ 16 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da58 : bv 32 := 0xd007f753.
Lemma F_2da58 : fetch_word Plain.M.loaded_segments (0x2dab0 : word) = Some W_2da58.
Proof. vm_refl. Qed.
Lemma D_2da58 : decode_any W_2da58 = Some (Fcvt FC_S FC_W 14 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da5c : bv 32 := 0x00261793.
Lemma F_2da5c : fetch_word Plain.M.loaded_segments (0x2dab4 : word) = Some W_2da5c.
Proof. vm_refl. Qed.
Lemma D_2da5c : decode_any W_2da5c = Some (ShiftImm ALU_SLL 15 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da60 : bv 32 := 0x08e7f653.
Lemma F_2da60 : fetch_word Plain.M.loaded_segments (0x2dab8 : word) = Some W_2da60.
Proof. vm_refl. Qed.
Lemma D_2da60 : decode_any W_2da60 = Some (Fari F_SUB FMT_S 12 15 14 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da64 : bv 32 := 0x00f507b3.
Lemma F_2da64 : fetch_word Plain.M.loaded_segments (0x2dabc : word) = Some W_2da64.
Proof. vm_refl. Qed.
Lemma D_2da64 : decode_any W_2da64 = Some (Op ALU_ADD 15 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da68 : bv 32 := 0x08e6f6d3.
Lemma F_2da68 : fetch_word Plain.M.loaded_segments (0x2dac0 : word) = Some W_2da68.
Proof. vm_refl. Qed.
Lemma D_2da68 : decode_any W_2da68 = Some (Fari F_SUB FMT_S 13 13 14 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da6c : bv 32 := 0x0016061b.
Lemma F_2da6c : fetch_word Plain.M.loaded_segments (0x2dac4 : word) = Some W_2da6c.
Proof. vm_refl. Qed.
Lemma D_2da6c : decode_any W_2da6c = Some (OpImm32 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da70 : bv 32 := 0x18c6f6d3.
Lemma F_2da70 : fetch_word Plain.M.loaded_segments (0x2dac8 : word) = Some W_2da70.
Proof. vm_refl. Qed.
Lemma D_2da70 : decode_any W_2da70 = Some (Fari F_DIV FMT_S 13 13 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da74 : bv 32 := 0x00d7a027.
Lemma F_2da74 : fetch_word Plain.M.loaded_segments (0x2dacc : word) = Some W_2da74.
Proof. vm_refl. Qed.
Lemma D_2da74 : decode_any W_2da74 = Some (FStore FMT_S 15 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da78 : bv 32 := 0xd00676d3.
Lemma F_2da78 : fetch_word Plain.M.loaded_segments (0x2dad0 : word) = Some W_2da78.
Proof. vm_refl. Qed.
Lemma D_2da78 : decode_any W_2da78 = Some (Fcvt FC_S FC_W 13 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da7c : bv 32 := 0xa0f69853.
Lemma F_2da7c : fetch_word Plain.M.loaded_segments (0x2dad4 : word) = Some W_2da7c.
Proof. vm_refl. Qed.
Lemma D_2da7c : decode_any W_2da7c = Some (Fcmp F_LT FMT_S 16 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da80 : bv 32 := 0x00478793.
Lemma F_2da80 : fetch_word Plain.M.loaded_segments (0x2dad8 : word) = Some W_2da80.
Proof. vm_refl. Qed.
Lemma D_2da80 : decode_any W_2da80 = Some (OpImm ALU_ADD 15 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da84 : bv 32 := 0xfe0812e3.
Lemma F_2da84 : fetch_word Plain.M.loaded_segments (0x2dadc : word) = Some W_2da84.
Proof. vm_refl. Qed.
Lemma D_2da84 : decode_any W_2da84 = Some (Branch BC_NE 16 0 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da88 : bv 32 := 0x00c5c663.
Lemma F_2da88 : fetch_word Plain.M.loaded_segments (0x2dae0 : word) = Some W_2da88.
Proof. vm_refl. Qed.
Lemma D_2da88 : decode_any W_2da88 = Some (Branch BC_LT 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da8c : bv 32 := 0x00070793.
Lemma F_2da8c : fetch_word Plain.M.loaded_segments (0x2dae4 : word) = Some W_2da8c.
Proof. vm_refl. Qed.
Lemma D_2da8c : decode_any W_2da8c = Some (OpImm ALU_ADD 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da90 : bv 32 := 0xfa86e4e3.
Lemma F_2da90 : fetch_word Plain.M.loaded_segments (0x2dae8 : word) = Some W_2da90.
Proof. vm_refl. Qed.
Lemma D_2da90 : decode_any W_2da90 = Some (Branch BC_LTU 13 8 8104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da94 : bv 32 := 0x00259593.
Lemma F_2da94 : fetch_word Plain.M.loaded_segments (0x2daec : word) = Some W_2da94.
Proof. vm_refl. Qed.
Lemma D_2da94 : decode_any W_2da94 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da98 : bv 32 := 0x3f800637.
Lemma F_2da98 : fetch_word Plain.M.loaded_segments (0x2daf0 : word) = Some W_2da98.
Proof. vm_refl. Qed.
Lemma D_2da98 : decode_any W_2da98 = Some (Lui 12 260096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2da9c : bv 32 := 0x00b505b3.
Lemma F_2da9c : fetch_word Plain.M.loaded_segments (0x2daf4 : word) = Some W_2da9c.
Proof. vm_refl. Qed.
Lemma D_2da9c : decode_any W_2da9c = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2daa0 : bv 32 := 0x00c5a023.
Lemma F_2daa0 : fetch_word Plain.M.loaded_segments (0x2daf8 : word) = Some W_2daa0.
Proof. vm_refl. Qed.
Lemma D_2daa0 : decode_any W_2daa0 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dad8 : bv 32 := 0x02840533.
Lemma F_2dad8 : fetch_word Plain.M.loaded_segments (0x2db30 : word) = Some W_2dad8.
Proof. vm_refl. Qed.
Lemma D_2dad8 : decode_any W_2dad8 = Some (Mul M_MUL 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dadc : bv 32 := 0xd01577d3.
Lemma F_2dadc : fetch_word Plain.M.loaded_segments (0x2db34 : word) = Some W_2dadc.
Proof. vm_refl. Qed.
Lemma D_2dadc : decode_any W_2dadc = Some (Fcvt FC_S FC_WU 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dae0 : bv 32 := 0x20f797d3.
Lemma F_2dae0 : fetch_word Plain.M.loaded_segments (0x2db38 : word) = Some W_2dae0.
Proof. vm_refl. Qed.
Lemma D_2dae0 : decode_any W_2dae0 = Some (Fsgnj F_SGNJN FMT_S 15 15 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dae4 : bv 32 := 0x1927f553.
Lemma F_2dae4 : fetch_word Plain.M.loaded_segments (0x2db3c : word) = Some W_2dae4.
Proof. vm_refl. Qed.
Lemma D_2dae4 : decode_any W_2dae4 = Some (Fari F_DIV FMT_S 10 15 18 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dae8 : bv 32 := 0x678030ef.
Lemma F_2dae8 : fetch_word Plain.M.loaded_segments (0x2db40 : word) = Some W_2dae8.
Proof. vm_refl. Qed.
Lemma D_2dae8 : decode_any W_2dae8 = Some (Jal 1 13944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2daec : bv 32 := 0x00a4a027.
Lemma F_2daec : fetch_word Plain.M.loaded_segments (0x2db44 : word) = Some W_2daec.
Proof. vm_refl. Qed.
Lemma D_2daec : decode_any W_2daec = Some (FStore FMT_S 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2daf0 : bv 32 := 0x00140413.
Lemma F_2daf0 : fetch_word Plain.M.loaded_segments (0x2db48 : word) = Some W_2daf0.
Proof. vm_refl. Qed.
Lemma D_2daf0 : decode_any W_2daf0 = Some (OpImm ALU_ADD 8 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2daf4 : bv 32 := 0x00448493.
Lemma F_2daf4 : fetch_word Plain.M.loaded_segments (0x2db4c : word) = Some W_2daf4.
Proof. vm_refl. Qed.
Lemma D_2daf4 : decode_any W_2daf4 = Some (OpImm ALU_ADD 9 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2daf8 : bv 32 := 0xfe8910e3.
Lemma F_2daf8 : fetch_word Plain.M.loaded_segments (0x2db50 : word) = Some W_2daf8.
Proof. vm_refl. Qed.
Lemma D_2daf8 : decode_any W_2daf8 = Some (Branch BC_NE 18 8 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2db2c : bv 32 := 0x02948533.
Lemma F_2db2c : fetch_word Plain.M.loaded_segments (0x2db84 : word) = Some W_2db2c.
Proof. vm_refl. Qed.
Lemma D_2db2c : decode_any W_2db2c = Some (Mul M_MUL 10 9 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2db30 : bv 32 := 0xd01577d3.
Lemma F_2db30 : fetch_word Plain.M.loaded_segments (0x2db88 : word) = Some W_2db30.
Proof. vm_refl. Qed.
Lemma D_2db30 : decode_any W_2db30 = Some (Fcvt FC_S FC_WU 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2db34 : bv 32 := 0x20f797d3.
Lemma F_2db34 : fetch_word Plain.M.loaded_segments (0x2db8c : word) = Some W_2db34.
Proof. vm_refl. Qed.
Lemma D_2db34 : decode_any W_2db34 = Some (Fsgnj F_SGNJN FMT_S 15 15 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2db38 : bv 32 := 0x1887f553.
Lemma F_2db38 : fetch_word Plain.M.loaded_segments (0x2db90 : word) = Some W_2db38.
Proof. vm_refl. Qed.
Lemma D_2db38 : decode_any W_2db38 = Some (Fari F_DIV FMT_S 10 15 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2db3c : bv 32 := 0x624030ef.
Lemma F_2db3c : fetch_word Plain.M.loaded_segments (0x2db94 : word) = Some W_2db3c.
Proof. vm_refl. Qed.
Lemma D_2db3c : decode_any W_2db3c = Some (Jal 1 13860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2db40 : bv 32 := 0x00a92027.
Lemma F_2db40 : fetch_word Plain.M.loaded_segments (0x2db98 : word) = Some W_2db40.
Proof. vm_refl. Qed.
Lemma D_2db40 : decode_any W_2db40 = Some (FStore FMT_S 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2db44 : bv 32 := 0x00148493.
Lemma F_2db44 : fetch_word Plain.M.loaded_segments (0x2db9c : word) = Some W_2db44.
Proof. vm_refl. Qed.
Lemma D_2db44 : decode_any W_2db44 = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2db48 : bv 32 := 0x00490913.
Lemma F_2db48 : fetch_word Plain.M.loaded_segments (0x2dba0 : word) = Some W_2db48.
Proof. vm_refl. Qed.
Lemma D_2db48 : decode_any W_2db48 = Some (OpImm ALU_ADD 18 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2db4c : bv 32 := 0xfe8490e3.
Lemma F_2db4c : fetch_word Plain.M.loaded_segments (0x2dba4 : word) = Some W_2db4c.
Proof. vm_refl. Qed.
Lemma D_2db4c : decode_any W_2db4c = Some (Branch BC_NE 9 8 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dca8 : bv 32 := 0x00150513.
Lemma F_2dca8 : fetch_word Plain.M.loaded_segments (0x2dd00 : word) = Some W_2dca8.
Proof. vm_refl. Qed.
Lemma D_2dca8 : decode_any W_2dca8 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dcac : bv 32 := 0x01360633.
Lemma F_2dcac : fetch_word Plain.M.loaded_segments (0x2dd04 : word) = Some W_2dcac.
Proof. vm_refl. Qed.
Lemma D_2dcac : decode_any W_2dcac = Some (Op ALU_ADD 12 12 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dcb0 : bv 32 := 0x0d550c63.
Lemma F_2dcb0 : fetch_word Plain.M.loaded_segments (0x2dd08 : word) = Some W_2dcb0.
Proof. vm_refl. Qed.
Lemma D_2dcb0 : decode_any W_2dcb0 = Some (Branch BC_EQ 10 21 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dcb4 : bv 32 := 0xff605ae3.
Lemma F_2dcb4 : fetch_word Plain.M.loaded_segments (0x2dd0c : word) = Some W_2dcb4.
Proof. vm_refl. Qed.
Lemma D_2dcb4 : decode_any W_2dcb4 = Some (Branch BC_GE 0 22 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dcb8 : bv 32 := 0x00000693.
Lemma F_2dcb8 : fetch_word Plain.M.loaded_segments (0x2dd10 : word) = Some W_2dcb8.
Proof. vm_refl. Qed.
Lemma D_2dcb8 : decode_any W_2dcb8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dcbc : bv 32 := 0x02a98733.
Lemma F_2dcbc : fetch_word Plain.M.loaded_segments (0x2dd14 : word) = Some W_2dcbc.
Proof. vm_refl. Qed.
Lemma D_2dcbc : decode_any W_2dcbc = Some (Mul M_MUL 14 19 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dcc0 : bv 32 := 0x01e507b3.
Lemma F_2dcc0 : fetch_word Plain.M.loaded_segments (0x2dd18 : word) = Some W_2dcc0.
Proof. vm_refl. Qed.
Lemma D_2dcc0 : decode_any W_2dcc0 = Some (Op ALU_ADD 15 10 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dcc4 : bv 32 := 0x00ef8733.
Lemma F_2dcc4 : fetch_word Plain.M.loaded_segments (0x2dd1c : word) = Some W_2dcc4.
Proof. vm_refl. Qed.
Lemma D_2dcc4 : decode_any W_2dcc4 = Some (Op ALU_ADD 14 31 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dcc8 : bv 32 := 0x03b787b3.
Lemma F_2dcc8 : fetch_word Plain.M.loaded_segments (0x2dd20 : word) = Some W_2dcc8.
Proof. vm_refl. Qed.
Lemma D_2dcc8 : decode_any W_2dcc8 = Some (Mul M_MUL 15 15 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dccc : bv 32 := 0x00279793.
Lemma F_2dccc : fetch_word Plain.M.loaded_segments (0x2dd24 : word) = Some W_2dccc.
Proof. vm_refl. Qed.
Lemma D_2dccc : decode_any W_2dccc = Some (ShiftImm ALU_SLL 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dcd0 : bv 32 := 0x00f587b3.
Lemma F_2dcd0 : fetch_word Plain.M.loaded_segments (0x2dd28 : word) = Some W_2dcd0.
Proof. vm_refl. Qed.
Lemma D_2dcd0 : decode_any W_2dcd0 = Some (Op ALU_ADD 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dcd4 : bv 32 := 0x00060813.
Lemma F_2dcd4 : fetch_word Plain.M.loaded_segments (0x2dd2c : word) = Some W_2dcd4.
Proof. vm_refl. Qed.
Lemma D_2dcd4 : decode_any W_2dcd4 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dcd8 : bv 32 := 0x0100006f.
Lemma F_2dcd8 : fetch_word Plain.M.loaded_segments (0x2dd30 : word) = Some W_2dcd8.
Proof. vm_refl. Qed.
Lemma D_2dcd8 : decode_any W_2dcd8 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dcdc : bv 32 := 0x00168693.
Lemma F_2dcdc : fetch_word Plain.M.loaded_segments (0x2dd34 : word) = Some W_2dcdc.
Proof. vm_refl. Qed.
Lemma D_2dcdc : decode_any W_2dcdc = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dce0 : bv 32 := 0x00180813.
Lemma F_2dce0 : fetch_word Plain.M.loaded_segments (0x2dd38 : word) = Some W_2dce0.
Proof. vm_refl. Qed.
Lemma D_2dce0 : decode_any W_2dce0 = Some (OpImm ALU_ADD 16 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dce4 : bv 32 := 0xfd6682e3.
Lemma F_2dce4 : fetch_word Plain.M.loaded_segments (0x2dd3c : word) = Some W_2dce4.
Proof. vm_refl. Qed.
Lemma D_2dce4 : decode_any W_2dce4 = Some (Branch BC_EQ 13 22 8132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dce8 : bv 32 := 0xfe0ccae3.
Lemma F_2dce8 : fetch_word Plain.M.loaded_segments (0x2dd40 : word) = Some W_2dce8.
Proof. vm_refl. Qed.
Lemma D_2dce8 : decode_any W_2dce8 = Some (Branch BC_LT 25 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dcec : bv 32 := 0x00d708b3.
Lemma F_2dcec : fetch_word Plain.M.loaded_segments (0x2dd44 : word) = Some W_2dcec.
Proof. vm_refl. Qed.
Lemma D_2dcec : decode_any W_2dcec = Some (Op ALU_ADD 17 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dcf0 : bv 32 := 0x00090293.
Lemma F_2dcf0 : fetch_word Plain.M.loaded_segments (0x2dd48 : word) = Some W_2dcf0.
Proof. vm_refl. Qed.
Lemma D_2dcf0 : decode_any W_2dcf0 = Some (OpImm ALU_ADD 5 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dcf4 : bv 32 := 0x00080313.
Lemma F_2dcf4 : fetch_word Plain.M.loaded_segments (0x2dd4c : word) = Some W_2dcf4.
Proof. vm_refl. Qed.
Lemma D_2dcf4 : decode_any W_2dcf4 = Some (OpImm ALU_ADD 6 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dcf8 : bv 32 := 0x208407d3.
Lemma F_2dcf8 : fetch_word Plain.M.loaded_segments (0x2dd50 : word) = Some W_2dcf8.
Proof. vm_refl. Qed.
Lemma D_2dcf8 : decode_any W_2dcf8 = Some (Fsgnj F_SGNJ FMT_S 15 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dcfc : bv 32 := 0x20840753.
Lemma F_2dcfc : fetch_word Plain.M.loaded_segments (0x2dd54 : word) = Some W_2dcfc.
Proof. vm_refl. Qed.
Lemma D_2dcfc : decode_any W_2dcfc = Some (Fsgnj F_SGNJ FMT_S 14 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd00 : bv 32 := 0x00334393.
Lemma F_2dd00 : fetch_word Plain.M.loaded_segments (0x2dd58 : word) = Some W_2dd00.
Proof. vm_refl. Qed.
Lemma D_2dd00 : decode_any W_2dd00 = Some (OpImm ALU_XOR 7 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd04 : bv 32 := 0x41f2de1b.
Lemma F_2dd04 : fetch_word Plain.M.loaded_segments (0x2dd5c : word) = Some W_2dd04.
Proof. vm_refl. Qed.
Lemma D_2dd04 : decode_any W_2dd04 = Some (ShiftImm32 ALU_SRA 28 5 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd08 : bv 32 := 0x0003c383.
Lemma F_2dd08 : fetch_word Plain.M.loaded_segments (0x2dd60 : word) = Some W_2dd08.
Proof. vm_refl. Qed.
Lemma D_2dd08 : decode_any W_2dd08 = Some (Load SZ1 false 7 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd0c : bv 32 := 0x01c2ceb3.
Lemma F_2dd0c : fetch_word Plain.M.loaded_segments (0x2dd64 : word) = Some W_2dd0c.
Proof. vm_refl. Qed.
Lemma D_2dd0c : decode_any W_2dd0c = Some (Op ALU_XOR 29 5 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd10 : bv 32 := 0x41ce8e3b.
Lemma F_2dd10 : fetch_word Plain.M.loaded_segments (0x2dd68 : word) = Some W_2dd10.
Proof. vm_refl. Qed.
Lemma D_2dd10 : decode_any W_2dd10 = Some (Op32 ALU_SUB 28 29 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd14 : bv 32 := 0x002e1e13.
Lemma F_2dd14 : fetch_word Plain.M.loaded_segments (0x2dd6c : word) = Some W_2dd14.
Proof. vm_refl. Qed.
Lemma D_2dd14 : decode_any W_2dd14 = Some (ShiftImm ALU_SLL 28 28 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd18 : bv 32 := 0x01cb8e33.
Lemma F_2dd18 : fetch_word Plain.M.loaded_segments (0x2dd70 : word) = Some W_2dd18.
Proof. vm_refl. Qed.
Lemma D_2dd18 : decode_any W_2dd18 = Some (Op ALU_ADD 28 23 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd1c : bv 32 := 0x0ff3f393.
Lemma F_2dd1c : fetch_word Plain.M.loaded_segments (0x2dd74 : word) = Some W_2dd1c.
Proof. vm_refl. Qed.
Lemma D_2dd1c : decode_any W_2dd1c = Some (OpImm ALU_AND 7 7 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd20 : bv 32 := 0x000e2687.
Lemma F_2dd20 : fetch_word Plain.M.loaded_segments (0x2dd78 : word) = Some W_2dd20.
Proof. vm_refl. Qed.
Lemma D_2dd20 : decode_any W_2dd20 = Some (FLoad FMT_S 13 28 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd24 : bv 32 := 0x407d0e3b.
Lemma F_2dd24 : fetch_word Plain.M.loaded_segments (0x2dd7c : word) = Some W_2dd24.
Proof. vm_refl. Qed.
Lemma D_2dd24 : decode_any W_2dd24 = Some (Op32 ALU_SUB 28 26 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd28 : bv 32 := 0x41fe5e9b.
Lemma F_2dd28 : fetch_word Plain.M.loaded_segments (0x2dd80 : word) = Some W_2dd28.
Proof. vm_refl. Qed.
Lemma D_2dd28 : decode_any W_2dd28 = Some (ShiftImm32 ALU_SRA 29 28 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd2c : bv 32 := 0x01de4e33.
Lemma F_2dd2c : fetch_word Plain.M.loaded_segments (0x2dd84 : word) = Some W_2dd2c.
Proof. vm_refl. Qed.
Lemma D_2dd2c : decode_any W_2dd2c = Some (Op ALU_XOR 28 28 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd30 : bv 32 := 0x41de0e3b.
Lemma F_2dd30 : fetch_word Plain.M.loaded_segments (0x2dd88 : word) = Some W_2dd30.
Proof. vm_refl. Qed.
Lemma D_2dd30 : decode_any W_2dd30 = Some (Op32 ALU_SUB 28 28 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd34 : bv 32 := 0x002e1e13.
Lemma F_2dd34 : fetch_word Plain.M.loaded_segments (0x2dd8c : word) = Some W_2dd34.
Proof. vm_refl. Qed.
Lemma D_2dd34 : decode_any W_2dd34 = Some (ShiftImm ALU_SLL 28 28 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd38 : bv 32 := 0x01cc0e33.
Lemma F_2dd38 : fetch_word Plain.M.loaded_segments (0x2dd90 : word) = Some W_2dd38.
Proof. vm_refl. Qed.
Lemma D_2dd38 : decode_any W_2dd38 = Some (Op ALU_ADD 28 24 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd3c : bv 32 := 0x000e2607.
Lemma F_2dd3c : fetch_word Plain.M.loaded_segments (0x2dd94 : word) = Some W_2dd3c.
Proof. vm_refl. Qed.
Lemma D_2dd3c : decode_any W_2dd3c = Some (FLoad FMT_S 12 28 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd40 : bv 32 := 0x00130313.
Lemma F_2dd40 : fetch_word Plain.M.loaded_segments (0x2dd98 : word) = Some W_2dd40.
Proof. vm_refl. Qed.
Lemma D_2dd40 : decode_any W_2dd40 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd44 : bv 32 := 0x10c6f6d3.
Lemma F_2dd44 : fetch_word Plain.M.loaded_segments (0x2dd9c : word) = Some W_2dd44.
Proof. vm_refl. Qed.
Lemma D_2dd44 : decode_any W_2dd44 = Some (Fari F_MUL FMT_S 13 13 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd48 : bv 32 := 0xd013f653.
Lemma F_2dd48 : fetch_word Plain.M.loaded_segments (0x2dda0 : word) = Some W_2dd48.
Proof. vm_refl. Qed.
Lemma D_2dd48 : decode_any W_2dd48 = Some (Fcvt FC_S FC_WU 12 7 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd4c : bv 32 := 0x78c6f7c3.
Lemma F_2dd4c : fetch_word Plain.M.loaded_segments (0x2dda4 : word) = Some W_2dd4c.
Proof. vm_refl. Qed.
Lemma D_2dd4c : decode_any W_2dd4c = Some (Fma F_MADD FMT_S 15 13 12 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd50 : bv 32 := 0x00d77753.
Lemma F_2dd50 : fetch_word Plain.M.loaded_segments (0x2dda8 : word) = Some W_2dd50.
Proof. vm_refl. Qed.
Lemma D_2dd50 : decode_any W_2dd50 = Some (Fari F_ADD FMT_S 14 14 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd54 : bv 32 := 0x00128293.
Lemma F_2dd54 : fetch_word Plain.M.loaded_segments (0x2ddac : word) = Some W_2dd54.
Proof. vm_refl. Qed.
Lemma D_2dd54 : decode_any W_2dd54 = Some (OpImm ALU_ADD 5 5 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd58 : bv 32 := 0xfb1314e3.
Lemma F_2dd58 : fetch_word Plain.M.loaded_segments (0x2ddb0 : word) = Some W_2dd58.
Proof. vm_refl. Qed.
Lemma D_2dd58 : decode_any W_2dd58 = Some (Branch BC_NE 6 17 8104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd5c : bv 32 := 0xa0e418d3.
Lemma F_2dd5c : fetch_word Plain.M.loaded_segments (0x2ddb4 : word) = Some W_2dd5c.
Proof. vm_refl. Qed.
Lemma D_2dd5c : decode_any W_2dd5c = Some (Fcmp F_LT FMT_S 17 8 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd60 : bv 32 := 0xf6088ee3.
Lemma F_2dd60 : fetch_word Plain.M.loaded_segments (0x2ddb8 : word) = Some W_2dd60.
Proof. vm_refl. Qed.
Lemma D_2dd60 : decode_any W_2dd60 = Some (Branch BC_EQ 17 0 8060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd64 : bv 32 := 0x8a84b687.
Lemma F_2dd64 : fetch_word Plain.M.loaded_segments (0x2ddbc : word) = Some W_2dd64.
Proof. vm_refl. Qed.
Lemma D_2dd64 : decode_any W_2dd64 = Some (FLoad FMT_D 13 9 2216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd68 : bv 32 := 0x18e7f7d3.
Lemma F_2dd68 : fetch_word Plain.M.loaded_segments (0x2ddc0 : word) = Some W_2dd68.
Proof. vm_refl. Qed.
Lemma D_2dd68 : decode_any W_2dd68 = Some (Fari F_DIV FMT_S 15 15 14 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd6c : bv 32 := 0x00d788b3.
Lemma F_2dd6c : fetch_word Plain.M.loaded_segments (0x2ddc4 : word) = Some W_2dd6c.
Proof. vm_refl. Qed.
Lemma D_2dd6c : decode_any W_2dd6c = Some (Op ALU_ADD 17 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd70 : bv 32 := 0x420787d3.
Lemma F_2dd70 : fetch_word Plain.M.loaded_segments (0x2ddc8 : word) = Some W_2dd70.
Proof. vm_refl. Qed.
Lemma D_2dd70 : decode_any W_2dd70 = Some (Fcvt FC_D FC_S 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd74 : bv 32 := 0x02d7f7d3.
Lemma F_2dd74 : fetch_word Plain.M.loaded_segments (0x2ddcc : word) = Some W_2dd74.
Proof. vm_refl. Qed.
Lemma D_2dd74 : decode_any W_2dd74 = Some (Fari F_ADD FMT_D 15 15 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd78 : bv 32 := 0xc20792d3.
Lemma F_2dd78 : fetch_word Plain.M.loaded_segments (0x2ddd0 : word) = Some W_2dd78.
Proof. vm_refl. Qed.
Lemma D_2dd78 : decode_any W_2dd78 = Some (Fcvt FC_W FC_D 5 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd7c : bv 32 := 0x0038c893.
Lemma F_2dd7c : fetch_word Plain.M.loaded_segments (0x2ddd4 : word) = Some W_2dd7c.
Proof. vm_refl. Qed.
Lemma D_2dd7c : decode_any W_2dd7c = Some (OpImm ALU_XOR 17 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd80 : bv 32 := 0x00588023.
Lemma F_2dd80 : fetch_word Plain.M.loaded_segments (0x2ddd8 : word) = Some W_2dd80.
Proof. vm_refl. Qed.
Lemma D_2dd80 : decode_any W_2dd80 = Some (Store SZ1 17 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dd84 : bv 32 := 0xf59ff06f.
Lemma F_2dd84 : fetch_word Plain.M.loaded_segments (0x2dddc : word) = Some W_2dd84.
Proof. vm_refl. Qed.
Lemma D_2dd84 : decode_any W_2dd84 = Some (Jal 0 2096984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ddec : bv 32 := 0x00158593.
Lemma F_2ddec : fetch_word Plain.M.loaded_segments (0x2de44 : word) = Some W_2ddec.
Proof. vm_refl. Qed.
Lemma D_2ddec : decode_any W_2ddec = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ddf0 : bv 32 := 0x00c686b3.
Lemma F_2ddf0 : fetch_word Plain.M.loaded_segments (0x2de48 : word) = Some W_2ddf0.
Proof. vm_refl. Qed.
Lemma D_2ddf0 : decode_any W_2ddf0 = Some (Op ALU_ADD 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ddf4 : bv 32 := 0xe35588e3.
Lemma F_2ddf4 : fetch_word Plain.M.loaded_segments (0x2de4c : word) = Some W_2ddf4.
Proof. vm_refl. Qed.
Lemma D_2ddf4 : decode_any W_2ddf4 = Some (Branch BC_EQ 11 21 7728, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ddf8 : bv 32 := 0xff605ae3.
Lemma F_2ddf8 : fetch_word Plain.M.loaded_segments (0x2de50 : word) = Some W_2ddf8.
Proof. vm_refl. Qed.
Lemma D_2ddf8 : decode_any W_2ddf8 = Some (Branch BC_GE 0 22 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ddfc : bv 32 := 0x00000713.
Lemma F_2ddfc : fetch_word Plain.M.loaded_segments (0x2de54 : word) = Some W_2ddfc.
Proof. vm_refl. Qed.
Lemma D_2ddfc : decode_any W_2ddfc = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de00 : bv 32 := 0x02a587b3.
Lemma F_2de00 : fetch_word Plain.M.loaded_segments (0x2de58 : word) = Some W_2de00.
Proof. vm_refl. Qed.
Lemma D_2de00 : decode_any W_2de00 = Some (Mul M_MUL 15 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de04 : bv 32 := 0x01f58833.
Lemma F_2de04 : fetch_word Plain.M.loaded_segments (0x2de5c : word) = Some W_2de04.
Proof. vm_refl. Qed.
Lemma D_2de04 : decode_any W_2de04 = Some (Op ALU_ADD 16 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de08 : bv 32 := 0x00279793.
Lemma F_2de08 : fetch_word Plain.M.loaded_segments (0x2de60 : word) = Some W_2de08.
Proof. vm_refl. Qed.
Lemma D_2de08 : decode_any W_2de08 = Some (ShiftImm ALU_SLL 15 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de0c : bv 32 := 0x03b80833.
Lemma F_2de0c : fetch_word Plain.M.loaded_segments (0x2de64 : word) = Some W_2de0c.
Proof. vm_refl. Qed.
Lemma D_2de0c : decode_any W_2de0c = Some (Mul M_MUL 16 16 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de10 : bv 32 := 0x00f407b3.
Lemma F_2de10 : fetch_word Plain.M.loaded_segments (0x2de68 : word) = Some W_2de10.
Proof. vm_refl. Qed.
Lemma D_2de10 : decode_any W_2de10 = Some (Op ALU_ADD 15 8 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de14 : bv 32 := 0x00281813.
Lemma F_2de14 : fetch_word Plain.M.loaded_segments (0x2de6c : word) = Some W_2de14.
Proof. vm_refl. Qed.
Lemma D_2de14 : decode_any W_2de14 = Some (ShiftImm ALU_SLL 16 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de18 : bv 32 := 0x01f088b3.
Lemma F_2de18 : fetch_word Plain.M.loaded_segments (0x2de70 : word) = Some W_2de18.
Proof. vm_refl. Qed.
Lemma D_2de18 : decode_any W_2de18 = Some (Op ALU_ADD 17 1 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de1c : bv 32 := 0x01088833.
Lemma F_2de1c : fetch_word Plain.M.loaded_segments (0x2de74 : word) = Some W_2de1c.
Proof. vm_refl. Qed.
Lemma D_2de1c : decode_any W_2de1c = Some (Op ALU_ADD 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de20 : bv 32 := 0x00068893.
Lemma F_2de20 : fetch_word Plain.M.loaded_segments (0x2de78 : word) = Some W_2de20.
Proof. vm_refl. Qed.
Lemma D_2de20 : decode_any W_2de20 = Some (OpImm ALU_ADD 17 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de24 : bv 32 := 0x0280006f.
Lemma F_2de24 : fetch_word Plain.M.loaded_segments (0x2de7c : word) = Some W_2de24.
Proof. vm_refl. Qed.
Lemma D_2de24 : decode_any W_2de24 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de28 : bv 32 := 0x00e802b3.
Lemma F_2de28 : fetch_word Plain.M.loaded_segments (0x2de80 : word) = Some W_2de28.
Proof. vm_refl. Qed.
Lemma D_2de28 : decode_any W_2de28 = Some (Op ALU_ADD 5 16 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de2c : bv 32 := 0x0032c293.
Lemma F_2de2c : fetch_word Plain.M.loaded_segments (0x2de84 : word) = Some W_2de2c.
Proof. vm_refl. Qed.
Lemma D_2de2c : decode_any W_2de2c = Some (OpImm ALU_XOR 5 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de30 : bv 32 := 0x0002c283.
Lemma F_2de30 : fetch_word Plain.M.loaded_segments (0x2de88 : word) = Some W_2de30.
Proof. vm_refl. Qed.
Lemma D_2de30 : decode_any W_2de30 = Some (Load SZ1 false 5 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de34 : bv 32 := 0x00e78333.
Lemma F_2de34 : fetch_word Plain.M.loaded_segments (0x2de8c : word) = Some W_2de34.
Proof. vm_refl. Qed.
Lemma D_2de34 : decode_any W_2de34 = Some (Op ALU_ADD 6 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de38 : bv 32 := 0x00170713.
Lemma F_2de38 : fetch_word Plain.M.loaded_segments (0x2de90 : word) = Some W_2de38.
Proof. vm_refl. Qed.
Lemma D_2de38 : decode_any W_2de38 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de3c : bv 32 := 0x00334313.
Lemma F_2de3c : fetch_word Plain.M.loaded_segments (0x2de94 : word) = Some W_2de3c.
Proof. vm_refl. Qed.
Lemma D_2de3c : decode_any W_2de3c = Some (OpImm ALU_XOR 6 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de40 : bv 32 := 0x00530023.
Lemma F_2de40 : fetch_word Plain.M.loaded_segments (0x2de98 : word) = Some W_2de40.
Proof. vm_refl. Qed.
Lemma D_2de40 : decode_any W_2de40 = Some (Store SZ1 6 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de44 : bv 32 := 0x00188893.
Lemma F_2de44 : fetch_word Plain.M.loaded_segments (0x2de9c : word) = Some W_2de44.
Proof. vm_refl. Qed.
Lemma D_2de44 : decode_any W_2de44 = Some (OpImm ALU_ADD 17 17 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de48 : bv 32 := 0xfb6702e3.
Lemma F_2de48 : fetch_word Plain.M.loaded_segments (0x2dea0 : word) = Some W_2de48.
Proof. vm_refl. Qed.
Lemma D_2de48 : decode_any W_2de48 = Some (Branch BC_EQ 14 22 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de4c : bv 32 := 0xfc0ccee3.
Lemma F_2de4c : fetch_word Plain.M.loaded_segments (0x2dea4 : word) = Some W_2de4c.
Proof. vm_refl. Qed.
Lemma D_2de4c : decode_any W_2de4c = Some (Branch BC_LT 25 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de50 : bv 32 := 0x000a0293.
Lemma F_2de50 : fetch_word Plain.M.loaded_segments (0x2dea8 : word) = Some W_2de50.
Proof. vm_refl. Qed.
Lemma D_2de50 : decode_any W_2de50 = Some (OpImm ALU_ADD 5 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de54 : bv 32 := 0x00090313.
Lemma F_2de54 : fetch_word Plain.M.loaded_segments (0x2deac : word) = Some W_2de54.
Proof. vm_refl. Qed.
Lemma D_2de54 : decode_any W_2de54 = Some (OpImm ALU_ADD 6 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de58 : bv 32 := 0x00088393.
Lemma F_2de58 : fetch_word Plain.M.loaded_segments (0x2deb0 : word) = Some W_2de58.
Proof. vm_refl. Qed.
Lemma D_2de58 : decode_any W_2de58 = Some (OpImm ALU_ADD 7 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de5c : bv 32 := 0x208407d3.
Lemma F_2de5c : fetch_word Plain.M.loaded_segments (0x2deb4 : word) = Some W_2de5c.
Proof. vm_refl. Qed.
Lemma D_2de5c : decode_any W_2de5c = Some (Fsgnj F_SGNJ FMT_S 15 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de60 : bv 32 := 0x20840753.
Lemma F_2de60 : fetch_word Plain.M.loaded_segments (0x2deb8 : word) = Some W_2de60.
Proof. vm_refl. Qed.
Lemma D_2de60 : decode_any W_2de60 = Some (Fsgnj F_SGNJ FMT_S 14 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de64 : bv 32 := 0x0033ce13.
Lemma F_2de64 : fetch_word Plain.M.loaded_segments (0x2debc : word) = Some W_2de64.
Proof. vm_refl. Qed.
Lemma D_2de64 : decode_any W_2de64 = Some (OpImm ALU_XOR 28 7 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de68 : bv 32 := 0x41f35e9b.
Lemma F_2de68 : fetch_word Plain.M.loaded_segments (0x2dec0 : word) = Some W_2de68.
Proof. vm_refl. Qed.
Lemma D_2de68 : decode_any W_2de68 = Some (ShiftImm32 ALU_SRA 29 6 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de6c : bv 32 := 0x000e4e03.
Lemma F_2de6c : fetch_word Plain.M.loaded_segments (0x2dec4 : word) = Some W_2de6c.
Proof. vm_refl. Qed.
Lemma D_2de6c : decode_any W_2de6c = Some (Load SZ1 false 28 28 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de70 : bv 32 := 0x01d34f33.
Lemma F_2de70 : fetch_word Plain.M.loaded_segments (0x2dec8 : word) = Some W_2de70.
Proof. vm_refl. Qed.
Lemma D_2de70 : decode_any W_2de70 = Some (Op ALU_XOR 30 6 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de74 : bv 32 := 0x41df0ebb.
Lemma F_2de74 : fetch_word Plain.M.loaded_segments (0x2decc : word) = Some W_2de74.
Proof. vm_refl. Qed.
Lemma D_2de74 : decode_any W_2de74 = Some (Op32 ALU_SUB 29 30 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de78 : bv 32 := 0x002e9e93.
Lemma F_2de78 : fetch_word Plain.M.loaded_segments (0x2ded0 : word) = Some W_2de78.
Proof. vm_refl. Qed.
Lemma D_2de78 : decode_any W_2de78 = Some (ShiftImm ALU_SLL 29 29 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de7c : bv 32 := 0x01db8eb3.
Lemma F_2de7c : fetch_word Plain.M.loaded_segments (0x2ded4 : word) = Some W_2de7c.
Proof. vm_refl. Qed.
Lemma D_2de7c : decode_any W_2de7c = Some (Op ALU_ADD 29 23 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de80 : bv 32 := 0x0ffe7e13.
Lemma F_2de80 : fetch_word Plain.M.loaded_segments (0x2ded8 : word) = Some W_2de80.
Proof. vm_refl. Qed.
Lemma D_2de80 : decode_any W_2de80 = Some (OpImm ALU_AND 28 28 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de84 : bv 32 := 0x000ea687.
Lemma F_2de84 : fetch_word Plain.M.loaded_segments (0x2dedc : word) = Some W_2de84.
Proof. vm_refl. Qed.
Lemma D_2de84 : decode_any W_2de84 = Some (FLoad FMT_S 13 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de88 : bv 32 := 0x41cd0ebb.
Lemma F_2de88 : fetch_word Plain.M.loaded_segments (0x2dee0 : word) = Some W_2de88.
Proof. vm_refl. Qed.
Lemma D_2de88 : decode_any W_2de88 = Some (Op32 ALU_SUB 29 26 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de8c : bv 32 := 0x41fedf1b.
Lemma F_2de8c : fetch_word Plain.M.loaded_segments (0x2dee4 : word) = Some W_2de8c.
Proof. vm_refl. Qed.
Lemma D_2de8c : decode_any W_2de8c = Some (ShiftImm32 ALU_SRA 30 29 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de90 : bv 32 := 0x01eeceb3.
Lemma F_2de90 : fetch_word Plain.M.loaded_segments (0x2dee8 : word) = Some W_2de90.
Proof. vm_refl. Qed.
Lemma D_2de90 : decode_any W_2de90 = Some (Op ALU_XOR 29 29 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de94 : bv 32 := 0x41ee8ebb.
Lemma F_2de94 : fetch_word Plain.M.loaded_segments (0x2deec : word) = Some W_2de94.
Proof. vm_refl. Qed.
Lemma D_2de94 : decode_any W_2de94 = Some (Op32 ALU_SUB 29 29 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de98 : bv 32 := 0x002e9e93.
Lemma F_2de98 : fetch_word Plain.M.loaded_segments (0x2def0 : word) = Some W_2de98.
Proof. vm_refl. Qed.
Lemma D_2de98 : decode_any W_2de98 = Some (ShiftImm ALU_SLL 29 29 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2de9c : bv 32 := 0x01dc0eb3.
Lemma F_2de9c : fetch_word Plain.M.loaded_segments (0x2def4 : word) = Some W_2de9c.
Proof. vm_refl. Qed.
Lemma D_2de9c : decode_any W_2de9c = Some (Op ALU_ADD 29 24 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dea0 : bv 32 := 0x000ea607.
Lemma F_2dea0 : fetch_word Plain.M.loaded_segments (0x2def8 : word) = Some W_2dea0.
Proof. vm_refl. Qed.
Lemma D_2dea0 : decode_any W_2dea0 = Some (FLoad FMT_S 12 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dea4 : bv 32 := 0x00c383b3.
Lemma F_2dea4 : fetch_word Plain.M.loaded_segments (0x2defc : word) = Some W_2dea4.
Proof. vm_refl. Qed.
Lemma D_2dea4 : decode_any W_2dea4 = Some (Op ALU_ADD 7 7 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dea8 : bv 32 := 0xfff2829b.
Lemma F_2dea8 : fetch_word Plain.M.loaded_segments (0x2df00 : word) = Some W_2dea8.
Proof. vm_refl. Qed.
Lemma D_2dea8 : decode_any W_2dea8 = Some (OpImm32 5 5 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2deac : bv 32 := 0x10c6f6d3.
Lemma F_2deac : fetch_word Plain.M.loaded_segments (0x2df04 : word) = Some W_2deac.
Proof. vm_refl. Qed.
Lemma D_2deac : decode_any W_2deac = Some (Fari F_MUL FMT_S 13 13 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2deb0 : bv 32 := 0xd01e7653.
Lemma F_2deb0 : fetch_word Plain.M.loaded_segments (0x2df08 : word) = Some W_2deb0.
Proof. vm_refl. Qed.
Lemma D_2deb0 : decode_any W_2deb0 = Some (Fcvt FC_S FC_WU 12 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2deb4 : bv 32 := 0x78c6f7c3.
Lemma F_2deb4 : fetch_word Plain.M.loaded_segments (0x2df0c : word) = Some W_2deb4.
Proof. vm_refl. Qed.
Lemma D_2deb4 : decode_any W_2deb4 = Some (Fma F_MADD FMT_S 15 13 12 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2deb8 : bv 32 := 0x00d77753.
Lemma F_2deb8 : fetch_word Plain.M.loaded_segments (0x2df10 : word) = Some W_2deb8.
Proof. vm_refl. Qed.
Lemma D_2deb8 : decode_any W_2deb8 = Some (Fari F_ADD FMT_S 14 14 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2debc : bv 32 := 0x00130313.
Lemma F_2debc : fetch_word Plain.M.loaded_segments (0x2df14 : word) = Some W_2debc.
Proof. vm_refl. Qed.
Lemma D_2debc : decode_any W_2debc = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dec0 : bv 32 := 0xfa0292e3.
Lemma F_2dec0 : fetch_word Plain.M.loaded_segments (0x2df18 : word) = Some W_2dec0.
Proof. vm_refl. Qed.
Lemma D_2dec0 : decode_any W_2dec0 = Some (Branch BC_NE 5 0 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dec4 : bv 32 := 0xa0e412d3.
Lemma F_2dec4 : fetch_word Plain.M.loaded_segments (0x2df1c : word) = Some W_2dec4.
Proof. vm_refl. Qed.
Lemma D_2dec4 : decode_any W_2dec4 = Some (Fcmp F_LT FMT_S 5 8 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dec8 : bv 32 := 0xf60280e3.
Lemma F_2dec8 : fetch_word Plain.M.loaded_segments (0x2df20 : word) = Some W_2dec8.
Proof. vm_refl. Qed.
Lemma D_2dec8 : decode_any W_2dec8 = Some (Branch BC_EQ 5 0 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2decc : bv 32 := 0x8a84b687.
Lemma F_2decc : fetch_word Plain.M.loaded_segments (0x2df24 : word) = Some W_2decc.
Proof. vm_refl. Qed.
Lemma D_2decc : decode_any W_2decc = Some (FLoad FMT_D 13 9 2216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ded0 : bv 32 := 0x18e7f7d3.
Lemma F_2ded0 : fetch_word Plain.M.loaded_segments (0x2df28 : word) = Some W_2ded0.
Proof. vm_refl. Qed.
Lemma D_2ded0 : decode_any W_2ded0 = Some (Fari F_DIV FMT_S 15 15 14 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ded4 : bv 32 := 0x420787d3.
Lemma F_2ded4 : fetch_word Plain.M.loaded_segments (0x2df2c : word) = Some W_2ded4.
Proof. vm_refl. Qed.
Lemma D_2ded4 : decode_any W_2ded4 = Some (Fcvt FC_D FC_S 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ded8 : bv 32 := 0x02d7f7d3.
Lemma F_2ded8 : fetch_word Plain.M.loaded_segments (0x2df30 : word) = Some W_2ded8.
Proof. vm_refl. Qed.
Lemma D_2ded8 : decode_any W_2ded8 = Some (Fari F_ADD FMT_D 15 15 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dedc : bv 32 := 0xc20792d3.
Lemma F_2dedc : fetch_word Plain.M.loaded_segments (0x2df34 : word) = Some W_2dedc.
Proof. vm_refl. Qed.
Lemma D_2dedc : decode_any W_2dedc = Some (Fcvt FC_W FC_D 5 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2dee0 : bv 32 := 0xf55ff06f.
Lemma F_2dee0 : fetch_word Plain.M.loaded_segments (0x2df38 : word) = Some W_2dee0.
Proof. vm_refl. Qed.
Lemma D_2dee0 : decode_any W_2dee0 = Some (Jal 0 2096980, 4%Z).
Proof. vm_refl. Qed.

