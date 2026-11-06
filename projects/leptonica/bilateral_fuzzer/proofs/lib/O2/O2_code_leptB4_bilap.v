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
Definition W_2e094 : bv 32 := 0xfffe4617.
Lemma F_2e094 : fetch_word Plain.M.loaded_segments (0x2e0ec : word) = Some W_2e094.
Proof. vm_refl. Qed.
Lemma D_2e094 : decode_any W_2e094 = Some (Auipc 12 1048548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e098 : bv 32 := 0x47c63787.
Lemma F_2e098 : fetch_word Plain.M.loaded_segments (0x2e0f0 : word) = Some W_2e098.
Proof. vm_refl. Qed.
Lemma D_2e098 : decode_any W_2e098 = Some (FLoad FMT_D 15 12 1148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e09c : bv 32 := 0xfffe4617.
Lemma F_2e09c : fetch_word Plain.M.loaded_segments (0x2e0f4 : word) = Some W_2e09c.
Proof. vm_refl. Qed.
Lemma D_2e09c : decode_any W_2e09c = Some (Auipc 12 1048548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0a0 : bv 32 := 0x49463707.
Lemma F_2e0a0 : fetch_word Plain.M.loaded_segments (0x2e0f8 : word) = Some W_2e0a0.
Proof. vm_refl. Qed.
Lemma D_2e0a0 : decode_any W_2e0a0 = Some (FLoad FMT_D 14 12 1172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0a4 : bv 32 := 0x00412803.
Lemma F_2e0a4 : fetch_word Plain.M.loaded_segments (0x2e0fc : word) = Some W_2e0a4.
Proof. vm_refl. Qed.
Lemma D_2e0a4 : decode_any W_2e0a4 = Some (Load SZ4 true 16 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0a8 : bv 32 := 0x002a9a93.
Lemma F_2e0a8 : fetch_word Plain.M.loaded_segments (0x2e100 : word) = Some W_2e0a8.
Proof. vm_refl. Qed.
Lemma D_2e0a8 : decode_any W_2e0a8 = Some (ShiftImm ALU_SLL 21 21 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0ac : bv 32 := 0x002a1a13.
Lemma F_2e0ac : fetch_word Plain.M.loaded_segments (0x2e104 : word) = Some W_2e0ac.
Proof. vm_refl. Qed.
Lemma D_2e0ac : decode_any W_2e0ac = Some (ShiftImm ALU_SLL 20 20 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0b0 : bv 32 := 0x0180006f.
Lemma F_2e0b0 : fetch_word Plain.M.loaded_segments (0x2e108 : word) = Some W_2e0b0.
Proof. vm_refl. Qed.
Lemma D_2e0b0 : decode_any W_2e0b0 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0b4 : bv 32 := 0x00012583.
Lemma F_2e0b4 : fetch_word Plain.M.loaded_segments (0x2e10c : word) = Some W_2e0b4.
Proof. vm_refl. Qed.
Lemma D_2e0b4 : decode_any W_2e0b4 = Some (Load SZ4 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0b8 : bv 32 := 0x00150513.
Lemma F_2e0b8 : fetch_word Plain.M.loaded_segments (0x2e110 : word) = Some W_2e0b8.
Proof. vm_refl. Qed.
Lemma D_2e0b8 : decode_any W_2e0b8 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0bc : bv 32 := 0x01590933.
Lemma F_2e0bc : fetch_word Plain.M.loaded_segments (0x2e114 : word) = Some W_2e0bc.
Proof. vm_refl. Qed.
Lemma D_2e0bc : decode_any W_2e0bc = Some (Op ALU_ADD 18 18 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0c0 : bv 32 := 0x014484b3.
Lemma F_2e0c0 : fetch_word Plain.M.loaded_segments (0x2e118 : word) = Some W_2e0c0.
Proof. vm_refl. Qed.
Lemma D_2e0c0 : decode_any W_2e0c0 = Some (Op ALU_ADD 9 9 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0c4 : bv 32 := 0x14b55063.
Lemma F_2e0c4 : fetch_word Plain.M.loaded_segments (0x2e11c : word) = Some W_2e0c4.
Proof. vm_refl. Qed.
Lemma D_2e0c4 : decode_any W_2e0c4 = Some (Branch BC_GE 10 11 320, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0c8 : bv 32 := 0xff0058e3.
Lemma F_2e0c8 : fetch_word Plain.M.loaded_segments (0x2e120 : word) = Some W_2e0c8.
Proof. vm_refl. Qed.
Lemma D_2e0c8 : decode_any W_2e0c8 = Some (Branch BC_GE 0 16 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0cc : bv 32 := 0x00000593.
Lemma F_2e0cc : fetch_word Plain.M.loaded_segments (0x2e124 : word) = Some W_2e0cc.
Proof. vm_refl. Qed.
Lemma D_2e0cc : decode_any W_2e0cc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0d0 : bv 32 := 0x00000613.
Lemma F_2e0d0 : fetch_word Plain.M.loaded_segments (0x2e128 : word) = Some W_2e0d0.
Proof. vm_refl. Qed.
Lemma D_2e0d0 : decode_any W_2e0d0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0d4 : bv 32 := 0x036546bb.
Lemma F_2e0d4 : fetch_word Plain.M.loaded_segments (0x2e12c : word) = Some W_2e0d4.
Proof. vm_refl. Qed.
Lemma D_2e0d4 : decode_any W_2e0d4 = Some (Mul32 M_DIV 13 10 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0d8 : bv 32 := 0x00369693.
Lemma F_2e0d8 : fetch_word Plain.M.loaded_segments (0x2e130 : word) = Some W_2e0d8.
Proof. vm_refl. Qed.
Lemma D_2e0d8 : decode_any W_2e0d8 = Some (ShiftImm ALU_SLL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0dc : bv 32 := 0x00048713.
Lemma F_2e0dc : fetch_word Plain.M.loaded_segments (0x2e134 : word) = Some W_2e0dc.
Proof. vm_refl. Qed.
Lemma D_2e0dc : decode_any W_2e0dc = Some (OpImm ALU_ADD 14 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0e0 : bv 32 := 0x00090793.
Lemma F_2e0e0 : fetch_word Plain.M.loaded_segments (0x2e138 : word) = Some W_2e0e0.
Proof. vm_refl. Qed.
Lemma D_2e0e0 : decode_any W_2e0e0 = Some (OpImm ALU_ADD 15 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0e4 : bv 32 := 0x00374813.
Lemma F_2e0e4 : fetch_word Plain.M.loaded_segments (0x2e13c : word) = Some W_2e0e4.
Proof. vm_refl. Qed.
Lemma D_2e0e4 : decode_any W_2e0e4 = Some (OpImm ALU_XOR 16 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0e8 : bv 32 := 0x00084803.
Lemma F_2e0e8 : fetch_word Plain.M.loaded_segments (0x2e140 : word) = Some W_2e0e8.
Proof. vm_refl. Qed.
Lemma D_2e0e8 : decode_any W_2e0e8 = Some (Load SZ1 false 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0ec : bv 32 := 0x00281813.
Lemma F_2e0ec : fetch_word Plain.M.loaded_segments (0x2e144 : word) = Some W_2e0ec.
Proof. vm_refl. Qed.
Lemma D_2e0ec : decode_any W_2e0ec = Some (ShiftImm ALU_SLL 16 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0f0 : bv 32 := 0x010b88b3.
Lemma F_2e0f0 : fetch_word Plain.M.loaded_segments (0x2e148 : word) = Some W_2e0f0.
Proof. vm_refl. Qed.
Lemma D_2e0f0 : decode_any W_2e0f0 = Some (Op ALU_ADD 17 23 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0f4 : bv 32 := 0x0008a883.
Lemma F_2e0f4 : fetch_word Plain.M.loaded_segments (0x2e14c : word) = Some W_2e0f4.
Proof. vm_refl. Qed.
Lemma D_2e0f4 : decode_any W_2e0f4 = Some (Load SZ4 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0f8 : bv 32 := 0x00389893.
Lemma F_2e0f8 : fetch_word Plain.M.loaded_segments (0x2e150 : word) = Some W_2e0f8.
Proof. vm_refl. Qed.
Lemma D_2e0f8 : decode_any W_2e0f8 = Some (ShiftImm ALU_SLL 17 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e0fc : bv 32 := 0x011c88b3.
Lemma F_2e0fc : fetch_word Plain.M.loaded_segments (0x2e154 : word) = Some W_2e0fc.
Proof. vm_refl. Qed.
Lemma D_2e0fc : decode_any W_2e0fc = Some (Op ALU_ADD 17 25 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e100 : bv 32 := 0x0008b283.
Lemma F_2e100 : fetch_word Plain.M.loaded_segments (0x2e158 : word) = Some W_2e100.
Proof. vm_refl. Qed.
Lemma D_2e100 : decode_any W_2e100 = Some (Load SZ8 true 5 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e104 : bv 32 := 0x0088b883.
Lemma F_2e104 : fetch_word Plain.M.loaded_segments (0x2e15c : word) = Some W_2e104.
Proof. vm_refl. Qed.
Lemma D_2e104 : decode_any W_2e104 = Some (Load SZ8 true 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e108 : bv 32 := 0x0365c33b.
Lemma F_2e108 : fetch_word Plain.M.loaded_segments (0x2e160 : word) = Some W_2e108.
Proof. vm_refl. Qed.
Lemma D_2e108 : decode_any W_2e108 = Some (Mul32 M_DIV 6 11 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e10c : bv 32 := 0x00d282b3.
Lemma F_2e10c : fetch_word Plain.M.loaded_segments (0x2e164 : word) = Some W_2e10c.
Proof. vm_refl. Qed.
Lemma D_2e10c : decode_any W_2e10c = Some (Op ALU_ADD 5 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e110 : bv 32 := 0x00d888b3.
Lemma F_2e110 : fetch_word Plain.M.loaded_segments (0x2e168 : word) = Some W_2e110.
Proof. vm_refl. Qed.
Lemma D_2e110 : decode_any W_2e110 = Some (Op ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e114 : bv 32 := 0x0002b283.
Lemma F_2e114 : fetch_word Plain.M.loaded_segments (0x2e16c : word) = Some W_2e114.
Proof. vm_refl. Qed.
Lemma D_2e114 : decode_any W_2e114 = Some (Load SZ8 true 5 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e118 : bv 32 := 0x0008b883.
Lemma F_2e118 : fetch_word Plain.M.loaded_segments (0x2e170 : word) = Some W_2e118.
Proof. vm_refl. Qed.
Lemma D_2e118 : decode_any W_2e118 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e11c : bv 32 := 0x010c0833.
Lemma F_2e11c : fetch_word Plain.M.loaded_segments (0x2e174 : word) = Some W_2e11c.
Proof. vm_refl. Qed.
Lemma D_2e11c : decode_any W_2e11c = Some (Op ALU_ADD 16 24 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e120 : bv 32 := 0x00082687.
Lemma F_2e120 : fetch_word Plain.M.loaded_segments (0x2e178 : word) = Some W_2e120.
Proof. vm_refl. Qed.
Lemma D_2e120 : decode_any W_2e120 = Some (FLoad FMT_S 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e124 : bv 32 := 0x006282b3.
Lemma F_2e124 : fetch_word Plain.M.loaded_segments (0x2e17c : word) = Some W_2e124.
Proof. vm_refl. Qed.
Lemma D_2e124 : decode_any W_2e124 = Some (Op ALU_ADD 5 5 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e128 : bv 32 := 0x006888b3.
Lemma F_2e128 : fetch_word Plain.M.loaded_segments (0x2e180 : word) = Some W_2e128.
Proof. vm_refl. Qed.
Lemma D_2e128 : decode_any W_2e128 = Some (Op ALU_ADD 17 17 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e12c : bv 32 := 0x0032c813.
Lemma F_2e12c : fetch_word Plain.M.loaded_segments (0x2e184 : word) = Some W_2e12c.
Proof. vm_refl. Qed.
Lemma D_2e12c : decode_any W_2e12c = Some (OpImm ALU_XOR 16 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e130 : bv 32 := 0x0038c893.
Lemma F_2e130 : fetch_word Plain.M.loaded_segments (0x2e188 : word) = Some W_2e130.
Proof. vm_refl. Qed.
Lemma D_2e130 : decode_any W_2e130 = Some (OpImm ALU_XOR 17 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e134 : bv 32 := 0x00084803.
Lemma F_2e134 : fetch_word Plain.M.loaded_segments (0x2e18c : word) = Some W_2e134.
Proof. vm_refl. Qed.
Lemma D_2e134 : decode_any W_2e134 = Some (Load SZ1 false 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e138 : bv 32 := 0x0008c883.
Lemma F_2e138 : fetch_word Plain.M.loaded_segments (0x2e190 : word) = Some W_2e138.
Proof. vm_refl. Qed.
Lemma D_2e138 : decode_any W_2e138 = Some (Load SZ1 false 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e13c : bv 32 := 0x42068653.
Lemma F_2e13c : fetch_word Plain.M.loaded_segments (0x2e194 : word) = Some W_2e13c.
Proof. vm_refl. Qed.
Lemma D_2e13c : decode_any W_2e13c = Some (Fcvt FC_D FC_S 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e140 : bv 32 := 0x0ac7f653.
Lemma F_2e140 : fetch_word Plain.M.loaded_segments (0x2e198 : word) = Some W_2e140.
Proof. vm_refl. Qed.
Lemma D_2e140 : decode_any W_2e140 = Some (Fari F_SUB FMT_D 12 15 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e144 : bv 32 := 0xd21805d3.
Lemma F_2e144 : fetch_word Plain.M.loaded_segments (0x2e19c : word) = Some W_2e144.
Proof. vm_refl. Qed.
Lemma D_2e144 : decode_any W_2e144 = Some (Fcvt FC_D FC_WU 11 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e148 : bv 32 := 0xd018f553.
Lemma F_2e148 : fetch_word Plain.M.loaded_segments (0x2e1a0 : word) = Some W_2e148.
Proof. vm_refl. Qed.
Lemma D_2e148 : decode_any W_2e148 = Some (Fcvt FC_S FC_WU 10 17 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e14c : bv 32 := 0x10a6f6d3.
Lemma F_2e14c : fetch_word Plain.M.loaded_segments (0x2e1a4 : word) = Some W_2e14c.
Proof. vm_refl. Qed.
Lemma D_2e14c : decode_any W_2e14c = Some (Fari F_MUL FMT_S 13 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e150 : bv 32 := 0x420686d3.
Lemma F_2e150 : fetch_word Plain.M.loaded_segments (0x2e1a8 : word) = Some W_2e150.
Proof. vm_refl. Qed.
Lemma D_2e150 : decode_any W_2e150 = Some (Fcvt FC_D FC_S 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e154 : bv 32 := 0x6ab676c3.
Lemma F_2e154 : fetch_word Plain.M.loaded_segments (0x2e1ac : word) = Some W_2e154.
Proof. vm_refl. Qed.
Lemma D_2e154 : decode_any W_2e154 = Some (Fma F_MADD FMT_D 13 12 11 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e158 : bv 32 := 0x02e6f6d3.
Lemma F_2e158 : fetch_word Plain.M.loaded_segments (0x2e1b0 : word) = Some W_2e158.
Proof. vm_refl. Qed.
Lemma D_2e158 : decode_any W_2e158 = Some (Fari F_ADD FMT_D 13 13 14 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e15c : bv 32 := 0xc2069853.
Lemma F_2e15c : fetch_word Plain.M.loaded_segments (0x2e1b4 : word) = Some W_2e15c.
Proof. vm_refl. Qed.
Lemma D_2e15c : decode_any W_2e15c = Some (Fcvt FC_W FC_D 16 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e160 : bv 32 := 0x0037c893.
Lemma F_2e160 : fetch_word Plain.M.loaded_segments (0x2e1b8 : word) = Some W_2e160.
Proof. vm_refl. Qed.
Lemma D_2e160 : decode_any W_2e160 = Some (OpImm ALU_XOR 17 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e164 : bv 32 := 0x01088023.
Lemma F_2e164 : fetch_word Plain.M.loaded_segments (0x2e1bc : word) = Some W_2e164.
Proof. vm_refl. Qed.
Lemma D_2e164 : decode_any W_2e164 = Some (Store SZ1 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e168 : bv 32 := 0x00412803.
Lemma F_2e168 : fetch_word Plain.M.loaded_segments (0x2e1c0 : word) = Some W_2e168.
Proof. vm_refl. Qed.
Lemma D_2e168 : decode_any W_2e168 = Some (Load SZ4 true 16 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e16c : bv 32 := 0x00160613.
Lemma F_2e16c : fetch_word Plain.M.loaded_segments (0x2e1c4 : word) = Some W_2e16c.
Proof. vm_refl. Qed.
Lemma D_2e16c : decode_any W_2e16c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e170 : bv 32 := 0x00158593.
Lemma F_2e170 : fetch_word Plain.M.loaded_segments (0x2e1c8 : word) = Some W_2e170.
Proof. vm_refl. Qed.
Lemma D_2e170 : decode_any W_2e170 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e174 : bv 32 := 0x00178793.
Lemma F_2e174 : fetch_word Plain.M.loaded_segments (0x2e1cc : word) = Some W_2e174.
Proof. vm_refl. Qed.
Lemma D_2e174 : decode_any W_2e174 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e178 : bv 32 := 0x00170713.
Lemma F_2e178 : fetch_word Plain.M.loaded_segments (0x2e1d0 : word) = Some W_2e178.
Proof. vm_refl. Qed.
Lemma D_2e178 : decode_any W_2e178 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e17c : bv 32 := 0xf70644e3.
Lemma F_2e17c : fetch_word Plain.M.loaded_segments (0x2e1d4 : word) = Some W_2e17c.
Proof. vm_refl. Qed.
Lemma D_2e17c : decode_any W_2e17c = Some (Branch BC_LT 12 16 8040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e180 : bv 32 := 0xf35ff06f.
Lemma F_2e180 : fetch_word Plain.M.loaded_segments (0x2e1d8 : word) = Some W_2e180.
Proof. vm_refl. Qed.
Lemma D_2e180 : decode_any W_2e180 = Some (Jal 0 2096948, 4%Z).
Proof. vm_refl. Qed.

