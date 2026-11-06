(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation ASEGS_I := ImgA.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_75a2c : bv 32 := 0x000b4697.
Lemma F_75a2c : fetch_word ASEGS_I (0x75a2c : word) = Some W_75a2c.
Proof. vm_refl. Qed.
Lemma D_75a2c : decode_any W_75a2c = Some (Auipc 13 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a30 : bv 32 := 0x47c6b683.
Lemma F_75a30 : fetch_word ASEGS_I (0x75a30 : word) = Some W_75a30.
Proof. vm_refl. Qed.
Lemma D_75a30 : decode_any W_75a30 = Some (Load SZ8 true 13 13 1148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a34 : bv 32 := 0x0006b703.
Lemma F_75a34 : fetch_word ASEGS_I (0x75a34 : word) = Some W_75a34.
Proof. vm_refl. Qed.
Lemma D_75a34 : decode_any W_75a34 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a38 : bv 32 := 0xfff98993.
Lemma F_75a38 : fetch_word ASEGS_I (0x75a38 : word) = Some W_75a38.
Proof. vm_refl. Qed.
Lemma D_75a38 : decode_any W_75a38 = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a3c : bv 32 := 0x0035d693.
Lemma F_75a3c : fetch_word ASEGS_I (0x75a3c : word) = Some W_75a3c.
Proof. vm_refl. Qed.
Lemma D_75a3c : decode_any W_75a3c = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a40 : bv 32 := 0x0039d793.
Lemma F_75a40 : fetch_word ASEGS_I (0x75a40 : word) = Some W_75a40.
Proof. vm_refl. Qed.
Lemma D_75a40 : decode_any W_75a40 = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a44 : bv 32 := 0x00d706b3.
Lemma F_75a44 : fetch_word ASEGS_I (0x75a44 : word) = Some W_75a44.
Proof. vm_refl. Qed.
Lemma D_75a44 : decode_any W_75a44 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a48 : bv 32 := 0x00f70733.
Lemma F_75a48 : fetch_word ASEGS_I (0x75a48 : word) = Some W_75a48.
Proof. vm_refl. Qed.
Lemma D_75a48 : decode_any W_75a48 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a4c : bv 32 := 0xff86f793.
Lemma F_75a4c : fetch_word ASEGS_I (0x75a4c : word) = Some W_75a4c.
Proof. vm_refl. Qed.
Lemma D_75a4c : decode_any W_75a4c = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a50 : bv 32 := 0xff877813.
Lemma F_75a50 : fetch_word ASEGS_I (0x75a50 : word) = Some W_75a50.
Proof. vm_refl. Qed.
Lemma D_75a50 : decode_any W_75a50 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a54 : bv 32 := 0x0007b783.
Lemma F_75a54 : fetch_word ASEGS_I (0x75a54 : word) = Some W_75a54.
Proof. vm_refl. Qed.
Lemma D_75a54 : decode_any W_75a54 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a58 : bv 32 := 0x00083803.
Lemma F_75a58 : fetch_word ASEGS_I (0x75a58 : word) = Some W_75a58.
Proof. vm_refl. Qed.
Lemma D_75a58 : decode_any W_75a58 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a5c : bv 32 := 0x00f867b3.
Lemma F_75a5c : fetch_word ASEGS_I (0x75a5c : word) = Some W_75a5c.
Proof. vm_refl. Qed.
Lemma D_75a5c : decode_any W_75a5c = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a60 : bv 32 := 0x2a079e63.
Lemma F_75a60 : fetch_word ASEGS_I (0x75a60 : word) = Some W_75a60.
Proof. vm_refl. Qed.
Lemma D_75a60 : decode_any W_75a60 = Some (Branch BC_NE 15 0 700, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a64 : bv 32 := 0xfff54693.
Lemma F_75a64 : fetch_word ASEGS_I (0x75a64 : word) = Some W_75a64.
Proof. vm_refl. Qed.
Lemma D_75a64 : decode_any W_75a64 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a74 : bv 32 := 0x000b4697.
Lemma F_75a74 : fetch_word ASEGS_I (0x75a74 : word) = Some W_75a74.
Proof. vm_refl. Qed.
Lemma D_75a74 : decode_any W_75a74 = Some (Auipc 13 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a78 : bv 32 := 0x4346b683.
Lemma F_75a78 : fetch_word ASEGS_I (0x75a78 : word) = Some W_75a78.
Proof. vm_refl. Qed.
Lemma D_75a78 : decode_any W_75a78 = Some (Load SZ8 true 13 13 1076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a7c : bv 32 := 0x0006b703.
Lemma F_75a7c : fetch_word ASEGS_I (0x75a7c : word) = Some W_75a7c.
Proof. vm_refl. Qed.
Lemma D_75a7c : decode_any W_75a7c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a80 : bv 32 := 0xfffa0a13.
Lemma F_75a80 : fetch_word ASEGS_I (0x75a80 : word) = Some W_75a80.
Proof. vm_refl. Qed.
Lemma D_75a80 : decode_any W_75a80 = Some (OpImm ALU_ADD 20 20 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a84 : bv 32 := 0x00355693.
Lemma F_75a84 : fetch_word ASEGS_I (0x75a84 : word) = Some W_75a84.
Proof. vm_refl. Qed.
Lemma D_75a84 : decode_any W_75a84 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a88 : bv 32 := 0x003a5793.
Lemma F_75a88 : fetch_word ASEGS_I (0x75a88 : word) = Some W_75a88.
Proof. vm_refl. Qed.
Lemma D_75a88 : decode_any W_75a88 = Some (ShiftImm ALU_SRL 15 20 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a8c : bv 32 := 0x00d706b3.
Lemma F_75a8c : fetch_word ASEGS_I (0x75a8c : word) = Some W_75a8c.
Proof. vm_refl. Qed.
Lemma D_75a8c : decode_any W_75a8c = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a90 : bv 32 := 0x00f70733.
Lemma F_75a90 : fetch_word ASEGS_I (0x75a90 : word) = Some W_75a90.
Proof. vm_refl. Qed.
Lemma D_75a90 : decode_any W_75a90 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a94 : bv 32 := 0xff86f793.
Lemma F_75a94 : fetch_word ASEGS_I (0x75a94 : word) = Some W_75a94.
Proof. vm_refl. Qed.
Lemma D_75a94 : decode_any W_75a94 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a98 : bv 32 := 0xff877813.
Lemma F_75a98 : fetch_word ASEGS_I (0x75a98 : word) = Some W_75a98.
Proof. vm_refl. Qed.
Lemma D_75a98 : decode_any W_75a98 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75a9c : bv 32 := 0x0007b783.
Lemma F_75a9c : fetch_word ASEGS_I (0x75a9c : word) = Some W_75a9c.
Proof. vm_refl. Qed.
Lemma D_75a9c : decode_any W_75a9c = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75aa0 : bv 32 := 0x00083803.
Lemma F_75aa0 : fetch_word ASEGS_I (0x75aa0 : word) = Some W_75aa0.
Proof. vm_refl. Qed.
Lemma D_75aa0 : decode_any W_75aa0 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75aa4 : bv 32 := 0x00f867b3.
Lemma F_75aa4 : fetch_word ASEGS_I (0x75aa4 : word) = Some W_75aa4.
Proof. vm_refl. Qed.
Lemma D_75aa4 : decode_any W_75aa4 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75aa8 : bv 32 := 0x36079a63.
Lemma F_75aa8 : fetch_word ASEGS_I (0x75aa8 : word) = Some W_75aa8.
Proof. vm_refl. Qed.
Lemma D_75aa8 : decode_any W_75aa8 = Some (Branch BC_NE 15 0 884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75aac : bv 32 := 0x000b6697.
Lemma F_75aac : fetch_word ASEGS_I (0x75aac : word) = Some W_75aac.
Proof. vm_refl. Qed.
Lemma D_75aac : decode_any W_75aac = Some (Auipc 13 182, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d1c : bv 32 := 0x00070783.
Lemma F_75d1c : fetch_word ASEGS_I (0x75d1c : word) = Some W_75d1c.
Proof. vm_refl. Qed.
Lemma D_75d1c : decode_any W_75d1c = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d20 : bv 32 := 0x0079f813.
Lemma F_75d20 : fetch_word ASEGS_I (0x75d20 : word) = Some W_75d20.
Proof. vm_refl. Qed.
Lemma D_75d20 : decode_any W_75d20 = Some (OpImm ALU_AND 16 19 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d24 : bv 32 := 0x00f038b3.
Lemma F_75d24 : fetch_word ASEGS_I (0x75d24 : word) = Some W_75d24.
Proof. vm_refl. Qed.
Lemma D_75d24 : decode_any W_75d24 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d28 : bv 32 := 0x00f827b3.
Lemma F_75d28 : fetch_word ASEGS_I (0x75d28 : word) = Some W_75d28.
Proof. vm_refl. Qed.
Lemma D_75d28 : decode_any W_75d28 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d2c : bv 32 := 0x0017c793.
Lemma F_75d2c : fetch_word ASEGS_I (0x75d2c : word) = Some W_75d2c.
Proof. vm_refl. Qed.
Lemma D_75d2c : decode_any W_75d2c = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d30 : bv 32 := 0x00f8f7b3.
Lemma F_75d30 : fetch_word ASEGS_I (0x75d30 : word) = Some W_75d30.
Proof. vm_refl. Qed.
Lemma D_75d30 : decode_any W_75d30 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d34 : bv 32 := 0x00e6fa63.
Lemma F_75d34 : fetch_word ASEGS_I (0x75d34 : word) = Some W_75d34.
Proof. vm_refl. Qed.
Lemma D_75d34 : decode_any W_75d34 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d38 : bv 32 := 0x0006c803.
Lemma F_75d38 : fetch_word ASEGS_I (0x75d38 : word) = Some W_75d38.
Proof. vm_refl. Qed.
Lemma D_75d38 : decode_any W_75d38 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d3c : bv 32 := 0x00168693.
Lemma F_75d3c : fetch_word ASEGS_I (0x75d3c : word) = Some W_75d3c.
Proof. vm_refl. Qed.
Lemma D_75d3c : decode_any W_75d3c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d40 : bv 32 := 0x00f867b3.
Lemma F_75d40 : fetch_word ASEGS_I (0x75d40 : word) = Some W_75d40.
Proof. vm_refl. Qed.
Lemma D_75d40 : decode_any W_75d40 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d44 : bv 32 := 0xfee69ae3.
Lemma F_75d44 : fetch_word ASEGS_I (0x75d44 : word) = Some W_75d44.
Proof. vm_refl. Qed.
Lemma D_75d44 : decode_any W_75d44 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d48 : bv 32 := 0x0ff7f693.
Lemma F_75d48 : fetch_word ASEGS_I (0x75d48 : word) = Some W_75d48.
Proof. vm_refl. Qed.
Lemma D_75d48 : decode_any W_75d48 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75d4c : bv 32 := 0xd0068ce3.
Lemma F_75d4c : fetch_word ASEGS_I (0x75d4c : word) = Some W_75d4c.
Proof. vm_refl. Qed.
Lemma D_75d4c : decode_any W_75d4c = Some (Branch BC_EQ 13 0 7448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e1c : bv 32 := 0x00070783.
Lemma F_75e1c : fetch_word ASEGS_I (0x75e1c : word) = Some W_75e1c.
Proof. vm_refl. Qed.
Lemma D_75e1c : decode_any W_75e1c = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e20 : bv 32 := 0x007a7813.
Lemma F_75e20 : fetch_word ASEGS_I (0x75e20 : word) = Some W_75e20.
Proof. vm_refl. Qed.
Lemma D_75e20 : decode_any W_75e20 = Some (OpImm ALU_AND 16 20 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e24 : bv 32 := 0x00f038b3.
Lemma F_75e24 : fetch_word ASEGS_I (0x75e24 : word) = Some W_75e24.
Proof. vm_refl. Qed.
Lemma D_75e24 : decode_any W_75e24 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e28 : bv 32 := 0x00f827b3.
Lemma F_75e28 : fetch_word ASEGS_I (0x75e28 : word) = Some W_75e28.
Proof. vm_refl. Qed.
Lemma D_75e28 : decode_any W_75e28 = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e2c : bv 32 := 0x0017c793.
Lemma F_75e2c : fetch_word ASEGS_I (0x75e2c : word) = Some W_75e2c.
Proof. vm_refl. Qed.
Lemma D_75e2c : decode_any W_75e2c = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e30 : bv 32 := 0x00f8f7b3.
Lemma F_75e30 : fetch_word ASEGS_I (0x75e30 : word) = Some W_75e30.
Proof. vm_refl. Qed.
Lemma D_75e30 : decode_any W_75e30 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e34 : bv 32 := 0x00e6fa63.
Lemma F_75e34 : fetch_word ASEGS_I (0x75e34 : word) = Some W_75e34.
Proof. vm_refl. Qed.
Lemma D_75e34 : decode_any W_75e34 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e38 : bv 32 := 0x0006c803.
Lemma F_75e38 : fetch_word ASEGS_I (0x75e38 : word) = Some W_75e38.
Proof. vm_refl. Qed.
Lemma D_75e38 : decode_any W_75e38 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e3c : bv 32 := 0x00168693.
Lemma F_75e3c : fetch_word ASEGS_I (0x75e3c : word) = Some W_75e3c.
Proof. vm_refl. Qed.
Lemma D_75e3c : decode_any W_75e3c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e40 : bv 32 := 0x00f867b3.
Lemma F_75e40 : fetch_word ASEGS_I (0x75e40 : word) = Some W_75e40.
Proof. vm_refl. Qed.
Lemma D_75e40 : decode_any W_75e40 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e44 : bv 32 := 0xfee69ae3.
Lemma F_75e44 : fetch_word ASEGS_I (0x75e44 : word) = Some W_75e44.
Proof. vm_refl. Qed.
Lemma D_75e44 : decode_any W_75e44 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e48 : bv 32 := 0x0ff7f693.
Lemma F_75e48 : fetch_word ASEGS_I (0x75e48 : word) = Some W_75e48.
Proof. vm_refl. Qed.
Lemma D_75e48 : decode_any W_75e48 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e4c : bv 32 := 0xc60680e3.
Lemma F_75e4c : fetch_word ASEGS_I (0x75e4c : word) = Some W_75e4c.
Proof. vm_refl. Qed.
Lemma D_75e4c : decode_any W_75e4c = Some (Branch BC_EQ 13 0 7264, 4%Z).
Proof. vm_refl. Qed.
