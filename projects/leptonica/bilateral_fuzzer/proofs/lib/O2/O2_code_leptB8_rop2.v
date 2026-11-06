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
Definition W_23d3c : bv 32 := 0x09813683.
Lemma F_23d3c : fetch_word Plain.M.loaded_segments (0x23d94 : word) = Some W_23d3c.
Proof. vm_refl. Qed.
Lemma D_23d3c : decode_any W_23d3c = Some (Load SZ8 true 13 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23d40 : bv 32 := 0x07813583.
Lemma F_23d40 : fetch_word Plain.M.loaded_segments (0x23d98 : word) = Some W_23d40.
Proof. vm_refl. Qed.
Lemma D_23d40 : decode_any W_23d40 = Some (Load SZ8 true 11 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23d44 : bv 32 := 0x08013b03.
Lemma F_23d44 : fetch_word Plain.M.loaded_segments (0x23d9c : word) = Some W_23d44.
Proof. vm_refl. Qed.
Lemma D_23d44 : decode_any W_23d44 = Some (Load SZ8 true 22 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23d48 : bv 32 := 0x01a9e7b3.
Lemma F_23d48 : fetch_word Plain.M.loaded_segments (0x23da0 : word) = Some W_23d48.
Proof. vm_refl. Qed.
Lemma D_23d48 : decode_any W_23d48 = Some (Op ALU_OR 15 19 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23d4c : bv 32 := 0x01f7f793.
Lemma F_23d4c : fetch_word Plain.M.loaded_segments (0x23da4 : word) = Some W_23d4c.
Proof. vm_refl. Qed.
Lemma D_23d4c : decode_any W_23d4c = Some (OpImm ALU_AND 15 15 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23d50 : bv 32 := 0xfff58a93.
Lemma F_23d50 : fetch_word Plain.M.loaded_segments (0x23da8 : word) = Some W_23d50.
Proof. vm_refl. Qed.
Lemma D_23d50 : decode_any W_23d50 = Some (OpImm ALU_ADD 21 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23d54 : bv 32 := 0x0a078463.
Lemma F_23d54 : fetch_word Plain.M.loaded_segments (0x23dac : word) = Some W_23d54.
Proof. vm_refl. Qed.
Lemma D_23d54 : decode_any W_23d54 = Some (Branch BC_EQ 15 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23d58 : bv 32 := 0x01f9fa13.
Lemma F_23d58 : fetch_word Plain.M.loaded_segments (0x23db0 : word) = Some W_23d58.
Proof. vm_refl. Qed.
Lemma D_23d58 : decode_any W_23d58 = Some (OpImm ALU_AND 20 19 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23d5c : bv 32 := 0x01fd7f13.
Lemma F_23d5c : fetch_word Plain.M.loaded_segments (0x23db4 : word) = Some W_23d5c.
Proof. vm_refl. Qed.
Lemma D_23d5c : decode_any W_23d5c = Some (OpImm ALU_AND 30 26 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23d60 : bv 32 := 0xfffed517.
Lemma F_23d60 : fetch_word Plain.M.loaded_segments (0x23db8 : word) = Some W_23d60.
Proof. vm_refl. Qed.
Lemma D_23d60 : decode_any W_23d60 = Some (Auipc 10 1048557, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23d64 : bv 32 := 0xa7150513.
Lemma F_23d64 : fetch_word Plain.M.loaded_segments (0x23dbc : word) = Some W_23d64.
Proof. vm_refl. Qed.
Lemma D_23d64 : decode_any W_23d64 = Some (OpImm ALU_ADD 10 10 2673, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23d68 : bv 32 := 0x0bea1a63.
Lemma F_23d68 : fetch_word Plain.M.loaded_segments (0x23dc0 : word) = Some W_23d68.
Proof. vm_refl. Qed.
Lemma D_23d68 : decode_any W_23d68 = Some (Branch BC_NE 20 30 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e1c : bv 32 := 0x001a3813.
Lemma F_23e1c : fetch_word Plain.M.loaded_segments (0x23e74 : word) = Some W_23e1c.
Proof. vm_refl. Qed.
Lemma D_23e1c : decode_any W_23e1c = Some (OpImm ALU_SLTU 16 20 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e20 : bv 32 := 0x02000393.
Lemma F_23e20 : fetch_word Plain.M.loaded_segments (0x23e78 : word) = Some W_23e20.
Proof. vm_refl. Qed.
Lemma D_23e20 : decode_any W_23e20 = Some (OpImm ALU_ADD 7 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e24 : bv 32 := 0x41438eb3.
Lemma F_23e24 : fetch_word Plain.M.loaded_segments (0x23e7c : word) = Some W_23e24.
Proof. vm_refl. Qed.
Lemma D_23e24 : decode_any W_23e24 = Some (Op ALU_SUB 29 7 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e28 : bv 32 := 0xfff80813.
Lemma F_23e28 : fetch_word Plain.M.loaded_segments (0x23e80 : word) = Some W_23e28.
Proof. vm_refl. Qed.
Lemma D_23e28 : decode_any W_23e28 = Some (OpImm ALU_ADD 16 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e2c : bv 32 := 0x01d87e33.
Lemma F_23e2c : fetch_word Plain.M.loaded_segments (0x23e84 : word) = Some W_23e2c.
Proof. vm_refl. Qed.
Lemma D_23e2c : decode_any W_23e2c = Some (Op ALU_AND 28 16 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e30 : bv 32 := 0x22078e63.
Lemma F_23e30 : fetch_word Plain.M.loaded_segments (0x23e88 : word) = Some W_23e30.
Proof. vm_refl. Qed.
Lemma D_23e30 : decode_any W_23e30 = Some (Branch BC_EQ 15 0 572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e34 : bv 32 := 0x41e38fb3.
Lemma F_23e34 : fetch_word Plain.M.loaded_segments (0x23e8c : word) = Some W_23e34.
Proof. vm_refl. Qed.
Lemma D_23e34 : decode_any W_23e34 = Some (Op ALU_SUB 31 7 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e38 : bv 32 := 0x001f3793.
Lemma F_23e38 : fetch_word Plain.M.loaded_segments (0x23e90 : word) = Some W_23e38.
Proof. vm_refl. Qed.
Lemma D_23e38 : decode_any W_23e38 = Some (OpImm ALU_SLTU 15 30 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e3c : bv 32 := 0x000e081b.
Lemma F_23e3c : fetch_word Plain.M.loaded_segments (0x23e94 : word) = Some W_23e3c.
Proof. vm_refl. Qed.
Lemma D_23e3c : decode_any W_23e3c = Some (OpImm32 16 28 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e40 : bv 32 := 0xfffef897.
Lemma F_23e40 : fetch_word Plain.M.loaded_segments (0x23e98 : word) = Some W_23e40.
Proof. vm_refl. Qed.
Lemma D_23e40 : decode_any W_23e40 = Some (Auipc 17 1048559, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e44 : bv 32 := 0xfff78793.
Lemma F_23e44 : fetch_word Plain.M.loaded_segments (0x23e9c : word) = Some W_23e44.
Proof. vm_refl. Qed.
Lemma D_23e44 : decode_any W_23e44 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e48 : bv 32 := 0x01f7f7b3.
Lemma F_23e48 : fetch_word Plain.M.loaded_segments (0x23ea0 : word) = Some W_23e48.
Proof. vm_refl. Qed.
Lemma D_23e48 : decode_any W_23e48 = Some (Op ALU_AND 15 15 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e4c : bv 32 := 0x0107b833.
Lemma F_23e4c : fetch_word Plain.M.loaded_segments (0x23ea4 : word) = Some W_23e4c.
Proof. vm_refl. Qed.
Lemma D_23e4c : decode_any W_23e4c = Some (Op ALU_SLTU 16 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e50 : bv 32 := 0x40fe07bb.
Lemma F_23e50 : fetch_word Plain.M.loaded_segments (0x23ea8 : word) = Some W_23e50.
Proof. vm_refl. Qed.
Lemma D_23e50 : decode_any W_23e50 = Some (Op32 ALU_SUB 15 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e54 : bv 32 := 0x00184813.
Lemma F_23e54 : fetch_word Plain.M.loaded_segments (0x23eac : word) = Some W_23e54.
Proof. vm_refl. Qed.
Lemma D_23e54 : decode_any W_23e54 = Some (OpImm ALU_XOR 16 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e58 : bv 32 := 0x00581813.
Lemma F_23e58 : fetch_word Plain.M.loaded_segments (0x23eb0 : word) = Some W_23e58.
Proof. vm_refl. Qed.
Lemma D_23e58 : decode_any W_23e58 = Some (ShiftImm ALU_SLL 16 16 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e5c : bv 32 := 0x010787bb.
Lemma F_23e5c : fetch_word Plain.M.loaded_segments (0x23eb4 : word) = Some W_23e5c.
Proof. vm_refl. Qed.
Lemma D_23e5c : decode_any W_23e5c = Some (Op32 ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e60 : bv 32 := 0x00279813.
Lemma F_23e60 : fetch_word Plain.M.loaded_segments (0x23eb8 : word) = Some W_23e60.
Proof. vm_refl. Qed.
Lemma D_23e60 : decode_any W_23e60 = Some (ShiftImm ALU_SLL 16 15 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e64 : bv 32 := 0xa1888413.
Lemma F_23e64 : fetch_word Plain.M.loaded_segments (0x23ebc : word) = Some W_23e64.
Proof. vm_refl. Qed.
Lemma D_23e64 : decode_any W_23e64 = Some (OpImm ALU_ADD 8 17 2584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e68 : bv 32 := 0x01040833.
Lemma F_23e68 : fetch_word Plain.M.loaded_segments (0x23ec0 : word) = Some W_23e68.
Proof. vm_refl. Qed.
Lemma D_23e68 : decode_any W_23e68 = Some (Op ALU_ADD 16 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e6c : bv 32 := 0x00082883.
Lemma F_23e6c : fetch_word Plain.M.loaded_segments (0x23ec4 : word) = Some W_23e6c.
Proof. vm_refl. Qed.
Lemma D_23e6c : decode_any W_23e6c = Some (Load SZ4 true 17 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e70 : bv 32 := 0x40f3883b.
Lemma F_23e70 : fetch_word Plain.M.loaded_segments (0x23ec8 : word) = Some W_23e70.
Proof. vm_refl. Qed.
Lemma D_23e70 : decode_any W_23e70 = Some (Op32 ALU_SUB 16 7 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e74 : bv 32 := 0x280a0263.
Lemma F_23e74 : fetch_word Plain.M.loaded_segments (0x23ecc : word) = Some W_23e74.
Proof. vm_refl. Qed.
Lemma D_23e74 : decode_any W_23e74 = Some (Branch BC_EQ 20 0 644, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e78 : bv 32 := 0x002e9493.
Lemma F_23e78 : fetch_word Plain.M.loaded_segments (0x23ed0 : word) = Some W_23e78.
Proof. vm_refl. Qed.
Lemma D_23e78 : decode_any W_23e78 = Some (ShiftImm ALU_SLL 9 29 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e7c : bv 32 := 0x02ed8933.
Lemma F_23e7c : fetch_word Plain.M.loaded_segments (0x23ed4 : word) = Some W_23e7c.
Proof. vm_refl. Qed.
Lemma D_23e7c : decode_any W_23e7c = Some (Mul M_MUL 18 27 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e80 : bv 32 := 0x0059dc1b.
Lemma F_23e80 : fetch_word Plain.M.loaded_segments (0x23ed8 : word) = Some W_23e80.
Proof. vm_refl. Qed.
Lemma D_23e80 : decode_any W_23e80 = Some (ShiftImm32 ALU_SRL 24 19 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e84 : bv 32 := 0x009404b3.
Lemma F_23e84 : fetch_word Plain.M.loaded_segments (0x23edc : word) = Some W_23e84.
Proof. vm_refl. Qed.
Lemma D_23e84 : decode_any W_23e84 = Some (Op ALU_ADD 9 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e88 : bv 32 := 0x02db8cb3.
Lemma F_23e88 : fetch_word Plain.M.loaded_segments (0x23ee0 : word) = Some W_23e88.
Proof. vm_refl. Qed.
Lemma D_23e88 : decode_any W_23e88 = Some (Mul M_MUL 25 23 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e8c : bv 32 := 0x00291913.
Lemma F_23e8c : fetch_word Plain.M.loaded_segments (0x23ee4 : word) = Some W_23e8c.
Proof. vm_refl. Qed.
Lemma D_23e8c : decode_any W_23e8c = Some (ShiftImm ALU_SLL 18 18 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e90 : bv 32 := 0x002c1413.
Lemma F_23e90 : fetch_word Plain.M.loaded_segments (0x23ee8 : word) = Some W_23e90.
Proof. vm_refl. Qed.
Lemma D_23e90 : decode_any W_23e90 = Some (ShiftImm ALU_SLL 8 24 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e94 : bv 32 := 0x01228933.
Lemma F_23e94 : fetch_word Plain.M.loaded_segments (0x23eec : word) = Some W_23e94.
Proof. vm_refl. Qed.
Lemma D_23e94 : decode_any W_23e94 = Some (Op ALU_ADD 18 5 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e98 : bv 32 := 0x00890433.
Lemma F_23e98 : fetch_word Plain.M.loaded_segments (0x23ef0 : word) = Some W_23e98.
Proof. vm_refl. Qed.
Lemma D_23e98 : decode_any W_23e98 = Some (Op ALU_ADD 8 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23e9c : bv 32 := 0x005d591b.
Lemma F_23e9c : fetch_word Plain.M.loaded_segments (0x23ef4 : word) = Some W_23e9c.
Proof. vm_refl. Qed.
Lemma D_23e9c : decode_any W_23e9c = Some (ShiftImm32 ALU_SRL 18 26 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23ea0 : bv 32 := 0x002c9c93.
Lemma F_23ea0 : fetch_word Plain.M.loaded_segments (0x23ef8 : word) = Some W_23ea0.
Proof. vm_refl. Qed.
Lemma D_23ea0 : decode_any W_23ea0 = Some (ShiftImm ALU_SLL 25 25 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23ea4 : bv 32 := 0x00291093.
Lemma F_23ea4 : fetch_word Plain.M.loaded_segments (0x23efc : word) = Some W_23ea4.
Proof. vm_refl. Qed.
Lemma D_23ea4 : decode_any W_23ea4 = Some (ShiftImm ALU_SLL 1 18 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23ea8 : bv 32 := 0x0004a903.
Lemma F_23ea8 : fetch_word Plain.M.loaded_segments (0x23f00 : word) = Some W_23ea8.
Proof. vm_refl. Qed.
Lemma D_23ea8 : decode_any W_23ea8 = Some (Load SZ4 true 18 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23eac : bv 32 := 0x019b0cb3.
Lemma F_23eac : fetch_word Plain.M.loaded_segments (0x23f04 : word) = Some W_23eac.
Proof. vm_refl. Qed.
Lemma D_23eac : decode_any W_23eac = Some (Op ALU_ADD 25 22 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23eb0 : bv 32 := 0x001c80b3.
Lemma F_23eb0 : fetch_word Plain.M.loaded_segments (0x23f08 : word) = Some W_23eb0.
Proof. vm_refl. Qed.
Lemma D_23eb0 : decode_any W_23eb0 = Some (Op ALU_ADD 1 25 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23eb4 : bv 32 := 0x01ea3cb3.
Lemma F_23eb4 : fetch_word Plain.M.loaded_segments (0x23f0c : word) = Some W_23eb4.
Proof. vm_refl. Qed.
Lemma D_23eb4 : decode_any W_23eb4 = Some (Op ALU_SLTU 25 20 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23eb8 : bv 32 := 0x006fbf33.
Lemma F_23eb8 : fetch_word Plain.M.loaded_segments (0x23f10 : word) = Some W_23eb8.
Proof. vm_refl. Qed.
Lemma D_23eb8 : decode_any W_23eb8 = Some (Op ALU_SLTU 30 31 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23ebc : bv 32 := 0x001f4c13.
Lemma F_23ebc : fetch_word Plain.M.loaded_segments (0x23f14 : word) = Some W_23ebc.
Proof. vm_refl. Qed.
Lemma D_23ebc : decode_any W_23ebc = Some (OpImm ALU_XOR 24 30 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23ec0 : bv 32 := 0x25d37463.
Lemma F_23ec0 : fetch_word Plain.M.loaded_segments (0x23f18 : word) = Some W_23ec0.
Proof. vm_refl. Qed.
Lemma D_23ec0 : decode_any W_23ec0 = Some (Branch BC_GEU 6 29 584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23ec4 : bv 32 := 0x00000493.
Lemma F_23ec4 : fetch_word Plain.M.loaded_segments (0x23f1c : word) = Some W_23ec4.
Proof. vm_refl. Qed.
Lemma D_23ec4 : decode_any W_23ec4 = Some (OpImm ALU_ADD 9 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23ec8 : bv 32 := 0x00000e93.
Lemma F_23ec8 : fetch_word Plain.M.loaded_segments (0x23f20 : word) = Some W_23ec8.
Proof. vm_refl. Qed.
Lemma D_23ec8 : decode_any W_23ec8 = Some (OpImm ALU_ADD 29 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23ecc : bv 32 := 0x00000e13.
Lemma F_23ecc : fetch_word Plain.M.loaded_segments (0x23f24 : word) = Some W_23ecc.
Proof. vm_refl. Qed.
Lemma D_23ecc : decode_any W_23ecc = Some (OpImm ALU_ADD 28 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23ed0 : bv 32 := 0x00000293.
Lemma F_23ed0 : fetch_word Plain.M.loaded_segments (0x23f28 : word) = Some W_23ed0.
Proof. vm_refl. Qed.
Lemma D_23ed0 : decode_any W_23ed0 = Some (OpImm ALU_ADD 5 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23ed4 : bv 32 := 0x00000d13.
Lemma F_23ed4 : fetch_word Plain.M.loaded_segments (0x23f2c : word) = Some W_23ed4.
Proof. vm_refl. Qed.
Lemma D_23ed4 : decode_any W_23ed4 = Some (OpImm ALU_ADD 26 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23ed8 : bv 32 := 0x0143033b.
Lemma F_23ed8 : fetch_word Plain.M.loaded_segments (0x23f30 : word) = Some W_23ed8.
Proof. vm_refl. Qed.
Lemma D_23ed8 : decode_any W_23ed8 = Some (Op32 ALU_ADD 6 6 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23edc : bv 32 := 0xfffef397.
Lemma F_23edc : fetch_word Plain.M.loaded_segments (0x23f34 : word) = Some W_23edc.
Proof. vm_refl. Qed.
Lemma D_23edc : decode_any W_23edc = Some (Auipc 7 1048559, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23ee0 : bv 32 := 0x00231313.
Lemma F_23ee0 : fetch_word Plain.M.loaded_segments (0x23f38 : word) = Some W_23ee0.
Proof. vm_refl. Qed.
Lemma D_23ee0 : decode_any W_23ee0 = Some (ShiftImm ALU_SLL 6 6 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23ee4 : bv 32 := 0xa0038393.
Lemma F_23ee4 : fetch_word Plain.M.loaded_segments (0x23f3c : word) = Some W_23ee4.
Proof. vm_refl. Qed.
Lemma D_23ee4 : decode_any W_23ee4 = Some (OpImm ALU_ADD 7 7 2560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23ee8 : bv 32 := 0x00638333.
Lemma F_23ee8 : fetch_word Plain.M.loaded_segments (0x23f40 : word) = Some W_23ee8.
Proof. vm_refl. Qed.
Lemma D_23ee8 : decode_any W_23ee8 = Some (Op ALU_ADD 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23eec : bv 32 := 0x00032303.
Lemma F_23eec : fetch_word Plain.M.loaded_segments (0x23f44 : word) = Some W_23eec.
Proof. vm_refl. Qed.
Lemma D_23eec : decode_any W_23eec = Some (Load SZ4 true 6 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23ef0 : bv 32 := 0x00100393.
Lemma F_23ef0 : fetch_word Plain.M.loaded_segments (0x23f48 : word) = Some W_23ef0.
Proof. vm_refl. Qed.
Lemma D_23ef0 : decode_any W_23ef0 = Some (OpImm ALU_ADD 7 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23ef4 : bv 32 := 0x00713023.
Lemma F_23ef4 : fetch_word Plain.M.loaded_segments (0x23f4c : word) = Some W_23ef4.
Proof. vm_refl. Qed.
Lemma D_23ef4 : decode_any W_23ef4 = Some (Store SZ8 2 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23ef8 : bv 32 := 0x01237933.
Lemma F_23ef8 : fetch_word Plain.M.loaded_segments (0x23f50 : word) = Some W_23ef8.
Proof. vm_refl. Qed.
Lemma D_23ef8 : decode_any W_23ef8 = Some (Op ALU_AND 18 6 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23efc : bv 32 := 0x00100993.
Lemma F_23efc : fetch_word Plain.M.loaded_segments (0x23f54 : word) = Some W_23efc.
Proof. vm_refl. Qed.
Lemma D_23efc : decode_any W_23efc = Some (OpImm ALU_ADD 19 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_23f00 : bv 32 := 0x2e40006f.
Lemma F_23f00 : fetch_word Plain.M.loaded_segments (0x23f58 : word) = Some W_23f00.
Proof. vm_refl. Qed.
Lemma D_23f00 : decode_any W_23f00 = Some (Jal 0 740, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_240f8 : bv 32 := 0x00000093.
Lemma F_240f8 : fetch_word Plain.M.loaded_segments (0x24150 : word) = Some W_240f8.
Proof. vm_refl. Qed.
Lemma D_240f8 : decode_any W_240f8 = Some (OpImm ALU_ADD 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_240fc : bv 32 := 0x00000413.
Lemma F_240fc : fetch_word Plain.M.loaded_segments (0x24154 : word) = Some W_240fc.
Proof. vm_refl. Qed.
Lemma D_240fc : decode_any W_240fc = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24100 : bv 32 := 0x00000e93.
Lemma F_24100 : fetch_word Plain.M.loaded_segments (0x24158 : word) = Some W_24100.
Proof. vm_refl. Qed.
Lemma D_24100 : decode_any W_24100 = Some (OpImm ALU_ADD 29 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24104 : bv 32 := 0x00000913.
Lemma F_24104 : fetch_word Plain.M.loaded_segments (0x2415c : word) = Some W_24104.
Proof. vm_refl. Qed.
Lemma D_24104 : decode_any W_24104 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24108 : bv 32 := 0x41d30fbb.
Lemma F_24108 : fetch_word Plain.M.loaded_segments (0x24160 : word) = Some W_24108.
Proof. vm_refl. Qed.
Lemma D_24108 : decode_any W_24108 = Some (Op32 ALU_SUB 31 6 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2410c : bv 32 := 0x013e0f33.
Lemma F_2410c : fetch_word Plain.M.loaded_segments (0x24164 : word) = Some W_2410c.
Proof. vm_refl. Qed.
Lemma D_2410c : decode_any W_2410c = Some (Op ALU_ADD 30 28 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24110 : bv 32 := 0x01ae0d33.
Lemma F_24110 : fetch_word Plain.M.loaded_segments (0x24168 : word) = Some W_24110.
Proof. vm_refl. Qed.
Lemma D_24110 : decode_any W_24110 = Some (Op ALU_ADD 26 28 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24114 : bv 32 := 0x007ffa63.
Lemma F_24114 : fetch_word Plain.M.loaded_segments (0x2416c : word) = Some W_24114.
Proof. vm_refl. Qed.
Lemma D_24114 : decode_any W_24114 = Some (Branch BC_GEU 31 7 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24118 : bv 32 := 0x00000e13.
Lemma F_24118 : fetch_word Plain.M.loaded_segments (0x24170 : word) = Some W_24118.
Proof. vm_refl. Qed.
Lemma D_24118 : decode_any W_24118 = Some (OpImm ALU_ADD 28 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2411c : bv 32 := 0x00000e93.
Lemma F_2411c : fetch_word Plain.M.loaded_segments (0x24174 : word) = Some W_2411c.
Proof. vm_refl. Qed.
Lemma D_2411c : decode_any W_2411c = Some (OpImm ALU_ADD 29 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24120 : bv 32 := 0x00000493.
Lemma F_24120 : fetch_word Plain.M.loaded_segments (0x24178 : word) = Some W_24120.
Proof. vm_refl. Qed.
Lemma D_24120 : decode_any W_24120 = Some (OpImm ALU_ADD 9 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24124 : bv 32 := 0x0380006f.
Lemma F_24124 : fetch_word Plain.M.loaded_segments (0x2417c : word) = Some W_24124.
Proof. vm_refl. Qed.
Lemma D_24124 : decode_any W_24124 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24128 : bv 32 := 0x005fde1b.
Lemma F_24128 : fetch_word Plain.M.loaded_segments (0x24180 : word) = Some W_24128.
Proof. vm_refl. Qed.
Lemma D_24128 : decode_any W_24128 = Some (ShiftImm32 ALU_SRL 28 31 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2412c : bv 32 := 0x02ed83b3.
Lemma F_2412c : fetch_word Plain.M.loaded_segments (0x24184 : word) = Some W_2412c.
Proof. vm_refl. Qed.
Lemma D_2412c : decode_any W_2412c = Some (Mul M_MUL 7 27 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24130 : bv 32 := 0x005f5e9b.
Lemma F_24130 : fetch_word Plain.M.loaded_segments (0x24188 : word) = Some W_24130.
Proof. vm_refl. Qed.
Lemma D_24130 : decode_any W_24130 = Some (ShiftImm32 ALU_SRL 29 30 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24134 : bv 32 := 0x02db84b3.
Lemma F_24134 : fetch_word Plain.M.loaded_segments (0x2418c : word) = Some W_24134.
Proof. vm_refl. Qed.
Lemma D_24134 : decode_any W_24134 = Some (Mul M_MUL 9 23 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24138 : bv 32 := 0x00239393.
Lemma F_24138 : fetch_word Plain.M.loaded_segments (0x24190 : word) = Some W_24138.
Proof. vm_refl. Qed.
Lemma D_24138 : decode_any W_24138 = Some (ShiftImm ALU_SLL 7 7 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2413c : bv 32 := 0x002e9e93.
Lemma F_2413c : fetch_word Plain.M.loaded_segments (0x24194 : word) = Some W_2413c.
Proof. vm_refl. Qed.
Lemma D_2413c : decode_any W_2413c = Some (ShiftImm ALU_SLL 29 29 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24140 : bv 32 := 0x007283b3.
Lemma F_24140 : fetch_word Plain.M.loaded_segments (0x24198 : word) = Some W_24140.
Proof. vm_refl. Qed.
Lemma D_24140 : decode_any W_24140 = Some (Op ALU_ADD 7 5 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24144 : bv 32 := 0x01d38eb3.
Lemma F_24144 : fetch_word Plain.M.loaded_segments (0x2419c : word) = Some W_24144.
Proof. vm_refl. Qed.
Lemma D_24144 : decode_any W_24144 = Some (Op ALU_ADD 29 7 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24148 : bv 32 := 0x005d539b.
Lemma F_24148 : fetch_word Plain.M.loaded_segments (0x241a0 : word) = Some W_24148.
Proof. vm_refl. Qed.
Lemma D_24148 : decode_any W_24148 = Some (ShiftImm32 ALU_SRL 7 26 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2414c : bv 32 := 0x00249493.
Lemma F_2414c : fetch_word Plain.M.loaded_segments (0x241a4 : word) = Some W_2414c.
Proof. vm_refl. Qed.
Lemma D_2414c : decode_any W_2414c = Some (ShiftImm ALU_SLL 9 9 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24150 : bv 32 := 0x00239393.
Lemma F_24150 : fetch_word Plain.M.loaded_segments (0x241a8 : word) = Some W_24150.
Proof. vm_refl. Qed.
Lemma D_24150 : decode_any W_24150 = Some (ShiftImm ALU_SLL 7 7 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24154 : bv 32 := 0x009b04b3.
Lemma F_24154 : fetch_word Plain.M.loaded_segments (0x241ac : word) = Some W_24154.
Proof. vm_refl. Qed.
Lemma D_24154 : decode_any W_24154 = Some (Op ALU_ADD 9 22 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24158 : bv 32 := 0x007484b3.
Lemma F_24158 : fetch_word Plain.M.loaded_segments (0x241b0 : word) = Some W_24158.
Proof. vm_refl. Qed.
Lemma D_24158 : decode_any W_24158 = Some (Op ALU_ADD 9 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2415c : bv 32 := 0x01330333.
Lemma F_2415c : fetch_word Plain.M.loaded_segments (0x241b4 : word) = Some W_2415c.
Proof. vm_refl. Qed.
Lemma D_2415c : decode_any W_2415c = Some (Op ALU_ADD 6 6 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24160 : bv 32 := 0x01f37393.
Lemma F_24160 : fetch_word Plain.M.loaded_segments (0x241b8 : word) = Some W_24160.
Proof. vm_refl. Qed.
Lemma D_24160 : decode_any W_24160 = Some (OpImm ALU_AND 7 6 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24164 : bv 32 := 0x020fb993.
Lemma F_24164 : fetch_word Plain.M.loaded_segments (0x241bc : word) = Some W_24164.
Proof. vm_refl. Qed.
Lemma D_24164 : decode_any W_24164 = Some (OpImm ALU_SLTU 19 31 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24168 : bv 32 := 0x06038663.
Lemma F_24168 : fetch_word Plain.M.loaded_segments (0x241c0 : word) = Some W_24168.
Proof. vm_refl. Qed.
Lemma D_24168 : decode_any W_24168 = Some (Branch BC_EQ 7 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2416c : bv 32 := 0x00013023.
Lemma F_2416c : fetch_word Plain.M.loaded_segments (0x241c4 : word) = Some W_2416c.
Proof. vm_refl. Qed.
Lemma D_2416c : decode_any W_2416c = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24170 : bv 32 := 0x00239313.
Lemma F_24170 : fetch_word Plain.M.loaded_segments (0x241c8 : word) = Some W_24170.
Proof. vm_refl. Qed.
Lemma D_24170 : decode_any W_24170 = Some (ShiftImm ALU_SLL 6 7 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24174 : bv 32 := 0xfffeef97.
Lemma F_24174 : fetch_word Plain.M.loaded_segments (0x241cc : word) = Some W_24174.
Proof. vm_refl. Qed.
Lemma D_24174 : decode_any W_24174 = Some (Auipc 31 1048558, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24178 : bv 32 := 0x768f8f93.
Lemma F_24178 : fetch_word Plain.M.loaded_segments (0x241d0 : word) = Some W_24178.
Proof. vm_refl. Qed.
Lemma D_24178 : decode_any W_24178 = Some (OpImm ALU_ADD 31 31 1896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2417c : bv 32 := 0x006f8333.
Lemma F_2417c : fetch_word Plain.M.loaded_segments (0x241d4 : word) = Some W_2417c.
Proof. vm_refl. Qed.
Lemma D_2417c : decode_any W_2417c = Some (Op ALU_ADD 6 31 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24180 : bv 32 := 0x02ed8fb3.
Lemma F_24180 : fetch_word Plain.M.loaded_segments (0x241d8 : word) = Some W_24180.
Proof. vm_refl. Qed.
Lemma D_24180 : decode_any W_24180 = Some (Mul M_MUL 31 27 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24184 : bv 32 := 0x005f5f1b.
Lemma F_24184 : fetch_word Plain.M.loaded_segments (0x241dc : word) = Some W_24184.
Proof. vm_refl. Qed.
Lemma D_24184 : decode_any W_24184 = Some (ShiftImm32 ALU_SRL 30 30 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24188 : bv 32 := 0x002f9f93.
Lemma F_24188 : fetch_word Plain.M.loaded_segments (0x241e0 : word) = Some W_24188.
Proof. vm_refl. Qed.
Lemma D_24188 : decode_any W_24188 = Some (ShiftImm ALU_SLL 31 31 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2418c : bv 32 := 0x01f282b3.
Lemma F_2418c : fetch_word Plain.M.loaded_segments (0x241e4 : word) = Some W_2418c.
Proof. vm_refl. Qed.
Lemma D_2418c : decode_any W_2418c = Some (Op ALU_ADD 5 5 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24190 : bv 32 := 0x002e1f93.
Lemma F_24190 : fetch_word Plain.M.loaded_segments (0x241e8 : word) = Some W_24190.
Proof. vm_refl. Qed.
Lemma D_24190 : decode_any W_24190 = Some (ShiftImm ALU_SLL 31 28 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24194 : bv 32 := 0x02db8bb3.
Lemma F_24194 : fetch_word Plain.M.loaded_segments (0x241ec : word) = Some W_24194.
Proof. vm_refl. Qed.
Lemma D_24194 : decode_any W_24194 = Some (Mul M_MUL 23 23 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24198 : bv 32 := 0x005d5d1b.
Lemma F_24198 : fetch_word Plain.M.loaded_segments (0x241f0 : word) = Some W_24198.
Proof. vm_refl. Qed.
Lemma D_24198 : decode_any W_24198 = Some (ShiftImm32 ALU_SRL 26 26 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2419c : bv 32 := 0x002f1f13.
Lemma F_2419c : fetch_word Plain.M.loaded_segments (0x241f4 : word) = Some W_2419c.
Proof. vm_refl. Qed.
Lemma D_2419c : decode_any W_2419c = Some (ShiftImm ALU_SLL 30 30 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241a0 : bv 32 := 0x002b9b93.
Lemma F_241a0 : fetch_word Plain.M.loaded_segments (0x241f8 : word) = Some W_241a0.
Proof. vm_refl. Qed.
Lemma D_241a0 : decode_any W_241a0 = Some (ShiftImm ALU_SLL 23 23 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241a4 : bv 32 := 0x002d1d13.
Lemma F_241a4 : fetch_word Plain.M.loaded_segments (0x241fc : word) = Some W_241a4.
Proof. vm_refl. Qed.
Lemma D_241a4 : decode_any W_241a4 = Some (ShiftImm ALU_SLL 26 26 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241a8 : bv 32 := 0x017b0b33.
Lemma F_241a8 : fetch_word Plain.M.loaded_segments (0x24200 : word) = Some W_241a8.
Proof. vm_refl. Qed.
Lemma D_241a8 : decode_any W_241a8 = Some (Op ALU_ADD 22 22 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241ac : bv 32 := 0x00032303.
Lemma F_241ac : fetch_word Plain.M.loaded_segments (0x24204 : word) = Some W_241ac.
Proof. vm_refl. Qed.
Lemma D_241ac : decode_any W_241ac = Some (Load SZ4 true 6 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241b0 : bv 32 := 0x01e282b3.
Lemma F_241b0 : fetch_word Plain.M.loaded_segments (0x24208 : word) = Some W_241b0.
Proof. vm_refl. Qed.
Lemma D_241b0 : decode_any W_241b0 = Some (Op ALU_ADD 5 5 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241b4 : bv 32 := 0x01ab0b33.
Lemma F_241b4 : fetch_word Plain.M.loaded_segments (0x2420c : word) = Some W_241b4.
Proof. vm_refl. Qed.
Lemma D_241b4 : decode_any W_241b4 = Some (Op ALU_ADD 22 22 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241b8 : bv 32 := 0x01f282b3.
Lemma F_241b8 : fetch_word Plain.M.loaded_segments (0x24210 : word) = Some W_241b8.
Proof. vm_refl. Qed.
Lemma D_241b8 : decode_any W_241b8 = Some (Op ALU_ADD 5 5 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241bc : bv 32 := 0x01fb0d33.
Lemma F_241bc : fetch_word Plain.M.loaded_segments (0x24214 : word) = Some W_241bc.
Proof. vm_refl. Qed.
Lemma D_241bc : decode_any W_241bc = Some (Op ALU_ADD 26 22 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241c0 : bv 32 := 0x007823b3.
Lemma F_241c0 : fetch_word Plain.M.loaded_segments (0x24218 : word) = Some W_241c0.
Proof. vm_refl. Qed.
Lemma D_241c0 : decode_any W_241c0 = Some (Op ALU_SLT 7 16 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241c4 : bv 32 := 0x0013cf13.
Lemma F_241c4 : fetch_word Plain.M.loaded_segments (0x2421c : word) = Some W_241c4.
Proof. vm_refl. Qed.
Lemma D_241c4 : decode_any W_241c4 = Some (OpImm ALU_XOR 30 7 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241c8 : bv 32 := 0x00d00393.
Lemma F_241c8 : fetch_word Plain.M.loaded_segments (0x24220 : word) = Some W_241c8.
Proof. vm_refl. Qed.
Lemma D_241c8 : decode_any W_241c8 = Some (OpImm ALU_ADD 7 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241cc : bv 32 := 0x0353f063.
Lemma F_241cc : fetch_word Plain.M.loaded_segments (0x24224 : word) = Some W_241cc.
Proof. vm_refl. Qed.
Lemma D_241cc : decode_any W_241cc = Some (Branch BC_GEU 7 21 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241d4 : bv 32 := 0x00000293.
Lemma F_241d4 : fetch_word Plain.M.loaded_segments (0x2422c : word) = Some W_241d4.
Proof. vm_refl. Qed.
Lemma D_241d4 : decode_any W_241d4 = Some (OpImm ALU_ADD 5 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241d8 : bv 32 := 0x00000d13.
Lemma F_241d8 : fetch_word Plain.M.loaded_segments (0x24230 : word) = Some W_241d8.
Proof. vm_refl. Qed.
Lemma D_241d8 : decode_any W_241d8 = Some (OpImm ALU_ADD 26 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241dc : bv 32 := 0x00100313.
Lemma F_241dc : fetch_word Plain.M.loaded_segments (0x24234 : word) = Some W_241dc.
Proof. vm_refl. Qed.
Lemma D_241dc : decode_any W_241dc = Some (OpImm ALU_ADD 6 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241e0 : bv 32 := 0x00613023.
Lemma F_241e0 : fetch_word Plain.M.loaded_segments (0x24238 : word) = Some W_241e0.
Proof. vm_refl. Qed.
Lemma D_241e0 : decode_any W_241e0 = Some (Store SZ8 2 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241e4 : bv 32 := 0x00d00393.
Lemma F_241e4 : fetch_word Plain.M.loaded_segments (0x2423c : word) = Some W_241e4.
Proof. vm_refl. Qed.
Lemma D_241e4 : decode_any W_241e4 = Some (OpImm ALU_ADD 7 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241e8 : bv 32 := 0x1953ea63.
Lemma F_241e8 : fetch_word Plain.M.loaded_segments (0x24240 : word) = Some W_241e8.
Proof. vm_refl. Qed.
Lemma D_241e8 : decode_any W_241e8 = Some (Branch BC_LTU 7 21 404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241ec : bv 32 := 0x002a9a93.
Lemma F_241ec : fetch_word Plain.M.loaded_segments (0x24244 : word) = Some W_241ec.
Proof. vm_refl. Qed.
Lemma D_241ec : decode_any W_241ec = Some (ShiftImm ALU_SLL 21 21 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241f0 : bv 32 := 0xfffee397.
Lemma F_241f0 : fetch_word Plain.M.loaded_segments (0x24248 : word) = Some W_241f0.
Proof. vm_refl. Qed.
Lemma D_241f0 : decode_any W_241f0 = Some (Auipc 7 1048558, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241f4 : bv 32 := 0x5c038393.
Lemma F_241f4 : fetch_word Plain.M.loaded_segments (0x2424c : word) = Some W_241f4.
Proof. vm_refl. Qed.
Lemma D_241f4 : decode_any W_241f4 = Some (OpImm ALU_ADD 7 7 1472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241f8 : bv 32 := 0x007a8ab3.
Lemma F_241f8 : fetch_word Plain.M.loaded_segments (0x24250 : word) = Some W_241f8.
Proof. vm_refl. Qed.
Lemma D_241f8 : decode_any W_241f8 = Some (Op ALU_ADD 21 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_241fc : bv 32 := 0x000aaf83.
Lemma F_241fc : fetch_word Plain.M.loaded_segments (0x24254 : word) = Some W_241fc.
Proof. vm_refl. Qed.
Lemma D_241fc : decode_any W_241fc = Some (Load SZ4 true 31 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24200 : bv 32 := 0x007f83b3.
Lemma F_24200 : fetch_word Plain.M.loaded_segments (0x24258 : word) = Some W_24200.
Proof. vm_refl. Qed.
Lemma D_24200 : decode_any W_24200 = Some (Op ALU_ADD 7 31 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_24204 : bv 32 := 0x00038067.
Lemma F_24204 : fetch_word Plain.M.loaded_segments (0x2425c : word) = Some W_24204.
Proof. vm_refl. Qed.
Lemma D_24204 : decode_any W_24204 = Some (Jalr 0 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25904 : bv 32 := 0x0e0a0e63.
Lemma F_25904 : fetch_word Plain.M.loaded_segments (0x2595c : word) = Some W_25904.
Proof. vm_refl. Qed.
Lemma D_25904 : decode_any W_25904 = Some (Branch BC_EQ 20 0 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25908 : bv 32 := 0xfff94513.
Lemma F_25908 : fetch_word Plain.M.loaded_segments (0x25960 : word) = Some W_25908.
Proof. vm_refl. Qed.
Lemma D_25908 : decode_any W_25908 = Some (OpImm ALU_XOR 10 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2590c : bv 32 := 0xfff8c593.
Lemma F_2590c : fetch_word Plain.M.loaded_segments (0x25964 : word) = Some W_2590c.
Proof. vm_refl. Qed.
Lemma D_2590c : decode_any W_2590c = Some (OpImm ALU_XOR 11 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25910 : bv 32 := 0x00408093.
Lemma F_25910 : fetch_word Plain.M.loaded_segments (0x25968 : word) = Some W_25910.
Proof. vm_refl. Qed.
Lemma D_25910 : decode_any W_25910 = Some (OpImm ALU_ADD 1 1 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25914 : bv 32 := 0x00269a13.
Lemma F_25914 : fetch_word Plain.M.loaded_segments (0x2596c : word) = Some W_25914.
Proof. vm_refl. Qed.
Lemma D_25914 : decode_any W_25914 = Some (ShiftImm ALU_SLL 20 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25918 : bv 32 := 0x00271a93.
Lemma F_25918 : fetch_word Plain.M.loaded_segments (0x25970 : word) = Some W_25918.
Proof. vm_refl. Qed.
Lemma D_25918 : decode_any W_25918 = Some (ShiftImm ALU_SLL 21 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2591c : bv 32 := 0x001cfb13.
Lemma F_2591c : fetch_word Plain.M.loaded_segments (0x25974 : word) = Some W_2591c.
Proof. vm_refl. Qed.
Lemma D_2591c : decode_any W_2591c = Some (OpImm ALU_AND 22 25 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25920 : bv 32 := 0x001c7b93.
Lemma F_25920 : fetch_word Plain.M.loaded_segments (0x25978 : word) = Some W_25920.
Proof. vm_refl. Qed.
Lemma D_25920 : decode_any W_25920 = Some (OpImm ALU_AND 23 24 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25924 : bv 32 := 0x00060c13.
Lemma F_25924 : fetch_word Plain.M.loaded_segments (0x2597c : word) = Some W_25924.
Proof. vm_refl. Qed.
Lemma D_25924 : decode_any W_25924 = Some (OpImm ALU_ADD 24 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25928 : bv 32 := 0x02c0006f.
Lemma F_25928 : fetch_word Plain.M.loaded_segments (0x25980 : word) = Some W_25928.
Proof. vm_refl. Qed.
Lemma D_25928 : decode_any W_25928 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2592c : bv 32 := 0x0103d3bb.
Lemma F_2592c : fetch_word Plain.M.loaded_segments (0x25984 : word) = Some W_2592c.
Proof. vm_refl. Qed.
Lemma D_2592c : decode_any W_2592c = Some (Op32 ALU_SRL 7 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25930 : bv 32 := 0x00042f83.
Lemma F_25930 : fetch_word Plain.M.loaded_segments (0x25988 : word) = Some W_25930.
Proof. vm_refl. Qed.
Lemma D_25930 : decode_any W_25930 = Some (Load SZ4 true 31 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25934 : bv 32 := 0x0123f3b3.
Lemma F_25934 : fetch_word Plain.M.loaded_segments (0x2598c : word) = Some W_25934.
Proof. vm_refl. Qed.
Lemma D_25934 : decode_any W_25934 = Some (Op ALU_AND 7 7 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25938 : bv 32 := 0xfffc0c1b.
Lemma F_25938 : fetch_word Plain.M.loaded_segments (0x25990 : word) = Some W_25938.
Proof. vm_refl. Qed.
Lemma D_25938 : decode_any W_25938 = Some (OpImm32 24 24 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2593c : bv 32 := 0x014080b3.
Lemma F_2593c : fetch_word Plain.M.loaded_segments (0x25994 : word) = Some W_2593c.
Proof. vm_refl. Qed.
Lemma D_2593c : decode_any W_2593c = Some (Op ALU_ADD 1 1 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25940 : bv 32 := 0x00afffb3.
Lemma F_25940 : fetch_word Plain.M.loaded_segments (0x25998 : word) = Some W_25940.
Proof. vm_refl. Qed.
Lemma D_25940 : decode_any W_25940 = Some (Op ALU_AND 31 31 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25944 : bv 32 := 0x007fe3b3.
Lemma F_25944 : fetch_word Plain.M.loaded_segments (0x2599c : word) = Some W_25944.
Proof. vm_refl. Qed.
Lemma D_25944 : decode_any W_25944 = Some (Op ALU_OR 7 31 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25948 : bv 32 := 0x00742023.
Lemma F_25948 : fetch_word Plain.M.loaded_segments (0x259a0 : word) = Some W_25948.
Proof. vm_refl. Qed.
Lemma D_25948 : decode_any W_25948 = Some (Store SZ4 8 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2594c : bv 32 := 0x01540433.
Lemma F_2594c : fetch_word Plain.M.loaded_segments (0x259a4 : word) = Some W_2594c.
Proof. vm_refl. Qed.
Lemma D_2594c : decode_any W_2594c = Some (Op ALU_ADD 8 8 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25950 : bv 32 := 0x0a0c0863.
Lemma F_25950 : fetch_word Plain.M.loaded_segments (0x259a8 : word) = Some W_25950.
Proof. vm_refl. Qed.
Lemma D_25950 : decode_any W_25950 = Some (Branch BC_EQ 24 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25954 : bv 32 := 0xffc0a383.
Lemma F_25954 : fetch_word Plain.M.loaded_segments (0x259ac : word) = Some W_25954.
Proof. vm_refl. Qed.
Lemma D_25954 : decode_any W_25954 = Some (Load SZ4 true 7 1 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25958 : bv 32 := 0xfc0b0ae3.
Lemma F_25958 : fetch_word Plain.M.loaded_segments (0x259b0 : word) = Some W_25958.
Proof. vm_refl. Qed.
Lemma D_25958 : decode_any W_25958 = Some (Branch BC_EQ 22 0 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2595c : bv 32 := 0x00f393bb.
Lemma F_2595c : fetch_word Plain.M.loaded_segments (0x259b4 : word) = Some W_2595c.
Proof. vm_refl. Qed.
Lemma D_2595c : decode_any W_2595c = Some (Op32 ALU_SLL 7 7 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25960 : bv 32 := 0xfc0b98e3.
Lemma F_25960 : fetch_word Plain.M.loaded_segments (0x259b8 : word) = Some W_25960.
Proof. vm_refl. Qed.
Lemma D_25960 : decode_any W_25960 = Some (Branch BC_NE 23 0 8144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25964 : bv 32 := 0x0000af83.
Lemma F_25964 : fetch_word Plain.M.loaded_segments (0x259bc : word) = Some W_25964.
Proof. vm_refl. Qed.
Lemma D_25964 : decode_any W_25964 = Some (Load SZ4 true 31 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25968 : bv 32 := 0x00b3f3b3.
Lemma F_25968 : fetch_word Plain.M.loaded_segments (0x259c0 : word) = Some W_25968.
Proof. vm_refl. Qed.
Lemma D_25968 : decode_any W_25968 = Some (Op ALU_AND 7 7 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2596c : bv 32 := 0x010fdfbb.
Lemma F_2596c : fetch_word Plain.M.loaded_segments (0x259c4 : word) = Some W_2596c.
Proof. vm_refl. Qed.
Lemma D_2596c : decode_any W_2596c = Some (Op32 ALU_SRL 31 31 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25970 : bv 32 := 0x011fffb3.
Lemma F_25970 : fetch_word Plain.M.loaded_segments (0x259c8 : word) = Some W_25970.
Proof. vm_refl. Qed.
Lemma D_25970 : decode_any W_25970 = Some (Op ALU_AND 31 31 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25974 : bv 32 := 0x007fe3b3.
Lemma F_25974 : fetch_word Plain.M.loaded_segments (0x259cc : word) = Some W_25974.
Proof. vm_refl. Qed.
Lemma D_25974 : decode_any W_25974 = Some (Op ALU_OR 7 31 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25978 : bv 32 := 0xfb9ff06f.
Lemma F_25978 : fetch_word Plain.M.loaded_segments (0x259d0 : word) = Some W_25978.
Proof. vm_refl. Qed.
Lemma D_25978 : decode_any W_25978 = Some (Jal 0 2097080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a00 : bv 32 := 0x3a0982e3.
Lemma F_25a00 : fetch_word Plain.M.loaded_segments (0x25a58 : word) = Some W_25a00.
Proof. vm_refl. Qed.
Lemma D_25a00 : decode_any W_25a00 = Some (Branch BC_EQ 19 0 2980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a04 : bv 32 := 0x00013503.
Lemma F_25a04 : fetch_word Plain.M.loaded_segments (0x25a5c : word) = Some W_25a04.
Proof. vm_refl. Qed.
Lemma D_25a04 : decode_any W_25a04 = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a08 : bv 32 := 0x18051063.
Lemma F_25a08 : fetch_word Plain.M.loaded_segments (0x25a60 : word) = Some W_25a08.
Proof. vm_refl. Qed.
Lemma D_25a08 : decode_any W_25a08 = Some (Branch BC_NE 10 0 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a0c : bv 32 := 0xfff34513.
Lemma F_25a0c : fetch_word Plain.M.loaded_segments (0x25a64 : word) = Some W_25a0c.
Proof. vm_refl. Qed.
Lemma D_25a0c : decode_any W_25a0c = Some (OpImm ALU_XOR 10 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a10 : bv 32 := 0xfff8c593.
Lemma F_25a10 : fetch_word Plain.M.loaded_segments (0x25a68 : word) = Some W_25a10.
Proof. vm_refl. Qed.
Lemma D_25a10 : decode_any W_25a10 = Some (OpImm ALU_XOR 11 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a14 : bv 32 := 0x004d0393.
Lemma F_25a14 : fetch_word Plain.M.loaded_segments (0x25a6c : word) = Some W_25a14.
Proof. vm_refl. Qed.
Lemma D_25a14 : decode_any W_25a14 = Some (OpImm ALU_ADD 7 26 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a18 : bv 32 := 0x00269693.
Lemma F_25a18 : fetch_word Plain.M.loaded_segments (0x25a70 : word) = Some W_25a18.
Proof. vm_refl. Qed.
Lemma D_25a18 : decode_any W_25a18 = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a1c : bv 32 := 0x00271713.
Lemma F_25a1c : fetch_word Plain.M.loaded_segments (0x25a74 : word) = Some W_25a1c.
Proof. vm_refl. Qed.
Lemma D_25a1c : decode_any W_25a1c = Some (ShiftImm ALU_SLL 14 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a20 : bv 32 := 0x001f7e13.
Lemma F_25a20 : fetch_word Plain.M.loaded_segments (0x25a78 : word) = Some W_25a20.
Proof. vm_refl. Qed.
Lemma D_25a20 : decode_any W_25a20 = Some (OpImm ALU_AND 28 30 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a24 : bv 32 := 0x0280006f.
Lemma F_25a24 : fetch_word Plain.M.loaded_segments (0x25a7c : word) = Some W_25a24.
Proof. vm_refl. Qed.
Lemma D_25a24 : decode_any W_25a24 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a28 : bv 32 := 0x0002af03.
Lemma F_25a28 : fetch_word Plain.M.loaded_segments (0x25a80 : word) = Some W_25a28.
Proof. vm_refl. Qed.
Lemma D_25a28 : decode_any W_25a28 = Some (Load SZ4 true 30 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a2c : bv 32 := 0x006efeb3.
Lemma F_25a2c : fetch_word Plain.M.loaded_segments (0x25a84 : word) = Some W_25a2c.
Proof. vm_refl. Qed.
Lemma D_25a2c : decode_any W_25a2c = Some (Op ALU_AND 29 29 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a30 : bv 32 := 0xfff6061b.
Lemma F_25a30 : fetch_word Plain.M.loaded_segments (0x25a88 : word) = Some W_25a30.
Proof. vm_refl. Qed.
Lemma D_25a30 : decode_any W_25a30 = Some (OpImm32 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a34 : bv 32 := 0x00d383b3.
Lemma F_25a34 : fetch_word Plain.M.loaded_segments (0x25a8c : word) = Some W_25a34.
Proof. vm_refl. Qed.
Lemma D_25a34 : decode_any W_25a34 = Some (Op ALU_ADD 7 7 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a38 : bv 32 := 0x00af7f33.
Lemma F_25a38 : fetch_word Plain.M.loaded_segments (0x25a90 : word) = Some W_25a38.
Proof. vm_refl. Qed.
Lemma D_25a38 : decode_any W_25a38 = Some (Op ALU_AND 30 30 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a3c : bv 32 := 0x01df6eb3.
Lemma F_25a3c : fetch_word Plain.M.loaded_segments (0x25a94 : word) = Some W_25a3c.
Proof. vm_refl. Qed.
Lemma D_25a3c : decode_any W_25a3c = Some (Op ALU_OR 29 30 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a40 : bv 32 := 0x01d2a023.
Lemma F_25a40 : fetch_word Plain.M.loaded_segments (0x25a98 : word) = Some W_25a40.
Proof. vm_refl. Qed.
Lemma D_25a40 : decode_any W_25a40 = Some (Store SZ4 5 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a44 : bv 32 := 0x00e282b3.
Lemma F_25a44 : fetch_word Plain.M.loaded_segments (0x25a9c : word) = Some W_25a44.
Proof. vm_refl. Qed.
Lemma D_25a44 : decode_any W_25a44 = Some (Op ALU_ADD 5 5 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a48 : bv 32 := 0x14060063.
Lemma F_25a48 : fetch_word Plain.M.loaded_segments (0x25aa0 : word) = Some W_25a48.
Proof. vm_refl. Qed.
Lemma D_25a48 : decode_any W_25a48 = Some (Branch BC_EQ 12 0 320, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a4c : bv 32 := 0xffc3ae83.
Lemma F_25a4c : fetch_word Plain.M.loaded_segments (0x25aa4 : word) = Some W_25a4c.
Proof. vm_refl. Qed.
Lemma D_25a4c : decode_any W_25a4c = Some (Load SZ4 true 29 7 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a50 : bv 32 := 0x00fe9ebb.
Lemma F_25a50 : fetch_word Plain.M.loaded_segments (0x25aa8 : word) = Some W_25a50.
Proof. vm_refl. Qed.
Lemma D_25a50 : decode_any W_25a50 = Some (Op32 ALU_SLL 29 29 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a54 : bv 32 := 0xfc0e1ae3.
Lemma F_25a54 : fetch_word Plain.M.loaded_segments (0x25aac : word) = Some W_25a54.
Proof. vm_refl. Qed.
Lemma D_25a54 : decode_any W_25a54 = Some (Branch BC_NE 28 0 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a58 : bv 32 := 0x0003af03.
Lemma F_25a58 : fetch_word Plain.M.loaded_segments (0x25ab0 : word) = Some W_25a58.
Proof. vm_refl. Qed.
Lemma D_25a58 : decode_any W_25a58 = Some (Load SZ4 true 30 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a5c : bv 32 := 0x00befeb3.
Lemma F_25a5c : fetch_word Plain.M.loaded_segments (0x25ab4 : word) = Some W_25a5c.
Proof. vm_refl. Qed.
Lemma D_25a5c : decode_any W_25a5c = Some (Op ALU_AND 29 29 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a60 : bv 32 := 0x010f5f3b.
Lemma F_25a60 : fetch_word Plain.M.loaded_segments (0x25ab8 : word) = Some W_25a60.
Proof. vm_refl. Qed.
Lemma D_25a60 : decode_any W_25a60 = Some (Op32 ALU_SRL 30 30 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a64 : bv 32 := 0x011f7f33.
Lemma F_25a64 : fetch_word Plain.M.loaded_segments (0x25abc : word) = Some W_25a64.
Proof. vm_refl. Qed.
Lemma D_25a64 : decode_any W_25a64 = Some (Op ALU_AND 30 30 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a68 : bv 32 := 0x01df6eb3.
Lemma F_25a68 : fetch_word Plain.M.loaded_segments (0x25ac0 : word) = Some W_25a68.
Proof. vm_refl. Qed.
Lemma D_25a68 : decode_any W_25a68 = Some (Op ALU_OR 29 30 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25a6c : bv 32 := 0xfbdff06f.
Lemma F_25a6c : fetch_word Plain.M.loaded_segments (0x25ac4 : word) = Some W_25a6c.
Proof. vm_refl. Qed.
Lemma D_25a6c : decode_any W_25a6c = Some (Jal 0 2097084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b88 : bv 32 := 0x06813083.
Lemma F_25b88 : fetch_word Plain.M.loaded_segments (0x25be0 : word) = Some W_25b88.
Proof. vm_refl. Qed.
Lemma D_25b88 : decode_any W_25b88 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b8c : bv 32 := 0x06013403.
Lemma F_25b8c : fetch_word Plain.M.loaded_segments (0x25be4 : word) = Some W_25b8c.
Proof. vm_refl. Qed.
Lemma D_25b8c : decode_any W_25b8c = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b90 : bv 32 := 0x05813483.
Lemma F_25b90 : fetch_word Plain.M.loaded_segments (0x25be8 : word) = Some W_25b90.
Proof. vm_refl. Qed.
Lemma D_25b90 : decode_any W_25b90 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b94 : bv 32 := 0x05013903.
Lemma F_25b94 : fetch_word Plain.M.loaded_segments (0x25bec : word) = Some W_25b94.
Proof. vm_refl. Qed.
Lemma D_25b94 : decode_any W_25b94 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b98 : bv 32 := 0x04813983.
Lemma F_25b98 : fetch_word Plain.M.loaded_segments (0x25bf0 : word) = Some W_25b98.
Proof. vm_refl. Qed.
Lemma D_25b98 : decode_any W_25b98 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25b9c : bv 32 := 0x04013a03.
Lemma F_25b9c : fetch_word Plain.M.loaded_segments (0x25bf4 : word) = Some W_25b9c.
Proof. vm_refl. Qed.
Lemma D_25b9c : decode_any W_25b9c = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25ba0 : bv 32 := 0x03813a83.
Lemma F_25ba0 : fetch_word Plain.M.loaded_segments (0x25bf8 : word) = Some W_25ba0.
Proof. vm_refl. Qed.
Lemma D_25ba0 : decode_any W_25ba0 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25ba4 : bv 32 := 0x03013b03.
Lemma F_25ba4 : fetch_word Plain.M.loaded_segments (0x25bfc : word) = Some W_25ba4.
Proof. vm_refl. Qed.
Lemma D_25ba4 : decode_any W_25ba4 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25ba8 : bv 32 := 0x02813b83.
Lemma F_25ba8 : fetch_word Plain.M.loaded_segments (0x25c00 : word) = Some W_25ba8.
Proof. vm_refl. Qed.
Lemma D_25ba8 : decode_any W_25ba8 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25bac : bv 32 := 0x02013c03.
Lemma F_25bac : fetch_word Plain.M.loaded_segments (0x25c04 : word) = Some W_25bac.
Proof. vm_refl. Qed.
Lemma D_25bac : decode_any W_25bac = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25bb0 : bv 32 := 0x01813c83.
Lemma F_25bb0 : fetch_word Plain.M.loaded_segments (0x25c08 : word) = Some W_25bb0.
Proof. vm_refl. Qed.
Lemma D_25bb0 : decode_any W_25bb0 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25bb4 : bv 32 := 0x01013d03.
Lemma F_25bb4 : fetch_word Plain.M.loaded_segments (0x25c0c : word) = Some W_25bb4.
Proof. vm_refl. Qed.
Lemma D_25bb4 : decode_any W_25bb4 = Some (Load SZ8 true 26 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25bb8 : bv 32 := 0x00813d83.
Lemma F_25bb8 : fetch_word Plain.M.loaded_segments (0x25c10 : word) = Some W_25bb8.
Proof. vm_refl. Qed.
Lemma D_25bb8 : decode_any W_25bb8 = Some (Load SZ8 true 27 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25bbc : bv 32 := 0x07010113.
Lemma F_25bbc : fetch_word Plain.M.loaded_segments (0x25c14 : word) = Some W_25bbc.
Proof. vm_refl. Qed.
Lemma D_25bbc : decode_any W_25bbc = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_25bc0 : bv 32 := 0x00008067.
Lemma F_25bc0 : fetch_word Plain.M.loaded_segments (0x25c18 : word) = Some W_25bc0.
Proof. vm_refl. Qed.
Lemma D_25bc0 : decode_any W_25bc0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265a4 : bv 32 := 0x00000513.
Lemma F_265a4 : fetch_word Plain.M.loaded_segments (0x265fc : word) = Some W_265a4.
Proof. vm_refl. Qed.
Lemma D_265a4 : decode_any W_265a4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265a8 : bv 32 := 0x00000593.
Lemma F_265a8 : fetch_word Plain.M.loaded_segments (0x26600 : word) = Some W_265a8.
Proof. vm_refl. Qed.
Lemma D_265a8 : decode_any W_265a8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265ac : bv 32 := 0xfff8c413.
Lemma F_265ac : fetch_word Plain.M.loaded_segments (0x26604 : word) = Some W_265ac.
Proof. vm_refl. Qed.
Lemma D_265ac : decode_any W_265ac = Some (OpImm ALU_XOR 8 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265b0 : bv 32 := 0x00271913.
Lemma F_265b0 : fetch_word Plain.M.loaded_segments (0x26608 : word) = Some W_265b0.
Proof. vm_refl. Qed.
Lemma D_265b0 : decode_any W_265b0 = Some (ShiftImm ALU_SLL 18 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265b4 : bv 32 := 0x00448493.
Lemma F_265b4 : fetch_word Plain.M.loaded_segments (0x2660c : word) = Some W_265b4.
Proof. vm_refl. Qed.
Lemma D_265b4 : decode_any W_265b4 = Some (OpImm ALU_ADD 9 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265b8 : bv 32 := 0x00269993.
Lemma F_265b8 : fetch_word Plain.M.loaded_segments (0x26610 : word) = Some W_265b8.
Proof. vm_refl. Qed.
Lemma D_265b8 : decode_any W_265b8 = Some (ShiftImm ALU_SLL 19 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265bc : bv 32 := 0x002e1a13.
Lemma F_265bc : fetch_word Plain.M.loaded_segments (0x26614 : word) = Some W_265bc.
Proof. vm_refl. Qed.
Lemma D_265bc : decode_any W_265bc = Some (ShiftImm ALU_SLL 20 28 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265c0 : bv 32 := 0x000e8a93.
Lemma F_265c0 : fetch_word Plain.M.loaded_segments (0x26618 : word) = Some W_265c0.
Proof. vm_refl. Qed.
Lemma D_265c0 : decode_any W_265c0 = Some (OpImm ALU_ADD 21 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265c4 : bv 32 := 0x0180006f.
Lemma F_265c4 : fetch_word Plain.M.loaded_segments (0x2661c : word) = Some W_265c4.
Proof. vm_refl. Qed.
Lemma D_265c4 : decode_any W_265c4 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265c8 : bv 32 := 0x0015859b.
Lemma F_265c8 : fetch_word Plain.M.loaded_segments (0x26620 : word) = Some W_265c8.
Proof. vm_refl. Qed.
Lemma D_265c8 : decode_any W_265c8 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265cc : bv 32 := 0x012a8ab3.
Lemma F_265cc : fetch_word Plain.M.loaded_segments (0x26624 : word) = Some W_265cc.
Proof. vm_refl. Qed.
Lemma D_265cc : decode_any W_265cc = Some (Op ALU_ADD 21 21 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265d0 : bv 32 := 0x013484b3.
Lemma F_265d0 : fetch_word Plain.M.loaded_segments (0x26628 : word) = Some W_265d0.
Proof. vm_refl. Qed.
Lemma D_265d0 : decode_any W_265d0 = Some (Op ALU_ADD 9 9 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265d4 : bv 32 := 0x00150513.
Lemma F_265d4 : fetch_word Plain.M.loaded_segments (0x2662c : word) = Some W_265d4.
Proof. vm_refl. Qed.
Lemma D_265d4 : decode_any W_265d4 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265d8 : bv 32 := 0xc2c58663.
Lemma F_265d8 : fetch_word Plain.M.loaded_segments (0x26630 : word) = Some W_265d8.
Proof. vm_refl. Qed.
Lemma D_265d8 : decode_any W_265d8 = Some (Branch BC_EQ 11 12 5164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265dc : bv 32 := 0xfe0e06e3.
Lemma F_265dc : fetch_word Plain.M.loaded_segments (0x26634 : word) = Some W_265dc.
Proof. vm_refl. Qed.
Lemma D_265dc : decode_any W_265dc = Some (Branch BC_EQ 28 0 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265e0 : bv 32 := 0x02a903b3.
Lemma F_265e0 : fetch_word Plain.M.loaded_segments (0x26638 : word) = Some W_265e0.
Proof. vm_refl. Qed.
Lemma D_265e0 : decode_any W_265e0 = Some (Mul M_MUL 7 18 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265e4 : bv 32 := 0x007a03b3.
Lemma F_265e4 : fetch_word Plain.M.loaded_segments (0x2663c : word) = Some W_265e4.
Proof. vm_refl. Qed.
Lemma D_265e4 : decode_any W_265e4 = Some (Op ALU_ADD 7 20 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265e8 : bv 32 := 0x007e83b3.
Lemma F_265e8 : fetch_word Plain.M.loaded_segments (0x26640 : word) = Some W_265e8.
Proof. vm_refl. Qed.
Lemma D_265e8 : decode_any W_265e8 = Some (Op ALU_ADD 7 29 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265ec : bv 32 := 0x00048b13.
Lemma F_265ec : fetch_word Plain.M.loaded_segments (0x26644 : word) = Some W_265ec.
Proof. vm_refl. Qed.
Lemma D_265ec : decode_any W_265ec = Some (OpImm ALU_ADD 22 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265f0 : bv 32 := 0x000a8b93.
Lemma F_265f0 : fetch_word Plain.M.loaded_segments (0x26648 : word) = Some W_265f0.
Proof. vm_refl. Qed.
Lemma D_265f0 : decode_any W_265f0 = Some (OpImm ALU_ADD 23 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265f4 : bv 32 := 0xffcb2f83.
Lemma F_265f4 : fetch_word Plain.M.loaded_segments (0x2664c : word) = Some W_265f4.
Proof. vm_refl. Qed.
Lemma D_265f4 : decode_any W_265f4 = Some (Load SZ4 true 31 22 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265f8 : bv 32 := 0x000b2c03.
Lemma F_265f8 : fetch_word Plain.M.loaded_segments (0x26650 : word) = Some W_265f8.
Proof. vm_refl. Qed.
Lemma D_265f8 : decode_any W_265f8 = Some (Load SZ4 true 24 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_265fc : bv 32 := 0x00ff9fbb.
Lemma F_265fc : fetch_word Plain.M.loaded_segments (0x26654 : word) = Some W_265fc.
Proof. vm_refl. Qed.
Lemma D_265fc : decode_any W_265fc = Some (Op32 ALU_SLL 31 31 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26600 : bv 32 := 0x010c5c3b.
Lemma F_26600 : fetch_word Plain.M.loaded_segments (0x26658 : word) = Some W_26600.
Proof. vm_refl. Qed.
Lemma D_26600 : decode_any W_26600 = Some (Op32 ALU_SRL 24 24 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26604 : bv 32 := 0x008fffb3.
Lemma F_26604 : fetch_word Plain.M.loaded_segments (0x2665c : word) = Some W_26604.
Proof. vm_refl. Qed.
Lemma D_26604 : decode_any W_26604 = Some (Op ALU_AND 31 31 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26608 : bv 32 := 0x011c7c33.
Lemma F_26608 : fetch_word Plain.M.loaded_segments (0x26660 : word) = Some W_26608.
Proof. vm_refl. Qed.
Lemma D_26608 : decode_any W_26608 = Some (Op ALU_AND 24 24 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2660c : bv 32 := 0x01fc6fb3.
Lemma F_2660c : fetch_word Plain.M.loaded_segments (0x26664 : word) = Some W_2660c.
Proof. vm_refl. Qed.
Lemma D_2660c : decode_any W_2660c = Some (Op ALU_OR 31 24 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26610 : bv 32 := 0x01fba023.
Lemma F_26610 : fetch_word Plain.M.loaded_segments (0x26668 : word) = Some W_26610.
Proof. vm_refl. Qed.
Lemma D_26610 : decode_any W_26610 = Some (Store SZ4 23 31 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26614 : bv 32 := 0x004b8b93.
Lemma F_26614 : fetch_word Plain.M.loaded_segments (0x2666c : word) = Some W_26614.
Proof. vm_refl. Qed.
Lemma D_26614 : decode_any W_26614 = Some (OpImm ALU_ADD 23 23 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26618 : bv 32 := 0x004b0b13.
Lemma F_26618 : fetch_word Plain.M.loaded_segments (0x26670 : word) = Some W_26618.
Proof. vm_refl. Qed.
Lemma D_26618 : decode_any W_26618 = Some (OpImm ALU_ADD 22 22 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2661c : bv 32 := 0xfc7b9ce3.
Lemma F_2661c : fetch_word Plain.M.loaded_segments (0x26674 : word) = Some W_2661c.
Proof. vm_refl. Qed.
Lemma D_2661c : decode_any W_2661c = Some (Branch BC_NE 23 7 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_26620 : bv 32 := 0xfa9ff06f.
Lemma F_26620 : fetch_word Plain.M.loaded_segments (0x26678 : word) = Some W_26620.
Proof. vm_refl. Qed.
Lemma D_26620 : decode_any W_26620 = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

