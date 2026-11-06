(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_799f0 : bv 32 := 0xf9010113.
Lemma F_799f0 : fetch_word Plain.M.loaded_segments (0x79a48 : word) = Some W_799f0.
Proof. vm_refl. Qed.
Lemma D_799f0 : decode_any W_799f0 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799f4 : bv 32 := 0x06113423.
Lemma F_799f4 : fetch_word Plain.M.loaded_segments (0x79a4c : word) = Some W_799f4.
Proof. vm_refl. Qed.
Lemma D_799f4 : decode_any W_799f4 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799f8 : bv 32 := 0x06813023.
Lemma F_799f8 : fetch_word Plain.M.loaded_segments (0x79a50 : word) = Some W_799f8.
Proof. vm_refl. Qed.
Lemma D_799f8 : decode_any W_799f8 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_799fc : bv 32 := 0x04913c23.
Lemma F_799fc : fetch_word Plain.M.loaded_segments (0x79a54 : word) = Some W_799fc.
Proof. vm_refl. Qed.
Lemma D_799fc : decode_any W_799fc = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a00 : bv 32 := 0x05213823.
Lemma F_79a00 : fetch_word Plain.M.loaded_segments (0x79a58 : word) = Some W_79a00.
Proof. vm_refl. Qed.
Lemma D_79a00 : decode_any W_79a00 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a04 : bv 32 := 0x05313423.
Lemma F_79a04 : fetch_word Plain.M.loaded_segments (0x79a5c : word) = Some W_79a04.
Proof. vm_refl. Qed.
Lemma D_79a04 : decode_any W_79a04 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a08 : bv 32 := 0x05413023.
Lemma F_79a08 : fetch_word Plain.M.loaded_segments (0x79a60 : word) = Some W_79a08.
Proof. vm_refl. Qed.
Lemma D_79a08 : decode_any W_79a08 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a0c : bv 32 := 0x03513c23.
Lemma F_79a0c : fetch_word Plain.M.loaded_segments (0x79a64 : word) = Some W_79a0c.
Proof. vm_refl. Qed.
Lemma D_79a0c : decode_any W_79a0c = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a10 : bv 32 := 0x03613823.
Lemma F_79a10 : fetch_word Plain.M.loaded_segments (0x79a68 : word) = Some W_79a10.
Proof. vm_refl. Qed.
Lemma D_79a10 : decode_any W_79a10 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a14 : bv 32 := 0x03713423.
Lemma F_79a14 : fetch_word Plain.M.loaded_segments (0x79a6c : word) = Some W_79a14.
Proof. vm_refl. Qed.
Lemma D_79a14 : decode_any W_79a14 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a18 : bv 32 := 0x03813023.
Lemma F_79a18 : fetch_word Plain.M.loaded_segments (0x79a70 : word) = Some W_79a18.
Proof. vm_refl. Qed.
Lemma D_79a18 : decode_any W_79a18 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a1c : bv 32 := 0x01913c23.
Lemma F_79a1c : fetch_word Plain.M.loaded_segments (0x79a74 : word) = Some W_79a1c.
Proof. vm_refl. Qed.
Lemma D_79a1c : decode_any W_79a1c = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a20 : bv 32 := 0x01a13823.
Lemma F_79a20 : fetch_word Plain.M.loaded_segments (0x79a78 : word) = Some W_79a20.
Proof. vm_refl. Qed.
Lemma D_79a20 : decode_any W_79a20 = Some (Store SZ8 2 26 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a24 : bv 32 := 0x01b13423.
Lemma F_79a24 : fetch_word Plain.M.loaded_segments (0x79a7c : word) = Some W_79a24.
Proof. vm_refl. Qed.
Lemma D_79a24 : decode_any W_79a24 = Some (Store SZ8 2 27 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a28 : bv 32 := 0x00070413.
Lemma F_79a28 : fetch_word Plain.M.loaded_segments (0x79a80 : word) = Some W_79a28.
Proof. vm_refl. Qed.
Lemma D_79a28 : decode_any W_79a28 = Some (OpImm ALU_ADD 8 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a2c : bv 32 := 0x02b685b3.
Lemma F_79a2c : fetch_word Plain.M.loaded_segments (0x79a84 : word) = Some W_79a2c.
Proof. vm_refl. Qed.
Lemma D_79a2c : decode_any W_79a2c = Some (Mul M_MUL 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a30 : bv 32 := 0x02d7873b.
Lemma F_79a30 : fetch_word Plain.M.loaded_segments (0x79a88 : word) = Some W_79a30.
Proof. vm_refl. Qed.
Lemma D_79a30 : decode_any W_79a30 = Some (Mul32 M_MUL 14 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a34 : bv 32 := 0x02d886b3.
Lemma F_79a34 : fetch_word Plain.M.loaded_segments (0x79a8c : word) = Some W_79a34.
Proof. vm_refl. Qed.
Lemma D_79a34 : decode_any W_79a34 = Some (Mul M_MUL 13 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a38 : bv 32 := 0x43f75793.
Lemma F_79a38 : fetch_word Plain.M.loaded_segments (0x79a90 : word) = Some W_79a38.
Proof. vm_refl. Qed.
Lemma D_79a38 : decode_any W_79a38 = Some (ShiftImm ALU_SRA 15 14 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a3c : bv 32 := 0x00e7f7b3.
Lemma F_79a3c : fetch_word Plain.M.loaded_segments (0x79a94 : word) = Some W_79a3c.
Proof. vm_refl. Qed.
Lemma D_79a3c : decode_any W_79a3c = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a40 : bv 32 := 0x00f687b3.
Lemma F_79a40 : fetch_word Plain.M.loaded_segments (0x79a98 : word) = Some W_79a40.
Proof. vm_refl. Qed.
Lemma D_79a40 : decode_any W_79a40 = Some (Op ALU_ADD 15 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a44 : bv 32 := 0x00e026b3.
Lemma F_79a44 : fetch_word Plain.M.loaded_segments (0x79a9c : word) = Some W_79a44.
Proof. vm_refl. Qed.
Lemma D_79a44 : decode_any W_79a44 = Some (Op ALU_SLT 13 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a48 : bv 32 := 0x40d006b3.
Lemma F_79a48 : fetch_word Plain.M.loaded_segments (0x79aa0 : word) = Some W_79a48.
Proof. vm_refl. Qed.
Lemma D_79a48 : decode_any W_79a48 = Some (Op ALU_SUB 13 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a4c : bv 32 := 0x00e6f6b3.
Lemma F_79a4c : fetch_word Plain.M.loaded_segments (0x79aa4 : word) = Some W_79a4c.
Proof. vm_refl. Qed.
Lemma D_79a4c : decode_any W_79a4c = Some (Op ALU_AND 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a50 : bv 32 := 0x40b685bb.
Lemma F_79a50 : fetch_word Plain.M.loaded_segments (0x79aa8 : word) = Some W_79a50.
Proof. vm_refl. Qed.
Lemma D_79a50 : decode_any W_79a50 = Some (Op32 ALU_SUB 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a54 : bv 32 := 0x00f585bb.
Lemma F_79a54 : fetch_word Plain.M.loaded_segments (0x79aac : word) = Some W_79a54.
Proof. vm_refl. Qed.
Lemma D_79a54 : decode_any W_79a54 = Some (Op32 ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a58 : bv 32 := 0x00b02733.
Lemma F_79a58 : fetch_word Plain.M.loaded_segments (0x79ab0 : word) = Some W_79a58.
Proof. vm_refl. Qed.
Lemma D_79a58 : decode_any W_79a58 = Some (Op ALU_SLT 14 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a5c : bv 32 := 0x40e0073b.
Lemma F_79a5c : fetch_word Plain.M.loaded_segments (0x79ab4 : word) = Some W_79a5c.
Proof. vm_refl. Qed.
Lemma D_79a5c : decode_any W_79a5c = Some (Op32 ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a60 : bv 32 := 0x00b775b3.
Lemma F_79a60 : fetch_word Plain.M.loaded_segments (0x79ab8 : word) = Some W_79a60.
Proof. vm_refl. Qed.
Lemma D_79a60 : decode_any W_79a60 = Some (Op ALU_AND 11 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a64 : bv 32 := 0x40b7893b.
Lemma F_79a64 : fetch_word Plain.M.loaded_segments (0x79abc : word) = Some W_79a64.
Proof. vm_refl. Qed.
Lemma D_79a64 : decode_any W_79a64 = Some (Op32 ALU_SUB 18 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a68 : bv 32 := 0x21205663.
Lemma F_79a68 : fetch_word Plain.M.loaded_segments (0x79ac0 : word) = Some W_79a68.
Proof. vm_refl. Qed.
Lemma D_79a68 : decode_any W_79a68 = Some (Branch BC_GE 0 18 524, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a6c : bv 32 := 0x07013583.
Lemma F_79a6c : fetch_word Plain.M.loaded_segments (0x79ac4 : word) = Some W_79a6c.
Proof. vm_refl. Qed.
Lemma D_79a6c : decode_any W_79a6c = Some (Load SZ8 true 11 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a70 : bv 32 := 0x43f85713.
Lemma F_79a70 : fetch_word Plain.M.loaded_segments (0x79ac8 : word) = Some W_79a70.
Proof. vm_refl. Qed.
Lemma D_79a70 : decode_any W_79a70 = Some (ShiftImm ALU_SRA 14 16 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a74 : bv 32 := 0x010027b3.
Lemma F_79a74 : fetch_word Plain.M.loaded_segments (0x79acc : word) = Some W_79a74.
Proof. vm_refl. Qed.
Lemma D_79a74 : decode_any W_79a74 = Some (Op ALU_SLT 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a78 : bv 32 := 0x010778b3.
Lemma F_79a78 : fetch_word Plain.M.loaded_segments (0x79ad0 : word) = Some W_79a78.
Proof. vm_refl. Qed.
Lemma D_79a78 : decode_any W_79a78 = Some (Op ALU_AND 17 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a7c : bv 32 := 0x40f00733.
Lemma F_79a7c : fetch_word Plain.M.loaded_segments (0x79ad4 : word) = Some W_79a7c.
Proof. vm_refl. Qed.
Lemma D_79a7c : decode_any W_79a7c = Some (Op ALU_SUB 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a80 : bv 32 := 0x01077733.
Lemma F_79a80 : fetch_word Plain.M.loaded_segments (0x79ad8 : word) = Some W_79a80.
Proof. vm_refl. Qed.
Lemma D_79a80 : decode_any W_79a80 = Some (Op ALU_AND 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a84 : bv 32 := 0x011585b3.
Lemma F_79a84 : fetch_word Plain.M.loaded_segments (0x79adc : word) = Some W_79a84.
Proof. vm_refl. Qed.
Lemma D_79a84 : decode_any W_79a84 = Some (Op ALU_ADD 11 11 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a88 : bv 32 := 0x40c7063b.
Lemma F_79a88 : fetch_word Plain.M.loaded_segments (0x79ae0 : word) = Some W_79a88.
Proof. vm_refl. Qed.
Lemma D_79a88 : decode_any W_79a88 = Some (Op32 ALU_SUB 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a8c : bv 32 := 0x00b6063b.
Lemma F_79a8c : fetch_word Plain.M.loaded_segments (0x79ae4 : word) = Some W_79a8c.
Proof. vm_refl. Qed.
Lemma D_79a8c : decode_any W_79a8c = Some (Op32 ALU_ADD 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a90 : bv 32 := 0x00c027b3.
Lemma F_79a90 : fetch_word Plain.M.loaded_segments (0x79ae8 : word) = Some W_79a90.
Proof. vm_refl. Qed.
Lemma D_79a90 : decode_any W_79a90 = Some (Op ALU_SLT 15 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a94 : bv 32 := 0x40f007bb.
Lemma F_79a94 : fetch_word Plain.M.loaded_segments (0x79aec : word) = Some W_79a94.
Proof. vm_refl. Qed.
Lemma D_79a94 : decode_any W_79a94 = Some (Op32 ALU_SUB 15 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a98 : bv 32 := 0x00c7f633.
Lemma F_79a98 : fetch_word Plain.M.loaded_segments (0x79af0 : word) = Some W_79a98.
Proof. vm_refl. Qed.
Lemma D_79a98 : decode_any W_79a98 = Some (Op ALU_AND 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79a9c : bv 32 := 0x40c589bb.
Lemma F_79a9c : fetch_word Plain.M.loaded_segments (0x79af4 : word) = Some W_79a9c.
Proof. vm_refl. Qed.
Lemma D_79a9c : decode_any W_79a9c = Some (Op32 ALU_SUB 19 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_79aa0 : bv 32 := 0x1d305a63.
Lemma F_79aa0 : fetch_word Plain.M.loaded_segments (0x79af8 : word) = Some W_79aa0.
Proof. vm_refl. Qed.
Lemma D_79aa0 : decode_any W_79aa0 = Some (Branch BC_GE 0 19 468, 4%Z).
Proof. vm_refl. Qed.

