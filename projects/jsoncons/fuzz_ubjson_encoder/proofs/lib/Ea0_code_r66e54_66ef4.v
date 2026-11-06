(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_81a18 : bv 32 := 0xff010113.
Lemma F_81a18 : fetch_word Asan.M.loaded_segments (0x81a68 : word) = Some W_81a18.
Proof. vm_refl. Qed.
Lemma D_81a18 : decode_any W_81a18 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a1c : bv 32 := 0x00113423.
Lemma F_81a1c : fetch_word Asan.M.loaded_segments (0x81a6c : word) = Some W_81a1c.
Proof. vm_refl. Qed.
Lemma D_81a1c : decode_any W_81a1c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a20 : bv 32 := 0x00813023.
Lemma F_81a20 : fetch_word Asan.M.loaded_segments (0x81a70 : word) = Some W_81a20.
Proof. vm_refl. Qed.
Lemma D_81a20 : decode_any W_81a20 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a24 : bv 32 := 0x000c1517.
Lemma F_81a24 : fetch_word Asan.M.loaded_segments (0x81a74 : word) = Some W_81a24.
Proof. vm_refl. Qed.
Lemma D_81a24 : decode_any W_81a24 = Some (Auipc 10 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a28 : bv 32 := 0xc6450413.
Lemma F_81a28 : fetch_word Asan.M.loaded_segments (0x81a78 : word) = Some W_81a28.
Proof. vm_refl. Qed.
Lemma D_81a28 : decode_any W_81a28 = Some (OpImm ALU_ADD 8 10 3172, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a2c : bv 32 := 0x00040583.
Lemma F_81a2c : fetch_word Asan.M.loaded_segments (0x81a7c : word) = Some W_81a2c.
Proof. vm_refl. Qed.
Lemma D_81a2c : decode_any W_81a2c = Some (Load SZ1 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a30 : bv 32 := 0x00100513.
Lemma F_81a30 : fetch_word Asan.M.loaded_segments (0x81a80 : word) = Some W_81a30.
Proof. vm_refl. Qed.
Lemma D_81a30 : decode_any W_81a30 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a34 : bv 32 := 0x0230000f.
Lemma F_81a34 : fetch_word Asan.M.loaded_segments (0x81a84 : word) = Some W_81a34.
Proof. vm_refl. Qed.
Lemma D_81a34 : decode_any W_81a34 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a38 : bv 32 := 0x00a59a63.
Lemma F_81a38 : fetch_word Asan.M.loaded_segments (0x81a88 : word) = Some W_81a38.
Proof. vm_refl. Qed.
Lemma D_81a38 : decode_any W_81a38 = Some (Branch BC_NE 11 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a3c : bv 32 := 0x00813083.
Lemma F_81a3c : fetch_word Asan.M.loaded_segments (0x81a8c : word) = Some W_81a3c.
Proof. vm_refl. Qed.
Lemma D_81a3c : decode_any W_81a3c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a40 : bv 32 := 0x00013403.
Lemma F_81a40 : fetch_word Asan.M.loaded_segments (0x81a90 : word) = Some W_81a40.
Proof. vm_refl. Qed.
Lemma D_81a40 : decode_any W_81a40 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a44 : bv 32 := 0x01010113.
Lemma F_81a44 : fetch_word Asan.M.loaded_segments (0x81a94 : word) = Some W_81a44.
Proof. vm_refl. Qed.
Lemma D_81a44 : decode_any W_81a44 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_81a48 : bv 32 := 0x00008067.
Lemma F_81a48 : fetch_word Asan.M.loaded_segments (0x81a98 : word) = Some W_81a48.
Proof. vm_refl. Qed.
Lemma D_81a48 : decode_any W_81a48 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
