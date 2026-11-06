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

Definition W_12c428 : bv 32 := 0x00020593.
Lemma F_12c428 : fetch_word Asan.M.loaded_segments (0x12c46c : word) = Some W_12c428.
Proof. vm_refl. Qed.
Lemma D_12c428 : decode_any W_12c428 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c42c : bv 32 := 0x00053603.
Lemma F_12c42c : fetch_word Asan.M.loaded_segments (0x12c470 : word) = Some W_12c42c.
Proof. vm_refl. Qed.
Lemma D_12c42c : decode_any W_12c42c = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c430 : bv 32 := 0xff85b583.
Lemma F_12c430 : fetch_word Asan.M.loaded_segments (0x12c474 : word) = Some W_12c430.
Proof. vm_refl. Qed.
Lemma D_12c430 : decode_any W_12c430 = Some (Load SZ8 true 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c434 : bv 32 := 0x00853503.
Lemma F_12c434 : fetch_word Asan.M.loaded_segments (0x12c478 : word) = Some W_12c434.
Proof. vm_refl. Qed.
Lemma D_12c434 : decode_any W_12c434 = Some (Load SZ8 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c438 : bv 32 := 0x00361613.
Lemma F_12c438 : fetch_word Asan.M.loaded_segments (0x12c47c : word) = Some W_12c438.
Proof. vm_refl. Qed.
Lemma D_12c438 : decode_any W_12c438 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c43c : bv 32 := 0x00c585b3.
Lemma F_12c43c : fetch_word Asan.M.loaded_segments (0x12c480 : word) = Some W_12c43c.
Proof. vm_refl. Qed.
Lemma D_12c43c : decode_any W_12c43c = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c440 : bv 32 := 0x0005b583.
Lemma F_12c440 : fetch_word Asan.M.loaded_segments (0x12c484 : word) = Some W_12c440.
Proof. vm_refl. Qed.
Lemma D_12c440 : decode_any W_12c440 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c444 : bv 32 := 0x00b50533.
Lemma F_12c444 : fetch_word Asan.M.loaded_segments (0x12c488 : word) = Some W_12c444.
Proof. vm_refl. Qed.
Lemma D_12c444 : decode_any W_12c444 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_12c448 : bv 32 := 0x00008067.
Lemma F_12c448 : fetch_word Asan.M.loaded_segments (0x12c48c : word) = Some W_12c448.
Proof. vm_refl. Qed.
Lemma D_12c448 : decode_any W_12c448 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
