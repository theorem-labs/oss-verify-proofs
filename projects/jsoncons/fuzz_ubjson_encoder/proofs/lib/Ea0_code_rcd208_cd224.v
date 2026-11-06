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

Definition W_12e070 : bv 32 := 0x00020593.
Lemma F_12e070 : fetch_word Asan.M.loaded_segments (0x12e0b4 : word) = Some W_12e070.
Proof. vm_refl. Qed.
Lemma D_12e070 : decode_any W_12e070 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12e074 : bv 32 := 0xfa85b583.
Lemma F_12e074 : fetch_word Asan.M.loaded_segments (0x12e0b8 : word) = Some W_12e074.
Proof. vm_refl. Qed.
Lemma D_12e074 : decode_any W_12e074 = Some (Load SZ8 true 11 11 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_12e078 : bv 32 := 0x02051513.
Lemma F_12e078 : fetch_word Asan.M.loaded_segments (0x12e0bc : word) = Some W_12e078.
Proof. vm_refl. Qed.
Lemma D_12e078 : decode_any W_12e078 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_12e07c : bv 32 := 0x01d55513.
Lemma F_12e07c : fetch_word Asan.M.loaded_segments (0x12e0c0 : word) = Some W_12e07c.
Proof. vm_refl. Qed.
Lemma D_12e07c : decode_any W_12e07c = Some (ShiftImm ALU_SRL 10 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_12e080 : bv 32 := 0x00a58533.
Lemma F_12e080 : fetch_word Asan.M.loaded_segments (0x12e0c4 : word) = Some W_12e080.
Proof. vm_refl. Qed.
Lemma D_12e080 : decode_any W_12e080 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_12e084 : bv 32 := 0x00053503.
Lemma F_12e084 : fetch_word Asan.M.loaded_segments (0x12e0c8 : word) = Some W_12e084.
Proof. vm_refl. Qed.
Lemma D_12e084 : decode_any W_12e084 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_12e088 : bv 32 := 0x00008067.
Lemma F_12e088 : fetch_word Asan.M.loaded_segments (0x12e0cc : word) = Some W_12e088.
Proof. vm_refl. Qed.
Lemma D_12e088 : decode_any W_12e088 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
