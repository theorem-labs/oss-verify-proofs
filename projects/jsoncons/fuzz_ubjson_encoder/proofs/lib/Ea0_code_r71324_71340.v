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

Definition W_8bee8 : bv 32 := 0x00000593.
Lemma F_8bee8 : fetch_word Asan.M.loaded_segments (0x8bf38 : word) = Some W_8bee8.
Proof. vm_refl. Qed.
Lemma D_8bee8 : decode_any W_8bee8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8beec : bv 32 := 0x00b50633.
Lemma F_8beec : fetch_word Asan.M.loaded_segments (0x8bf3c : word) = Some W_8beec.
Proof. vm_refl. Qed.
Lemma D_8beec : decode_any W_8beec = Some (Op ALU_ADD 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bef0 : bv 32 := 0x00064603.
Lemma F_8bef0 : fetch_word Asan.M.loaded_segments (0x8bf40 : word) = Some W_8bef0.
Proof. vm_refl. Qed.
Lemma D_8bef0 : decode_any W_8bef0 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bef4 : bv 32 := 0x00158593.
Lemma F_8bef4 : fetch_word Asan.M.loaded_segments (0x8bf44 : word) = Some W_8bef4.
Proof. vm_refl. Qed.
Lemma D_8bef4 : decode_any W_8bef4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bef8 : bv 32 := 0xfe061ae3.
Lemma F_8bef8 : fetch_word Asan.M.loaded_segments (0x8bf48 : word) = Some W_8bef8.
Proof. vm_refl. Qed.
Lemma D_8bef8 : decode_any W_8bef8 = Some (Branch BC_NE 12 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_8befc : bv 32 := 0xfff58513.
Lemma F_8befc : fetch_word Asan.M.loaded_segments (0x8bf4c : word) = Some W_8befc.
Proof. vm_refl. Qed.
Lemma D_8befc : decode_any W_8befc = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8bf00 : bv 32 := 0x00008067.
Lemma F_8bf00 : fetch_word Asan.M.loaded_segments (0x8bf50 : word) = Some W_8bf00.
Proof. vm_refl. Qed.
Lemma D_8bf00 : decode_any W_8bf00 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
