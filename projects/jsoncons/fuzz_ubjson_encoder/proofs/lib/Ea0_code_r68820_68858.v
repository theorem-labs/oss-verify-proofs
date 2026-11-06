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

Definition W_833e4 : bv 32 := 0xff010113.
Lemma F_833e4 : fetch_word Asan.M.loaded_segments (0x83434 : word) = Some W_833e4.
Proof. vm_refl. Qed.
Lemma D_833e4 : decode_any W_833e4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_833e8 : bv 32 := 0x00113423.
Lemma F_833e8 : fetch_word Asan.M.loaded_segments (0x83438 : word) = Some W_833e8.
Proof. vm_refl. Qed.
Lemma D_833e8 : decode_any W_833e8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_833ec : bv 32 := 0x62d000ef.
Lemma F_833ec : fetch_word Asan.M.loaded_segments (0x8343c : word) = Some W_833ec.
Proof. vm_refl. Qed.
Lemma D_833ec : decode_any W_833ec = Some (Jal 1 3628, 4%Z).
Proof. vm_refl. Qed.

Definition W_833f0 : bv 32 := 0x00050c63.
Lemma F_833f0 : fetch_word Asan.M.loaded_segments (0x83440 : word) = Some W_833f0.
Proof. vm_refl. Qed.
Lemma D_833f0 : decode_any W_833f0 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_833f4 : bv 32 := 0x7ff50513.
Lemma F_833f4 : fetch_word Asan.M.loaded_segments (0x83444 : word) = Some W_833f4.
Proof. vm_refl. Qed.
Lemma D_833f4 : decode_any W_833f4 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_833f8 : bv 32 := 0x2f150513.
Lemma F_833f8 : fetch_word Asan.M.loaded_segments (0x83448 : word) = Some W_833f8.
Proof. vm_refl. Qed.
Lemma D_833f8 : decode_any W_833f8 = Some (OpImm ALU_ADD 10 10 753, 4%Z).
Proof. vm_refl. Qed.

Definition W_833fc : bv 32 := 0x00813083.
Lemma F_833fc : fetch_word Asan.M.loaded_segments (0x8344c : word) = Some W_833fc.
Proof. vm_refl. Qed.
Lemma D_833fc : decode_any W_833fc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_83400 : bv 32 := 0x01010113.
Lemma F_83400 : fetch_word Asan.M.loaded_segments (0x83450 : word) = Some W_83400.
Proof. vm_refl. Qed.
Lemma D_83400 : decode_any W_83400 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_83404 : bv 32 := 0x00008067.
Lemma F_83404 : fetch_word Asan.M.loaded_segments (0x83454 : word) = Some W_83404.
Proof. vm_refl. Qed.
Lemma D_83404 : decode_any W_83404 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
