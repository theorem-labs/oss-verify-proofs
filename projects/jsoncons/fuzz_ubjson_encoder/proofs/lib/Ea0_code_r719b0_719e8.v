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

Definition W_8c590 : bv 32 := 0xfffff637.
Lemma F_8c590 : fetch_word Asan.M.loaded_segments (0x8c5e0 : word) = Some W_8c590.
Proof. vm_refl. Qed.
Lemma D_8c590 : decode_any W_8c590 = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c594 : bv 32 := 0x0016069b.
Lemma F_8c594 : fetch_word Asan.M.loaded_segments (0x8c5e4 : word) = Some W_8c594.
Proof. vm_refl. Qed.
Lemma D_8c594 : decode_any W_8c594 = Some (OpImm32 13 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c598 : bv 32 := 0x00d56863.
Lemma F_8c598 : fetch_word Asan.M.loaded_segments (0x8c5e8 : word) = Some W_8c598.
Proof. vm_refl. Qed.
Lemma D_8c598 : decode_any W_8c598 = Some (Branch BC_LTU 10 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5a8 : bv 32 := 0x00a63533.
Lemma F_8c5a8 : fetch_word Asan.M.loaded_segments (0x8c5f8 : word) = Some W_8c5a8.
Proof. vm_refl. Qed.
Lemma D_8c5a8 : decode_any W_8c5a8 = Some (Op ALU_SLTU 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5ac : bv 32 := 0x00008067.
Lemma F_8c5ac : fetch_word Asan.M.loaded_segments (0x8c5fc : word) = Some W_8c5ac.
Proof. vm_refl. Qed.
Lemma D_8c5ac : decode_any W_8c5ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5b0 : bv 32 := 0x0de00893.
Lemma F_8c5b0 : fetch_word Asan.M.loaded_segments (0x8c600 : word) = Some W_8c5b0.
Proof. vm_refl. Qed.
Lemma D_8c5b0 : decode_any W_8c5b0 = Some (OpImm ALU_ADD 17 0 222, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5b4 : bv 32 := 0x00000073.
Lemma F_8c5b4 : fetch_word Asan.M.loaded_segments (0x8c604 : word) = Some W_8c5b4.
Proof. vm_refl. Qed.
Lemma D_8c5b4 : decode_any W_8c5b4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_8c5b4 : is_ecall W_8c5b4 = true.
Proof. reflexivity. Qed.

Definition W_8c5b8 : bv 32 := 0x00008067.
Lemma F_8c5b8 : fetch_word Asan.M.loaded_segments (0x8c608 : word) = Some W_8c5b8.
Proof. vm_refl. Qed.
Lemma D_8c5b8 : decode_any W_8c5b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5bc : bv 32 := 0x0d700893.
Lemma F_8c5bc : fetch_word Asan.M.loaded_segments (0x8c60c : word) = Some W_8c5bc.
Proof. vm_refl. Qed.
Lemma D_8c5bc : decode_any W_8c5bc = Some (OpImm ALU_ADD 17 0 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_8c5c0 : bv 32 := 0x00000073.
Lemma F_8c5c0 : fetch_word Asan.M.loaded_segments (0x8c610 : word) = Some W_8c5c0.
Proof. vm_refl. Qed.
Lemma D_8c5c0 : decode_any W_8c5c0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_8c5c0 : is_ecall W_8c5c0 = true.
Proof. reflexivity. Qed.

Definition W_8c5c4 : bv 32 := 0x00008067.
Lemma F_8c5c4 : fetch_word Asan.M.loaded_segments (0x8c614 : word) = Some W_8c5c4.
Proof. vm_refl. Qed.
Lemma D_8c5c4 : decode_any W_8c5c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
