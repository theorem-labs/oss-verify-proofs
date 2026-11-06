(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_a8620 : bv 32 := 0x00096517.
Lemma F_a8620 : fetch_word AsanUbsan.M.loaded_segments (0xa8670 : word) = Some W_a8620.
Proof. vm_refl. Qed.
Lemma D_a8620 : decode_any W_a8620 = Some (Auipc 10 150, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8624 : bv 32 := 0xeb853503.
Lemma F_a8624 : fetch_word AsanUbsan.M.loaded_segments (0xa8674 : word) = Some W_a8624.
Proof. vm_refl. Qed.
Lemma D_a8624 : decode_any W_a8624 = Some (Load SZ8 true 10 10 3768, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8628 : bv 32 := 0x00450533.
Lemma F_a8628 : fetch_word AsanUbsan.M.loaded_segments (0xa8678 : word) = Some W_a8628.
Proof. vm_refl. Qed.
Lemma D_a8628 : decode_any W_a8628 = Some (Op ALU_ADD 10 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a862c : bv 32 := 0x00052503.
Lemma F_a862c : fetch_word AsanUbsan.M.loaded_segments (0xa867c : word) = Some W_a862c.
Proof. vm_refl. Qed.
Lemma D_a862c : decode_any W_a862c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8630 : bv 32 := 0x00a02533.
Lemma F_a8630 : fetch_word AsanUbsan.M.loaded_segments (0xa8680 : word) = Some W_a8630.
Proof. vm_refl. Qed.
Lemma D_a8630 : decode_any W_a8630 = Some (Op ALU_SLT 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_a8634 : bv 32 := 0x00008067.
Lemma F_a8634 : fetch_word AsanUbsan.M.loaded_segments (0xa8684 : word) = Some W_a8634.
Proof. vm_refl. Qed.
Lemma D_a8634 : decode_any W_a8634 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
