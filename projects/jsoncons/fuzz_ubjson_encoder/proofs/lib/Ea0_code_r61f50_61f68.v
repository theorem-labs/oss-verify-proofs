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

Definition W_7c898 : bv 32 := 0x000c5517.
Lemma F_7c898 : fetch_word Asan.M.loaded_segments (0x7c8e8 : word) = Some W_7c898.
Proof. vm_refl. Qed.
Lemma D_7c898 : decode_any W_7c898 = Some (Auipc 10 197, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c89c : bv 32 := 0x97850513.
Lemma F_7c89c : fetch_word Asan.M.loaded_segments (0x7c8ec : word) = Some W_7c89c.
Proof. vm_refl. Qed.
Lemma D_7c89c : decode_any W_7c89c = Some (OpImm ALU_ADD 10 10 2424, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c8a0 : bv 32 := 0x00054583.
Lemma F_7c8a0 : fetch_word Asan.M.loaded_segments (0x7c8f0 : word) = Some W_7c8a0.
Proof. vm_refl. Qed.
Lemma D_7c8a0 : decode_any W_7c8a0 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c8a4 : bv 32 := 0x00058663.
Lemma F_7c8a4 : fetch_word Asan.M.loaded_segments (0x7c8f4 : word) = Some W_7c8a4.
Proof. vm_refl. Qed.
Lemma D_7c8a4 : decode_any W_7c8a4 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c8a8 : bv 32 := 0x00452503.
Lemma F_7c8a8 : fetch_word Asan.M.loaded_segments (0x7c8f8 : word) = Some W_7c8a8.
Proof. vm_refl. Qed.
Lemma D_7c8a8 : decode_any W_7c8a8 = Some (Load SZ4 true 10 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c8ac : bv 32 := 0x7b8b106f.
Lemma F_7c8ac : fetch_word Asan.M.loaded_segments (0x7c8fc : word) = Some W_7c8ac.
Proof. vm_refl. Qed.
Lemma D_7c8ac : decode_any W_7c8ac = Some (Jal 0 726968, 4%Z).
Proof. vm_refl. Qed.
