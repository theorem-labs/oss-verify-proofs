(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_620e0 : bv 32 := 0x0007b517.
Lemma F_620e0 : fetch_word Asan.M.loaded_segments (0x620e0 : word) = Some W_620e0.
Proof. vm_refl. Qed.
Lemma D_620e0 : decode_any W_620e0 = Some (Auipc 10 123, 4%Z).
Proof. vm_refl. Qed.

Definition W_620e4 : bv 32 := 0x2c050513.
Lemma F_620e4 : fetch_word Asan.M.loaded_segments (0x620e4 : word) = Some W_620e4.
Proof. vm_refl. Qed.
Lemma D_620e4 : decode_any W_620e4 = Some (OpImm ALU_ADD 10 10 704, 4%Z).
Proof. vm_refl. Qed.

Definition W_620e8 : bv 32 := 0x00054583.
Lemma F_620e8 : fetch_word Asan.M.loaded_segments (0x620e8 : word) = Some W_620e8.
Proof. vm_refl. Qed.
Lemma D_620e8 : decode_any W_620e8 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_620ec : bv 32 := 0x00058663.
Lemma F_620ec : fetch_word Asan.M.loaded_segments (0x620ec : word) = Some W_620ec.
Proof. vm_refl. Qed.
Lemma D_620ec : decode_any W_620ec = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_620f0 : bv 32 := 0x00452503.
Lemma F_620f0 : fetch_word Asan.M.loaded_segments (0x620f0 : word) = Some W_620f0.
Proof. vm_refl. Qed.
Lemma D_620f0 : decode_any W_620f0 = Some (Load SZ4 true 10 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_620f4 : bv 32 := 0x45c6b06f.
Lemma F_620f4 : fetch_word Asan.M.loaded_segments (0x620f4 : word) = Some W_620f4.
Proof. vm_refl. Qed.
Lemma D_620f4 : decode_any W_620f4 = Some (Jal 0 439388, 4%Z).
Proof. vm_refl. Qed.
