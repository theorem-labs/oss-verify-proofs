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

Definition W_b0430 : bv 32 := 0x825af06f.
Lemma F_b0430 : fetch_word Asan.M.loaded_segments (0xb0430 : word) = Some W_b0430.
Proof. vm_refl. Qed.
Lemma D_b0430 : decode_any W_b0430 = Some (Jal 0 1767460, 4%Z).
Proof. vm_refl. Qed.

Definition W_b0434 : bv 32 := 0xffdff06f.
Lemma F_b0434 : fetch_word Asan.M.loaded_segments (0xb0434 : word) = Some W_b0434.
Proof. vm_refl. Qed.
Lemma D_b0434 : decode_any W_b0434 = Some (Jal 0 2097148, 4%Z).
Proof. vm_refl. Qed.
