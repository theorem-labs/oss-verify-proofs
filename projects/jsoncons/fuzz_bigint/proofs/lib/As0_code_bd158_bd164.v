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

Definition W_bd158 : bv 32 := 0x00020513.
Lemma F_bd158 : fetch_word Asan.M.loaded_segments (0xbd158 : word) = Some W_bd158.
Proof. vm_refl. Qed.
Lemma D_bd158 : decode_any W_bd158 = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd15c : bv 32 := 0xf5c50513.
Lemma F_bd15c : fetch_word Asan.M.loaded_segments (0xbd15c : word) = Some W_bd15c.
Proof. vm_refl. Qed.
Lemma D_bd15c : decode_any W_bd15c = Some (OpImm ALU_ADD 10 10 3932, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd160 : bv 32 := 0x00008067.
Lemma F_bd160 : fetch_word Asan.M.loaded_segments (0xbd160 : word) = Some W_bd160.
Proof. vm_refl. Qed.
Lemma D_bd160 : decode_any W_bd160 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
