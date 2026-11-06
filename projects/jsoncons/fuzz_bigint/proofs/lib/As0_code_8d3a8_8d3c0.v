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

Definition W_8d3a8 : bv 32 := 0x00049517.
Lemma F_8d3a8 : fetch_word Asan.M.loaded_segments (0x8d3a8 : word) = Some W_8d3a8.
Proof. vm_refl. Qed.
Lemma D_8d3a8 : decode_any W_8d3a8 = Some (Auipc 10 73, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d3ac : bv 32 := 0x16853503.
Lemma F_8d3ac : fetch_word Asan.M.loaded_segments (0x8d3ac : word) = Some W_8d3ac.
Proof. vm_refl. Qed.
Lemma D_8d3ac : decode_any W_8d3ac = Some (Load SZ8 true 10 10 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d3b0 : bv 32 := 0x00450533.
Lemma F_8d3b0 : fetch_word Asan.M.loaded_segments (0x8d3b0 : word) = Some W_8d3b0.
Proof. vm_refl. Qed.
Lemma D_8d3b0 : decode_any W_8d3b0 = Some (Op ALU_ADD 10 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d3b4 : bv 32 := 0x00052503.
Lemma F_8d3b4 : fetch_word Asan.M.loaded_segments (0x8d3b4 : word) = Some W_8d3b4.
Proof. vm_refl. Qed.
Lemma D_8d3b4 : decode_any W_8d3b4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d3b8 : bv 32 := 0x00a02533.
Lemma F_8d3b8 : fetch_word Asan.M.loaded_segments (0x8d3b8 : word) = Some W_8d3b8.
Proof. vm_refl. Qed.
Lemma D_8d3b8 : decode_any W_8d3b8 = Some (Op ALU_SLT 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d3bc : bv 32 := 0x00008067.
Lemma F_8d3bc : fetch_word Asan.M.loaded_segments (0x8d3bc : word) = Some W_8d3bc.
Proof. vm_refl. Qed.
Lemma D_8d3bc : decode_any W_8d3bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
