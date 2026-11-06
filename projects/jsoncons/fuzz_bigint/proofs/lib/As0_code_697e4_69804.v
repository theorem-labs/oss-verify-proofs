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

Definition W_697e4 : bv 32 := 0xff010113.
Lemma F_697e4 : fetch_word Asan.M.loaded_segments (0x697e4 : word) = Some W_697e4.
Proof. vm_refl. Qed.
Lemma D_697e4 : decode_any W_697e4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_697e8 : bv 32 := 0x00113423.
Lemma F_697e8 : fetch_word Asan.M.loaded_segments (0x697e8 : word) = Some W_697e8.
Proof. vm_refl. Qed.
Lemma D_697e8 : decode_any W_697e8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_697ec : bv 32 := 0x8f5f80ef.
Lemma F_697ec : fetch_word Asan.M.loaded_segments (0x697ec : word) = Some W_697ec.
Proof. vm_refl. Qed.
Lemma D_697ec : decode_any W_697ec = Some (Jal 1 2066676, 4%Z).
Proof. vm_refl. Qed.

Definition W_697f0 : bv 32 := 0x00050463.
Lemma F_697f0 : fetch_word Asan.M.loaded_segments (0x697f0 : word) = Some W_697f0.
Proof. vm_refl. Qed.
Lemma D_697f0 : decode_any W_697f0 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_697f4 : bv 32 := 0x09853503.
Lemma F_697f4 : fetch_word Asan.M.loaded_segments (0x697f4 : word) = Some W_697f4.
Proof. vm_refl. Qed.
Lemma D_697f4 : decode_any W_697f4 = Some (Load SZ8 true 10 10 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_697f8 : bv 32 := 0x00813083.
Lemma F_697f8 : fetch_word Asan.M.loaded_segments (0x697f8 : word) = Some W_697f8.
Proof. vm_refl. Qed.
Lemma D_697f8 : decode_any W_697f8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_697fc : bv 32 := 0x01010113.
Lemma F_697fc : fetch_word Asan.M.loaded_segments (0x697fc : word) = Some W_697fc.
Proof. vm_refl. Qed.
Lemma D_697fc : decode_any W_697fc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_69800 : bv 32 := 0x00008067.
Lemma F_69800 : fetch_word Asan.M.loaded_segments (0x69800 : word) = Some W_69800.
Proof. vm_refl. Qed.
Lemma D_69800 : decode_any W_69800 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
