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

Definition W_cd550 : bv 32 := 0x00020593.
Lemma F_cd550 : fetch_word Asan.M.loaded_segments (0xcd550 : word) = Some W_cd550.
Proof. vm_refl. Qed.
Lemma D_cd550 : decode_any W_cd550 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cd554 : bv 32 := 0xfa85b583.
Lemma F_cd554 : fetch_word Asan.M.loaded_segments (0xcd554 : word) = Some W_cd554.
Proof. vm_refl. Qed.
Lemma D_cd554 : decode_any W_cd554 = Some (Load SZ8 true 11 11 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_cd558 : bv 32 := 0x02051513.
Lemma F_cd558 : fetch_word Asan.M.loaded_segments (0xcd558 : word) = Some W_cd558.
Proof. vm_refl. Qed.
Lemma D_cd558 : decode_any W_cd558 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cd55c : bv 32 := 0x01d55513.
Lemma F_cd55c : fetch_word Asan.M.loaded_segments (0xcd55c : word) = Some W_cd55c.
Proof. vm_refl. Qed.
Lemma D_cd55c : decode_any W_cd55c = Some (ShiftImm ALU_SRL 10 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_cd560 : bv 32 := 0x00a58533.
Lemma F_cd560 : fetch_word Asan.M.loaded_segments (0xcd560 : word) = Some W_cd560.
Proof. vm_refl. Qed.
Lemma D_cd560 : decode_any W_cd560 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_cd564 : bv 32 := 0x00053503.
Lemma F_cd564 : fetch_word Asan.M.loaded_segments (0xcd564 : word) = Some W_cd564.
Proof. vm_refl. Qed.
Lemma D_cd564 : decode_any W_cd564 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cd568 : bv 32 := 0x00008067.
Lemma F_cd568 : fetch_word Asan.M.loaded_segments (0xcd568 : word) = Some W_cd568.
Proof. vm_refl. Qed.
Lemma D_cd568 : decode_any W_cd568 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
