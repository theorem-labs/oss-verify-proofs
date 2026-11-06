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

Definition W_cc49c : bv 32 := 0x00020593.
Lemma F_cc49c : fetch_word Asan.M.loaded_segments (0xcc49c : word) = Some W_cc49c.
Proof. vm_refl. Qed.
Lemma D_cc49c : decode_any W_cc49c = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc4a0 : bv 32 := 0x00053603.
Lemma F_cc4a0 : fetch_word Asan.M.loaded_segments (0xcc4a0 : word) = Some W_cc4a0.
Proof. vm_refl. Qed.
Lemma D_cc4a0 : decode_any W_cc4a0 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc4a4 : bv 32 := 0xff85b583.
Lemma F_cc4a4 : fetch_word Asan.M.loaded_segments (0xcc4a4 : word) = Some W_cc4a4.
Proof. vm_refl. Qed.
Lemma D_cc4a4 : decode_any W_cc4a4 = Some (Load SZ8 true 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc4a8 : bv 32 := 0x00853503.
Lemma F_cc4a8 : fetch_word Asan.M.loaded_segments (0xcc4a8 : word) = Some W_cc4a8.
Proof. vm_refl. Qed.
Lemma D_cc4a8 : decode_any W_cc4a8 = Some (Load SZ8 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc4ac : bv 32 := 0x00361613.
Lemma F_cc4ac : fetch_word Asan.M.loaded_segments (0xcc4ac : word) = Some W_cc4ac.
Proof. vm_refl. Qed.
Lemma D_cc4ac : decode_any W_cc4ac = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc4b0 : bv 32 := 0x00c585b3.
Lemma F_cc4b0 : fetch_word Asan.M.loaded_segments (0xcc4b0 : word) = Some W_cc4b0.
Proof. vm_refl. Qed.
Lemma D_cc4b0 : decode_any W_cc4b0 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc4b4 : bv 32 := 0x0005b583.
Lemma F_cc4b4 : fetch_word Asan.M.loaded_segments (0xcc4b4 : word) = Some W_cc4b4.
Proof. vm_refl. Qed.
Lemma D_cc4b4 : decode_any W_cc4b4 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc4b8 : bv 32 := 0x00b50533.
Lemma F_cc4b8 : fetch_word Asan.M.loaded_segments (0xcc4b8 : word) = Some W_cc4b8.
Proof. vm_refl. Qed.
Lemma D_cc4b8 : decode_any W_cc4b8 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_cc4bc : bv 32 := 0x00008067.
Lemma F_cc4bc : fetch_word Asan.M.loaded_segments (0xcc4bc : word) = Some W_cc4bc.
Proof. vm_refl. Qed.
Lemma D_cc4bc : decode_any W_cc4bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
