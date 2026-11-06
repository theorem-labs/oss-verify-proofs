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

Definition W_714b4 : bv 32 := 0x00000593.
Lemma F_714b4 : fetch_word Asan.M.loaded_segments (0x714b4 : word) = Some W_714b4.
Proof. vm_refl. Qed.
Lemma D_714b4 : decode_any W_714b4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_714b8 : bv 32 := 0x00b50633.
Lemma F_714b8 : fetch_word Asan.M.loaded_segments (0x714b8 : word) = Some W_714b8.
Proof. vm_refl. Qed.
Lemma D_714b8 : decode_any W_714b8 = Some (Op ALU_ADD 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_714bc : bv 32 := 0x00064603.
Lemma F_714bc : fetch_word Asan.M.loaded_segments (0x714bc : word) = Some W_714bc.
Proof. vm_refl. Qed.
Lemma D_714bc : decode_any W_714bc = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_714c0 : bv 32 := 0x00158593.
Lemma F_714c0 : fetch_word Asan.M.loaded_segments (0x714c0 : word) = Some W_714c0.
Proof. vm_refl. Qed.
Lemma D_714c0 : decode_any W_714c0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_714c4 : bv 32 := 0xfe061ae3.
Lemma F_714c4 : fetch_word Asan.M.loaded_segments (0x714c4 : word) = Some W_714c4.
Proof. vm_refl. Qed.
Lemma D_714c4 : decode_any W_714c4 = Some (Branch BC_NE 12 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_714c8 : bv 32 := 0xfff58513.
Lemma F_714c8 : fetch_word Asan.M.loaded_segments (0x714c8 : word) = Some W_714c8.
Proof. vm_refl. Qed.
Lemma D_714c8 : decode_any W_714c8 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_714cc : bv 32 := 0x00008067.
Lemma F_714cc : fetch_word Asan.M.loaded_segments (0x714cc : word) = Some W_714cc.
Proof. vm_refl. Qed.
Lemma D_714cc : decode_any W_714cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
