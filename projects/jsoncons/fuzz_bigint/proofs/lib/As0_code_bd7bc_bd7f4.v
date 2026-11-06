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

Definition W_bd7bc : bv 32 := 0xfffff5b7.
Lemma F_bd7bc : fetch_word Asan.M.loaded_segments (0xbd7bc : word) = Some W_bd7bc.
Proof. vm_refl. Qed.
Lemma D_bd7bc : decode_any W_bd7bc = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd7c0 : bv 32 := 0x0015859b.
Lemma F_bd7c0 : fetch_word Asan.M.loaded_segments (0xbd7c0 : word) = Some W_bd7c0.
Proof. vm_refl. Qed.
Lemma D_bd7c0 : decode_any W_bd7c0 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd7c4 : bv 32 := 0x02b56663.
Lemma F_bd7c4 : fetch_word Asan.M.loaded_segments (0xbd7c4 : word) = Some W_bd7c4.
Proof. vm_refl. Qed.
Lemma D_bd7c4 : decode_any W_bd7c4 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd7c8 : bv 32 := 0xff010113.
Lemma F_bd7c8 : fetch_word Asan.M.loaded_segments (0xbd7c8 : word) = Some W_bd7c8.
Proof. vm_refl. Qed.
Lemma D_bd7c8 : decode_any W_bd7c8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd7cc : bv 32 := 0x00113423.
Lemma F_bd7cc : fetch_word Asan.M.loaded_segments (0xbd7cc : word) = Some W_bd7cc.
Proof. vm_refl. Qed.
Lemma D_bd7cc : decode_any W_bd7cc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd7d0 : bv 32 := 0x00813023.
Lemma F_bd7d0 : fetch_word Asan.M.loaded_segments (0xbd7d0 : word) = Some W_bd7d0.
Proof. vm_refl. Qed.
Lemma D_bd7d0 : decode_any W_bd7d0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd7d4 : bv 32 := 0x40a0043b.
Lemma F_bd7d4 : fetch_word Asan.M.loaded_segments (0xbd7d4 : word) = Some W_bd7d4.
Proof. vm_refl. Qed.
Lemma D_bd7d4 : decode_any W_bd7d4 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd7d8 : bv 32 := 0x981ff0ef.
Lemma F_bd7d8 : fetch_word Asan.M.loaded_segments (0xbd7d8 : word) = Some W_bd7d8.
Proof. vm_refl. Qed.
Lemma D_bd7d8 : decode_any W_bd7d8 = Some (Jal 1 2095488, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd7dc : bv 32 := 0x00852023.
Lemma F_bd7dc : fetch_word Asan.M.loaded_segments (0xbd7dc : word) = Some W_bd7dc.
Proof. vm_refl. Qed.
Lemma D_bd7dc : decode_any W_bd7dc = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd7e0 : bv 32 := 0xfff00513.
Lemma F_bd7e0 : fetch_word Asan.M.loaded_segments (0xbd7e0 : word) = Some W_bd7e0.
Proof. vm_refl. Qed.
Lemma D_bd7e0 : decode_any W_bd7e0 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd7e4 : bv 32 := 0x00813083.
Lemma F_bd7e4 : fetch_word Asan.M.loaded_segments (0xbd7e4 : word) = Some W_bd7e4.
Proof. vm_refl. Qed.
Lemma D_bd7e4 : decode_any W_bd7e4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd7e8 : bv 32 := 0x00013403.
Lemma F_bd7e8 : fetch_word Asan.M.loaded_segments (0xbd7e8 : word) = Some W_bd7e8.
Proof. vm_refl. Qed.
Lemma D_bd7e8 : decode_any W_bd7e8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd7ec : bv 32 := 0x01010113.
Lemma F_bd7ec : fetch_word Asan.M.loaded_segments (0xbd7ec : word) = Some W_bd7ec.
Proof. vm_refl. Qed.
Lemma D_bd7ec : decode_any W_bd7ec = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_bd7f0 : bv 32 := 0x00008067.
Lemma F_bd7f0 : fetch_word Asan.M.loaded_segments (0xbd7f0 : word) = Some W_bd7f0.
Proof. vm_refl. Qed.
Lemma D_bd7f0 : decode_any W_bd7f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
