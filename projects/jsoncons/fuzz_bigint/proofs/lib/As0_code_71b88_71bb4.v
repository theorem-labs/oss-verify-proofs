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

Definition W_71b88 : bv 32 := 0x00064697.
Lemma F_71b88 : fetch_word Asan.M.loaded_segments (0x71b88 : word) = Some W_71b88.
Proof. vm_refl. Qed.
Lemma D_71b88 : decode_any W_71b88 = Some (Auipc 13 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b8c : bv 32 := 0xd706b683.
Lemma F_71b8c : fetch_word Asan.M.loaded_segments (0x71b8c : word) = Some W_71b8c.
Proof. vm_refl. Qed.
Lemma D_71b8c : decode_any W_71b8c = Some (Load SZ8 true 13 13 3440, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b90 : bv 32 := 0x00068a63.
Lemma F_71b90 : fetch_word Asan.M.loaded_segments (0x71b90 : word) = Some W_71b90.
Proof. vm_refl. Qed.
Lemma D_71b90 : decode_any W_71b90 = Some (Branch BC_EQ 13 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b94 : bv 32 := 0x00400693.
Lemma F_71b94 : fetch_word Asan.M.loaded_segments (0x71b94 : word) = Some W_71b94.
Proof. vm_refl. Qed.
Lemma D_71b94 : decode_any W_71b94 = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b98 : bv 32 := 0x00d60663.
Lemma F_71b98 : fetch_word Asan.M.loaded_segments (0x71b98 : word) = Some W_71b98.
Proof. vm_refl. Qed.
Lemma D_71b98 : decode_any W_71b98 = Some (Branch BC_EQ 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_71b9c : bv 32 := 0x0000051b.
Lemma F_71b9c : fetch_word Asan.M.loaded_segments (0x71b9c : word) = Some W_71b9c.
Proof. vm_refl. Qed.
Lemma D_71b9c : decode_any W_71b9c = Some (OpImm32 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71ba0 : bv 32 := 0x00008067.
Lemma F_71ba0 : fetch_word Asan.M.loaded_segments (0x71ba0 : word) = Some W_71ba0.
Proof. vm_refl. Qed.
Lemma D_71ba0 : decode_any W_71ba0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71ba4 : bv 32 := 0x0e900893.
Lemma F_71ba4 : fetch_word Asan.M.loaded_segments (0x71ba4 : word) = Some W_71ba4.
Proof. vm_refl. Qed.
Lemma D_71ba4 : decode_any W_71ba4 = Some (OpImm ALU_ADD 17 0 233, 4%Z).
Proof. vm_refl. Qed.

Definition W_71ba8 : bv 32 := 0x00000073.
Lemma F_71ba8 : fetch_word Asan.M.loaded_segments (0x71ba8 : word) = Some W_71ba8.
Proof. vm_refl. Qed.
Lemma D_71ba8 : decode_any W_71ba8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_71ba8 : is_ecall W_71ba8 = true.
Proof. reflexivity. Qed.

Definition W_71bac : bv 32 := 0x0005051b.
Lemma F_71bac : fetch_word Asan.M.loaded_segments (0x71bac : word) = Some W_71bac.
Proof. vm_refl. Qed.
Lemma D_71bac : decode_any W_71bac = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71bb0 : bv 32 := 0x00008067.
Lemma F_71bb0 : fetch_word Asan.M.loaded_segments (0x71bb0 : word) = Some W_71bb0.
Proof. vm_refl. Qed.
Lemma D_71bb0 : decode_any W_71bb0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
