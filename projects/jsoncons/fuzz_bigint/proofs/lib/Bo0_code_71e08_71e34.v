(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_71e08 : bv 32 := 0x00064697.
Lemma F_71e08 : fetch_word AsanUbsan.M.loaded_segments (0x71e08 : word) = Some W_71e08.
Proof. vm_refl. Qed.
Lemma D_71e08 : decode_any W_71e08 = Some (Auipc 13 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_71e0c : bv 32 := 0x7006b683.
Lemma F_71e0c : fetch_word AsanUbsan.M.loaded_segments (0x71e0c : word) = Some W_71e0c.
Proof. vm_refl. Qed.
Lemma D_71e0c : decode_any W_71e0c = Some (Load SZ8 true 13 13 1792, 4%Z).
Proof. vm_refl. Qed.

Definition W_71e10 : bv 32 := 0x00068a63.
Lemma F_71e10 : fetch_word AsanUbsan.M.loaded_segments (0x71e10 : word) = Some W_71e10.
Proof. vm_refl. Qed.
Lemma D_71e10 : decode_any W_71e10 = Some (Branch BC_EQ 13 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_71e14 : bv 32 := 0x00400693.
Lemma F_71e14 : fetch_word AsanUbsan.M.loaded_segments (0x71e14 : word) = Some W_71e14.
Proof. vm_refl. Qed.
Lemma D_71e14 : decode_any W_71e14 = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_71e18 : bv 32 := 0x00d60663.
Lemma F_71e18 : fetch_word AsanUbsan.M.loaded_segments (0x71e18 : word) = Some W_71e18.
Proof. vm_refl. Qed.
Lemma D_71e18 : decode_any W_71e18 = Some (Branch BC_EQ 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_71e1c : bv 32 := 0x0000051b.
Lemma F_71e1c : fetch_word AsanUbsan.M.loaded_segments (0x71e1c : word) = Some W_71e1c.
Proof. vm_refl. Qed.
Lemma D_71e1c : decode_any W_71e1c = Some (OpImm32 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71e20 : bv 32 := 0x00008067.
Lemma F_71e20 : fetch_word AsanUbsan.M.loaded_segments (0x71e20 : word) = Some W_71e20.
Proof. vm_refl. Qed.
Lemma D_71e20 : decode_any W_71e20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71e24 : bv 32 := 0x0e900893.
Lemma F_71e24 : fetch_word AsanUbsan.M.loaded_segments (0x71e24 : word) = Some W_71e24.
Proof. vm_refl. Qed.
Lemma D_71e24 : decode_any W_71e24 = Some (OpImm ALU_ADD 17 0 233, 4%Z).
Proof. vm_refl. Qed.

Definition W_71e28 : bv 32 := 0x00000073.
Lemma F_71e28 : fetch_word AsanUbsan.M.loaded_segments (0x71e28 : word) = Some W_71e28.
Proof. vm_refl. Qed.
Lemma D_71e28 : decode_any W_71e28 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_71e28 : is_ecall W_71e28 = true.
Proof. reflexivity. Qed.

Definition W_71e2c : bv 32 := 0x0005051b.
Lemma F_71e2c : fetch_word AsanUbsan.M.loaded_segments (0x71e2c : word) = Some W_71e2c.
Proof. vm_refl. Qed.
Lemma D_71e2c : decode_any W_71e2c = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_71e30 : bv 32 := 0x00008067.
Lemma F_71e30 : fetch_word AsanUbsan.M.loaded_segments (0x71e30 : word) = Some W_71e30.
Proof. vm_refl. Qed.
Lemma D_71e30 : decode_any W_71e30 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
