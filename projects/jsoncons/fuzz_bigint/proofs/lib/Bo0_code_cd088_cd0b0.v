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

Definition W_cd088 : bv 32 := 0x00050893.
Lemma F_cd088 : fetch_word AsanUbsan.M.loaded_segments (0xcd088 : word) = Some W_cd088.
Proof. vm_refl. Qed.
Lemma D_cd088 : decode_any W_cd088 = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cd08c : bv 32 := 0x00058513.
Lemma F_cd08c : fetch_word AsanUbsan.M.loaded_segments (0xcd08c : word) = Some W_cd08c.
Proof. vm_refl. Qed.
Lemma D_cd08c : decode_any W_cd08c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cd090 : bv 32 := 0x00060593.
Lemma F_cd090 : fetch_word AsanUbsan.M.loaded_segments (0xcd090 : word) = Some W_cd090.
Proof. vm_refl. Qed.
Lemma D_cd090 : decode_any W_cd090 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cd094 : bv 32 := 0x00068613.
Lemma F_cd094 : fetch_word AsanUbsan.M.loaded_segments (0xcd094 : word) = Some W_cd094.
Proof. vm_refl. Qed.
Lemma D_cd094 : decode_any W_cd094 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cd098 : bv 32 := 0x00070693.
Lemma F_cd098 : fetch_word AsanUbsan.M.loaded_segments (0xcd098 : word) = Some W_cd098.
Proof. vm_refl. Qed.
Lemma D_cd098 : decode_any W_cd098 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cd09c : bv 32 := 0x00078713.
Lemma F_cd09c : fetch_word AsanUbsan.M.loaded_segments (0xcd09c : word) = Some W_cd09c.
Proof. vm_refl. Qed.
Lemma D_cd09c : decode_any W_cd09c = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cd0a0 : bv 32 := 0x00080793.
Lemma F_cd0a0 : fetch_word AsanUbsan.M.loaded_segments (0xcd0a0 : word) = Some W_cd0a0.
Proof. vm_refl. Qed.
Lemma D_cd0a0 : decode_any W_cd0a0 = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cd0a4 : bv 32 := 0x00000073.
Lemma F_cd0a4 : fetch_word AsanUbsan.M.loaded_segments (0xcd0a4 : word) = Some W_cd0a4.
Proof. vm_refl. Qed.
Lemma D_cd0a4 : decode_any W_cd0a4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_cd0a4 : is_ecall W_cd0a4 = true.
Proof. reflexivity. Qed.

Definition W_cd0a8 : bv 32 := 0x00008067.
Lemma F_cd0a8 : fetch_word AsanUbsan.M.loaded_segments (0xcd0a8 : word) = Some W_cd0a8.
Proof. vm_refl. Qed.
Lemma D_cd0a8 : decode_any W_cd0a8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cd0ac : bv 32 := 0xfddff06f.
Lemma F_cd0ac : fetch_word AsanUbsan.M.loaded_segments (0xcd0ac : word) = Some W_cd0ac.
Proof. vm_refl. Qed.
Lemma D_cd0ac : decode_any W_cd0ac = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.
