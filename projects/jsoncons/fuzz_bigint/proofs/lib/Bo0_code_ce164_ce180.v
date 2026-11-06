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

Definition W_ce164 : bv 32 := 0x00020593.
Lemma F_ce164 : fetch_word AsanUbsan.M.loaded_segments (0xce164 : word) = Some W_ce164.
Proof. vm_refl. Qed.
Lemma D_ce164 : decode_any W_ce164 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ce168 : bv 32 := 0xfa85b583.
Lemma F_ce168 : fetch_word AsanUbsan.M.loaded_segments (0xce168 : word) = Some W_ce168.
Proof. vm_refl. Qed.
Lemma D_ce168 : decode_any W_ce168 = Some (Load SZ8 true 11 11 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_ce16c : bv 32 := 0x02051513.
Lemma F_ce16c : fetch_word AsanUbsan.M.loaded_segments (0xce16c : word) = Some W_ce16c.
Proof. vm_refl. Qed.
Lemma D_ce16c : decode_any W_ce16c = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_ce170 : bv 32 := 0x01d55513.
Lemma F_ce170 : fetch_word AsanUbsan.M.loaded_segments (0xce170 : word) = Some W_ce170.
Proof. vm_refl. Qed.
Lemma D_ce170 : decode_any W_ce170 = Some (ShiftImm ALU_SRL 10 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_ce174 : bv 32 := 0x00a58533.
Lemma F_ce174 : fetch_word AsanUbsan.M.loaded_segments (0xce174 : word) = Some W_ce174.
Proof. vm_refl. Qed.
Lemma D_ce174 : decode_any W_ce174 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_ce178 : bv 32 := 0x00053503.
Lemma F_ce178 : fetch_word AsanUbsan.M.loaded_segments (0xce178 : word) = Some W_ce178.
Proof. vm_refl. Qed.
Lemma D_ce178 : decode_any W_ce178 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ce17c : bv 32 := 0x00008067.
Lemma F_ce17c : fetch_word AsanUbsan.M.loaded_segments (0xce17c : word) = Some W_ce17c.
Proof. vm_refl. Qed.
Lemma D_ce17c : decode_any W_ce17c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
