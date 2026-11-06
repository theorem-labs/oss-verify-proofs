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

Definition W_8d628 : bv 32 := 0x0004a517.
Lemma F_8d628 : fetch_word AsanUbsan.M.loaded_segments (0x8d628 : word) = Some W_8d628.
Proof. vm_refl. Qed.
Lemma D_8d628 : decode_any W_8d628 = Some (Auipc 10 74, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d62c : bv 32 := 0xaf853503.
Lemma F_8d62c : fetch_word AsanUbsan.M.loaded_segments (0x8d62c : word) = Some W_8d62c.
Proof. vm_refl. Qed.
Lemma D_8d62c : decode_any W_8d62c = Some (Load SZ8 true 10 10 2808, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d630 : bv 32 := 0x00450533.
Lemma F_8d630 : fetch_word AsanUbsan.M.loaded_segments (0x8d630 : word) = Some W_8d630.
Proof. vm_refl. Qed.
Lemma D_8d630 : decode_any W_8d630 = Some (Op ALU_ADD 10 10 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d634 : bv 32 := 0x00052503.
Lemma F_8d634 : fetch_word AsanUbsan.M.loaded_segments (0x8d634 : word) = Some W_8d634.
Proof. vm_refl. Qed.
Lemma D_8d634 : decode_any W_8d634 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d638 : bv 32 := 0x00a02533.
Lemma F_8d638 : fetch_word AsanUbsan.M.loaded_segments (0x8d638 : word) = Some W_8d638.
Proof. vm_refl. Qed.
Lemma D_8d638 : decode_any W_8d638 = Some (Op ALU_SLT 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8d63c : bv 32 := 0x00008067.
Lemma F_8d63c : fetch_word AsanUbsan.M.loaded_segments (0x8d63c : word) = Some W_8d63c.
Proof. vm_refl. Qed.
Lemma D_8d63c : decode_any W_8d63c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
