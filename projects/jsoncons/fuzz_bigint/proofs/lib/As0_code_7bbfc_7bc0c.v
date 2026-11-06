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

Definition W_7bbfc : bv 32 := 0x00058513.
Lemma F_7bbfc : fetch_word Asan.M.loaded_segments (0x7bbfc : word) = Some W_7bbfc.
Proof. vm_refl. Qed.
Lemma D_7bbfc : decode_any W_7bbfc = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bc00 : bv 32 := 0x00060593.
Lemma F_7bc00 : fetch_word Asan.M.loaded_segments (0x7bc00 : word) = Some W_7bc00.
Proof. vm_refl. Qed.
Lemma D_7bc00 : decode_any W_7bc00 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bc04 : bv 32 := 0x00068613.
Lemma F_7bc04 : fetch_word Asan.M.loaded_segments (0x7bc04 : word) = Some W_7bc04.
Proof. vm_refl. Qed.
Lemma D_7bc04 : decode_any W_7bc04 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bc08 : bv 32 := 0xc65f706f.
Lemma F_7bc08 : fetch_word Asan.M.loaded_segments (0x7bc08 : word) = Some W_7bc08.
Proof. vm_refl. Qed.
Lemma D_7bc08 : decode_any W_7bc08 = Some (Jal 0 2063460, 4%Z).
Proof. vm_refl. Qed.
