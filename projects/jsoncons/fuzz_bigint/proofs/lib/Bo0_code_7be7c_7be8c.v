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

Definition W_7be7c : bv 32 := 0x00058513.
Lemma F_7be7c : fetch_word AsanUbsan.M.loaded_segments (0x7be7c : word) = Some W_7be7c.
Proof. vm_refl. Qed.
Lemma D_7be7c : decode_any W_7be7c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be80 : bv 32 := 0x00060593.
Lemma F_7be80 : fetch_word AsanUbsan.M.loaded_segments (0x7be80 : word) = Some W_7be80.
Proof. vm_refl. Qed.
Lemma D_7be80 : decode_any W_7be80 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be84 : bv 32 := 0x00068613.
Lemma F_7be84 : fetch_word AsanUbsan.M.loaded_segments (0x7be84 : word) = Some W_7be84.
Proof. vm_refl. Qed.
Lemma D_7be84 : decode_any W_7be84 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be88 : bv 32 := 0xc65f706f.
Lemma F_7be88 : fetch_word AsanUbsan.M.loaded_segments (0x7be88 : word) = Some W_7be88.
Proof. vm_refl. Qed.
Lemma D_7be88 : decode_any W_7be88 = Some (Jal 0 2063460, 4%Z).
Proof. vm_refl. Qed.
