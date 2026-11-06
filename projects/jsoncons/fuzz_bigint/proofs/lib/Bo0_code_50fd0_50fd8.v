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

Definition W_50fd0 : bv 32 := 0xda0b9ae3.
Lemma F_50fd0 : fetch_word AsanUbsan.M.loaded_segments (0x50fd0 : word) = Some W_50fd0.
Proof. vm_refl. Qed.
Lemma D_50fd0 : decode_any W_50fd0 = Some (Branch BC_NE 23 0 7604, 4%Z).
Proof. vm_refl. Qed.

Definition W_50fd4 : bv 32 := 0xc89ff06f.
Lemma F_50fd4 : fetch_word AsanUbsan.M.loaded_segments (0x50fd4 : word) = Some W_50fd4.
Proof. vm_refl. Qed.
Lemma D_50fd4 : decode_any W_50fd4 = Some (Jal 0 2096264, 4%Z).
Proof. vm_refl. Qed.
