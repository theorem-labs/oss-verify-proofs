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

Definition W_4de50 : bv 32 := 0x51d0106f.
Lemma F_4de50 : fetch_word AsanUbsan.M.loaded_segments (0x4de50 : word) = Some W_4de50.
Proof. vm_refl. Qed.
Lemma D_4de50 : decode_any W_4de50 = Some (Jal 0 7452, 4%Z).
Proof. vm_refl. Qed.
