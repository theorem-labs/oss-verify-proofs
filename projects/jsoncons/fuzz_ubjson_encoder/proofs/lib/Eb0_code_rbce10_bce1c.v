(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_11e78c : bv 32 := 0x00020513.
Lemma F_11e78c : fetch_word AsanUbsan.M.loaded_segments (0x11e7d0 : word) = Some W_11e78c.
Proof. vm_refl. Qed.
Lemma D_11e78c : decode_any W_11e78c = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_11e790 : bv 32 := 0xf5c50513.
Lemma F_11e790 : fetch_word AsanUbsan.M.loaded_segments (0x11e7d4 : word) = Some W_11e790.
Proof. vm_refl. Qed.
Lemma D_11e790 : decode_any W_11e790 = Some (OpImm ALU_ADD 10 10 3932, 4%Z).
Proof. vm_refl. Qed.

Definition W_11e794 : bv 32 := 0x00008067.
Lemma F_11e794 : fetch_word AsanUbsan.M.loaded_segments (0x11e7d8 : word) = Some W_11e794.
Proof. vm_refl. Qed.
Lemma D_11e794 : decode_any W_11e794 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
