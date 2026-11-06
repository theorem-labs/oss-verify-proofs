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

Definition W_b3590 : bv 32 := 0x40375713.
Lemma F_b3590 : fetch_word AsanUbsan.M.loaded_segments (0xb35e0 : word) = Some W_b3590.
Proof. vm_refl. Qed.
Lemma D_b3590 : decode_any W_b3590 = Some (ShiftImm ALU_SRA 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_b3594 : bv 32 := 0x02c70633.
Lemma F_b3594 : fetch_word AsanUbsan.M.loaded_segments (0xb35e4 : word) = Some W_b3594.
Proof. vm_refl. Qed.
Lemma D_b3594 : decode_any W_b3594 = Some (Mul M_MUL 12 14 12, 4%Z).
Proof. vm_refl. Qed.
