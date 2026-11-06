(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_abc94 : bv 32 := 0x40355513.
Lemma F_abc94 : fetch_word Asan.M.loaded_segments (0xabce4 : word) = Some W_abc94.
Proof. vm_refl. Qed.
Lemma D_abc94 : decode_any W_abc94 = Some (ShiftImm ALU_SRA 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_abc98 : bv 32 := 0x02c505b3.
Lemma F_abc98 : fetch_word Asan.M.loaded_segments (0xabce8 : word) = Some W_abc98.
Proof. vm_refl. Qed.
Lemma D_abc98 : decode_any W_abc98 = Some (Mul M_MUL 11 10 12, 4%Z).
Proof. vm_refl. Qed.
