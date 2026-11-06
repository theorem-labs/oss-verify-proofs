(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_38d50 : bv 32 := 0xf00507d3.
Lemma F_38d50 : fetch_word Plain.M.loaded_segments (0x38da8 : word) = Some W_38d50.
Proof. vm_refl. Qed.
Lemma D_38d50 : decode_any W_38d50 = Some (Fmv FMV_F_X FMT_S 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_38d54 : bv 32 := 0x42078553.
Lemma F_38d54 : fetch_word Plain.M.loaded_segments (0x38dac : word) = Some W_38d54.
Proof. vm_refl. Qed.
Lemma D_38d54 : decode_any W_38d54 = Some (Fcvt FC_D FC_S 10 15 0, 4%Z).
Proof. vm_refl. Qed.
