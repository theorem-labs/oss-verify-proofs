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

Definition W_ad358 : bv 32 := 0x00052583.
Lemma F_ad358 : fetch_word Plain.M.loaded_segments (0xad3a4 : word) = Some W_ad358.
Proof. vm_refl. Qed.
Lemma D_ad358 : decode_any W_ad358 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_ad35c : bv 32 := 0x0005c463.
Lemma F_ad35c : fetch_word Plain.M.loaded_segments (0xad3a8 : word) = Some W_ad35c.
Proof. vm_refl. Qed.
Lemma D_ad35c : decode_any W_ad35c = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_ad360 : bv 32 := 0x00008067.
Lemma F_ad360 : fetch_word Plain.M.loaded_segments (0xad3ac : word) = Some W_ad360.
Proof. vm_refl. Qed.
Lemma D_ad360 : decode_any W_ad360 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
