(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_aeed4 : bv 32 := 0x00052583.
Lemma F_aeed4 : fetch_word Ubsan.M.loaded_segments (0xaef20 : word) = Some W_aeed4.
Proof. vm_refl. Qed.
Lemma D_aeed4 : decode_any W_aeed4 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_aeed8 : bv 32 := 0x0005c463.
Lemma F_aeed8 : fetch_word Ubsan.M.loaded_segments (0xaef24 : word) = Some W_aeed8.
Proof. vm_refl. Qed.
Lemma D_aeed8 : decode_any W_aeed8 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_aeedc : bv 32 := 0x00008067.
Lemma F_aeedc : fetch_word Ubsan.M.loaded_segments (0xaef28 : word) = Some W_aeedc.
Proof. vm_refl. Qed.
Lemma D_aeedc : decode_any W_aeedc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
