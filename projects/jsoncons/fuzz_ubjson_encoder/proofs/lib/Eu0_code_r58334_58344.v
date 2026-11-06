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

Definition W_5a48c : bv 32 := 0x00054583.
Lemma F_5a48c : fetch_word Ubsan.M.loaded_segments (0x5a4e4 : word) = Some W_5a48c.
Proof. vm_refl. Qed.
Lemma D_5a48c : decode_any W_5a48c = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a490 : bv 32 := 0x0015f593.
Lemma F_5a490 : fetch_word Ubsan.M.loaded_segments (0x5a4e8 : word) = Some W_5a490.
Proof. vm_refl. Qed.
Lemma D_5a490 : decode_any W_5a490 = Some (OpImm ALU_AND 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a494 : bv 32 := 0x00059463.
Lemma F_5a494 : fetch_word Ubsan.M.loaded_segments (0x5a4ec : word) = Some W_5a494.
Proof. vm_refl. Qed.
Lemma D_5a494 : decode_any W_5a494 = Some (Branch BC_NE 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5a498 : bv 32 := 0x00008067.
Lemma F_5a498 : fetch_word Ubsan.M.loaded_segments (0x5a4f0 : word) = Some W_5a498.
Proof. vm_refl. Qed.
Lemma D_5a498 : decode_any W_5a498 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
