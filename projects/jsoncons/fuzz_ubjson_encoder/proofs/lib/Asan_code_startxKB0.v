(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_11e0a8 : bv 32 := 0x0004b503.
Lemma F_11e0a8 : fetch_word AsanUbsan.M.loaded_segments (0x11e0f8 : word) = Some W_11e0a8.
Proof. vm_refl. Qed.
Lemma D_11e0a8 : decode_any W_11e0a8 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11e0ac : bv 32 := 0x00848493.
Lemma F_11e0ac : fetch_word AsanUbsan.M.loaded_segments (0x11e0fc : word) = Some W_11e0ac.
Proof. vm_refl. Qed.
Lemma D_11e0ac : decode_any W_11e0ac = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11e0b0 : bv 32 := 0xfe051ce3.
Lemma F_11e0b0 : fetch_word AsanUbsan.M.loaded_segments (0x11e100 : word) = Some W_11e0b0.
Proof. vm_refl. Qed.
Lemma D_11e0b0 : decode_any W_11e0b0 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11e164 : bv 32 := 0x00b53023.
Lemma F_11e164 : fetch_word AsanUbsan.M.loaded_segments (0x11e1b4 : word) = Some W_11e164.
Proof. vm_refl. Qed.
Lemma D_11e164 : decode_any W_11e164 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11e168 : bv 32 := 0x00158593.
Lemma F_11e168 : fetch_word AsanUbsan.M.loaded_segments (0x11e1b8 : word) = Some W_11e168.
Proof. vm_refl. Qed.
Lemma D_11e168 : decode_any W_11e168 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11e16c : bv 32 := 0xfff5c683.
Lemma F_11e16c : fetch_word AsanUbsan.M.loaded_segments (0x11e1bc : word) = Some W_11e16c.
Proof. vm_refl. Qed.
Lemma D_11e16c : decode_any W_11e16c = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11e170 : bv 32 := 0xfec68ae3.
Lemma F_11e170 : fetch_word AsanUbsan.M.loaded_segments (0x11e1c0 : word) = Some W_11e170.
Proof. vm_refl. Qed.
Lemma D_11e170 : decode_any W_11e170 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11e174 : bv 32 := 0xfe069ae3.
Lemma F_11e174 : fetch_word AsanUbsan.M.loaded_segments (0x11e1c4 : word) = Some W_11e174.
Proof. vm_refl. Qed.
Lemma D_11e174 : decode_any W_11e174 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
