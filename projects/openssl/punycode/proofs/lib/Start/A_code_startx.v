(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.punycode.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_51e604 : bv 32 := 0x0004b503.
Lemma F_51e604 : fetch_word Asan.M.loaded_segments (0x51e644 : word) = Some W_51e604.
Proof. vm_refl. Qed.
Lemma D_51e604 : decode_any W_51e604 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e608 : bv 32 := 0x00848493.
Lemma F_51e608 : fetch_word Asan.M.loaded_segments (0x51e648 : word) = Some W_51e608.
Proof. vm_refl. Qed.
Lemma D_51e608 : decode_any W_51e608 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e60c : bv 32 := 0xfe051ce3.
Lemma F_51e60c : fetch_word Asan.M.loaded_segments (0x51e64c : word) = Some W_51e60c.
Proof. vm_refl. Qed.
Lemma D_51e60c : decode_any W_51e60c = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e6c0 : bv 32 := 0x00b53023.
Lemma F_51e6c0 : fetch_word Asan.M.loaded_segments (0x51e700 : word) = Some W_51e6c0.
Proof. vm_refl. Qed.
Lemma D_51e6c0 : decode_any W_51e6c0 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e6c4 : bv 32 := 0x00158593.
Lemma F_51e6c4 : fetch_word Asan.M.loaded_segments (0x51e704 : word) = Some W_51e6c4.
Proof. vm_refl. Qed.
Lemma D_51e6c4 : decode_any W_51e6c4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e6c8 : bv 32 := 0xfff5c683.
Lemma F_51e6c8 : fetch_word Asan.M.loaded_segments (0x51e708 : word) = Some W_51e6c8.
Proof. vm_refl. Qed.
Lemma D_51e6c8 : decode_any W_51e6c8 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e6cc : bv 32 := 0xfec68ae3.
Lemma F_51e6cc : fetch_word Asan.M.loaded_segments (0x51e70c : word) = Some W_51e6cc.
Proof. vm_refl. Qed.
Lemma D_51e6cc : decode_any W_51e6cc = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e6d0 : bv 32 := 0xfe069ae3.
Lemma F_51e6d0 : fetch_word Asan.M.loaded_segments (0x51e710 : word) = Some W_51e6d0.
Proof. vm_refl. Qed.
Lemma D_51e6d0 : decode_any W_51e6d0 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
