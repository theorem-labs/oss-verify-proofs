(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation ASEGS_I := ImgA.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_10b068 : bv 32 := 0x0004b503.
Lemma F_10b068 : fetch_word ASEGS_I (0x10b068 : word) = Some W_10b068.
Proof. vm_refl. Qed.
Lemma D_10b068 : decode_any W_10b068 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10b06c : bv 32 := 0x00848493.
Lemma F_10b06c : fetch_word ASEGS_I (0x10b06c : word) = Some W_10b06c.
Proof. vm_refl. Qed.
Lemma D_10b06c : decode_any W_10b06c = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10b070 : bv 32 := 0xfe051ce3.
Lemma F_10b070 : fetch_word ASEGS_I (0x10b070 : word) = Some W_10b070.
Proof. vm_refl. Qed.
Lemma D_10b070 : decode_any W_10b070 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10b124 : bv 32 := 0x00b53023.
Lemma F_10b124 : fetch_word ASEGS_I (0x10b124 : word) = Some W_10b124.
Proof. vm_refl. Qed.
Lemma D_10b124 : decode_any W_10b124 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10b128 : bv 32 := 0x00158593.
Lemma F_10b128 : fetch_word ASEGS_I (0x10b128 : word) = Some W_10b128.
Proof. vm_refl. Qed.
Lemma D_10b128 : decode_any W_10b128 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10b12c : bv 32 := 0xfff5c683.
Lemma F_10b12c : fetch_word ASEGS_I (0x10b12c : word) = Some W_10b12c.
Proof. vm_refl. Qed.
Lemma D_10b12c : decode_any W_10b12c = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10b130 : bv 32 := 0xfec68ae3.
Lemma F_10b130 : fetch_word ASEGS_I (0x10b130 : word) = Some W_10b130.
Proof. vm_refl. Qed.
Lemma D_10b130 : decode_any W_10b130 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10b134 : bv 32 := 0xfe069ae3.
Lemma F_10b134 : fetch_word ASEGS_I (0x10b134 : word) = Some W_10b134.
Proof. vm_refl. Qed.
Lemma D_10b134 : decode_any W_10b134 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
