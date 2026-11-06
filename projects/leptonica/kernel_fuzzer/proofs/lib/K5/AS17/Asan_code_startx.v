(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_b43f8 : bv 32 := 0x0004b503.
Lemma F_b43f8 : fetch_word Asan.M.loaded_segments (0xb5f1c : word) = Some W_b43f8.
Proof. vm_refl. Qed.
Lemma D_b43f8 : decode_any W_b43f8 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b43fc : bv 32 := 0x00848493.
Lemma F_b43fc : fetch_word Asan.M.loaded_segments (0xb5f20 : word) = Some W_b43fc.
Proof. vm_refl. Qed.
Lemma D_b43fc : decode_any W_b43fc = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b4400 : bv 32 := 0xfe051ce3.
Lemma F_b4400 : fetch_word Asan.M.loaded_segments (0xb5f24 : word) = Some W_b4400.
Proof. vm_refl. Qed.
Lemma D_b4400 : decode_any W_b4400 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_b44b4 : bv 32 := 0x00b53023.
Lemma F_b44b4 : fetch_word Asan.M.loaded_segments (0xb5fd8 : word) = Some W_b44b4.
Proof. vm_refl. Qed.
Lemma D_b44b4 : decode_any W_b44b4 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b44b8 : bv 32 := 0x00158593.
Lemma F_b44b8 : fetch_word Asan.M.loaded_segments (0xb5fdc : word) = Some W_b44b8.
Proof. vm_refl. Qed.
Lemma D_b44b8 : decode_any W_b44b8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b44bc : bv 32 := 0xfff5c683.
Lemma F_b44bc : fetch_word Asan.M.loaded_segments (0xb5fe0 : word) = Some W_b44bc.
Proof. vm_refl. Qed.
Lemma D_b44bc : decode_any W_b44bc = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b44c0 : bv 32 := 0xfec68ae3.
Lemma F_b44c0 : fetch_word Asan.M.loaded_segments (0xb5fe4 : word) = Some W_b44c0.
Proof. vm_refl. Qed.
Lemma D_b44c0 : decode_any W_b44c0 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b44c4 : bv 32 := 0xfe069ae3.
Lemma F_b44c4 : fetch_word Asan.M.loaded_segments (0xb5fe8 : word) = Some W_b44c4.
Proof. vm_refl. Qed.
Lemma D_b44c4 : decode_any W_b44c4 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
