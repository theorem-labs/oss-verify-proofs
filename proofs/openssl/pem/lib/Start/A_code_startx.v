(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.pem.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_552d90 : bv 32 := 0x0004b503.
Lemma F_552d90 : fetch_word Asan.M.loaded_segments (0x51a66c : word) = Some W_552d90.
Proof. vm_refl. Qed.
Lemma D_552d90 : decode_any W_552d90 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_552d94 : bv 32 := 0x00848493.
Lemma F_552d94 : fetch_word Asan.M.loaded_segments (0x51a670 : word) = Some W_552d94.
Proof. vm_refl. Qed.
Lemma D_552d94 : decode_any W_552d94 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_552d98 : bv 32 := 0xfe051ce3.
Lemma F_552d98 : fetch_word Asan.M.loaded_segments (0x51a674 : word) = Some W_552d98.
Proof. vm_refl. Qed.
Lemma D_552d98 : decode_any W_552d98 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_552e4c : bv 32 := 0x00b53023.
Lemma F_552e4c : fetch_word Asan.M.loaded_segments (0x51a728 : word) = Some W_552e4c.
Proof. vm_refl. Qed.
Lemma D_552e4c : decode_any W_552e4c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_552e50 : bv 32 := 0x00158593.
Lemma F_552e50 : fetch_word Asan.M.loaded_segments (0x51a72c : word) = Some W_552e50.
Proof. vm_refl. Qed.
Lemma D_552e50 : decode_any W_552e50 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_552e54 : bv 32 := 0xfff5c683.
Lemma F_552e54 : fetch_word Asan.M.loaded_segments (0x51a730 : word) = Some W_552e54.
Proof. vm_refl. Qed.
Lemma D_552e54 : decode_any W_552e54 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_552e58 : bv 32 := 0xfec68ae3.
Lemma F_552e58 : fetch_word Asan.M.loaded_segments (0x51a734 : word) = Some W_552e58.
Proof. vm_refl. Qed.
Lemma D_552e58 : decode_any W_552e58 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_552e5c : bv 32 := 0xfe069ae3.
Lemma F_552e5c : fetch_word Asan.M.loaded_segments (0x51a738 : word) = Some W_552e5c.
Proof. vm_refl. Qed.
Lemma D_552e5c : decode_any W_552e5c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
