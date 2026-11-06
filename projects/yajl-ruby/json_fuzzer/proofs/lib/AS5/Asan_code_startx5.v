(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)


(* [comment removed for export] *)
Definition W_910ec : bv 32 := 0x0004b503.
Lemma F_910ec : fetch_word Asan.M.loaded_segments (0x9132c : word) = Some W_910ec.
Proof. vm_refl. Qed.
Lemma D_910ec : decode_any W_910ec = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_910f0 : bv 32 := 0x00848493.
Lemma F_910f0 : fetch_word Asan.M.loaded_segments (0x91330 : word) = Some W_910f0.
Proof. vm_refl. Qed.
Lemma D_910f0 : decode_any W_910f0 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_910f4 : bv 32 := 0xfe051ce3.
Lemma F_910f4 : fetch_word Asan.M.loaded_segments (0x91334 : word) = Some W_910f4.
Proof. vm_refl. Qed.
Lemma D_910f4 : decode_any W_910f4 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition W_911a8 : bv 32 := 0x00b53023.
Lemma F_911a8 : fetch_word Asan.M.loaded_segments (0x913e8 : word) = Some W_911a8.
Proof. vm_refl. Qed.
Lemma D_911a8 : decode_any W_911a8 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_911ac : bv 32 := 0x00158593.
Lemma F_911ac : fetch_word Asan.M.loaded_segments (0x913ec : word) = Some W_911ac.
Proof. vm_refl. Qed.
Lemma D_911ac : decode_any W_911ac = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_911b0 : bv 32 := 0xfff5c683.
Lemma F_911b0 : fetch_word Asan.M.loaded_segments (0x913f0 : word) = Some W_911b0.
Proof. vm_refl. Qed.
Lemma D_911b0 : decode_any W_911b0 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_911b4 : bv 32 := 0xfec68ae3.
Lemma F_911b4 : fetch_word Asan.M.loaded_segments (0x913f4 : word) = Some W_911b4.
Proof. vm_refl. Qed.
Lemma D_911b4 : decode_any W_911b4 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_911b8 : bv 32 := 0xfe069ae3.
Lemma F_911b8 : fetch_word Asan.M.loaded_segments (0x913f8 : word) = Some W_911b8.
Proof. vm_refl. Qed.
Lemma D_911b8 : decode_any W_911b8 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

