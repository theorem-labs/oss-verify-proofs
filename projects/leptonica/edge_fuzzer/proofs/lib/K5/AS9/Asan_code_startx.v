(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1a5cdc : bv 32 := 0x0004b503.
Lemma F_1a5cdc : fetch_word Asan.M.loaded_segments (0x1a5e20 : word) = Some W_1a5cdc.
Proof. vm_refl. Qed.
Lemma D_1a5cdc : decode_any W_1a5cdc = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a5ce0 : bv 32 := 0x00848493.
Lemma F_1a5ce0 : fetch_word Asan.M.loaded_segments (0x1a5e24 : word) = Some W_1a5ce0.
Proof. vm_refl. Qed.
Lemma D_1a5ce0 : decode_any W_1a5ce0 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a5ce4 : bv 32 := 0xfe051ce3.
Lemma F_1a5ce4 : fetch_word Asan.M.loaded_segments (0x1a5e28 : word) = Some W_1a5ce4.
Proof. vm_refl. Qed.
Lemma D_1a5ce4 : decode_any W_1a5ce4 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_1a5d98 : bv 32 := 0x00b53023.
Lemma F_1a5d98 : fetch_word Asan.M.loaded_segments (0x1a5edc : word) = Some W_1a5d98.
Proof. vm_refl. Qed.
Lemma D_1a5d98 : decode_any W_1a5d98 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a5d9c : bv 32 := 0x00158593.
Lemma F_1a5d9c : fetch_word Asan.M.loaded_segments (0x1a5ee0 : word) = Some W_1a5d9c.
Proof. vm_refl. Qed.
Lemma D_1a5d9c : decode_any W_1a5d9c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a5da0 : bv 32 := 0xfff5c683.
Lemma F_1a5da0 : fetch_word Asan.M.loaded_segments (0x1a5ee4 : word) = Some W_1a5da0.
Proof. vm_refl. Qed.
Lemma D_1a5da0 : decode_any W_1a5da0 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a5da4 : bv 32 := 0xfec68ae3.
Lemma F_1a5da4 : fetch_word Asan.M.loaded_segments (0x1a5ee8 : word) = Some W_1a5da4.
Proof. vm_refl. Qed.
Lemma D_1a5da4 : decode_any W_1a5da4 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a5da8 : bv 32 := 0xfe069ae3.
Lemma F_1a5da8 : fetch_word Asan.M.loaded_segments (0x1a5eec : word) = Some W_1a5da8.
Proof. vm_refl. Qed.
Lemma D_1a5da8 : decode_any W_1a5da8 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
