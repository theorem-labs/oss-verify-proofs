(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.zstd.simple_decompress.images Require Import Asan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_bacc4 : bv 32 := 0x0004b503.
Lemma F_bacc4 : fetch_word Asan.M.loaded_segments (0xb6440 : word) = Some W_bacc4.
Proof. vm_refl. Qed.
Lemma D_bacc4 : decode_any W_bacc4 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bacc8 : bv 32 := 0x00848493.
Lemma F_bacc8 : fetch_word Asan.M.loaded_segments (0xb6444 : word) = Some W_bacc8.
Proof. vm_refl. Qed.
Lemma D_bacc8 : decode_any W_bacc8 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_baccc : bv 32 := 0xfe051ce3.
Lemma F_baccc : fetch_word Asan.M.loaded_segments (0xb6448 : word) = Some W_baccc.
Proof. vm_refl. Qed.
Lemma D_baccc : decode_any W_baccc = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_bad80 : bv 32 := 0x00b53023.
Lemma F_bad80 : fetch_word Asan.M.loaded_segments (0xb64fc : word) = Some W_bad80.
Proof. vm_refl. Qed.
Lemma D_bad80 : decode_any W_bad80 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bad84 : bv 32 := 0x00158593.
Lemma F_bad84 : fetch_word Asan.M.loaded_segments (0xb6500 : word) = Some W_bad84.
Proof. vm_refl. Qed.
Lemma D_bad84 : decode_any W_bad84 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bad88 : bv 32 := 0xfff5c683.
Lemma F_bad88 : fetch_word Asan.M.loaded_segments (0xb6504 : word) = Some W_bad88.
Proof. vm_refl. Qed.
Lemma D_bad88 : decode_any W_bad88 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bad8c : bv 32 := 0xfec68ae3.
Lemma F_bad8c : fetch_word Asan.M.loaded_segments (0xb6508 : word) = Some W_bad8c.
Proof. vm_refl. Qed.
Lemma D_bad8c : decode_any W_bad8c = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bad90 : bv 32 := 0xfe069ae3.
Lemma F_bad90 : fetch_word Asan.M.loaded_segments (0xb650c : word) = Some W_bad90.
Proof. vm_refl. Qed.
Lemma D_bad90 : decode_any W_bad90 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
