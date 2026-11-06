(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_ae7d8 : bv 32 := 0x0004b503.
Lemma F_ae7d8 : fetch_word Asan.M.loaded_segments (0xae968 : word) = Some W_ae7d8.
Proof. vm_refl. Qed.
Lemma D_ae7d8 : decode_any W_ae7d8 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ae7dc : bv 32 := 0x00848493.
Lemma F_ae7dc : fetch_word Asan.M.loaded_segments (0xae96c : word) = Some W_ae7dc.
Proof. vm_refl. Qed.
Lemma D_ae7dc : decode_any W_ae7dc = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ae7e0 : bv 32 := 0xfe051ce3.
Lemma F_ae7e0 : fetch_word Asan.M.loaded_segments (0xae970 : word) = Some W_ae7e0.
Proof. vm_refl. Qed.
Lemma D_ae7e0 : decode_any W_ae7e0 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_ae894 : bv 32 := 0x00b53023.
Lemma F_ae894 : fetch_word Asan.M.loaded_segments (0xaea24 : word) = Some W_ae894.
Proof. vm_refl. Qed.
Lemma D_ae894 : decode_any W_ae894 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ae898 : bv 32 := 0x00158593.
Lemma F_ae898 : fetch_word Asan.M.loaded_segments (0xaea28 : word) = Some W_ae898.
Proof. vm_refl. Qed.
Lemma D_ae898 : decode_any W_ae898 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ae89c : bv 32 := 0xfff5c683.
Lemma F_ae89c : fetch_word Asan.M.loaded_segments (0xaea2c : word) = Some W_ae89c.
Proof. vm_refl. Qed.
Lemma D_ae89c : decode_any W_ae89c = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ae8a0 : bv 32 := 0xfec68ae3.
Lemma F_ae8a0 : fetch_word Asan.M.loaded_segments (0xaea30 : word) = Some W_ae8a0.
Proof. vm_refl. Qed.
Lemma D_ae8a0 : decode_any W_ae8a0 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ae8a4 : bv 32 := 0xfe069ae3.
Lemma F_ae8a4 : fetch_word Asan.M.loaded_segments (0xaea34 : word) = Some W_ae8a4.
Proof. vm_refl. Qed.
Lemma D_ae8a4 : decode_any W_ae8a4 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
