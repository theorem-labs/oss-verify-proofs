(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_bca80 : bv 32 := 0x0004b503.
Lemma F_bca80 : fetch_word Asan.M.loaded_segments (0xbca80 : word) = Some W_bca80.
Proof. vm_refl. Qed.
Lemma D_bca80 : decode_any W_bca80 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bca84 : bv 32 := 0x00848493.
Lemma F_bca84 : fetch_word Asan.M.loaded_segments (0xbca84 : word) = Some W_bca84.
Proof. vm_refl. Qed.
Lemma D_bca84 : decode_any W_bca84 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bca88 : bv 32 := 0xfe051ce3.
Lemma F_bca88 : fetch_word Asan.M.loaded_segments (0xbca88 : word) = Some W_bca88.
Proof. vm_refl. Qed.
Lemma D_bca88 : decode_any W_bca88 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcb3c : bv 32 := 0x00b53023.
Lemma F_bcb3c : fetch_word Asan.M.loaded_segments (0xbcb3c : word) = Some W_bcb3c.
Proof. vm_refl. Qed.
Lemma D_bcb3c : decode_any W_bcb3c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcb40 : bv 32 := 0x00158593.
Lemma F_bcb40 : fetch_word Asan.M.loaded_segments (0xbcb40 : word) = Some W_bcb40.
Proof. vm_refl. Qed.
Lemma D_bcb40 : decode_any W_bcb40 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcb44 : bv 32 := 0xfff5c683.
Lemma F_bcb44 : fetch_word Asan.M.loaded_segments (0xbcb44 : word) = Some W_bcb44.
Proof. vm_refl. Qed.
Lemma D_bcb44 : decode_any W_bcb44 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcb48 : bv 32 := 0xfec68ae3.
Lemma F_bcb48 : fetch_word Asan.M.loaded_segments (0xbcb48 : word) = Some W_bcb48.
Proof. vm_refl. Qed.
Lemma D_bcb48 : decode_any W_bcb48 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bcb4c : bv 32 := 0xfe069ae3.
Lemma F_bcb4c : fetch_word Asan.M.loaded_segments (0xbcb4c : word) = Some W_bcb4c.
Proof. vm_refl. Qed.
Lemma D_bcb4c : decode_any W_bcb4c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
