(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.hashtable.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_51c410 : bv 32 := 0x0004b503.
Lemma F_51c410 : fetch_word Asan.M.loaded_segments (0x51c470 : word) = Some W_51c410.
Proof. vm_refl. Qed.
Lemma D_51c410 : decode_any W_51c410 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c414 : bv 32 := 0x00848493.
Lemma F_51c414 : fetch_word Asan.M.loaded_segments (0x51c474 : word) = Some W_51c414.
Proof. vm_refl. Qed.
Lemma D_51c414 : decode_any W_51c414 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c418 : bv 32 := 0xfe051ce3.
Lemma F_51c418 : fetch_word Asan.M.loaded_segments (0x51c478 : word) = Some W_51c418.
Proof. vm_refl. Qed.
Lemma D_51c418 : decode_any W_51c418 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c4cc : bv 32 := 0x00b53023.
Lemma F_51c4cc : fetch_word Asan.M.loaded_segments (0x51c52c : word) = Some W_51c4cc.
Proof. vm_refl. Qed.
Lemma D_51c4cc : decode_any W_51c4cc = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c4d0 : bv 32 := 0x00158593.
Lemma F_51c4d0 : fetch_word Asan.M.loaded_segments (0x51c530 : word) = Some W_51c4d0.
Proof. vm_refl. Qed.
Lemma D_51c4d0 : decode_any W_51c4d0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c4d4 : bv 32 := 0xfff5c683.
Lemma F_51c4d4 : fetch_word Asan.M.loaded_segments (0x51c534 : word) = Some W_51c4d4.
Proof. vm_refl. Qed.
Lemma D_51c4d4 : decode_any W_51c4d4 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c4d8 : bv 32 := 0xfec68ae3.
Lemma F_51c4d8 : fetch_word Asan.M.loaded_segments (0x51c538 : word) = Some W_51c4d8.
Proof. vm_refl. Qed.
Lemma D_51c4d8 : decode_any W_51c4d8 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c4dc : bv 32 := 0xfe069ae3.
Lemma F_51c4dc : fetch_word Asan.M.loaded_segments (0x51c53c : word) = Some W_51c4dc.
Proof. vm_refl. Qed.
Lemma D_51c4dc : decode_any W_51c4dc = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
