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
From OSSVerify.leptonica.fhmtgen_fuzzer.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_cfd58 : bv 32 := 0x0004b503.
Lemma F_cfd58 : fetch_word Asan.M.loaded_segments (0xcfec8 : word) = Some W_cfd58.
Proof. vm_refl. Qed.
Lemma D_cfd58 : decode_any W_cfd58 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cfd5c : bv 32 := 0x00848493.
Lemma F_cfd5c : fetch_word Asan.M.loaded_segments (0xcfecc : word) = Some W_cfd5c.
Proof. vm_refl. Qed.
Lemma D_cfd5c : decode_any W_cfd5c = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cfd60 : bv 32 := 0xfe051ce3.
Lemma F_cfd60 : fetch_word Asan.M.loaded_segments (0xcfed0 : word) = Some W_cfd60.
Proof. vm_refl. Qed.
Lemma D_cfd60 : decode_any W_cfd60 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_cfe14 : bv 32 := 0x00b53023.
Lemma F_cfe14 : fetch_word Asan.M.loaded_segments (0xcff84 : word) = Some W_cfe14.
Proof. vm_refl. Qed.
Lemma D_cfe14 : decode_any W_cfe14 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cfe18 : bv 32 := 0x00158593.
Lemma F_cfe18 : fetch_word Asan.M.loaded_segments (0xcff88 : word) = Some W_cfe18.
Proof. vm_refl. Qed.
Lemma D_cfe18 : decode_any W_cfe18 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cfe1c : bv 32 := 0xfff5c683.
Lemma F_cfe1c : fetch_word Asan.M.loaded_segments (0xcff8c : word) = Some W_cfe1c.
Proof. vm_refl. Qed.
Lemma D_cfe1c : decode_any W_cfe1c = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cfe20 : bv 32 := 0xfec68ae3.
Lemma F_cfe20 : fetch_word Asan.M.loaded_segments (0xcff90 : word) = Some W_cfe20.
Proof. vm_refl. Qed.
Lemma D_cfe20 : decode_any W_cfe20 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cfe24 : bv 32 := 0xfe069ae3.
Lemma F_cfe24 : fetch_word Asan.M.loaded_segments (0xcff94 : word) = Some W_cfe24.
Proof. vm_refl. Qed.
Lemma D_cfe24 : decode_any W_cfe24 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
