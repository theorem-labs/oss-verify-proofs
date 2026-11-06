(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_cdc74 : bv 32 := 0x0004b503.
Lemma F_cdc74 : fetch_word Asan.M.loaded_segments (0xcded0 : word) = Some W_cdc74.
Proof. vm_refl. Qed.
Lemma D_cdc74 : decode_any W_cdc74 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cdc78 : bv 32 := 0x00848493.
Lemma F_cdc78 : fetch_word Asan.M.loaded_segments (0xcded4 : word) = Some W_cdc78.
Proof. vm_refl. Qed.
Lemma D_cdc78 : decode_any W_cdc78 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cdc7c : bv 32 := 0xfe051ce3.
Lemma F_cdc7c : fetch_word Asan.M.loaded_segments (0xcded8 : word) = Some W_cdc7c.
Proof. vm_refl. Qed.
Lemma D_cdc7c : decode_any W_cdc7c = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_cdd30 : bv 32 := 0x00b53023.
Lemma F_cdd30 : fetch_word Asan.M.loaded_segments (0xcdf8c : word) = Some W_cdd30.
Proof. vm_refl. Qed.
Lemma D_cdd30 : decode_any W_cdd30 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cdd34 : bv 32 := 0x00158593.
Lemma F_cdd34 : fetch_word Asan.M.loaded_segments (0xcdf90 : word) = Some W_cdd34.
Proof. vm_refl. Qed.
Lemma D_cdd34 : decode_any W_cdd34 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cdd38 : bv 32 := 0xfff5c683.
Lemma F_cdd38 : fetch_word Asan.M.loaded_segments (0xcdf94 : word) = Some W_cdd38.
Proof. vm_refl. Qed.
Lemma D_cdd38 : decode_any W_cdd38 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cdd3c : bv 32 := 0xfec68ae3.
Lemma F_cdd3c : fetch_word Asan.M.loaded_segments (0xcdf98 : word) = Some W_cdd3c.
Proof. vm_refl. Qed.
Lemma D_cdd3c : decode_any W_cdd3c = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_cdd40 : bv 32 := 0xfe069ae3.
Lemma F_cdd40 : fetch_word Asan.M.loaded_segments (0xcdf9c : word) = Some W_cdd40.
Proof. vm_refl. Qed.
Lemma D_cdd40 : decode_any W_cdd40 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
