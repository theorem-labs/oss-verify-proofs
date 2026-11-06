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
From OSSVerify.leptonica.grayquant_fuzzer.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_ccc40 : bv 32 := 0x0004b503.
Lemma F_ccc40 : fetch_word Asan.M.loaded_segments (0xcccb0 : word) = Some W_ccc40.
Proof. vm_refl. Qed.
Lemma D_ccc40 : decode_any W_ccc40 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ccc44 : bv 32 := 0x00848493.
Lemma F_ccc44 : fetch_word Asan.M.loaded_segments (0xcccb4 : word) = Some W_ccc44.
Proof. vm_refl. Qed.
Lemma D_ccc44 : decode_any W_ccc44 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ccc48 : bv 32 := 0xfe051ce3.
Lemma F_ccc48 : fetch_word Asan.M.loaded_segments (0xcccb8 : word) = Some W_ccc48.
Proof. vm_refl. Qed.
Lemma D_ccc48 : decode_any W_ccc48 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_cccfc : bv 32 := 0x00b53023.
Lemma F_cccfc : fetch_word Asan.M.loaded_segments (0xccd6c : word) = Some W_cccfc.
Proof. vm_refl. Qed.
Lemma D_cccfc : decode_any W_cccfc = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ccd00 : bv 32 := 0x00158593.
Lemma F_ccd00 : fetch_word Asan.M.loaded_segments (0xccd70 : word) = Some W_ccd00.
Proof. vm_refl. Qed.
Lemma D_ccd00 : decode_any W_ccd00 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ccd04 : bv 32 := 0xfff5c683.
Lemma F_ccd04 : fetch_word Asan.M.loaded_segments (0xccd74 : word) = Some W_ccd04.
Proof. vm_refl. Qed.
Lemma D_ccd04 : decode_any W_ccd04 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ccd08 : bv 32 := 0xfec68ae3.
Lemma F_ccd08 : fetch_word Asan.M.loaded_segments (0xccd78 : word) = Some W_ccd08.
Proof. vm_refl. Qed.
Lemma D_ccd08 : decode_any W_ccd08 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ccd0c : bv 32 := 0xfe069ae3.
Lemma F_ccd0c : fetch_word Asan.M.loaded_segments (0xccd7c : word) = Some W_ccd0c.
Proof. vm_refl. Qed.
Lemma D_ccd0c : decode_any W_ccd0c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
