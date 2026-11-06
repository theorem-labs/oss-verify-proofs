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
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_8d834 : bv 32 := 0x0004b503.
Lemma F_8d834 : fetch_word Asan.M.loaded_segments (0x8d834 : word) = Some W_8d834.
Proof. vm_refl. Qed.
Lemma D_8d834 : decode_any W_8d834 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d838 : bv 32 := 0x00848493.
Lemma F_8d838 : fetch_word Asan.M.loaded_segments (0x8d838 : word) = Some W_8d838.
Proof. vm_refl. Qed.
Lemma D_8d838 : decode_any W_8d838 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d83c : bv 32 := 0xfe051ce3.
Lemma F_8d83c : fetch_word Asan.M.loaded_segments (0x8d83c : word) = Some W_8d83c.
Proof. vm_refl. Qed.
Lemma D_8d83c : decode_any W_8d83c = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_8d8f0 : bv 32 := 0x00b53023.
Lemma F_8d8f0 : fetch_word Asan.M.loaded_segments (0x8d8f0 : word) = Some W_8d8f0.
Proof. vm_refl. Qed.
Lemma D_8d8f0 : decode_any W_8d8f0 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d8f4 : bv 32 := 0x00158593.
Lemma F_8d8f4 : fetch_word Asan.M.loaded_segments (0x8d8f4 : word) = Some W_8d8f4.
Proof. vm_refl. Qed.
Lemma D_8d8f4 : decode_any W_8d8f4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d8f8 : bv 32 := 0xfff5c683.
Lemma F_8d8f8 : fetch_word Asan.M.loaded_segments (0x8d8f8 : word) = Some W_8d8f8.
Proof. vm_refl. Qed.
Lemma D_8d8f8 : decode_any W_8d8f8 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d8fc : bv 32 := 0xfec68ae3.
Lemma F_8d8fc : fetch_word Asan.M.loaded_segments (0x8d8fc : word) = Some W_8d8fc.
Proof. vm_refl. Qed.
Lemma D_8d8fc : decode_any W_8d8fc = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d900 : bv 32 := 0xfe069ae3.
Lemma F_8d900 : fetch_word Asan.M.loaded_segments (0x8d900 : word) = Some W_8d900.
Proof. vm_refl. Qed.
Lemma D_8d900 : decode_any W_8d900 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
