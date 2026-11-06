(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
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
From OSSVerify.simdjson.fuzz_parser.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_ee2a8 : bv 32 := 0x0004b503.
Lemma F_ee2a8 : fetch_word Asan.M.loaded_segments (0xee470 : word) = Some W_ee2a8.
Proof. vm_refl. Qed.
Lemma D_ee2a8 : decode_any W_ee2a8 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ee2ac : bv 32 := 0x00848493.
Lemma F_ee2ac : fetch_word Asan.M.loaded_segments (0xee474 : word) = Some W_ee2ac.
Proof. vm_refl. Qed.
Lemma D_ee2ac : decode_any W_ee2ac = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ee2b0 : bv 32 := 0xfe051ce3.
Lemma F_ee2b0 : fetch_word Asan.M.loaded_segments (0xee478 : word) = Some W_ee2b0.
Proof. vm_refl. Qed.
Lemma D_ee2b0 : decode_any W_ee2b0 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition W_ee364 : bv 32 := 0x00b53023.
Lemma F_ee364 : fetch_word Asan.M.loaded_segments (0xee52c : word) = Some W_ee364.
Proof. vm_refl. Qed.
Lemma D_ee364 : decode_any W_ee364 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ee368 : bv 32 := 0x00158593.
Lemma F_ee368 : fetch_word Asan.M.loaded_segments (0xee530 : word) = Some W_ee368.
Proof. vm_refl. Qed.
Lemma D_ee368 : decode_any W_ee368 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ee36c : bv 32 := 0xfff5c683.
Lemma F_ee36c : fetch_word Asan.M.loaded_segments (0xee534 : word) = Some W_ee36c.
Proof. vm_refl. Qed.
Lemma D_ee36c : decode_any W_ee36c = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ee370 : bv 32 := 0xfec68ae3.
Lemma F_ee370 : fetch_word Asan.M.loaded_segments (0xee538 : word) = Some W_ee370.
Proof. vm_refl. Qed.
Lemma D_ee370 : decode_any W_ee370 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ee374 : bv 32 := 0xfe069ae3.
Lemma F_ee374 : fetch_word Asan.M.loaded_segments (0xee53c : word) = Some W_ee374.
Proof. vm_refl. Qed.
Lemma D_ee374 : decode_any W_ee374 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.
