(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_229d0 : bv 32 := 0x00148a83.
Lemma F_229d0 : fetch_word Ubsan.M.loaded_segments (0x229d0 : word) = Some W_229d0.
Proof. vm_refl. Qed.
Lemma D_229d0 : decode_any W_229d0 = Some (Load SZ1 true 21 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229d4 : bv 32 := 0x0004c503.
Lemma F_229d4 : fetch_word Ubsan.M.loaded_segments (0x229d4 : word) = Some W_229d4.
Proof. vm_refl. Qed.
Lemma D_229d4 : decode_any W_229d4 = Some (Load SZ1 false 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229d8 : bv 32 := 0x039a9593.
Lemma F_229d8 : fetch_word Ubsan.M.loaded_segments (0x229d8 : word) = Some W_229d8.
Proof. vm_refl. Qed.
Lemma D_229d8 : decode_any W_229d8 = Some (ShiftImm ALU_SLL 11 21 57, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229dc : bv 32 := 0x0315d593.
Lemma F_229dc : fetch_word Ubsan.M.loaded_segments (0x229dc : word) = Some W_229dc.
Proof. vm_refl. Qed.
Lemma D_229dc : decode_any W_229dc = Some (ShiftImm ALU_SRL 11 11 49, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229e0 : bv 32 := 0x00a5e933.
Lemma F_229e0 : fetch_word Ubsan.M.loaded_segments (0x229e0 : word) = Some W_229e0.
Proof. vm_refl. Qed.
Lemma D_229e0 : decode_any W_229e0 = Some (Op ALU_OR 18 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_229e4 : bv 32 := 0x00690513.
Lemma F_229e4 : fetch_word Ubsan.M.loaded_segments (0x229e4 : word) = Some W_229e4.
Proof. vm_refl. Qed.
Lemma D_229e4 : decode_any W_229e4 = Some (OpImm ALU_ADD 10 18 6, 4%Z).
Proof. vm_refl. Qed.
