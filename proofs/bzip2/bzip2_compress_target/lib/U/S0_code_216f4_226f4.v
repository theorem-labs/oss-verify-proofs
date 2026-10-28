(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W_21a70 : bv 32 := 0xff010113.
Lemma F_21a70 : fetch_word Ubsan.M.loaded_segments (0x2bbdc : word) = Some W_21a70.
Proof. vm_refl. Qed.
Lemma D_21a70 : decode_any W_21a70 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21a74 : bv 32 := 0x00113423.
Lemma F_21a74 : fetch_word Ubsan.M.loaded_segments (0x2bbe0 : word) = Some W_21a74.
Proof. vm_refl. Qed.
Lemma D_21a74 : decode_any W_21a74 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21a78 : bv 32 := 0x00813023.
Lemma F_21a78 : fetch_word Ubsan.M.loaded_segments (0x2bbe4 : word) = Some W_21a78.
Proof. vm_refl. Qed.
Lemma D_21a78 : decode_any W_21a78 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21a7c : bv 32 := 0x00039517.
Lemma F_21a7c : fetch_word Ubsan.M.loaded_segments (0x2bbe8 : word) = Some W_21a7c.
Proof. vm_refl. Qed.
Lemma D_21a7c : decode_any W_21a7c = Some (Auipc 10 57, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21a80 : bv 32 := 0xca850413.
Lemma F_21a80 : fetch_word Ubsan.M.loaded_segments (0x2bbec : word) = Some W_21a80.
Proof. vm_refl. Qed.
Lemma D_21a80 : decode_any W_21a80 = Some (OpImm ALU_ADD 8 10 3240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21a84 : bv 32 := 0x00040513.
Lemma F_21a84 : fetch_word Ubsan.M.loaded_segments (0x2bbf0 : word) = Some W_21a84.
Proof. vm_refl. Qed.
Lemma D_21a84 : decode_any W_21a84 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21a88 : bv 32 := 0x0c4050ef.
Lemma F_21a88 : fetch_word Ubsan.M.loaded_segments (0x2bbf4 : word) = Some W_21a88.
Proof. vm_refl. Qed.
Lemma D_21a88 : decode_any W_21a88 = Some (Jal 1 20676, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21a8c : bv 32 := 0x00840513.
Lemma F_21a8c : fetch_word Ubsan.M.loaded_segments (0x2bbf8 : word) = Some W_21a8c.
Proof. vm_refl. Qed.
Lemma D_21a8c : decode_any W_21a8c = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21a90 : bv 32 := 0x00813083.
Lemma F_21a90 : fetch_word Ubsan.M.loaded_segments (0x2bbfc : word) = Some W_21a90.
Proof. vm_refl. Qed.
Lemma D_21a90 : decode_any W_21a90 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21a94 : bv 32 := 0x00013403.
Lemma F_21a94 : fetch_word Ubsan.M.loaded_segments (0x2bc00 : word) = Some W_21a94.
Proof. vm_refl. Qed.
Lemma D_21a94 : decode_any W_21a94 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21a98 : bv 32 := 0x01010113.
Lemma F_21a98 : fetch_word Ubsan.M.loaded_segments (0x2bc04 : word) = Some W_21a98.
Proof. vm_refl. Qed.
Lemma D_21a98 : decode_any W_21a98 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21a9c : bv 32 := 0x00008067.
Lemma F_21a9c : fetch_word Ubsan.M.loaded_segments (0x2bc08 : word) = Some W_21a9c.
Proof. vm_refl. Qed.
Lemma D_21a9c : decode_any W_21a9c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

