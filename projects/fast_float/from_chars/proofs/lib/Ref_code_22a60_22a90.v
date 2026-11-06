(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_22a60 : bv 32 := 0x00052517.
Lemma F_22a60 : fetch_word Plain.M.loaded_segments (0x22a60 : word) = Some W_22a60.
Proof. vm_refl. Qed.
Lemma D_22a60 : decode_any W_22a60 = Some (Auipc 10 82, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a64 : bv 32 := 0x60454503.
Lemma F_22a64 : fetch_word Plain.M.loaded_segments (0x22a64 : word) = Some W_22a64.
Proof. vm_refl. Qed.
Lemma D_22a64 : decode_any W_22a64 = Some (Load SZ1 false 10 10 1540, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a68 : bv 32 := 0x00051463.
Lemma F_22a68 : fetch_word Plain.M.loaded_segments (0x22a68 : word) = Some W_22a68.
Proof. vm_refl. Qed.
Lemma D_22a68 : decode_any W_22a68 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a6c : bv 32 := 0x00008067.
Lemma F_22a6c : fetch_word Plain.M.loaded_segments (0x22a6c : word) = Some W_22a6c.
Proof. vm_refl. Qed.
Lemma D_22a6c : decode_any W_22a6c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a70 : bv 32 := 0xff010113.
Lemma F_22a70 : fetch_word Plain.M.loaded_segments (0x22a70 : word) = Some W_22a70.
Proof. vm_refl. Qed.
Lemma D_22a70 : decode_any W_22a70 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a74 : bv 32 := 0x00113423.
Lemma F_22a74 : fetch_word Plain.M.loaded_segments (0x22a74 : word) = Some W_22a74.
Proof. vm_refl. Qed.
Lemma D_22a74 : decode_any W_22a74 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a78 : bv 32 := 0x00041517.
Lemma F_22a78 : fetch_word Plain.M.loaded_segments (0x22a78 : word) = Some W_22a78.
Proof. vm_refl. Qed.
Lemma D_22a78 : decode_any W_22a78 = Some (Auipc 10 65, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a7c : bv 32 := 0x23853503.
Lemma F_22a7c : fetch_word Plain.M.loaded_segments (0x22a7c : word) = Some W_22a7c.
Proof. vm_refl. Qed.
Lemma D_22a7c : decode_any W_22a7c = Some (Load SZ8 true 10 10 568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a80 : bv 32 := 0x00053503.
Lemma F_22a80 : fetch_word Plain.M.loaded_segments (0x22a80 : word) = Some W_22a80.
Proof. vm_refl. Qed.
Lemma D_22a80 : decode_any W_22a80 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a84 : bv 32 := 0x3c9300ef.
Lemma F_22a84 : fetch_word Plain.M.loaded_segments (0x22a84 : word) = Some W_22a84.
Proof. vm_refl. Qed.
Lemma D_22a84 : decode_any W_22a84 = Some (Jal 1 199624, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a88 : bv 32 := 0x04d00513.
Lemma F_22a88 : fetch_word Plain.M.loaded_segments (0x22a88 : word) = Some W_22a88.
Proof. vm_refl. Qed.
Lemma D_22a88 : decode_any W_22a88 = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_22a8c : bv 32 := 0x6b93c0ef.
Lemma F_22a8c : fetch_word Plain.M.loaded_segments (0x22a8c : word) = Some W_22a8c.
Proof. vm_refl. Qed.
Lemma D_22a8c : decode_any W_22a8c = Some (Jal 1 249528, 4%Z).
Proof. vm_refl. Qed.
