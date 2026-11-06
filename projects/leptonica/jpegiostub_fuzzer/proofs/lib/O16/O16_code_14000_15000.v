(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.H Require GcFlushS16.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.jpegiostub_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_14b24 : bv 32 := 0xff010113.
Lemma F_14b24 : fetch_word Plain.M.loaded_segments (0x14c20 : word) = Some W_14b24.
Proof. vm_refl. Qed.
Lemma D_14b24 : decode_any W_14b24 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b28 : bv 32 := 0x00113423.
Lemma F_14b28 : fetch_word Plain.M.loaded_segments (0x14c24 : word) = Some W_14b28.
Proof. vm_refl. Qed.
Lemma D_14b28 : decode_any W_14b28 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b2c : bv 32 := 0x00050863.
Lemma F_14b2c : fetch_word Plain.M.loaded_segments (0x14c28 : word) = Some W_14b2c.
Proof. vm_refl. Qed.
Lemma D_14b2c : decode_any W_14b2c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b30 : bv 32 := 0x04058063.
Lemma F_14b30 : fetch_word Plain.M.loaded_segments (0x14c2c : word) = Some W_14b30.
Proof. vm_refl. Qed.
Lemma D_14b30 : decode_any W_14b30 = Some (Branch BC_EQ 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b70 : bv 32 := 0x00100593.
Lemma F_14b70 : fetch_word Plain.M.loaded_segments (0x14c6c : word) = Some W_14b70.
Proof. vm_refl. Qed.
Lemma D_14b70 : decode_any W_14b70 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b74 : bv 32 := 0xbe0ff0ef.
Lemma F_14b74 : fetch_word Plain.M.loaded_segments (0x14c70 : word) = Some W_14b74.
Proof. vm_refl. Qed.
Lemma D_14b74 : decode_any W_14b74 = Some (Jal 1 2094048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b78 : bv 32 := 0x00000513.
Lemma F_14b78 : fetch_word Plain.M.loaded_segments (0x14c74 : word) = Some W_14b78.
Proof. vm_refl. Qed.
Lemma D_14b78 : decode_any W_14b78 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b7c : bv 32 := 0x0080006f.
Lemma F_14b7c : fetch_word Plain.M.loaded_segments (0x14c78 : word) = Some W_14b7c.
Proof. vm_refl. Qed.
Lemma D_14b7c : decode_any W_14b7c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b84 : bv 32 := 0x00813083.
Lemma F_14b84 : fetch_word Plain.M.loaded_segments (0x14c80 : word) = Some W_14b84.
Proof. vm_refl. Qed.
Lemma D_14b84 : decode_any W_14b84 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b88 : bv 32 := 0x01010113.
Lemma F_14b88 : fetch_word Plain.M.loaded_segments (0x14c84 : word) = Some W_14b88.
Proof. vm_refl. Qed.
Lemma D_14b88 : decode_any W_14b88 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b8c : bv 32 := 0x00008067.
Lemma F_14b8c : fetch_word Plain.M.loaded_segments (0x14c88 : word) = Some W_14b8c.
Proof. vm_refl. Qed.
Lemma D_14b8c : decode_any W_14b8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b90 : bv 32 := 0x0040006f.
Lemma F_14b90 : fetch_word Plain.M.loaded_segments (0x14c8c : word) = Some W_14b90.
Proof. vm_refl. Qed.
Lemma D_14b90 : decode_any W_14b90 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.
