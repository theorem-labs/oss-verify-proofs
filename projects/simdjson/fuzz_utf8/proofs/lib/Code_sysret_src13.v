(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_b33e0 : bv 32 := 0xfffff5b7.
Lemma F_b33e0 : fetch_word Plain.M.loaded_segments (0xb3598 : word) = Some W_b33e0.
Proof. vm_refl. Qed.
Lemma D_b33e0 : decode_any W_b33e0 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b33e4 : bv 32 := 0x0015859b.
Lemma F_b33e4 : fetch_word Plain.M.loaded_segments (0xb359c : word) = Some W_b33e4.
Proof. vm_refl. Qed.
Lemma D_b33e4 : decode_any W_b33e4 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b33e8 : bv 32 := 0x02b56663.
Lemma F_b33e8 : fetch_word Plain.M.loaded_segments (0xb35a0 : word) = Some W_b33e8.
Proof. vm_refl. Qed.
Lemma D_b33e8 : decode_any W_b33e8 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b33ec : bv 32 := 0xff010113.
Lemma F_b33ec : fetch_word Plain.M.loaded_segments (0xb35a4 : word) = Some W_b33ec.
Proof. vm_refl. Qed.
Lemma D_b33ec : decode_any W_b33ec = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b33f0 : bv 32 := 0x00113423.
Lemma F_b33f0 : fetch_word Plain.M.loaded_segments (0xb35a8 : word) = Some W_b33f0.
Proof. vm_refl. Qed.
Lemma D_b33f0 : decode_any W_b33f0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b33f4 : bv 32 := 0x00813023.
Lemma F_b33f4 : fetch_word Plain.M.loaded_segments (0xb35ac : word) = Some W_b33f4.
Proof. vm_refl. Qed.
Lemma D_b33f4 : decode_any W_b33f4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b33f8 : bv 32 := 0x40a0043b.
Lemma F_b33f8 : fetch_word Plain.M.loaded_segments (0xb35b0 : word) = Some W_b33f8.
Proof. vm_refl. Qed.
Lemma D_b33f8 : decode_any W_b33f8 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b33fc : bv 32 := 0xa8dff0ef.
Lemma F_b33fc : fetch_word Plain.M.loaded_segments (0xb35b4 : word) = Some W_b33fc.
Proof. vm_refl. Qed.
Lemma D_b33fc : decode_any W_b33fc = Some (Jal 1 2095756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b3400 : bv 32 := 0x00852023.
Lemma F_b3400 : fetch_word Plain.M.loaded_segments (0xb35b8 : word) = Some W_b3400.
Proof. vm_refl. Qed.
Lemma D_b3400 : decode_any W_b3400 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b3404 : bv 32 := 0xfff00513.
Lemma F_b3404 : fetch_word Plain.M.loaded_segments (0xb35bc : word) = Some W_b3404.
Proof. vm_refl. Qed.
Lemma D_b3404 : decode_any W_b3404 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b3408 : bv 32 := 0x00813083.
Lemma F_b3408 : fetch_word Plain.M.loaded_segments (0xb35c0 : word) = Some W_b3408.
Proof. vm_refl. Qed.
Lemma D_b3408 : decode_any W_b3408 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b340c : bv 32 := 0x00013403.
Lemma F_b340c : fetch_word Plain.M.loaded_segments (0xb35c4 : word) = Some W_b340c.
Proof. vm_refl. Qed.
Lemma D_b340c : decode_any W_b340c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b3410 : bv 32 := 0x01010113.
Lemma F_b3410 : fetch_word Plain.M.loaded_segments (0xb35c8 : word) = Some W_b3410.
Proof. vm_refl. Qed.
Lemma D_b3410 : decode_any W_b3410 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_b3414 : bv 32 := 0x00008067.
Lemma F_b3414 : fetch_word Plain.M.loaded_segments (0xb35cc : word) = Some W_b3414.
Proof. vm_refl. Qed.
Lemma D_b3414 : decode_any W_b3414 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
