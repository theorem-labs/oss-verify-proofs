(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_193d0 : bv 32 := 0xfe010113.
Lemma F_193d0 : fetch_word Plain.M.loaded_segments (0x19428 : word) = Some W_193d0.
Proof. vm_refl. Qed.
Lemma D_193d0 : decode_any W_193d0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193d4 : bv 32 := 0x00113c23.
Lemma F_193d4 : fetch_word Plain.M.loaded_segments (0x1942c : word) = Some W_193d4.
Proof. vm_refl. Qed.
Lemma D_193d4 : decode_any W_193d4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193d8 : bv 32 := 0x00813823.
Lemma F_193d8 : fetch_word Plain.M.loaded_segments (0x19430 : word) = Some W_193d8.
Proof. vm_refl. Qed.
Lemma D_193d8 : decode_any W_193d8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193dc : bv 32 := 0x00913423.
Lemma F_193dc : fetch_word Plain.M.loaded_segments (0x19434 : word) = Some W_193dc.
Proof. vm_refl. Qed.
Lemma D_193dc : decode_any W_193dc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193e0 : bv 32 := 0x06050863.
Lemma F_193e0 : fetch_word Plain.M.loaded_segments (0x19438 : word) = Some W_193e0.
Proof. vm_refl. Qed.
Lemma D_193e0 : decode_any W_193e0 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193e4 : bv 32 := 0x00053403.
Lemma F_193e4 : fetch_word Plain.M.loaded_segments (0x1943c : word) = Some W_193e4.
Proof. vm_refl. Qed.
Lemma D_193e4 : decode_any W_193e4 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193e8 : bv 32 := 0x0a040063.
Lemma F_193e8 : fetch_word Plain.M.loaded_segments (0x19440 : word) = Some W_193e8.
Proof. vm_refl. Qed.
Lemma D_193e8 : decode_any W_193e8 = Some (Branch BC_EQ 8 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193ec : bv 32 := 0x01440593.
Lemma F_193ec : fetch_word Plain.M.loaded_segments (0x19444 : word) = Some W_193ec.
Proof. vm_refl. Qed.
Lemma D_193ec : decode_any W_193ec = Some (OpImm ALU_ADD 11 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193f0 : bv 32 := 0xfff00613.
Lemma F_193f0 : fetch_word Plain.M.loaded_segments (0x19448 : word) = Some W_193f0.
Proof. vm_refl. Qed.
Lemma D_193f0 : decode_any W_193f0 = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193f4 : bv 32 := 0x06c5a5af.
Lemma F_193f4 : fetch_word Plain.M.loaded_segments (0x1944c : word) = Some W_193f4.
Proof. vm_refl. Qed.
Lemma D_193f4 : decode_any W_193f4 = Some (Amo AMO_ADD AW true true 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193f8 : bv 32 := 0x00100613.
Lemma F_193f8 : fetch_word Plain.M.loaded_segments (0x19450 : word) = Some W_193f8.
Proof. vm_refl. Qed.
Lemma D_193f8 : decode_any W_193f8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_193fc : bv 32 := 0x04c59663.
Lemma F_193fc : fetch_word Plain.M.loaded_segments (0x19454 : word) = Some W_193fc.
Proof. vm_refl. Qed.
Lemma D_193fc : decode_any W_193fc = Some (Branch BC_NE 11 12 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19448 : bv 32 := 0x00053023.
Lemma F_19448 : fetch_word Plain.M.loaded_segments (0x194a0 : word) = Some W_19448.
Proof. vm_refl. Qed.
Lemma D_19448 : decode_any W_19448 = Some (Store SZ8 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1944c : bv 32 := 0x03c0006f.
Lemma F_1944c : fetch_word Plain.M.loaded_segments (0x194a4 : word) = Some W_1944c.
Proof. vm_refl. Qed.
Lemma D_1944c : decode_any W_1944c = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19488 : bv 32 := 0x01813083.
Lemma F_19488 : fetch_word Plain.M.loaded_segments (0x194e0 : word) = Some W_19488.
Proof. vm_refl. Qed.
Lemma D_19488 : decode_any W_19488 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1948c : bv 32 := 0x01013403.
Lemma F_1948c : fetch_word Plain.M.loaded_segments (0x194e4 : word) = Some W_1948c.
Proof. vm_refl. Qed.
Lemma D_1948c : decode_any W_1948c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19490 : bv 32 := 0x00813483.
Lemma F_19490 : fetch_word Plain.M.loaded_segments (0x194e8 : word) = Some W_19490.
Proof. vm_refl. Qed.
Lemma D_19490 : decode_any W_19490 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19494 : bv 32 := 0x02010113.
Lemma F_19494 : fetch_word Plain.M.loaded_segments (0x194ec : word) = Some W_19494.
Proof. vm_refl. Qed.
Lemma D_19494 : decode_any W_19494 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_19498 : bv 32 := 0x00008067.
Lemma F_19498 : fetch_word Plain.M.loaded_segments (0x194f0 : word) = Some W_19498.
Proof. vm_refl. Qed.
Lemma D_19498 : decode_any W_19498 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
