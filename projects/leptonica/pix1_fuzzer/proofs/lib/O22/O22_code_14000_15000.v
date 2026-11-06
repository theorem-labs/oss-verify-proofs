(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.H Require GcFlushS22.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix1_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_14040 : bv 32 := 0x00058513.
Lemma F_14040 : fetch_word Plain.M.loaded_segments (0x1413c : word) = Some W_14040.
Proof. vm_refl. Qed.
Lemma D_14040 : decode_any W_14040 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14044 : bv 32 := 0x01813083.
Lemma F_14044 : fetch_word Plain.M.loaded_segments (0x14140 : word) = Some W_14044.
Proof. vm_refl. Qed.
Lemma D_14044 : decode_any W_14044 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14048 : bv 32 := 0x01013403.
Lemma F_14048 : fetch_word Plain.M.loaded_segments (0x14144 : word) = Some W_14048.
Proof. vm_refl. Qed.
Lemma D_14048 : decode_any W_14048 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1404c : bv 32 := 0x00813483.
Lemma F_1404c : fetch_word Plain.M.loaded_segments (0x14148 : word) = Some W_1404c.
Proof. vm_refl. Qed.
Lemma D_1404c : decode_any W_1404c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14050 : bv 32 := 0x02010113.
Lemma F_14050 : fetch_word Plain.M.loaded_segments (0x1414c : word) = Some W_14050.
Proof. vm_refl. Qed.
Lemma D_14050 : decode_any W_14050 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14054 : bv 32 := 0x00008067.
Lemma F_14054 : fetch_word Plain.M.loaded_segments (0x14150 : word) = Some W_14054.
Proof. vm_refl. Qed.
Lemma D_14054 : decode_any W_14054 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14be0 : bv 32 := 0x0040006f.
Lemma F_14be0 : fetch_word Plain.M.loaded_segments (0x14cdc : word) = Some W_14be0.
Proof. vm_refl. Qed.
Lemma D_14be0 : decode_any W_14be0 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.
