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
Definition W_1a434 : bv 32 := 0x00b73023.
Lemma F_1a434 : fetch_word Plain.M.loaded_segments (0x1a48c : word) = Some W_1a434.
Proof. vm_refl. Qed.
Lemma D_1a434 : decode_any W_1a434 = Some (Store SZ8 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a438 : bv 32 := 0x00870713.
Lemma F_1a438 : fetch_word Plain.M.loaded_segments (0x1a490 : word) = Some W_1a438.
Proof. vm_refl. Qed.
Lemma D_1a438 : decode_any W_1a438 = Some (OpImm ALU_ADD 14 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a43c : bv 32 := 0x00c585b3.
Lemma F_1a43c : fetch_word Plain.M.loaded_segments (0x1a494 : word) = Some W_1a43c.
Proof. vm_refl. Qed.
Lemma D_1a43c : decode_any W_1a43c = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a440 : bv 32 := 0xfed71ae3.
Lemma F_1a440 : fetch_word Plain.M.loaded_segments (0x1a498 : word) = Some W_1a440.
Proof. vm_refl. Qed.
Lemma D_1a440 : decode_any W_1a440 = Some (Branch BC_NE 14 13 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a444 : bv 32 := 0x0640006f.
Lemma F_1a444 : fetch_word Plain.M.loaded_segments (0x1a49c : word) = Some W_1a444.
Proof. vm_refl. Qed.
Lemma D_1a444 : decode_any W_1a444 = Some (Jal 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a4a8 : bv 32 := 0x01813083.
Lemma F_1a4a8 : fetch_word Plain.M.loaded_segments (0x1a500 : word) = Some W_1a4a8.
Proof. vm_refl. Qed.
Lemma D_1a4a8 : decode_any W_1a4a8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a4ac : bv 32 := 0x01013403.
Lemma F_1a4ac : fetch_word Plain.M.loaded_segments (0x1a504 : word) = Some W_1a4ac.
Proof. vm_refl. Qed.
Lemma D_1a4ac : decode_any W_1a4ac = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a4b0 : bv 32 := 0x00813483.
Lemma F_1a4b0 : fetch_word Plain.M.loaded_segments (0x1a508 : word) = Some W_1a4b0.
Proof. vm_refl. Qed.
Lemma D_1a4b0 : decode_any W_1a4b0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a4b4 : bv 32 := 0x02010113.
Lemma F_1a4b4 : fetch_word Plain.M.loaded_segments (0x1a50c : word) = Some W_1a4b4.
Proof. vm_refl. Qed.
Lemma D_1a4b4 : decode_any W_1a4b4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a4b8 : bv 32 := 0x00008067.
Lemma F_1a4b8 : fetch_word Plain.M.loaded_segments (0x1a510 : word) = Some W_1a4b8.
Proof. vm_refl. Qed.
Lemma D_1a4b8 : decode_any W_1a4b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
