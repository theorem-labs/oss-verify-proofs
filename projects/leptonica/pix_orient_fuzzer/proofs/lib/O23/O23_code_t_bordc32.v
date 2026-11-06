(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6f064 : bv 32 := 0x00050e63.
Lemma F_6f064 : fetch_word Plain.M.loaded_segments (0x6f0bc : word) = Some W_6f064.
Proof. vm_refl. Qed.
Lemma D_6f064 : decode_any W_6f064 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f068 : bv 32 := 0x04058263.
Lemma F_6f068 : fetch_word Plain.M.loaded_segments (0x6f0c0 : word) = Some W_6f068.
Proof. vm_refl. Qed.
Lemma D_6f068 : decode_any W_6f068 = Some (Branch BC_EQ 11 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f06c : bv 32 := 0x00060793.
Lemma F_6f06c : fetch_word Plain.M.loaded_segments (0x6f0c4 : word) = Some W_6f06c.
Proof. vm_refl. Qed.
Lemma D_6f06c : decode_any W_6f06c = Some (OpImm ALU_ADD 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f070 : bv 32 := 0x00058613.
Lemma F_6f070 : fetch_word Plain.M.loaded_segments (0x6f0c8 : word) = Some W_6f070.
Proof. vm_refl. Qed.
Lemma D_6f070 : decode_any W_6f070 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f074 : bv 32 := 0x00058693.
Lemma F_6f074 : fetch_word Plain.M.loaded_segments (0x6f0cc : word) = Some W_6f074.
Proof. vm_refl. Qed.
Lemma D_6f074 : decode_any W_6f074 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f078 : bv 32 := 0x00058713.
Lemma F_6f078 : fetch_word Plain.M.loaded_segments (0x6f0d0 : word) = Some W_6f078.
Proof. vm_refl. Qed.
Lemma D_6f078 : decode_any W_6f078 = Some (OpImm ALU_ADD 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f07c : bv 32 := 0x03c0006f.
Lemma F_6f07c : fetch_word Plain.M.loaded_segments (0x6f0d4 : word) = Some W_6f07c.
Proof. vm_refl. Qed.
Lemma D_6f07c : decode_any W_6f07c = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

