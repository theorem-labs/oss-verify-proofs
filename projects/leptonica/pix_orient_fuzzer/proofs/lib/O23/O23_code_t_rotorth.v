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
Definition W_87740 : bv 32 := 0x02050c63.
Lemma F_87740 : fetch_word Plain.M.loaded_segments (0x87798 : word) = Some W_87740.
Proof. vm_refl. Qed.
Lemma D_87740 : decode_any W_87740 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87744 : bv 32 := 0x00400613.
Lemma F_87744 : fetch_word Plain.M.loaded_segments (0x8779c : word) = Some W_87744.
Proof. vm_refl. Qed.
Lemma D_87744 : decode_any W_87744 = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_87748 : bv 32 := 0x06c5e263.
Lemma F_87748 : fetch_word Plain.M.loaded_segments (0x877a0 : word) = Some W_87748.
Proof. vm_refl. Qed.
Lemma D_87748 : decode_any W_87748 = Some (Branch BC_LTU 11 12 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_877ac : bv 32 := 0x00200613.
Lemma F_877ac : fetch_word Plain.M.loaded_segments (0x87804 : word) = Some W_877ac.
Proof. vm_refl. Qed.
Lemma D_877ac : decode_any W_877ac = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_877b0 : bv 32 := 0x02c58263.
Lemma F_877b0 : fetch_word Plain.M.loaded_segments (0x87808 : word) = Some W_877b0.
Proof. vm_refl. Qed.
Lemma D_877b0 : decode_any W_877b0 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_877b4 : bv 32 := 0x00100613.
Lemma F_877b4 : fetch_word Plain.M.loaded_segments (0x8780c : word) = Some W_877b4.
Proof. vm_refl. Qed.
Lemma D_877b4 : decode_any W_877b4 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_877b8 : bv 32 := 0x00c58a63.
Lemma F_877b8 : fetch_word Plain.M.loaded_segments (0x87810 : word) = Some W_877b8.
Proof. vm_refl. Qed.
Lemma D_877b8 : decode_any W_877b8 = Some (Branch BC_EQ 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_877bc : bv 32 := 0x02059263.
Lemma F_877bc : fetch_word Plain.M.loaded_segments (0x87814 : word) = Some W_877bc.
Proof. vm_refl. Qed.
Lemma D_877bc : decode_any W_877bc = Some (Branch BC_NE 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_877cc : bv 32 := 0x00100593.
Lemma F_877cc : fetch_word Plain.M.loaded_segments (0x87824 : word) = Some W_877cc.
Proof. vm_refl. Qed.
Lemma D_877cc : decode_any W_877cc = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_877d0 : bv 32 := 0x0180006f.
Lemma F_877d0 : fetch_word Plain.M.loaded_segments (0x87828 : word) = Some W_877d0.
Proof. vm_refl. Qed.
Lemma D_877d0 : decode_any W_877d0 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_877d4 : bv 32 := 0x00050593.
Lemma F_877d4 : fetch_word Plain.M.loaded_segments (0x8782c : word) = Some W_877d4.
Proof. vm_refl. Qed.
Lemma D_877d4 : decode_any W_877d4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_877d8 : bv 32 := 0x00000513.
Lemma F_877d8 : fetch_word Plain.M.loaded_segments (0x87830 : word) = Some W_877d8.
Proof. vm_refl. Qed.
Lemma D_877d8 : decode_any W_877d8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_877dc : bv 32 := 0x2f50006f.
Lemma F_877dc : fetch_word Plain.M.loaded_segments (0x87834 : word) = Some W_877dc.
Proof. vm_refl. Qed.
Lemma D_877dc : decode_any W_877dc = Some (Jal 0 2804, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_877e0 : bv 32 := 0xfff00593.
Lemma F_877e0 : fetch_word Plain.M.loaded_segments (0x87838 : word) = Some W_877e0.
Proof. vm_refl. Qed.
Lemma D_877e0 : decode_any W_877e0 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_877e4 : bv 32 := 0x0040006f.
Lemma F_877e4 : fetch_word Plain.M.loaded_segments (0x8783c : word) = Some W_877e4.
Proof. vm_refl. Qed.
Lemma D_877e4 : decode_any W_877e4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.
