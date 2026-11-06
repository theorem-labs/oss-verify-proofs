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
Definition W_925f0 : bv 32 := 0x00058463.
Lemma F_925f0 : fetch_word Plain.M.loaded_segments (0x92648 : word) = Some W_925f0.
Proof. vm_refl. Qed.
Lemma D_925f0 : decode_any W_925f0 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925f4 : bv 32 := 0x0005a023.
Lemma F_925f4 : fetch_word Plain.M.loaded_segments (0x9264c : word) = Some W_925f4.
Proof. vm_refl. Qed.
Lemma D_925f4 : decode_any W_925f4 = Some (Store SZ4 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925f8 : bv 32 := 0x00060463.
Lemma F_925f8 : fetch_word Plain.M.loaded_segments (0x92650 : word) = Some W_925f8.
Proof. vm_refl. Qed.
Lemma D_925f8 : decode_any W_925f8 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_925fc : bv 32 := 0x00062023.
Lemma F_925fc : fetch_word Plain.M.loaded_segments (0x92654 : word) = Some W_925fc.
Proof. vm_refl. Qed.
Lemma D_925fc : decode_any W_925fc = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92600 : bv 32 := 0x00068463.
Lemma F_92600 : fetch_word Plain.M.loaded_segments (0x92658 : word) = Some W_92600.
Proof. vm_refl. Qed.
Lemma D_92600 : decode_any W_92600 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92604 : bv 32 := 0x0006a023.
Lemma F_92604 : fetch_word Plain.M.loaded_segments (0x9265c : word) = Some W_92604.
Proof. vm_refl. Qed.
Lemma D_92604 : decode_any W_92604 = Some (Store SZ4 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92608 : bv 32 := 0x00070463.
Lemma F_92608 : fetch_word Plain.M.loaded_segments (0x92660 : word) = Some W_92608.
Proof. vm_refl. Qed.
Lemma D_92608 : decode_any W_92608 = Some (Branch BC_EQ 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9260c : bv 32 := 0x00072023.
Lemma F_9260c : fetch_word Plain.M.loaded_segments (0x92664 : word) = Some W_9260c.
Proof. vm_refl. Qed.
Lemma D_9260c : decode_any W_9260c = Some (Store SZ4 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92610 : bv 32 := 0x04050063.
Lemma F_92610 : fetch_word Plain.M.loaded_segments (0x92668 : word) = Some W_92610.
Proof. vm_refl. Qed.
Lemma D_92610 : decode_any W_92610 = Some (Branch BC_EQ 10 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92614 : bv 32 := 0x00058663.
Lemma F_92614 : fetch_word Plain.M.loaded_segments (0x9266c : word) = Some W_92614.
Proof. vm_refl. Qed.
Lemma D_92614 : decode_any W_92614 = Some (Branch BC_EQ 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92618 : bv 32 := 0x00052783.
Lemma F_92618 : fetch_word Plain.M.loaded_segments (0x92670 : word) = Some W_92618.
Proof. vm_refl. Qed.
Lemma D_92618 : decode_any W_92618 = Some (Load SZ4 true 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9261c : bv 32 := 0x00f5a023.
Lemma F_9261c : fetch_word Plain.M.loaded_segments (0x92674 : word) = Some W_9261c.
Proof. vm_refl. Qed.
Lemma D_9261c : decode_any W_9261c = Some (Store SZ4 11 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92620 : bv 32 := 0x00060663.
Lemma F_92620 : fetch_word Plain.M.loaded_segments (0x92678 : word) = Some W_92620.
Proof. vm_refl. Qed.
Lemma D_92620 : decode_any W_92620 = Some (Branch BC_EQ 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92624 : bv 32 := 0x00452583.
Lemma F_92624 : fetch_word Plain.M.loaded_segments (0x9267c : word) = Some W_92624.
Proof. vm_refl. Qed.
Lemma D_92624 : decode_any W_92624 = Some (Load SZ4 true 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92628 : bv 32 := 0x00b62023.
Lemma F_92628 : fetch_word Plain.M.loaded_segments (0x92680 : word) = Some W_92628.
Proof. vm_refl. Qed.
Lemma D_92628 : decode_any W_92628 = Some (Store SZ4 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9262c : bv 32 := 0x00068663.
Lemma F_9262c : fetch_word Plain.M.loaded_segments (0x92684 : word) = Some W_9262c.
Proof. vm_refl. Qed.
Lemma D_9262c : decode_any W_9262c = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92630 : bv 32 := 0x00852583.
Lemma F_92630 : fetch_word Plain.M.loaded_segments (0x92688 : word) = Some W_92630.
Proof. vm_refl. Qed.
Lemma D_92630 : decode_any W_92630 = Some (Load SZ4 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92634 : bv 32 := 0x00b6a023.
Lemma F_92634 : fetch_word Plain.M.loaded_segments (0x9268c : word) = Some W_92634.
Proof. vm_refl. Qed.
Lemma D_92634 : decode_any W_92634 = Some (Store SZ4 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92638 : bv 32 := 0x00000593.
Lemma F_92638 : fetch_word Plain.M.loaded_segments (0x92690 : word) = Some W_92638.
Proof. vm_refl. Qed.
Lemma D_92638 : decode_any W_92638 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9263c : bv 32 := 0x00070663.
Lemma F_9263c : fetch_word Plain.M.loaded_segments (0x92694 : word) = Some W_9263c.
Proof. vm_refl. Qed.
Lemma D_9263c : decode_any W_9263c = Some (Branch BC_EQ 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92640 : bv 32 := 0x00c52503.
Lemma F_92640 : fetch_word Plain.M.loaded_segments (0x92698 : word) = Some W_92640.
Proof. vm_refl. Qed.
Lemma D_92640 : decode_any W_92640 = Some (Load SZ4 true 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92644 : bv 32 := 0x00a72023.
Lemma F_92644 : fetch_word Plain.M.loaded_segments (0x9269c : word) = Some W_92644.
Proof. vm_refl. Qed.
Lemma D_92644 : decode_any W_92644 = Some (Store SZ4 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_92648 : bv 32 := 0x00058513.
Lemma F_92648 : fetch_word Plain.M.loaded_segments (0x926a0 : word) = Some W_92648.
Proof. vm_refl. Qed.
Lemma D_92648 : decode_any W_92648 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9264c : bv 32 := 0x00008067.
Lemma F_9264c : fetch_word Plain.M.loaded_segments (0x926a4 : word) = Some W_9264c.
Proof. vm_refl. Qed.
Lemma D_9264c : decode_any W_9264c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

