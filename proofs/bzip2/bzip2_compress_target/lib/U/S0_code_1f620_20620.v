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
Definition W_1f620 : bv 32 := 0xfea5b823.
Lemma F_1f620 : fetch_word Ubsan.M.loaded_segments (0x29368 : word) = Some W_1f620.
Proof. vm_refl. Qed.
Lemma D_1f620 : decode_any W_1f620 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f624 : bv 32 := 0x00813083.
Lemma F_1f624 : fetch_word Ubsan.M.loaded_segments (0x2936c : word) = Some W_1f624.
Proof. vm_refl. Qed.
Lemma D_1f624 : decode_any W_1f624 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f628 : bv 32 := 0x01010113.
Lemma F_1f628 : fetch_word Ubsan.M.loaded_segments (0x29370 : word) = Some W_1f628.
Proof. vm_refl. Qed.
Lemma D_1f628 : decode_any W_1f628 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f62c : bv 32 := 0x00008067.
Lemma F_1f62c : fetch_word Ubsan.M.loaded_segments (0x29374 : word) = Some W_1f62c.
Proof. vm_refl. Qed.
Lemma D_1f62c : decode_any W_1f62c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f638 : bv 32 := 0xfffff5b7.
Lemma F_1f638 : fetch_word Ubsan.M.loaded_segments (0x29380 : word) = Some W_1f638.
Proof. vm_refl. Qed.
Lemma D_1f638 : decode_any W_1f638 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f63c : bv 32 := 0x0015859b.
Lemma F_1f63c : fetch_word Ubsan.M.loaded_segments (0x29384 : word) = Some W_1f63c.
Proof. vm_refl. Qed.
Lemma D_1f63c : decode_any W_1f63c = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f640 : bv 32 := 0x02b56663.
Lemma F_1f640 : fetch_word Ubsan.M.loaded_segments (0x29388 : word) = Some W_1f640.
Proof. vm_refl. Qed.
Lemma D_1f640 : decode_any W_1f640 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1f66c : bv 32 := 0x00008067.
Lemma F_1f66c : fetch_word Ubsan.M.loaded_segments (0x293b4 : word) = Some W_1f66c.
Proof. vm_refl. Qed.
Lemma D_1f66c : decode_any W_1f66c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

