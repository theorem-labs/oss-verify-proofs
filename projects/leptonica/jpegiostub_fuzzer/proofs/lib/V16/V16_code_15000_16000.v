(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.H Require GcFlushU16.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.jpegiostub_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_150c4 : bv 32 := 0xff010113.
Lemma F_150c4 : fetch_word Ubsan.M.loaded_segments (0x151c8 : word) = Some W_150c4.
Proof. vm_refl. Qed.
Lemma D_150c4 : decode_any W_150c4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150c8 : bv 32 := 0x00113423.
Lemma F_150c8 : fetch_word Ubsan.M.loaded_segments (0x151cc : word) = Some W_150c8.
Proof. vm_refl. Qed.
Lemma D_150c8 : decode_any W_150c8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150cc : bv 32 := 0x00050863.
Lemma F_150cc : fetch_word Ubsan.M.loaded_segments (0x151d0 : word) = Some W_150cc.
Proof. vm_refl. Qed.
Lemma D_150cc : decode_any W_150cc = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_150d0 : bv 32 := 0x04058063.
Lemma F_150d0 : fetch_word Ubsan.M.loaded_segments (0x151d4 : word) = Some W_150d0.
Proof. vm_refl. Qed.
Lemma D_150d0 : decode_any W_150d0 = Some (Branch BC_EQ 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15110 : bv 32 := 0x00100593.
Lemma F_15110 : fetch_word Ubsan.M.loaded_segments (0x15214 : word) = Some W_15110.
Proof. vm_refl. Qed.
Lemma D_15110 : decode_any W_15110 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15114 : bv 32 := 0x968ff0ef.
Lemma F_15114 : fetch_word Ubsan.M.loaded_segments (0x15218 : word) = Some W_15114.
Proof. vm_refl. Qed.
Lemma D_15114 : decode_any W_15114 = Some (Jal 1 2093416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15118 : bv 32 := 0x00000513.
Lemma F_15118 : fetch_word Ubsan.M.loaded_segments (0x1521c : word) = Some W_15118.
Proof. vm_refl. Qed.
Lemma D_15118 : decode_any W_15118 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1511c : bv 32 := 0x0080006f.
Lemma F_1511c : fetch_word Ubsan.M.loaded_segments (0x15220 : word) = Some W_1511c.
Proof. vm_refl. Qed.
Lemma D_1511c : decode_any W_1511c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15124 : bv 32 := 0x00813083.
Lemma F_15124 : fetch_word Ubsan.M.loaded_segments (0x15228 : word) = Some W_15124.
Proof. vm_refl. Qed.
Lemma D_15124 : decode_any W_15124 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15128 : bv 32 := 0x01010113.
Lemma F_15128 : fetch_word Ubsan.M.loaded_segments (0x1522c : word) = Some W_15128.
Proof. vm_refl. Qed.
Lemma D_15128 : decode_any W_15128 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1512c : bv 32 := 0x00008067.
Lemma F_1512c : fetch_word Ubsan.M.loaded_segments (0x15230 : word) = Some W_1512c.
Proof. vm_refl. Qed.
Lemma D_1512c : decode_any W_1512c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15130 : bv 32 := 0x0040006f.
Lemma F_15130 : fetch_word Ubsan.M.loaded_segments (0x15234 : word) = Some W_15130.
Proof. vm_refl. Qed.
Lemma D_15130 : decode_any W_15130 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.
